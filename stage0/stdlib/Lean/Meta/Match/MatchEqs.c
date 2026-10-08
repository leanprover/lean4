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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
if (lean_obj_tag(v_a_50_) == 0)
{
lean_object* v___x_52_; 
v___x_52_ = l_List_reverse___redArg(v_a_51_);
return v___x_52_;
}
else
{
lean_object* v_head_53_; lean_object* v_tail_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_63_; 
v_head_53_ = lean_ctor_get(v_a_50_, 0);
v_tail_54_ = lean_ctor_get(v_a_50_, 1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_a_50_);
if (v_isSharedCheck_63_ == 0)
{
v___x_56_ = v_a_50_;
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_tail_54_);
lean_inc(v_head_53_);
lean_dec(v_a_50_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = l_Lean_MessageData_ofExpr(v_head_53_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v_a_51_);
lean_ctor_set(v___x_56_, 0, v___x_58_);
v___x_60_ = v___x_56_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_a_51_);
v___x_60_ = v_reuseFailAlloc_62_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
v_a_50_ = v_tail_54_;
v_a_51_ = v___x_60_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__0));
v___x_69_ = l_Lean_stringToMessageData(v___x_68_);
return v___x_69_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__2));
v___x_72_ = l_Lean_stringToMessageData(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__4));
v___x_75_ = l_Lean_stringToMessageData(v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__6));
v___x_78_ = l_Lean_stringToMessageData(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__8));
v___x_81_ = l_Lean_stringToMessageData(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(lean_object* v_alt_82_, lean_object* v_heqs_83_, lean_object* v_numDiscrEqs_84_, lean_object* v_e_85_, lean_object* v_ty_86_, lean_object* v_i_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_nat_dec_lt(v_i_87_, v_numDiscrEqs_84_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec_ref(v_ty_86_);
lean_dec(v_numDiscrEqs_84_);
lean_dec_ref(v_heqs_83_);
lean_dec_ref(v_alt_82_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v_e_85_);
return v___x_94_;
}
else
{
if (lean_obj_tag(v_ty_86_) == 7)
{
lean_object* v_binderName_95_; lean_object* v_binderType_96_; lean_object* v_body_97_; lean_object* v___x_98_; size_t v_sz_99_; size_t v___x_100_; lean_object* v___x_101_; 
v_binderName_95_ = lean_ctor_get(v_ty_86_, 0);
lean_inc(v_binderName_95_);
v_binderType_96_ = lean_ctor_get(v_ty_86_, 1);
lean_inc_ref_n(v_binderType_96_, 2);
v_body_97_ = lean_ctor_get(v_ty_86_, 2);
lean_inc_ref(v_body_97_);
lean_dec_ref_known(v_ty_86_, 3);
v___x_98_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0));
v_sz_99_ = lean_array_size(v_heqs_83_);
v___x_100_ = ((size_t)0ULL);
lean_inc_ref(v_heqs_83_);
v___x_101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(v_binderType_96_, v_e_85_, v_body_97_, v_i_87_, v_alt_82_, v_heqs_83_, v_numDiscrEqs_84_, v_heqs_83_, v_sz_99_, v___x_100_, v___x_98_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
lean_dec_ref(v_body_97_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_133_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_133_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_133_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_133_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_fst_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_131_; 
v_fst_106_ = lean_ctor_get(v_a_102_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v_a_102_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v_a_102_, 1);
lean_dec(v_unused_132_);
v___x_108_ = v_a_102_;
v_isShared_109_ = v_isSharedCheck_131_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_fst_106_);
lean_dec(v_a_102_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_131_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
if (lean_obj_tag(v_fst_106_) == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
lean_del_object(v___x_104_);
v___x_110_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1);
v___x_111_ = l_Lean_MessageData_ofName(v_binderName_95_);
if (v_isShared_109_ == 0)
{
lean_ctor_set_tag(v___x_108_, 7);
lean_ctor_set(v___x_108_, 1, v___x_111_);
lean_ctor_set(v___x_108_, 0, v___x_110_);
v___x_113_ = v___x_108_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v___x_111_);
v___x_113_ = v_reuseFailAlloc_126_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_114_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3);
v___x_115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = l_Lean_MessageData_ofExpr(v_binderType_96_);
v___x_117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5);
v___x_119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = lean_array_to_list(v_heqs_83_);
v___x_121_ = lean_box(0);
v___x_122_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_120_, v___x_121_);
v___x_123_ = l_Lean_MessageData_ofList(v___x_122_);
v___x_124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_119_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_124_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
return v___x_125_;
}
}
else
{
lean_object* v_val_127_; lean_object* v___x_129_; 
lean_del_object(v___x_108_);
lean_dec_ref(v_binderType_96_);
lean_dec(v_binderName_95_);
lean_dec_ref(v_heqs_83_);
v_val_127_ = lean_ctor_get(v_fst_106_, 0);
lean_inc(v_val_127_);
lean_dec_ref_known(v_fst_106_, 1);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v_val_127_);
v___x_129_ = v___x_104_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_val_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_dec_ref(v_binderType_96_);
lean_dec(v_binderName_95_);
lean_dec_ref(v_heqs_83_);
v_a_134_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_101_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_101_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec_ref(v_ty_86_);
lean_dec_ref(v_e_85_);
lean_dec_ref(v_heqs_83_);
v___x_142_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7);
v___x_143_ = l_Nat_reprFast(v_numDiscrEqs_84_);
v___x_144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
v___x_145_ = l_Lean_MessageData_ofFormat(v___x_144_);
v___x_146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_142_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9);
v___x_148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = l_Lean_indentExpr(v_alt_82_);
v___x_150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_150_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
return v___x_151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(lean_object* v_binderType_152_, lean_object* v_e_153_, lean_object* v_body_154_, lean_object* v_i_155_, lean_object* v_alt_156_, lean_object* v_heqs_157_, lean_object* v_numDiscrEqs_158_, lean_object* v_as_159_, size_t v_sz_160_, size_t v_i_161_, lean_object* v_b_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = lean_usize_dec_lt(v_i_161_, v_sz_160_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_dec(v_numDiscrEqs_158_);
lean_dec_ref(v_heqs_157_);
lean_dec_ref(v_alt_156_);
lean_dec_ref(v_e_153_);
lean_dec_ref(v_binderType_152_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v_b_162_);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_a_172_; lean_object* v___x_173_; 
lean_dec_ref(v_b_162_);
v___x_170_ = lean_box(0);
v___x_171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0));
v_a_172_ = lean_array_uget_borrowed(v_as_159_, v_i_161_);
lean_inc(v___y_166_);
lean_inc_ref(v___y_165_);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v_a_172_);
v___x_173_ = lean_infer_type(v_a_172_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_175_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_173_, 1);
lean_inc_ref(v_binderType_152_);
v___x_175_ = l_Lean_Meta_isExprDefEq(v_a_174_, v_binderType_152_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; uint8_t v___x_177_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref_known(v___x_175_, 1);
v___x_177_ = lean_unbox(v_a_176_);
lean_dec(v_a_176_);
if (v___x_177_ == 0)
{
size_t v___x_178_; size_t v___x_179_; 
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_161_, v___x_178_);
v_i_161_ = v___x_179_;
v_b_162_ = v___x_171_;
goto _start;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec_ref(v_binderType_152_);
lean_inc(v_a_172_);
v___x_181_ = l_Lean_Expr_app___override(v_e_153_, v_a_172_);
v___x_182_ = lean_expr_instantiate1(v_body_154_, v_a_172_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v_i_155_, v___x_183_);
v___x_185_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_156_, v_heqs_157_, v_numDiscrEqs_158_, v___x_181_, v___x_182_, v___x_184_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___x_184_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_195_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_195_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_a_186_);
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_170_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_191_);
v___x_193_ = v___x_188_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_185_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_185_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec(v_numDiscrEqs_158_);
lean_dec_ref(v_heqs_157_);
lean_dec_ref(v_alt_156_);
lean_dec_ref(v_e_153_);
lean_dec_ref(v_binderType_152_);
v_a_204_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_175_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_175_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v_numDiscrEqs_158_);
lean_dec_ref(v_heqs_157_);
lean_dec_ref(v_alt_156_);
lean_dec_ref(v_e_153_);
lean_dec_ref(v_binderType_152_);
v_a_212_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_173_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_173_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___boxed(lean_object* v_binderType_220_, lean_object* v_e_221_, lean_object* v_body_222_, lean_object* v_i_223_, lean_object* v_alt_224_, lean_object* v_heqs_225_, lean_object* v_numDiscrEqs_226_, lean_object* v_as_227_, lean_object* v_sz_228_, lean_object* v_i_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
size_t v_sz_boxed_236_; size_t v_i_boxed_237_; lean_object* v_res_238_; 
v_sz_boxed_236_ = lean_unbox_usize(v_sz_228_);
lean_dec(v_sz_228_);
v_i_boxed_237_ = lean_unbox_usize(v_i_229_);
lean_dec(v_i_229_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(v_binderType_220_, v_e_221_, v_body_222_, v_i_223_, v_alt_224_, v_heqs_225_, v_numDiscrEqs_226_, v_as_227_, v_sz_boxed_236_, v_i_boxed_237_, v_b_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v_as_227_);
lean_dec(v_i_223_);
lean_dec_ref(v_body_222_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___boxed(lean_object* v_alt_239_, lean_object* v_heqs_240_, lean_object* v_numDiscrEqs_241_, lean_object* v_e_242_, lean_object* v_ty_243_, lean_object* v_i_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_239_, v_heqs_240_, v_numDiscrEqs_241_, v_e_242_, v_ty_243_, v_i_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_i_244_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2(lean_object* v_00_u03b1_251_, lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___boxed(lean_object* v_00_u03b1_259_, lean_object* v_msg_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2(v_00_u03b1_259_, v_msg_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkAppDiscrEqs(lean_object* v_alt_267_, lean_object* v_heqs_268_, lean_object* v_numDiscrEqs_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; 
lean_inc(v_a_273_);
lean_inc_ref(v_a_272_);
lean_inc(v_a_271_);
lean_inc_ref(v_a_270_);
lean_inc_ref(v_alt_267_);
v___x_275_ = lean_infer_type(v_alt_267_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alt_267_);
v___x_278_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_267_, v_heqs_268_, v_numDiscrEqs_269_, v_alt_267_, v_a_276_, v___x_277_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
return v___x_278_;
}
else
{
lean_dec(v_numDiscrEqs_269_);
lean_dec_ref(v_heqs_268_);
lean_dec_ref(v_alt_267_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkAppDiscrEqs___boxed(lean_object* v_alt_279_, lean_object* v_heqs_280_, lean_object* v_numDiscrEqs_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_Match_mkAppDiscrEqs(v_alt_279_, v_heqs_280_, v_numDiscrEqs_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
return v_res_287_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0(lean_object* v_x_288_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = 0;
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0___boxed(lean_object* v_x_290_){
_start:
{
uint8_t v_res_291_; lean_object* v_r_292_; 
v_res_291_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0(v_x_290_);
lean_dec(v_x_290_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1(lean_object* v_fvarId_293_, lean_object* v_x_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = l_Lean_instBEqFVarId_beq(v_fvarId_293_, v_x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_296_, lean_object* v_x_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1(v_fvarId_296_, v_x_297_);
lean_dec(v_x_297_);
lean_dec(v_fvarId_296_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_box(0);
v___x_302_ = lean_unsigned_to_nat(16u);
v___x_303_ = lean_mk_array(v___x_302_, v___x_301_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1);
v___x_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(lean_object* v_e_307_, lean_object* v_fvarId_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___f_311_; lean_object* v___f_312_; lean_object* v___x_313_; uint8_t v_fst_315_; lean_object* v_mctx_316_; lean_object* v___y_334_; lean_object* v_mctx_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___f_311_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0));
v___f_312_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_312_, 0, v_fvarId_308_);
v___x_313_ = lean_st_ref_get(v___y_309_);
v_mctx_339_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref_n(v_mctx_339_, 2);
lean_dec(v___x_313_);
v___x_340_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v_mctx_339_);
v___x_342_ = l_Lean_Expr_hasFVar(v_e_307_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
v___x_343_ = l_Lean_Expr_hasMVar(v_e_307_);
if (v___x_343_ == 0)
{
lean_dec_ref_known(v___x_341_, 2);
lean_dec_ref(v___f_312_);
lean_dec_ref(v_e_307_);
v_fst_315_ = v___x_343_;
v_mctx_316_ = v_mctx_339_;
goto v___jp_314_;
}
else
{
lean_object* v___x_344_; 
lean_dec_ref(v_mctx_339_);
v___x_344_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_312_, v___f_311_, v_e_307_, v___x_341_);
v___y_334_ = v___x_344_;
goto v___jp_333_;
}
}
else
{
lean_object* v___x_345_; 
lean_dec_ref(v_mctx_339_);
v___x_345_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_312_, v___f_311_, v_e_307_, v___x_341_);
v___y_334_ = v___x_345_;
goto v___jp_333_;
}
v___jp_314_:
{
lean_object* v___x_317_; lean_object* v_cache_318_; lean_object* v_zetaDeltaFVarIds_319_; lean_object* v_postponed_320_; lean_object* v_diag_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_331_; 
v___x_317_ = lean_st_ref_take(v___y_309_);
v_cache_318_ = lean_ctor_get(v___x_317_, 1);
v_zetaDeltaFVarIds_319_ = lean_ctor_get(v___x_317_, 2);
v_postponed_320_ = lean_ctor_get(v___x_317_, 3);
v_diag_321_ = lean_ctor_get(v___x_317_, 4);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v___x_317_, 0);
lean_dec(v_unused_332_);
v___x_323_ = v___x_317_;
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_diag_321_);
lean_inc(v_postponed_320_);
lean_inc(v_zetaDeltaFVarIds_319_);
lean_inc(v_cache_318_);
lean_dec(v___x_317_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_331_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v_mctx_316_);
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_mctx_316_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_cache_318_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_zetaDeltaFVarIds_319_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_postponed_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_diag_321_);
v___x_326_ = v_reuseFailAlloc_330_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_st_ref_put(v___y_309_, v___x_326_);
v___x_328_ = lean_box(v_fst_315_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
}
v___jp_333_:
{
lean_object* v_snd_335_; lean_object* v_fst_336_; lean_object* v_mctx_337_; uint8_t v___x_338_; 
v_snd_335_ = lean_ctor_get(v___y_334_, 1);
lean_inc(v_snd_335_);
v_fst_336_ = lean_ctor_get(v___y_334_, 0);
lean_inc(v_fst_336_);
lean_dec_ref(v___y_334_);
v_mctx_337_ = lean_ctor_get(v_snd_335_, 1);
lean_inc_ref(v_mctx_337_);
lean_dec(v_snd_335_);
v___x_338_ = lean_unbox(v_fst_336_);
lean_dec(v_fst_336_);
v_fst_315_ = v___x_338_;
v_mctx_316_ = v_mctx_337_;
goto v___jp_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___boxed(lean_object* v_e_346_, lean_object* v_fvarId_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_346_, v_fvarId_347_, v___y_348_);
lean_dec(v___y_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(lean_object* v_e_351_, lean_object* v_fvarId_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_351_, v_fvarId_352_, v___y_354_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___boxed(lean_object* v_e_359_, lean_object* v_fvarId_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(v_e_359_, v_fvarId_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(lean_object* v_mvarId_367_, lean_object* v_x_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_367_, v_x_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
v_a_383_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_374_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_374_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg___boxed(lean_object* v_mvarId_391_, lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_391_, v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(lean_object* v_00_u03b1_399_, lean_object* v_mvarId_400_, lean_object* v_x_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_400_, v_x_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___boxed(lean_object* v_00_u03b1_408_, lean_object* v_mvarId_409_, lean_object* v_x_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(v_00_u03b1_408_, v_mvarId_409_, v_x_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(lean_object* v_mvarId_420_, lean_object* v_as_421_, size_t v_sz_422_, size_t v_i_423_, lean_object* v_b_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_423_, v_sz_422_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_dec(v_mvarId_420_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_b_424_);
return v___x_431_;
}
else
{
lean_object* v_snd_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_534_; 
v_snd_432_ = lean_ctor_get(v_b_424_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_b_424_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v_b_424_, 0);
lean_dec(v_unused_535_);
v___x_434_ = v_b_424_;
v_isShared_435_ = v_isSharedCheck_534_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snd_432_);
lean_dec(v_b_424_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_534_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v_a_438_; lean_object* v_a_445_; 
v___x_436_ = lean_box(0);
v_a_445_ = lean_array_uget(v_as_421_, v_i_423_);
if (lean_obj_tag(v_a_445_) == 0)
{
v_a_438_ = v_snd_432_;
goto v___jp_437_;
}
else
{
lean_object* v_val_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_533_; 
v_val_446_ = lean_ctor_get(v_a_445_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_a_445_);
if (v_isSharedCheck_533_ == 0)
{
v___x_448_ = v_a_445_;
v_isShared_449_ = v_isSharedCheck_533_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_val_446_);
lean_dec(v_a_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_533_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_450_ = lean_box(0);
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
v___x_452_ = l_Lean_LocalDecl_type(v_val_446_);
lean_dec(v_val_446_);
v___x_453_ = l_Lean_Meta_matchEq_x3f(v___x_452_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
if (lean_obj_tag(v_a_454_) == 1)
{
lean_object* v_val_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_524_; 
v_val_455_ = lean_ctor_get(v_a_454_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v_a_454_);
if (v_isSharedCheck_524_ == 0)
{
v___x_457_ = v_a_454_;
v_isShared_458_ = v_isSharedCheck_524_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_val_455_);
lean_dec(v_a_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_524_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_snd_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_522_; 
v_snd_459_ = lean_ctor_get(v_val_455_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_val_455_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v_val_455_, 0);
lean_dec(v_unused_523_);
v___x_461_ = v_val_455_;
v_isShared_462_ = v_isSharedCheck_522_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_snd_459_);
lean_dec(v_val_455_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_522_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_521_; 
v_fst_463_ = lean_ctor_get(v_snd_459_, 0);
v_snd_464_ = lean_ctor_get(v_snd_459_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_snd_459_);
if (v_isSharedCheck_521_ == 0)
{
v___x_466_ = v_snd_459_;
v_isShared_467_ = v_isSharedCheck_521_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_snd_464_);
lean_inc(v_fst_463_);
lean_dec(v_snd_459_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_521_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
uint8_t v___x_468_; 
v___x_468_ = l_Lean_Expr_isFVar(v_fst_463_);
if (v___x_468_ == 0)
{
lean_del_object(v___x_466_);
lean_dec(v_snd_464_);
lean_dec(v_fst_463_);
lean_del_object(v___x_461_);
lean_del_object(v___x_457_);
lean_del_object(v___x_448_);
lean_dec(v_snd_432_);
v_a_438_ = v___x_451_;
goto v___jp_437_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = l_Lean_Expr_fvarId_x21(v_fst_463_);
lean_dec(v_fst_463_);
lean_inc(v___x_469_);
v___x_470_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_464_, v___x_469_, v___y_426_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; uint8_t v___x_472_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = lean_unbox(v_a_471_);
lean_dec(v_a_471_);
if (v___x_472_ == 0)
{
if (v___x_468_ == 0)
{
lean_dec(v___x_469_);
lean_del_object(v___x_466_);
lean_del_object(v___x_461_);
lean_del_object(v___x_457_);
lean_del_object(v___x_448_);
lean_dec(v_snd_432_);
v_a_438_ = v___x_451_;
goto v___jp_437_;
}
else
{
lean_object* v___x_473_; 
lean_inc(v_mvarId_420_);
v___x_473_ = l_Lean_Meta_subst_x3f(v_mvarId_420_, v___x_469_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_504_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_504_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_504_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_504_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
if (lean_obj_tag(v_a_474_) == 0)
{
lean_del_object(v___x_476_);
lean_del_object(v___x_466_);
lean_del_object(v___x_461_);
lean_del_object(v___x_457_);
lean_del_object(v___x_448_);
lean_dec(v_snd_432_);
v_a_438_ = v___x_451_;
goto v___jp_437_;
}
else
{
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_503_; 
lean_del_object(v___x_434_);
lean_dec(v_mvarId_420_);
v_val_478_ = lean_ctor_get(v_a_474_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_a_474_);
if (v_isSharedCheck_503_ == 0)
{
v___x_480_ = v_a_474_;
v_isShared_481_ = v_isSharedCheck_503_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_val_478_);
lean_dec(v_a_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_503_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_mk_empty_array_with_capacity(v___x_482_);
v___x_484_ = lean_array_push(v___x_483_, v_val_478_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_484_);
v___x_486_ = v___x_480_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_502_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___x_450_);
lean_ctor_set(v___x_466_, 0, v___x_486_);
v___x_488_ = v___x_466_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_450_);
v___x_488_ = v_reuseFailAlloc_501_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 0);
lean_ctor_set(v___x_448_, 0, v___x_488_);
v___x_490_ = v___x_448_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_500_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_490_);
v___x_492_ = v___x_457_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_490_);
v___x_492_ = v_reuseFailAlloc_499_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v_snd_432_);
lean_ctor_set(v___x_461_, 0, v___x_492_);
v___x_494_ = v___x_461_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_snd_432_);
v___x_494_ = v_reuseFailAlloc_498_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_496_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_494_);
v___x_496_ = v___x_476_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
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
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_del_object(v___x_466_);
lean_del_object(v___x_461_);
lean_del_object(v___x_457_);
lean_del_object(v___x_448_);
lean_del_object(v___x_434_);
lean_dec(v_snd_432_);
lean_dec(v_mvarId_420_);
v_a_505_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_473_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_473_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
else
{
lean_dec(v___x_469_);
lean_del_object(v___x_466_);
lean_del_object(v___x_461_);
lean_del_object(v___x_457_);
lean_del_object(v___x_448_);
lean_dec(v_snd_432_);
v_a_438_ = v___x_451_;
goto v___jp_437_;
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v___x_469_);
lean_del_object(v___x_466_);
lean_del_object(v___x_461_);
lean_del_object(v___x_457_);
lean_del_object(v___x_448_);
lean_del_object(v___x_434_);
lean_dec(v_snd_432_);
lean_dec(v_mvarId_420_);
v_a_513_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_470_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_470_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
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
lean_dec(v_a_454_);
lean_del_object(v___x_448_);
lean_dec(v_snd_432_);
v_a_438_ = v___x_451_;
goto v___jp_437_;
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_del_object(v___x_448_);
lean_del_object(v___x_434_);
lean_dec(v_snd_432_);
lean_dec(v_mvarId_420_);
v_a_525_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_453_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_453_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
v___jp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v_a_438_);
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_440_ = v___x_434_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_a_438_);
v___x_440_ = v_reuseFailAlloc_444_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
size_t v___x_441_; size_t v___x_442_; 
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_i_423_, v___x_441_);
v_i_423_ = v___x_442_;
v_b_424_ = v___x_440_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_mvarId_536_, lean_object* v_as_537_, lean_object* v_sz_538_, lean_object* v_i_539_, lean_object* v_b_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
size_t v_sz_boxed_546_; size_t v_i_boxed_547_; lean_object* v_res_548_; 
v_sz_boxed_546_ = lean_unbox_usize(v_sz_538_);
lean_dec(v_sz_538_);
v_i_boxed_547_ = lean_unbox_usize(v_i_539_);
lean_dec(v_i_539_);
v_res_548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_536_, v_as_537_, v_sz_boxed_546_, v_i_boxed_547_, v_b_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec_ref(v_as_537_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(lean_object* v_mvarId_549_, lean_object* v_as_550_, size_t v_sz_551_, size_t v_i_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_lt(v_i_552_, v_sz_551_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
lean_dec(v_mvarId_549_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v_b_553_);
return v___x_560_;
}
else
{
lean_object* v_snd_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_663_; 
v_snd_561_ = lean_ctor_get(v_b_553_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_b_553_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v_b_553_, 0);
lean_dec(v_unused_664_);
v___x_563_ = v_b_553_;
v_isShared_564_ = v_isSharedCheck_663_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_snd_561_);
lean_dec(v_b_553_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_663_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v_a_567_; lean_object* v_a_574_; 
v___x_565_ = lean_box(0);
v_a_574_ = lean_array_uget(v_as_550_, v_i_552_);
if (lean_obj_tag(v_a_574_) == 0)
{
v_a_567_ = v_snd_561_;
goto v___jp_566_;
}
else
{
lean_object* v_val_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_662_; 
v_val_575_ = lean_ctor_get(v_a_574_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v_a_574_);
if (v_isSharedCheck_662_ == 0)
{
v___x_577_ = v_a_574_;
v_isShared_578_ = v_isSharedCheck_662_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_val_575_);
lean_dec(v_a_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_662_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = lean_box(0);
v___x_580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
v___x_581_ = l_Lean_LocalDecl_type(v_val_575_);
lean_dec(v_val_575_);
v___x_582_ = l_Lean_Meta_matchEq_x3f(v___x_581_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
if (lean_obj_tag(v_a_583_) == 1)
{
lean_object* v_val_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_653_; 
v_val_584_ = lean_ctor_get(v_a_583_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_a_583_);
if (v_isSharedCheck_653_ == 0)
{
v___x_586_ = v_a_583_;
v_isShared_587_ = v_isSharedCheck_653_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_val_584_);
lean_dec(v_a_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_653_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_snd_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_651_; 
v_snd_588_ = lean_ctor_get(v_val_584_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_val_584_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v_val_584_, 0);
lean_dec(v_unused_652_);
v___x_590_ = v_val_584_;
v_isShared_591_ = v_isSharedCheck_651_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snd_588_);
lean_dec(v_val_584_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_651_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_650_; 
v_fst_592_ = lean_ctor_get(v_snd_588_, 0);
v_snd_593_ = lean_ctor_get(v_snd_588_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_snd_588_);
if (v_isSharedCheck_650_ == 0)
{
v___x_595_ = v_snd_588_;
v_isShared_596_ = v_isSharedCheck_650_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_snd_593_);
lean_inc(v_fst_592_);
lean_dec(v_snd_588_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_650_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
uint8_t v___x_597_; 
v___x_597_ = l_Lean_Expr_isFVar(v_fst_592_);
if (v___x_597_ == 0)
{
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
lean_dec(v_fst_592_);
lean_del_object(v___x_590_);
lean_del_object(v___x_586_);
lean_del_object(v___x_577_);
lean_dec(v_snd_561_);
v_a_567_ = v___x_580_;
goto v___jp_566_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = l_Lean_Expr_fvarId_x21(v_fst_592_);
lean_dec(v_fst_592_);
lean_inc(v___x_598_);
v___x_599_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_593_, v___x_598_, v___y_555_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; uint8_t v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = lean_unbox(v_a_600_);
lean_dec(v_a_600_);
if (v___x_601_ == 0)
{
if (v___x_597_ == 0)
{
lean_dec(v___x_598_);
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_del_object(v___x_586_);
lean_del_object(v___x_577_);
lean_dec(v_snd_561_);
v_a_567_ = v___x_580_;
goto v___jp_566_;
}
else
{
lean_object* v___x_602_; 
lean_inc(v_mvarId_549_);
v___x_602_ = l_Lean_Meta_subst_x3f(v_mvarId_549_, v___x_598_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_633_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_633_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_633_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_633_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
if (lean_obj_tag(v_a_603_) == 0)
{
lean_del_object(v___x_605_);
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_del_object(v___x_586_);
lean_del_object(v___x_577_);
lean_dec(v_snd_561_);
v_a_567_ = v___x_580_;
goto v___jp_566_;
}
else
{
lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_632_; 
lean_del_object(v___x_563_);
lean_dec(v_mvarId_549_);
v_val_607_ = lean_ctor_get(v_a_603_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_a_603_);
if (v_isSharedCheck_632_ == 0)
{
v___x_609_ = v_a_603_;
v_isShared_610_ = v_isSharedCheck_632_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_dec(v_a_603_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_632_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_mk_empty_array_with_capacity(v___x_611_);
v___x_613_ = lean_array_push(v___x_612_, v_val_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_613_);
v___x_615_ = v___x_609_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_631_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_617_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___x_579_);
lean_ctor_set(v___x_595_, 0, v___x_615_);
v___x_617_ = v___x_595_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_579_);
v___x_617_ = v_reuseFailAlloc_630_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 0);
lean_ctor_set(v___x_577_, 0, v___x_617_);
v___x_619_ = v___x_577_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_629_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_619_);
v___x_621_ = v___x_586_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_628_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_snd_561_);
lean_ctor_set(v___x_590_, 0, v___x_621_);
v___x_623_ = v___x_590_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_snd_561_);
v___x_623_ = v_reuseFailAlloc_627_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_623_);
v___x_625_ = v___x_605_;
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_del_object(v___x_586_);
lean_del_object(v___x_577_);
lean_del_object(v___x_563_);
lean_dec(v_snd_561_);
lean_dec(v_mvarId_549_);
v_a_634_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_602_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_602_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
else
{
lean_dec(v___x_598_);
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_del_object(v___x_586_);
lean_del_object(v___x_577_);
lean_dec(v_snd_561_);
v_a_567_ = v___x_580_;
goto v___jp_566_;
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v___x_598_);
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_del_object(v___x_586_);
lean_del_object(v___x_577_);
lean_del_object(v___x_563_);
lean_dec(v_snd_561_);
lean_dec(v_mvarId_549_);
v_a_642_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_599_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_599_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
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
lean_dec(v_a_583_);
lean_del_object(v___x_577_);
lean_dec(v_snd_561_);
v_a_567_ = v___x_580_;
goto v___jp_566_;
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_del_object(v___x_577_);
lean_del_object(v___x_563_);
lean_dec(v_snd_561_);
lean_dec(v_mvarId_549_);
v_a_654_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_582_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_582_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
v___jp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v_a_567_);
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_569_ = v___x_563_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_a_567_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((size_t)1ULL);
v___x_571_ = lean_usize_add(v_i_552_, v___x_570_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_549_, v_as_550_, v_sz_551_, v___x_571_, v___x_569_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4___boxed(lean_object* v_mvarId_665_, lean_object* v_as_666_, lean_object* v_sz_667_, lean_object* v_i_668_, lean_object* v_b_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
size_t v_sz_boxed_675_; size_t v_i_boxed_676_; lean_object* v_res_677_; 
v_sz_boxed_675_ = lean_unbox_usize(v_sz_667_);
lean_dec(v_sz_667_);
v_i_boxed_676_ = lean_unbox_usize(v_i_668_);
lean_dec(v_i_668_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_665_, v_as_666_, v_sz_boxed_675_, v_i_boxed_676_, v_b_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec_ref(v_as_666_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(lean_object* v_init_678_, lean_object* v_mvarId_679_, lean_object* v_n_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
if (lean_obj_tag(v_n_680_) == 0)
{
lean_object* v_cs_687_; lean_object* v___x_688_; lean_object* v___x_689_; size_t v_sz_690_; size_t v___x_691_; lean_object* v___x_692_; 
v_cs_687_ = lean_ctor_get(v_n_680_, 0);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v_b_681_);
v_sz_690_ = lean_array_size(v_cs_687_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_678_, v_mvarId_679_, v_cs_687_, v_sz_690_, v___x_691_, v___x_689_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_707_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_707_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_707_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_707_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_fst_697_; 
v_fst_697_ = lean_ctor_get(v_a_693_, 0);
if (lean_obj_tag(v_fst_697_) == 0)
{
lean_object* v_snd_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v_snd_698_ = lean_ctor_get(v_a_693_, 1);
lean_inc(v_snd_698_);
lean_dec(v_a_693_);
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v_snd_698_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_699_);
v___x_701_ = v___x_695_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
else
{
lean_object* v_val_703_; lean_object* v___x_705_; 
lean_inc_ref(v_fst_697_);
lean_dec(v_a_693_);
v_val_703_ = lean_ctor_get(v_fst_697_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v_fst_697_, 1);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v_val_703_);
v___x_705_ = v___x_695_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_val_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
v_a_708_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_692_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_692_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_vs_716_; lean_object* v___x_717_; lean_object* v___x_718_; size_t v_sz_719_; size_t v___x_720_; lean_object* v___x_721_; 
v_vs_716_ = lean_ctor_get(v_n_680_, 0);
v___x_717_ = lean_box(0);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v_b_681_);
v_sz_719_ = lean_array_size(v_vs_716_);
v___x_720_ = ((size_t)0ULL);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_679_, v_vs_716_, v_sz_719_, v___x_720_, v___x_718_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_736_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_736_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_736_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_736_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_fst_726_; 
v_fst_726_ = lean_ctor_get(v_a_722_, 0);
if (lean_obj_tag(v_fst_726_) == 0)
{
lean_object* v_snd_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v_snd_727_ = lean_ctor_get(v_a_722_, 1);
lean_inc(v_snd_727_);
lean_dec(v_a_722_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_snd_727_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_728_);
v___x_730_ = v___x_724_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
lean_object* v_val_732_; lean_object* v___x_734_; 
lean_inc_ref(v_fst_726_);
lean_dec(v_a_722_);
v_val_732_ = lean_ctor_get(v_fst_726_, 0);
lean_inc(v_val_732_);
lean_dec_ref_known(v_fst_726_, 1);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v_val_732_);
v___x_734_ = v___x_724_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_val_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_a_737_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_721_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_721_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(lean_object* v_init_745_, lean_object* v_mvarId_746_, lean_object* v_as_747_, size_t v_sz_748_, size_t v_i_749_, lean_object* v_b_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = lean_usize_dec_lt(v_i_749_, v_sz_748_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec(v_mvarId_746_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v_b_750_);
return v___x_757_;
}
else
{
lean_object* v_snd_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_792_; 
v_snd_758_ = lean_ctor_get(v_b_750_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_b_750_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_b_750_, 0);
lean_dec(v_unused_793_);
v___x_760_ = v_b_750_;
v_isShared_761_ = v_isSharedCheck_792_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snd_758_);
lean_dec(v_b_750_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_792_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v_a_763_; lean_object* v___x_764_; 
v___x_762_ = lean_box(0);
v_a_763_ = lean_array_uget_borrowed(v_as_747_, v_i_749_);
lean_inc(v_snd_758_);
lean_inc(v_mvarId_746_);
v___x_764_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_745_, v_mvarId_746_, v_a_763_, v_snd_758_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_783_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_783_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_783_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_783_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
if (lean_obj_tag(v_a_765_) == 0)
{
lean_object* v___x_769_; lean_object* v___x_771_; 
lean_dec(v_mvarId_746_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v_a_765_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_769_);
v___x_771_ = v___x_760_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_snd_758_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_771_);
v___x_773_ = v___x_767_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; 
lean_del_object(v___x_767_);
lean_dec(v_snd_758_);
v_a_776_ = lean_ctor_get(v_a_765_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v_a_765_, 1);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v_a_776_);
lean_ctor_set(v___x_760_, 0, v___x_762_);
v___x_778_ = v___x_760_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_a_776_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
size_t v___x_779_; size_t v___x_780_; 
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_add(v_i_749_, v___x_779_);
v_i_749_ = v___x_780_;
v_b_750_ = v___x_778_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_del_object(v___x_760_);
lean_dec(v_snd_758_);
lean_dec(v_mvarId_746_);
v_a_784_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_764_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_764_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3___boxed(lean_object* v_init_794_, lean_object* v_mvarId_795_, lean_object* v_as_796_, lean_object* v_sz_797_, lean_object* v_i_798_, lean_object* v_b_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_797_);
lean_dec(v_sz_797_);
v_i_boxed_806_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_794_, v_mvarId_795_, v_as_796_, v_sz_boxed_805_, v_i_boxed_806_, v_b_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v_as_796_);
lean_dec_ref(v_init_794_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1___boxed(lean_object* v_init_808_, lean_object* v_mvarId_809_, lean_object* v_n_810_, lean_object* v_b_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_808_, v_mvarId_809_, v_n_810_, v_b_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v_n_810_);
lean_dec_ref(v_init_808_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(lean_object* v_mvarId_821_, lean_object* v_as_822_, size_t v_sz_823_, size_t v_i_824_, lean_object* v_b_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = lean_usize_dec_lt(v_i_824_, v_sz_823_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec(v_mvarId_821_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v_b_825_);
return v___x_832_;
}
else
{
lean_object* v_snd_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_928_; 
v_snd_833_ = lean_ctor_get(v_b_825_, 1);
v_isSharedCheck_928_ = !lean_is_exclusive(v_b_825_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_b_825_, 0);
lean_dec(v_unused_929_);
v___x_835_ = v_b_825_;
v_isShared_836_ = v_isSharedCheck_928_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_snd_833_);
lean_dec(v_b_825_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_928_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v_a_839_; lean_object* v_a_846_; 
v___x_837_ = lean_box(0);
v_a_846_ = lean_array_uget_borrowed(v_as_822_, v_i_824_);
if (lean_obj_tag(v_a_846_) == 0)
{
v_a_839_ = v_snd_833_;
goto v___jp_838_;
}
else
{
lean_object* v_val_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_val_847_ = lean_ctor_get(v_a_846_, 0);
v___x_848_ = lean_box(0);
v___x_849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
v___x_850_ = l_Lean_LocalDecl_type(v_val_847_);
v___x_851_ = l_Lean_Meta_matchEq_x3f(v___x_850_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
if (lean_obj_tag(v_a_852_) == 1)
{
lean_object* v_val_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_919_; 
v_val_853_ = lean_ctor_get(v_a_852_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v_a_852_);
if (v_isSharedCheck_919_ == 0)
{
v___x_855_ = v_a_852_;
v_isShared_856_ = v_isSharedCheck_919_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_val_853_);
lean_dec(v_a_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_919_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_snd_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_917_; 
v_snd_857_ = lean_ctor_get(v_val_853_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_val_853_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v_val_853_, 0);
lean_dec(v_unused_918_);
v___x_859_ = v_val_853_;
v_isShared_860_ = v_isSharedCheck_917_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_snd_857_);
lean_dec(v_val_853_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_917_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_fst_861_; lean_object* v_snd_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_916_; 
v_fst_861_ = lean_ctor_get(v_snd_857_, 0);
v_snd_862_ = lean_ctor_get(v_snd_857_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_snd_857_);
if (v_isSharedCheck_916_ == 0)
{
v___x_864_ = v_snd_857_;
v_isShared_865_ = v_isSharedCheck_916_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_snd_862_);
lean_inc(v_fst_861_);
lean_dec(v_snd_857_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_916_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint8_t v___x_866_; 
v___x_866_ = l_Lean_Expr_isFVar(v_fst_861_);
if (v___x_866_ == 0)
{
lean_del_object(v___x_864_);
lean_dec(v_snd_862_);
lean_dec(v_fst_861_);
lean_del_object(v___x_859_);
lean_del_object(v___x_855_);
lean_dec(v_snd_833_);
v_a_839_ = v___x_849_;
goto v___jp_838_;
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = l_Lean_Expr_fvarId_x21(v_fst_861_);
lean_dec(v_fst_861_);
lean_inc(v___x_867_);
v___x_868_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_862_, v___x_867_, v___y_827_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; uint8_t v___x_870_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v___x_870_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
if (v___x_870_ == 0)
{
if (v___x_866_ == 0)
{
lean_dec(v___x_867_);
lean_del_object(v___x_864_);
lean_del_object(v___x_859_);
lean_del_object(v___x_855_);
lean_dec(v_snd_833_);
v_a_839_ = v___x_849_;
goto v___jp_838_;
}
else
{
lean_object* v___x_871_; 
lean_inc(v_mvarId_821_);
v___x_871_ = l_Lean_Meta_subst_x3f(v_mvarId_821_, v___x_867_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_899_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_899_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_899_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_899_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
if (lean_obj_tag(v_a_872_) == 0)
{
lean_del_object(v___x_874_);
lean_del_object(v___x_864_);
lean_del_object(v___x_859_);
lean_del_object(v___x_855_);
lean_dec(v_snd_833_);
v_a_839_ = v___x_849_;
goto v___jp_838_;
}
else
{
lean_object* v_val_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_898_; 
lean_del_object(v___x_835_);
lean_dec(v_mvarId_821_);
v_val_876_ = lean_ctor_get(v_a_872_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_a_872_);
if (v_isSharedCheck_898_ == 0)
{
v___x_878_ = v_a_872_;
v_isShared_879_ = v_isSharedCheck_898_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_val_876_);
lean_dec(v_a_872_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_898_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = lean_mk_empty_array_with_capacity(v___x_880_);
v___x_882_ = lean_array_push(v___x_881_, v_val_876_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_882_);
v___x_884_ = v___x_878_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_897_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_848_);
lean_ctor_set(v___x_864_, 0, v___x_884_);
v___x_886_ = v___x_864_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_848_);
v___x_886_ = v_reuseFailAlloc_896_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_886_);
v___x_888_ = v___x_855_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_895_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v_snd_833_);
lean_ctor_set(v___x_859_, 0, v___x_888_);
v___x_890_ = v___x_859_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_snd_833_);
v___x_890_ = v_reuseFailAlloc_894_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_892_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_890_);
v___x_892_ = v___x_874_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
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
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_del_object(v___x_864_);
lean_del_object(v___x_859_);
lean_del_object(v___x_855_);
lean_del_object(v___x_835_);
lean_dec(v_snd_833_);
lean_dec(v_mvarId_821_);
v_a_900_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_871_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_871_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
else
{
lean_dec(v___x_867_);
lean_del_object(v___x_864_);
lean_del_object(v___x_859_);
lean_del_object(v___x_855_);
lean_dec(v_snd_833_);
v_a_839_ = v___x_849_;
goto v___jp_838_;
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v___x_867_);
lean_del_object(v___x_864_);
lean_del_object(v___x_859_);
lean_del_object(v___x_855_);
lean_del_object(v___x_835_);
lean_dec(v_snd_833_);
lean_dec(v_mvarId_821_);
v_a_908_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_868_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_868_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
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
lean_dec(v_a_852_);
lean_dec(v_snd_833_);
v_a_839_ = v___x_849_;
goto v___jp_838_;
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_del_object(v___x_835_);
lean_dec(v_snd_833_);
lean_dec(v_mvarId_821_);
v_a_920_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_851_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_851_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
v___jp_838_:
{
lean_object* v___x_841_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v_a_839_);
lean_ctor_set(v___x_835_, 0, v___x_837_);
v___x_841_ = v___x_835_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_a_839_);
v___x_841_ = v_reuseFailAlloc_845_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
size_t v___x_842_; size_t v___x_843_; 
v___x_842_ = ((size_t)1ULL);
v___x_843_ = lean_usize_add(v_i_824_, v___x_842_);
v_i_824_ = v___x_843_;
v_b_825_ = v___x_841_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___boxed(lean_object* v_mvarId_930_, lean_object* v_as_931_, lean_object* v_sz_932_, lean_object* v_i_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
size_t v_sz_boxed_940_; size_t v_i_boxed_941_; lean_object* v_res_942_; 
v_sz_boxed_940_ = lean_unbox_usize(v_sz_932_);
lean_dec(v_sz_932_);
v_i_boxed_941_ = lean_unbox_usize(v_i_933_);
lean_dec(v_i_933_);
v_res_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_930_, v_as_931_, v_sz_boxed_940_, v_i_boxed_941_, v_b_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec_ref(v_as_931_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(lean_object* v_mvarId_943_, lean_object* v_as_944_, size_t v_sz_945_, size_t v_i_946_, lean_object* v_b_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
uint8_t v___x_953_; 
v___x_953_ = lean_usize_dec_lt(v_i_946_, v_sz_945_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
lean_dec(v_mvarId_943_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v_b_947_);
return v___x_954_;
}
else
{
lean_object* v_snd_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1050_; 
v_snd_955_ = lean_ctor_get(v_b_947_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_b_947_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v_b_947_, 0);
lean_dec(v_unused_1051_);
v___x_957_ = v_b_947_;
v_isShared_958_ = v_isSharedCheck_1050_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_snd_955_);
lean_dec(v_b_947_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1050_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v_a_961_; lean_object* v_a_968_; 
v___x_959_ = lean_box(0);
v_a_968_ = lean_array_uget_borrowed(v_as_944_, v_i_946_);
if (lean_obj_tag(v_a_968_) == 0)
{
v_a_961_ = v_snd_955_;
goto v___jp_960_;
}
else
{
lean_object* v_val_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_val_969_ = lean_ctor_get(v_a_968_, 0);
v___x_970_ = lean_box(0);
v___x_971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
v___x_972_ = l_Lean_LocalDecl_type(v_val_969_);
v___x_973_ = l_Lean_Meta_matchEq_x3f(v___x_972_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
if (lean_obj_tag(v_a_974_) == 1)
{
lean_object* v_val_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1041_; 
v_val_975_ = lean_ctor_get(v_a_974_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_a_974_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_977_ = v_a_974_;
v_isShared_978_ = v_isSharedCheck_1041_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_val_975_);
lean_dec(v_a_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1041_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_snd_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1039_; 
v_snd_979_ = lean_ctor_get(v_val_975_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_val_975_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v_val_975_, 0);
lean_dec(v_unused_1040_);
v___x_981_ = v_val_975_;
v_isShared_982_ = v_isSharedCheck_1039_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_snd_979_);
lean_dec(v_val_975_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1039_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1038_; 
v_fst_983_ = lean_ctor_get(v_snd_979_, 0);
v_snd_984_ = lean_ctor_get(v_snd_979_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_snd_979_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_986_ = v_snd_979_;
v_isShared_987_ = v_isSharedCheck_1038_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_snd_984_);
lean_inc(v_fst_983_);
lean_dec(v_snd_979_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1038_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
uint8_t v___x_988_; 
v___x_988_ = l_Lean_Expr_isFVar(v_fst_983_);
if (v___x_988_ == 0)
{
lean_del_object(v___x_986_);
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_del_object(v___x_981_);
lean_del_object(v___x_977_);
lean_dec(v_snd_955_);
v_a_961_ = v___x_971_;
goto v___jp_960_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = l_Lean_Expr_fvarId_x21(v_fst_983_);
lean_dec(v_fst_983_);
lean_inc(v___x_989_);
v___x_990_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_984_, v___x_989_, v___y_949_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; uint8_t v___x_992_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_unbox(v_a_991_);
lean_dec(v_a_991_);
if (v___x_992_ == 0)
{
if (v___x_988_ == 0)
{
lean_dec(v___x_989_);
lean_del_object(v___x_986_);
lean_del_object(v___x_981_);
lean_del_object(v___x_977_);
lean_dec(v_snd_955_);
v_a_961_ = v___x_971_;
goto v___jp_960_;
}
else
{
lean_object* v___x_993_; 
lean_inc(v_mvarId_943_);
v___x_993_ = l_Lean_Meta_subst_x3f(v_mvarId_943_, v___x_989_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1021_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1021_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1021_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
if (lean_obj_tag(v_a_994_) == 0)
{
lean_del_object(v___x_996_);
lean_del_object(v___x_986_);
lean_del_object(v___x_981_);
lean_del_object(v___x_977_);
lean_dec(v_snd_955_);
v_a_961_ = v___x_971_;
goto v___jp_960_;
}
else
{
lean_object* v_val_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1020_; 
lean_del_object(v___x_957_);
lean_dec(v_mvarId_943_);
v_val_998_ = lean_ctor_get(v_a_994_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_a_994_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1000_ = v_a_994_;
v_isShared_1001_ = v_isSharedCheck_1020_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_val_998_);
lean_dec(v_a_994_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1020_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_mk_empty_array_with_capacity(v___x_1002_);
v___x_1004_ = lean_array_push(v___x_1003_, v_val_998_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1004_);
v___x_1006_ = v___x_1000_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___x_970_);
lean_ctor_set(v___x_986_, 0, v___x_1006_);
v___x_1008_ = v___x_986_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v___x_970_);
v___x_1008_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1010_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_1008_);
v___x_1010_ = v___x_977_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v_snd_955_);
lean_ctor_set(v___x_981_, 0, v___x_1010_);
v___x_1012_ = v___x_981_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_snd_955_);
v___x_1012_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1012_);
v___x_1014_ = v___x_996_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
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
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_del_object(v___x_986_);
lean_del_object(v___x_981_);
lean_del_object(v___x_977_);
lean_del_object(v___x_957_);
lean_dec(v_snd_955_);
lean_dec(v_mvarId_943_);
v_a_1022_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_993_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_993_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
else
{
lean_dec(v___x_989_);
lean_del_object(v___x_986_);
lean_del_object(v___x_981_);
lean_del_object(v___x_977_);
lean_dec(v_snd_955_);
v_a_961_ = v___x_971_;
goto v___jp_960_;
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v___x_989_);
lean_del_object(v___x_986_);
lean_del_object(v___x_981_);
lean_del_object(v___x_977_);
lean_del_object(v___x_957_);
lean_dec(v_snd_955_);
lean_dec(v_mvarId_943_);
v_a_1030_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_990_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_990_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
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
lean_dec(v_a_974_);
lean_dec(v_snd_955_);
v_a_961_ = v___x_971_;
goto v___jp_960_;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_del_object(v___x_957_);
lean_dec(v_snd_955_);
lean_dec(v_mvarId_943_);
v_a_1042_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_973_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_973_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
v___jp_960_:
{
lean_object* v___x_963_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_a_961_);
lean_ctor_set(v___x_957_, 0, v___x_959_);
v___x_963_ = v___x_957_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_a_961_);
v___x_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
size_t v___x_964_; size_t v___x_965_; lean_object* v___x_966_; 
v___x_964_ = ((size_t)1ULL);
v___x_965_ = lean_usize_add(v_i_946_, v___x_964_);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_943_, v_as_944_, v_sz_945_, v___x_965_, v___x_963_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
return v___x_966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2___boxed(lean_object* v_mvarId_1052_, lean_object* v_as_1053_, lean_object* v_sz_1054_, lean_object* v_i_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
size_t v_sz_boxed_1062_; size_t v_i_boxed_1063_; lean_object* v_res_1064_; 
v_sz_boxed_1062_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1063_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1052_, v_as_1053_, v_sz_boxed_1062_, v_i_boxed_1063_, v_b_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v_as_1053_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(lean_object* v_mvarId_1065_, lean_object* v_t_1066_, lean_object* v_init_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_root_1073_; lean_object* v_tail_1074_; lean_object* v___x_1075_; 
v_root_1073_ = lean_ctor_get(v_t_1066_, 0);
v_tail_1074_ = lean_ctor_get(v_t_1066_, 1);
lean_inc(v_mvarId_1065_);
lean_inc_ref(v_init_1067_);
v___x_1075_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_1067_, v_mvarId_1065_, v_root_1073_, v_init_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec_ref(v_init_1067_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1112_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1112_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1112_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
if (lean_obj_tag(v_a_1076_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; 
lean_dec(v_mvarId_1065_);
v_a_1080_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v_a_1076_, 1);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v_a_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; size_t v_sz_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
lean_del_object(v___x_1078_);
v_a_1084_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v_a_1076_, 1);
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v_a_1084_);
v_sz_1087_ = lean_array_size(v_tail_1074_);
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1065_, v_tail_1074_, v_sz_1087_, v___x_1088_, v___x_1086_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1103_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1103_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1103_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_fst_1094_; 
v_fst_1094_ = lean_ctor_get(v_a_1090_, 0);
if (lean_obj_tag(v_fst_1094_) == 0)
{
lean_object* v_snd_1095_; lean_object* v___x_1097_; 
v_snd_1095_ = lean_ctor_get(v_a_1090_, 1);
lean_inc(v_snd_1095_);
lean_dec(v_a_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v_snd_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_snd_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
else
{
lean_object* v_val_1099_; lean_object* v___x_1101_; 
lean_inc_ref(v_fst_1094_);
lean_dec(v_a_1090_);
v_val_1099_ = lean_ctor_get(v_fst_1094_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v_fst_1094_, 1);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v_val_1099_);
v___x_1101_ = v___x_1092_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_val_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1089_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1089_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_mvarId_1065_);
v_a_1113_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1075_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1075_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1___boxed(lean_object* v_mvarId_1121_, lean_object* v_t_1122_, lean_object* v_init_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1121_, v_t_1122_, v_init_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec_ref(v_t_1122_);
return v_res_1129_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(lean_object* v_mvarId_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_lctx_1142_; lean_object* v_decls_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_lctx_1142_ = lean_ctor_get(v___y_1137_, 2);
v_decls_1143_ = lean_ctor_get(v_lctx_1142_, 1);
v___x_1144_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0));
v___x_1145_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1136_, v_decls_1143_, v___x_1144_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1157_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1157_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1157_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_fst_1150_; 
v_fst_1150_ = lean_ctor_get(v_a_1146_, 0);
lean_inc(v_fst_1150_);
lean_dec(v_a_1146_);
if (lean_obj_tag(v_fst_1150_) == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_del_object(v___x_1148_);
v___x_1151_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2);
v___x_1152_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1151_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1152_;
}
else
{
lean_object* v_val_1153_; lean_object* v___x_1155_; 
v_val_1153_ = lean_ctor_get(v_fst_1150_, 0);
lean_inc(v_val_1153_);
lean_dec_ref_known(v_fst_1150_, 1);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_val_1153_);
v___x_1155_ = v___x_1148_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_val_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_a_1158_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1145_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1145_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed(lean_object* v_mvarId_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(v_mvarId_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(lean_object* v_mvarId_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v___f_1179_; lean_object* v___x_1180_; 
lean_inc(v_mvarId_1173_);
v___f_1179_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1179_, 0, v_mvarId_1173_);
v___x_1180_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_1173_, v___f_1179_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___boxed(lean_object* v_mvarId_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v_mvarId_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object* v_x_1195_){
_start:
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1197_ = lean_name_eq(v_x_1195_, v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object* v_x_1198_){
_start:
{
uint8_t v_res_1199_; lean_object* v_r_1200_; 
v_res_1199_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(v_x_1198_);
lean_dec(v_x_1198_);
v_r_1200_ = lean_box(v_res_1199_);
return v_r_1200_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object* v_e_1201_){
_start:
{
lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1203_ = l_Lean_Expr_isConstOf(v_e_1201_, v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object* v_e_1204_){
_start:
{
uint8_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(v_e_1204_);
lean_dec_ref(v_e_1204_);
v_r_1206_ = lean_box(v_res_1205_);
return v_r_1206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2));
v___x_1211_ = l_Lean_stringToMessageData(v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object* v_mvarId_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; 
v___f_1218_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0));
v___f_1219_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1));
lean_inc(v_mvarId_1212_);
v___x_1220_ = l_Lean_MVarId_getType(v_mvarId_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1222_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v___x_1222_ = lean_find_expr(v___f_1219_, v_a_1221_);
lean_dec(v_a_1221_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_mvarId_1212_);
v___x_1223_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3);
v___x_1224_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1223_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
else
{
lean_object* v___x_1233_; 
lean_dec_ref_known(v___x_1222_, 1);
v___x_1233_ = l_Lean_MVarId_deltaTarget(v_mvarId_1212_, v___f_1218_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
return v___x_1233_;
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_mvarId_1212_);
v_a_1234_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1220_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1220_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object* v_mvarId_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_mvarId_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
return v_res_1248_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = l_Lean_maxRecDepthErrorMessage;
v___x_1255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3);
v___x_1257_ = l_Lean_MessageData_ofFormat(v___x_1256_);
return v___x_1257_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4);
v___x_1259_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2));
v___x_1260_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___x_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(lean_object* v_ref_1261_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_ref_1261_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___boxed(lean_object* v_ref_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object* v_00_u03b1_1269_, lean_object* v_ref_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1270_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object* v_00_u03b1_1277_, lean_object* v_ref_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v_00_u03b1_1277_, v_ref_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object* v_a_1285_, lean_object* v_____r_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1292_ = lean_unsigned_to_nat(1u);
v___x_1293_ = lean_mk_empty_array_with_capacity(v___x_1292_);
v___x_1294_ = lean_array_push(v___x_1293_, v_a_1285_);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object* v_a_1296_, lean_object* v_____r_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1296_, v_____r_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
return v_res_1303_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1304_; double v___x_1305_; 
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_float_of_nat(v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object* v_cls_1309_, lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_ref_1316_; lean_object* v___x_1317_; lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1363_; 
v_ref_1316_ = lean_ctor_get(v___y_1313_, 2);
v___x_1317_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1363_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1363_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v_traceState_1323_; lean_object* v_env_1324_; lean_object* v_nextMacroScope_1325_; lean_object* v_ngen_1326_; lean_object* v_auxDeclNGen_1327_; lean_object* v_cache_1328_; lean_object* v_recordedDeps_1329_; lean_object* v_messages_1330_; lean_object* v_infoState_1331_; lean_object* v_snapshotTasks_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1362_; 
v___x_1322_ = lean_st_ref_take(v___y_1314_);
v_traceState_1323_ = lean_ctor_get(v___x_1322_, 4);
v_env_1324_ = lean_ctor_get(v___x_1322_, 0);
v_nextMacroScope_1325_ = lean_ctor_get(v___x_1322_, 1);
v_ngen_1326_ = lean_ctor_get(v___x_1322_, 2);
v_auxDeclNGen_1327_ = lean_ctor_get(v___x_1322_, 3);
v_cache_1328_ = lean_ctor_get(v___x_1322_, 5);
v_recordedDeps_1329_ = lean_ctor_get(v___x_1322_, 6);
v_messages_1330_ = lean_ctor_get(v___x_1322_, 7);
v_infoState_1331_ = lean_ctor_get(v___x_1322_, 8);
v_snapshotTasks_1332_ = lean_ctor_get(v___x_1322_, 9);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1334_ = v___x_1322_;
v_isShared_1335_ = v_isSharedCheck_1362_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_snapshotTasks_1332_);
lean_inc(v_infoState_1331_);
lean_inc(v_messages_1330_);
lean_inc(v_recordedDeps_1329_);
lean_inc(v_cache_1328_);
lean_inc(v_traceState_1323_);
lean_inc(v_auxDeclNGen_1327_);
lean_inc(v_ngen_1326_);
lean_inc(v_nextMacroScope_1325_);
lean_inc(v_env_1324_);
lean_dec(v___x_1322_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1362_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
uint64_t v_tid_1336_; lean_object* v_traces_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1361_; 
v_tid_1336_ = lean_ctor_get_uint64(v_traceState_1323_, sizeof(void*)*1);
v_traces_1337_ = lean_ctor_get(v_traceState_1323_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_traceState_1323_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1339_ = v_traceState_1323_;
v_isShared_1340_ = v_isSharedCheck_1361_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_traces_1337_);
lean_dec(v_traceState_1323_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1361_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; double v___x_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = lean_box(0);
v___x_1343_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0);
v___x_1344_ = 0;
v___x_1345_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1));
v___x_1346_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1346_, 0, v_cls_1309_);
lean_ctor_set(v___x_1346_, 1, v___x_1342_);
lean_ctor_set(v___x_1346_, 2, v___x_1345_);
lean_ctor_set_float(v___x_1346_, sizeof(void*)*3, v___x_1343_);
lean_ctor_set_float(v___x_1346_, sizeof(void*)*3 + 8, v___x_1343_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 16, v___x_1344_);
v___x_1347_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2));
v___x_1348_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v_a_1318_);
lean_ctor_set(v___x_1348_, 2, v___x_1347_);
lean_inc(v_ref_1316_);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_ref_1316_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = l_Lean_PersistentArray_push___redArg(v_traces_1337_, v___x_1349_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1350_);
v___x_1352_ = v___x_1339_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1350_);
lean_ctor_set_uint64(v_reuseFailAlloc_1360_, sizeof(void*)*1, v_tid_1336_);
v___x_1352_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 4, v___x_1352_);
v___x_1354_ = v___x_1334_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_env_1324_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_nextMacroScope_1325_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_ngen_1326_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v_auxDeclNGen_1327_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1359_, 5, v_cache_1328_);
lean_ctor_set(v_reuseFailAlloc_1359_, 6, v_recordedDeps_1329_);
lean_ctor_set(v_reuseFailAlloc_1359_, 7, v_messages_1330_);
lean_ctor_set(v_reuseFailAlloc_1359_, 8, v_infoState_1331_);
lean_ctor_set(v_reuseFailAlloc_1359_, 9, v_snapshotTasks_1332_);
v___x_1354_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = lean_st_ref_put(v___y_1314_, v___x_1354_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1341_);
v___x_1357_ = v___x_1320_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1341_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object* v_cls_1364_, lean_object* v_msg_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1364_, v_msg_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0));
v___x_1374_ = l_Lean_stringToMessageData(v___x_1373_);
return v___x_1374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16(void){
_start:
{
lean_object* v_cls_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_cls_1397_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1398_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15));
v___x_1399_ = l_Lean_Name_append(v___x_1398_, v_cls_1397_);
return v___x_1399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17));
v___x_1402_ = l_Lean_stringToMessageData(v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1403_, lean_object* v_mvarId_1404_, lean_object* v_depth_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v_a_1416_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; uint8_t v___y_1453_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; uint8_t v___y_1478_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v_a_1502_; uint8_t v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; uint8_t v___y_1514_; uint8_t v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v_a_1556_; uint8_t v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; uint8_t v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; uint8_t v___y_1579_; lean_object* v___y_1603_; uint8_t v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; uint8_t v___y_1611_; lean_object* v___y_1628_; uint8_t v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; uint8_t v___y_1636_; uint8_t v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; uint8_t v___y_1661_; lean_object* v___y_1679_; uint8_t v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; uint8_t v___y_1687_; uint8_t v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; uint8_t v___y_1716_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v_toCold_1767_; lean_object* v_currRecDepth_1768_; lean_object* v_ref_1769_; uint16_t v_optionFlags_1770_; uint8_t v_suppressElabErrors_1771_; uint8_t v_isRecordingDeps_1772_; lean_object* v_options_1773_; lean_object* v_maxRecDepth_1774_; lean_object* v_inheritedTraceOptions_1775_; lean_object* v_cls_1776_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_toCold_1767_ = lean_ctor_get(v_a_1408_, 0);
v_currRecDepth_1768_ = lean_ctor_get(v_a_1408_, 1);
v_ref_1769_ = lean_ctor_get(v_a_1408_, 2);
v_optionFlags_1770_ = lean_ctor_get_uint16(v_a_1408_, sizeof(void*)*3);
v_suppressElabErrors_1771_ = lean_ctor_get_uint8(v_a_1408_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1772_ = lean_ctor_get_uint8(v_a_1408_, sizeof(void*)*3 + 3);
v_options_1773_ = lean_ctor_get(v_toCold_1767_, 2);
v_maxRecDepth_1774_ = lean_ctor_get(v_toCold_1767_, 3);
v_inheritedTraceOptions_1775_ = lean_ctor_get(v_toCold_1767_, 11);
v_cls_1776_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_nat_dec_eq(v_maxRecDepth_1774_, v___x_1788_);
if (v___x_1789_ == 0)
{
uint8_t v___x_1790_; 
v___x_1790_ = lean_nat_dec_eq(v_currRecDepth_1768_, v_maxRecDepth_1774_);
if (v___x_1790_ == 0)
{
goto v___jp_1777_;
}
else
{
lean_object* v___x_1791_; 
lean_dec(v_mvarId_1404_);
lean_dec(v_matchDeclName_1403_);
lean_inc(v_ref_1769_);
v___x_1791_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1769_);
return v___x_1791_;
}
}
else
{
goto v___jp_1777_;
}
v___jp_1411_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = lean_array_get_size(v_a_1416_);
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_nat_dec_lt(v___x_1417_, v___x_1418_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v_a_1416_);
lean_dec_ref(v___y_1413_);
lean_dec(v_matchDeclName_1403_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1419_);
return v___x_1421_;
}
else
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_nat_dec_le(v___x_1418_, v___x_1418_);
if (v___x_1422_ == 0)
{
if (v___x_1420_ == 0)
{
lean_object* v___x_1423_; 
lean_dec_ref(v_a_1416_);
lean_dec_ref(v___y_1413_);
lean_dec(v_matchDeclName_1403_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1419_);
return v___x_1423_;
}
else
{
size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = lean_usize_of_nat(v___x_1418_);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1405_, v_matchDeclName_1403_, v_a_1416_, v___x_1424_, v___x_1425_, v___x_1419_, v___y_1412_, v___y_1415_, v___y_1413_, v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec_ref(v_a_1416_);
return v___x_1426_;
}
}
else
{
size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = lean_usize_of_nat(v___x_1418_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1405_, v_matchDeclName_1403_, v_a_1416_, v___x_1427_, v___x_1428_, v___x_1419_, v___y_1412_, v___y_1415_, v___y_1413_, v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec_ref(v_a_1416_);
return v___x_1429_;
}
}
}
v___jp_1430_:
{
if (lean_obj_tag(v___y_1435_) == 0)
{
lean_object* v_a_1436_; 
v_a_1436_ = lean_ctor_get(v___y_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___y_1435_, 1);
v___y_1412_ = v___y_1431_;
v___y_1413_ = v___y_1432_;
v___y_1414_ = v___y_1433_;
v___y_1415_ = v___y_1434_;
v_a_1416_ = v_a_1436_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v___y_1432_);
lean_dec(v_matchDeclName_1403_);
v_a_1437_ = lean_ctor_get(v___y_1435_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___y_1435_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___y_1435_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___y_1435_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
v___jp_1445_:
{
if (v___y_1453_ == 0)
{
lean_object* v___x_1454_; 
lean_dec_ref(v___y_1446_);
v___x_1454_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1447_, v___y_1452_, v___y_1451_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1468_; 
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v___x_1454_, 0);
lean_dec(v_unused_1469_);
v___x_1456_ = v___x_1454_;
v_isShared_1457_ = v_isSharedCheck_1468_;
goto v_resetjp_1455_;
}
else
{
lean_dec(v___x_1454_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1468_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1458_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1403_);
v___x_1459_ = l_Lean_MessageData_ofName(v_matchDeclName_1403_);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 1);
lean_ctor_set(v___x_1456_, 0, v___y_1450_);
v___x_1464_ = v___x_1456_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___y_1450_);
v___x_1464_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1462_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1465_, v___y_1448_, v___y_1452_, v___y_1449_, v___y_1451_);
v___y_1431_ = v___y_1448_;
v___y_1432_ = v___y_1449_;
v___y_1433_ = v___y_1451_;
v___y_1434_ = v___y_1452_;
v___y_1435_ = v___x_1466_;
goto v___jp_1430_;
}
}
}
else
{
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v_matchDeclName_1403_);
return v___x_1454_;
}
}
else
{
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1447_);
v___y_1431_ = v___y_1448_;
v___y_1432_ = v___y_1449_;
v___y_1433_ = v___y_1451_;
v___y_1434_ = v___y_1452_;
v___y_1435_ = v___y_1446_;
goto v___jp_1430_;
}
}
v___jp_1470_:
{
if (v___y_1478_ == 0)
{
lean_object* v___x_1479_; 
lean_dec_ref(v___y_1471_);
v___x_1479_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1476_, v___y_1477_, v___y_1475_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v___x_1480_; 
lean_dec_ref_known(v___x_1479_, 1);
v___x_1480_ = l_Lean_Meta_saveState___redArg(v___y_1477_, v___y_1475_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1482_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
lean_inc(v___y_1474_);
v___x_1482_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1474_, v___y_1472_, v___y_1477_, v___y_1473_, v___y_1475_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_dec(v_a_1481_);
lean_dec(v___y_1474_);
v___y_1431_ = v___y_1472_;
v___y_1432_ = v___y_1473_;
v___y_1433_ = v___y_1475_;
v___y_1434_ = v___y_1477_;
v___y_1435_ = v___x_1482_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1483_; uint8_t v___x_1484_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v___x_1484_ = l_Lean_Exception_isInterrupt(v_a_1483_);
if (v___x_1484_ == 0)
{
uint8_t v___x_1485_; 
lean_inc(v_a_1483_);
v___x_1485_ = l_Lean_Exception_isRuntime(v_a_1483_);
v___y_1446_ = v___x_1482_;
v___y_1447_ = v_a_1481_;
v___y_1448_ = v___y_1472_;
v___y_1449_ = v___y_1473_;
v___y_1450_ = v___y_1474_;
v___y_1451_ = v___y_1475_;
v___y_1452_ = v___y_1477_;
v___y_1453_ = v___x_1485_;
goto v___jp_1445_;
}
else
{
v___y_1446_ = v___x_1482_;
v___y_1447_ = v_a_1481_;
v___y_1448_ = v___y_1472_;
v___y_1449_ = v___y_1473_;
v___y_1450_ = v___y_1474_;
v___y_1451_ = v___y_1475_;
v___y_1452_ = v___y_1477_;
v___y_1453_ = v___x_1484_;
goto v___jp_1445_;
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v_matchDeclName_1403_);
v_a_1486_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1480_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1480_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v_matchDeclName_1403_);
return v___x_1479_;
}
}
else
{
lean_object* v___x_1494_; 
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v_matchDeclName_1403_);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___y_1471_);
return v___x_1494_;
}
}
v___jp_1495_:
{
uint8_t v___x_1503_; 
v___x_1503_ = l_Lean_Exception_isInterrupt(v_a_1502_);
if (v___x_1503_ == 0)
{
uint8_t v___x_1504_; 
lean_inc_ref(v_a_1502_);
v___x_1504_ = l_Lean_Exception_isRuntime(v_a_1502_);
v___y_1471_ = v_a_1502_;
v___y_1472_ = v___y_1496_;
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___y_1499_;
v___y_1475_ = v___y_1498_;
v___y_1476_ = v___y_1500_;
v___y_1477_ = v___y_1501_;
v___y_1478_ = v___x_1504_;
goto v___jp_1470_;
}
else
{
v___y_1471_ = v_a_1502_;
v___y_1472_ = v___y_1496_;
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___y_1499_;
v___y_1475_ = v___y_1498_;
v___y_1476_ = v___y_1500_;
v___y_1477_ = v___y_1501_;
v___y_1478_ = v___x_1503_;
goto v___jp_1470_;
}
}
v___jp_1505_:
{
if (v___y_1514_ == 0)
{
lean_object* v___x_1515_; 
lean_dec_ref(v___y_1507_);
v___x_1515_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1513_, v___y_1512_, v___y_1511_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref_known(v___x_1515_, 1);
v___x_1516_ = lean_box(0);
v___x_1517_ = l_Lean_Meta_saveState___redArg(v___y_1512_, v___y_1511_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
lean_inc(v___y_1510_);
v___x_1519_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1510_, v___x_1516_, v___y_1506_, v___y_1508_, v___y_1512_, v___y_1509_, v___y_1511_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
if (lean_obj_tag(v_a_1520_) == 1)
{
lean_object* v_val_1521_; lean_object* v_fst_1522_; lean_object* v_snd_1523_; lean_object* v_mvarId_1524_; lean_object* v_fvarId_1525_; lean_object* v___x_1526_; 
v_val_1521_ = lean_ctor_get(v_a_1520_, 0);
lean_inc(v_val_1521_);
lean_dec_ref_known(v_a_1520_, 1);
v_fst_1522_ = lean_ctor_get(v_val_1521_, 0);
lean_inc(v_fst_1522_);
v_snd_1523_ = lean_ctor_get(v_val_1521_, 1);
lean_inc(v_snd_1523_);
lean_dec(v_val_1521_);
v_mvarId_1524_ = lean_ctor_get(v_fst_1522_, 0);
lean_inc(v_mvarId_1524_);
v_fvarId_1525_ = lean_ctor_get(v_fst_1522_, 1);
lean_inc(v_fvarId_1525_);
lean_dec(v_fst_1522_);
v___x_1526_ = l_Lean_Meta_trySubst(v_mvarId_1524_, v_fvarId_1525_, v___y_1508_, v___y_1512_, v___y_1509_, v___y_1511_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v_mvarId_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_a_1518_);
lean_dec(v___y_1510_);
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v_mvarId_1528_ = lean_ctor_get(v_snd_1523_, 0);
lean_inc(v_mvarId_1528_);
lean_dec(v_snd_1523_);
v___x_1529_ = lean_unsigned_to_nat(2u);
v___x_1530_ = lean_mk_empty_array_with_capacity(v___x_1529_);
v___x_1531_ = lean_array_push(v___x_1530_, v_a_1527_);
v___x_1532_ = lean_array_push(v___x_1531_, v_mvarId_1528_);
v___y_1412_ = v___y_1508_;
v___y_1413_ = v___y_1509_;
v___y_1414_ = v___y_1511_;
v___y_1415_ = v___y_1512_;
v_a_1416_ = v___x_1532_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1533_; 
lean_dec(v_snd_1523_);
v_a_1533_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1526_, 1);
v___y_1496_ = v___y_1508_;
v___y_1497_ = v___y_1509_;
v___y_1498_ = v___y_1511_;
v___y_1499_ = v___y_1510_;
v___y_1500_ = v_a_1518_;
v___y_1501_ = v___y_1512_;
v_a_1502_ = v_a_1533_;
goto v___jp_1495_;
}
}
else
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v_a_1520_);
v___x_1534_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1535_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1534_, v___y_1508_, v___y_1512_, v___y_1509_, v___y_1511_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; 
lean_dec(v_a_1518_);
lean_dec(v___y_1510_);
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___y_1412_ = v___y_1508_;
v___y_1413_ = v___y_1509_;
v___y_1414_ = v___y_1511_;
v___y_1415_ = v___y_1512_;
v_a_1416_ = v_a_1536_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1537_; 
v_a_1537_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1535_, 1);
v___y_1496_ = v___y_1508_;
v___y_1497_ = v___y_1509_;
v___y_1498_ = v___y_1511_;
v___y_1499_ = v___y_1510_;
v___y_1500_ = v_a_1518_;
v___y_1501_ = v___y_1512_;
v_a_1502_ = v_a_1537_;
goto v___jp_1495_;
}
}
}
else
{
lean_object* v_a_1538_; 
v_a_1538_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1519_, 1);
v___y_1496_ = v___y_1508_;
v___y_1497_ = v___y_1509_;
v___y_1498_ = v___y_1511_;
v___y_1499_ = v___y_1510_;
v___y_1500_ = v_a_1518_;
v___y_1501_ = v___y_1512_;
v_a_1502_ = v_a_1538_;
goto v___jp_1495_;
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v_matchDeclName_1403_);
v_a_1539_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1517_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1517_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v_matchDeclName_1403_);
return v___x_1515_;
}
}
else
{
lean_object* v___x_1547_; 
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v_matchDeclName_1403_);
v___x_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___y_1507_);
return v___x_1547_;
}
}
v___jp_1548_:
{
uint8_t v___x_1557_; 
v___x_1557_ = l_Lean_Exception_isInterrupt(v_a_1556_);
if (v___x_1557_ == 0)
{
uint8_t v___x_1558_; 
lean_inc_ref(v_a_1556_);
v___x_1558_ = l_Lean_Exception_isRuntime(v_a_1556_);
v___y_1506_ = v___y_1549_;
v___y_1507_ = v_a_1556_;
v___y_1508_ = v___y_1550_;
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___y_1553_;
v___y_1511_ = v___y_1552_;
v___y_1512_ = v___y_1554_;
v___y_1513_ = v___y_1555_;
v___y_1514_ = v___x_1558_;
goto v___jp_1505_;
}
else
{
v___y_1506_ = v___y_1549_;
v___y_1507_ = v_a_1556_;
v___y_1508_ = v___y_1550_;
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___y_1553_;
v___y_1511_ = v___y_1552_;
v___y_1512_ = v___y_1554_;
v___y_1513_ = v___y_1555_;
v___y_1514_ = v___x_1557_;
goto v___jp_1505_;
}
}
v___jp_1559_:
{
if (lean_obj_tag(v___y_1567_) == 0)
{
lean_object* v_a_1568_; 
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1563_);
v_a_1568_ = lean_ctor_get(v___y_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___y_1567_, 1);
v___y_1412_ = v___y_1561_;
v___y_1413_ = v___y_1562_;
v___y_1414_ = v___y_1564_;
v___y_1415_ = v___y_1565_;
v_a_1416_ = v_a_1568_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1569_; 
v_a_1569_ = lean_ctor_get(v___y_1567_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___y_1567_, 1);
v___y_1549_ = v___y_1560_;
v___y_1550_ = v___y_1561_;
v___y_1551_ = v___y_1562_;
v___y_1552_ = v___y_1564_;
v___y_1553_ = v___y_1563_;
v___y_1554_ = v___y_1565_;
v___y_1555_ = v___y_1566_;
v_a_1556_ = v_a_1569_;
goto v___jp_1548_;
}
}
v___jp_1570_:
{
if (v___y_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref(v___y_1577_);
v___x_1580_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1573_, v___y_1578_, v___y_1576_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v___x_1581_; 
lean_dec_ref_known(v___x_1580_, 1);
v___x_1581_ = l_Lean_Meta_saveState___redArg(v___y_1578_, v___y_1576_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
lean_inc(v___y_1575_);
v___x_1583_ = l_Lean_Meta_simpIfTarget(v___y_1575_, v___y_1571_, v___y_1571_, v___y_1572_, v___y_1578_, v___y_1574_, v___y_1576_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; uint8_t v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = l_Lean_instBEqMVarId_beq(v_a_1584_, v___y_1575_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_box(0);
v___x_1587_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1584_, v___x_1586_, v___y_1572_, v___y_1578_, v___y_1574_, v___y_1576_);
v___y_1560_ = v___y_1571_;
v___y_1561_ = v___y_1572_;
v___y_1562_ = v___y_1574_;
v___y_1563_ = v___y_1575_;
v___y_1564_ = v___y_1576_;
v___y_1565_ = v___y_1578_;
v___y_1566_ = v_a_1582_;
v___y_1567_ = v___x_1587_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1589_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1588_, v___y_1572_, v___y_1578_, v___y_1574_, v___y_1576_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1584_, v_a_1590_, v___y_1572_, v___y_1578_, v___y_1574_, v___y_1576_);
v___y_1560_ = v___y_1571_;
v___y_1561_ = v___y_1572_;
v___y_1562_ = v___y_1574_;
v___y_1563_ = v___y_1575_;
v___y_1564_ = v___y_1576_;
v___y_1565_ = v___y_1578_;
v___y_1566_ = v_a_1582_;
v___y_1567_ = v___x_1591_;
goto v___jp_1559_;
}
else
{
lean_object* v_a_1592_; 
lean_dec(v_a_1584_);
v_a_1592_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1589_, 1);
v___y_1549_ = v___y_1571_;
v___y_1550_ = v___y_1572_;
v___y_1551_ = v___y_1574_;
v___y_1552_ = v___y_1576_;
v___y_1553_ = v___y_1575_;
v___y_1554_ = v___y_1578_;
v___y_1555_ = v_a_1582_;
v_a_1556_ = v_a_1592_;
goto v___jp_1548_;
}
}
}
else
{
lean_object* v_a_1593_; 
v_a_1593_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1583_, 1);
v___y_1549_ = v___y_1571_;
v___y_1550_ = v___y_1572_;
v___y_1551_ = v___y_1574_;
v___y_1552_ = v___y_1576_;
v___y_1553_ = v___y_1575_;
v___y_1554_ = v___y_1578_;
v___y_1555_ = v_a_1582_;
v_a_1556_ = v_a_1593_;
goto v___jp_1548_;
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v_matchDeclName_1403_);
v_a_1594_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1581_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1581_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v_matchDeclName_1403_);
return v___x_1580_;
}
}
else
{
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1573_);
v___y_1431_ = v___y_1572_;
v___y_1432_ = v___y_1574_;
v___y_1433_ = v___y_1576_;
v___y_1434_ = v___y_1578_;
v___y_1435_ = v___y_1577_;
goto v___jp_1430_;
}
}
v___jp_1602_:
{
if (v___y_1611_ == 0)
{
lean_object* v___x_1612_; 
lean_dec_ref(v___y_1603_);
v___x_1612_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1609_, v___y_1610_, v___y_1608_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v___x_1613_; 
lean_dec_ref_known(v___x_1612_, 1);
v___x_1613_ = l_Lean_Meta_saveState___redArg(v___y_1610_, v___y_1608_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1615_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
lean_inc(v___y_1607_);
v___x_1615_ = l_Lean_Meta_splitSparseCasesOn(v___y_1607_, v___y_1605_, v___y_1610_, v___y_1606_, v___y_1608_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_dec(v_a_1614_);
lean_dec(v___y_1607_);
v___y_1431_ = v___y_1605_;
v___y_1432_ = v___y_1606_;
v___y_1433_ = v___y_1608_;
v___y_1434_ = v___y_1610_;
v___y_1435_ = v___x_1615_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1616_; uint8_t v___x_1617_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v___x_1617_ = l_Lean_Exception_isInterrupt(v_a_1616_);
if (v___x_1617_ == 0)
{
uint8_t v___x_1618_; 
lean_inc(v_a_1616_);
v___x_1618_ = l_Lean_Exception_isRuntime(v_a_1616_);
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v_a_1614_;
v___y_1574_ = v___y_1606_;
v___y_1575_ = v___y_1607_;
v___y_1576_ = v___y_1608_;
v___y_1577_ = v___x_1615_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___x_1618_;
goto v___jp_1570_;
}
else
{
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v_a_1614_;
v___y_1574_ = v___y_1606_;
v___y_1575_ = v___y_1607_;
v___y_1576_ = v___y_1608_;
v___y_1577_ = v___x_1615_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___x_1617_;
goto v___jp_1570_;
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v_matchDeclName_1403_);
v_a_1619_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1613_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1613_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
else
{
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v_matchDeclName_1403_);
return v___x_1612_;
}
}
else
{
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1607_);
v___y_1431_ = v___y_1605_;
v___y_1432_ = v___y_1606_;
v___y_1433_ = v___y_1608_;
v___y_1434_ = v___y_1610_;
v___y_1435_ = v___y_1603_;
goto v___jp_1430_;
}
}
v___jp_1627_:
{
if (v___y_1636_ == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref(v___y_1628_);
v___x_1637_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1634_, v___y_1635_, v___y_1633_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v___x_1638_; 
lean_dec_ref_known(v___x_1637_, 1);
v___x_1638_ = l_Lean_Meta_saveState___redArg(v___y_1635_, v___y_1633_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
lean_inc(v___y_1632_);
v___x_1640_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1632_, v___y_1630_, v___y_1635_, v___y_1631_, v___y_1633_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_dec(v_a_1639_);
lean_dec(v___y_1632_);
v___y_1431_ = v___y_1630_;
v___y_1432_ = v___y_1631_;
v___y_1433_ = v___y_1633_;
v___y_1434_ = v___y_1635_;
v___y_1435_ = v___x_1640_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1641_; uint8_t v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v___x_1642_ = l_Lean_Exception_isInterrupt(v_a_1641_);
if (v___x_1642_ == 0)
{
uint8_t v___x_1643_; 
lean_inc(v_a_1641_);
v___x_1643_ = l_Lean_Exception_isRuntime(v_a_1641_);
v___y_1603_ = v___x_1640_;
v___y_1604_ = v___y_1629_;
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___y_1631_;
v___y_1607_ = v___y_1632_;
v___y_1608_ = v___y_1633_;
v___y_1609_ = v_a_1639_;
v___y_1610_ = v___y_1635_;
v___y_1611_ = v___x_1643_;
goto v___jp_1602_;
}
else
{
v___y_1603_ = v___x_1640_;
v___y_1604_ = v___y_1629_;
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___y_1631_;
v___y_1607_ = v___y_1632_;
v___y_1608_ = v___y_1633_;
v___y_1609_ = v_a_1639_;
v___y_1610_ = v___y_1635_;
v___y_1611_ = v___x_1642_;
goto v___jp_1602_;
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v_matchDeclName_1403_);
v_a_1644_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1638_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1638_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v_matchDeclName_1403_);
return v___x_1637_;
}
}
else
{
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1632_);
v___y_1431_ = v___y_1630_;
v___y_1432_ = v___y_1631_;
v___y_1433_ = v___y_1633_;
v___y_1434_ = v___y_1635_;
v___y_1435_ = v___y_1628_;
goto v___jp_1430_;
}
}
v___jp_1652_:
{
if (v___y_1661_ == 0)
{
lean_object* v___x_1662_; 
lean_dec_ref(v___y_1660_);
v___x_1662_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1656_, v___y_1659_, v___y_1658_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v___x_1663_; 
lean_dec_ref_known(v___x_1662_, 1);
v___x_1663_ = l_Lean_Meta_saveState___redArg(v___y_1659_, v___y_1658_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
lean_inc(v___y_1657_);
v___x_1665_ = l_Lean_Meta_casesOnStuckLHS(v___y_1657_, v___y_1654_, v___y_1659_, v___y_1655_, v___y_1658_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_dec(v_a_1664_);
lean_dec(v___y_1657_);
v___y_1431_ = v___y_1654_;
v___y_1432_ = v___y_1655_;
v___y_1433_ = v___y_1658_;
v___y_1434_ = v___y_1659_;
v___y_1435_ = v___x_1665_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1666_; uint8_t v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v___x_1667_ = l_Lean_Exception_isInterrupt(v_a_1666_);
if (v___x_1667_ == 0)
{
uint8_t v___x_1668_; 
lean_inc(v_a_1666_);
v___x_1668_ = l_Lean_Exception_isRuntime(v_a_1666_);
v___y_1628_ = v___x_1665_;
v___y_1629_ = v___y_1653_;
v___y_1630_ = v___y_1654_;
v___y_1631_ = v___y_1655_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___y_1658_;
v___y_1634_ = v_a_1664_;
v___y_1635_ = v___y_1659_;
v___y_1636_ = v___x_1668_;
goto v___jp_1627_;
}
else
{
v___y_1628_ = v___x_1665_;
v___y_1629_ = v___y_1653_;
v___y_1630_ = v___y_1654_;
v___y_1631_ = v___y_1655_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___y_1658_;
v___y_1634_ = v_a_1664_;
v___y_1635_ = v___y_1659_;
v___y_1636_ = v___x_1667_;
goto v___jp_1627_;
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1655_);
lean_dec(v_matchDeclName_1403_);
v_a_1669_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1663_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1663_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1655_);
lean_dec(v_matchDeclName_1403_);
return v___x_1662_;
}
}
else
{
lean_object* v___x_1677_; 
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v_matchDeclName_1403_);
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___y_1660_);
return v___x_1677_;
}
}
v___jp_1678_:
{
if (v___y_1687_ == 0)
{
lean_object* v___x_1688_; 
lean_dec_ref(v___y_1679_);
v___x_1688_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1682_, v___y_1686_, v___y_1685_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v___x_1689_; 
lean_dec_ref_known(v___x_1688_, 1);
v___x_1689_ = l_Lean_Meta_saveState___redArg(v___y_1686_, v___y_1685_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1691_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
lean_inc(v___y_1684_);
v___x_1691_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1684_, v___y_1681_, v___y_1686_, v___y_1683_, v___y_1685_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v_a_1690_);
lean_dec(v___y_1684_);
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = lean_unsigned_to_nat(1u);
v___x_1694_ = lean_mk_empty_array_with_capacity(v___x_1693_);
v___x_1695_ = lean_array_push(v___x_1694_, v_a_1692_);
v___y_1412_ = v___y_1681_;
v___y_1413_ = v___y_1683_;
v___y_1414_ = v___y_1685_;
v___y_1415_ = v___y_1686_;
v_a_1416_ = v___x_1695_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1696_; uint8_t v___x_1697_; 
v_a_1696_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1697_ = l_Lean_Exception_isInterrupt(v_a_1696_);
if (v___x_1697_ == 0)
{
uint8_t v___x_1698_; 
lean_inc(v_a_1696_);
v___x_1698_ = l_Lean_Exception_isRuntime(v_a_1696_);
v___y_1653_ = v___y_1680_;
v___y_1654_ = v___y_1681_;
v___y_1655_ = v___y_1683_;
v___y_1656_ = v_a_1690_;
v___y_1657_ = v___y_1684_;
v___y_1658_ = v___y_1685_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v_a_1696_;
v___y_1661_ = v___x_1698_;
goto v___jp_1652_;
}
else
{
v___y_1653_ = v___y_1680_;
v___y_1654_ = v___y_1681_;
v___y_1655_ = v___y_1683_;
v___y_1656_ = v_a_1690_;
v___y_1657_ = v___y_1684_;
v___y_1658_ = v___y_1685_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v_a_1696_;
v___y_1661_ = v___x_1697_;
goto v___jp_1652_;
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_matchDeclName_1403_);
v_a_1699_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1689_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1689_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_matchDeclName_1403_);
return v___x_1688_;
}
}
else
{
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v_matchDeclName_1403_);
return v___y_1679_;
}
}
v___jp_1707_:
{
if (v___y_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref(v___y_1710_);
v___x_1717_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1709_, v___y_1715_, v___y_1714_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec_ref_known(v___x_1717_, 1);
v___x_1718_ = lean_unsigned_to_nat(16u);
v___x_1719_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*1, v___y_1708_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*1 + 1, v___y_1708_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*1 + 2, v___y_1708_);
v___x_1720_ = l_Lean_Meta_saveState___redArg(v___y_1715_, v___y_1714_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
lean_inc(v___y_1713_);
v___x_1722_ = l_Lean_MVarId_contradiction(v___y_1713_, v___x_1719_, v___y_1711_, v___y_1715_, v___y_1712_, v___y_1714_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v___x_1723_; 
lean_dec_ref_known(v___x_1722_, 1);
lean_dec(v_a_1721_);
lean_dec(v___y_1713_);
v___x_1723_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1412_ = v___y_1711_;
v___y_1413_ = v___y_1712_;
v___y_1414_ = v___y_1714_;
v___y_1415_ = v___y_1715_;
v_a_1416_ = v___x_1723_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1724_; uint8_t v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1722_, 0);
v___x_1725_ = l_Lean_Exception_isInterrupt(v_a_1724_);
if (v___x_1725_ == 0)
{
uint8_t v___x_1726_; 
lean_inc(v_a_1724_);
v___x_1726_ = l_Lean_Exception_isRuntime(v_a_1724_);
v___y_1679_ = v___x_1722_;
v___y_1680_ = v___y_1708_;
v___y_1681_ = v___y_1711_;
v___y_1682_ = v_a_1721_;
v___y_1683_ = v___y_1712_;
v___y_1684_ = v___y_1713_;
v___y_1685_ = v___y_1714_;
v___y_1686_ = v___y_1715_;
v___y_1687_ = v___x_1726_;
goto v___jp_1678_;
}
else
{
v___y_1679_ = v___x_1722_;
v___y_1680_ = v___y_1708_;
v___y_1681_ = v___y_1711_;
v___y_1682_ = v_a_1721_;
v___y_1683_ = v___y_1712_;
v___y_1684_ = v___y_1713_;
v___y_1685_ = v___y_1714_;
v___y_1686_ = v___y_1715_;
v___y_1687_ = v___x_1725_;
goto v___jp_1678_;
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec_ref_known(v___x_1719_, 1);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v_matchDeclName_1403_);
v_a_1727_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1720_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1720_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v_matchDeclName_1403_);
return v___x_1717_;
}
}
else
{
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec_ref(v___y_1709_);
lean_dec(v_matchDeclName_1403_);
return v___y_1710_;
}
}
v___jp_1735_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1741_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1404_, v___x_1740_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
v___x_1743_ = 1;
v___x_1744_ = l_Lean_Meta_saveState___redArg(v___y_1737_, v___y_1739_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
lean_inc(v_a_1742_);
v___x_1746_ = l_Lean_MVarId_refl(v_a_1742_, v___x_1743_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v___x_1747_; 
lean_dec_ref_known(v___x_1746_, 1);
lean_dec(v_a_1745_);
lean_dec(v_a_1742_);
v___x_1747_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1412_ = v___y_1736_;
v___y_1413_ = v___y_1738_;
v___y_1414_ = v___y_1739_;
v___y_1415_ = v___y_1737_;
v_a_1416_ = v___x_1747_;
goto v___jp_1411_;
}
else
{
lean_object* v_a_1748_; uint8_t v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___x_1746_, 0);
v___x_1749_ = l_Lean_Exception_isInterrupt(v_a_1748_);
if (v___x_1749_ == 0)
{
uint8_t v___x_1750_; 
lean_inc(v_a_1748_);
v___x_1750_ = l_Lean_Exception_isRuntime(v_a_1748_);
v___y_1708_ = v___x_1743_;
v___y_1709_ = v_a_1745_;
v___y_1710_ = v___x_1746_;
v___y_1711_ = v___y_1736_;
v___y_1712_ = v___y_1738_;
v___y_1713_ = v_a_1742_;
v___y_1714_ = v___y_1739_;
v___y_1715_ = v___y_1737_;
v___y_1716_ = v___x_1750_;
goto v___jp_1707_;
}
else
{
v___y_1708_ = v___x_1743_;
v___y_1709_ = v_a_1745_;
v___y_1710_ = v___x_1746_;
v___y_1711_ = v___y_1736_;
v___y_1712_ = v___y_1738_;
v___y_1713_ = v_a_1742_;
v___y_1714_ = v___y_1739_;
v___y_1715_ = v___y_1737_;
v___y_1716_ = v___x_1749_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_a_1742_);
lean_dec_ref(v___y_1738_);
lean_dec(v_matchDeclName_1403_);
v_a_1751_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1744_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1744_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec_ref(v___y_1738_);
lean_dec(v_matchDeclName_1403_);
v_a_1759_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1741_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1741_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
v___jp_1777_:
{
uint8_t v_hasTrace_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_hasTrace_1778_ = lean_ctor_get_uint8(v_options_1773_, sizeof(void*)*1);
v___x_1779_ = lean_unsigned_to_nat(1u);
v___x_1780_ = lean_nat_add(v_currRecDepth_1768_, v___x_1779_);
lean_inc(v_ref_1769_);
lean_inc_ref(v_toCold_1767_);
v___x_1781_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1781_, 0, v_toCold_1767_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
lean_ctor_set(v___x_1781_, 2, v_ref_1769_);
lean_ctor_set_uint16(v___x_1781_, sizeof(void*)*3, v_optionFlags_1770_);
lean_ctor_set_uint8(v___x_1781_, sizeof(void*)*3 + 2, v_suppressElabErrors_1771_);
lean_ctor_set_uint8(v___x_1781_, sizeof(void*)*3 + 3, v_isRecordingDeps_1772_);
if (v_hasTrace_1778_ == 0)
{
v___y_1736_ = v_a_1406_;
v___y_1737_ = v_a_1407_;
v___y_1738_ = v___x_1781_;
v___y_1739_ = v_a_1409_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1782_; uint8_t v___x_1783_; 
v___x_1782_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1783_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1775_, v_options_1773_, v___x_1782_);
if (v___x_1783_ == 0)
{
v___y_1736_ = v_a_1406_;
v___y_1737_ = v_a_1407_;
v___y_1738_ = v___x_1781_;
v___y_1739_ = v_a_1409_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1784_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1404_);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_mvarId_1404_);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1776_, v___x_1786_, v_a_1406_, v_a_1407_, v___x_1781_, v_a_1409_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_dec_ref_known(v___x_1787_, 1);
v___y_1736_ = v_a_1406_;
v___y_1737_ = v_a_1407_;
v___y_1738_ = v___x_1781_;
v___y_1739_ = v_a_1409_;
goto v___jp_1735_;
}
else
{
lean_dec_ref_known(v___x_1781_, 3);
lean_dec(v_mvarId_1404_);
lean_dec(v_matchDeclName_1403_);
return v___x_1787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1792_, lean_object* v_matchDeclName_1793_, lean_object* v_as_1794_, size_t v_i_1795_, size_t v_stop_1796_, lean_object* v_b_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_usize_dec_eq(v_i_1795_, v_stop_1796_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1804_ = lean_array_uget_borrowed(v_as_1794_, v_i_1795_);
v___x_1805_ = lean_unsigned_to_nat(1u);
v___x_1806_ = lean_nat_add(v_depth_1792_, v___x_1805_);
lean_inc(v___x_1804_);
lean_inc(v_matchDeclName_1793_);
v___x_1807_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1793_, v___x_1804_, v___x_1806_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec(v___x_1806_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; size_t v___x_1809_; size_t v___x_1810_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v___x_1809_ = ((size_t)1ULL);
v___x_1810_ = lean_usize_add(v_i_1795_, v___x_1809_);
v_i_1795_ = v___x_1810_;
v_b_1797_ = v_a_1808_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1793_);
return v___x_1807_;
}
}
else
{
lean_object* v___x_1812_; 
lean_dec(v_matchDeclName_1793_);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_b_1797_);
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1813_, lean_object* v_matchDeclName_1814_, lean_object* v_as_1815_, lean_object* v_i_1816_, lean_object* v_stop_1817_, lean_object* v_b_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
size_t v_i_boxed_1824_; size_t v_stop_boxed_1825_; lean_object* v_res_1826_; 
v_i_boxed_1824_ = lean_unbox_usize(v_i_1816_);
lean_dec(v_i_1816_);
v_stop_boxed_1825_ = lean_unbox_usize(v_stop_1817_);
lean_dec(v_stop_1817_);
v_res_1826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1813_, v_matchDeclName_1814_, v_as_1815_, v_i_boxed_1824_, v_stop_boxed_1825_, v_b_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec_ref(v_as_1815_);
lean_dec(v_depth_1813_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1827_, lean_object* v_mvarId_1828_, lean_object* v_depth_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1827_, v_mvarId_1828_, v_depth_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_depth_1829_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1836_, lean_object* v___y_1837_){
_start:
{
uint8_t v___x_1839_; 
v___x_1839_ = l_Lean_Expr_hasMVar(v_e_1836_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_e_1836_);
return v___x_1840_;
}
else
{
lean_object* v___x_1841_; lean_object* v_mctx_1842_; lean_object* v___x_1843_; lean_object* v_fst_1844_; lean_object* v_snd_1845_; lean_object* v___x_1846_; lean_object* v_cache_1847_; lean_object* v_zetaDeltaFVarIds_1848_; lean_object* v_postponed_1849_; lean_object* v_diag_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1859_; 
v___x_1841_ = lean_st_ref_get(v___y_1837_);
v_mctx_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc_ref(v_mctx_1842_);
lean_dec(v___x_1841_);
v___x_1843_ = l_Lean_instantiateMVarsCore(v_mctx_1842_, v_e_1836_);
v_fst_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_fst_1844_);
v_snd_1845_ = lean_ctor_get(v___x_1843_, 1);
lean_inc(v_snd_1845_);
lean_dec_ref(v___x_1843_);
v___x_1846_ = lean_st_ref_take(v___y_1837_);
v_cache_1847_ = lean_ctor_get(v___x_1846_, 1);
v_zetaDeltaFVarIds_1848_ = lean_ctor_get(v___x_1846_, 2);
v_postponed_1849_ = lean_ctor_get(v___x_1846_, 3);
v_diag_1850_ = lean_ctor_get(v___x_1846_, 4);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1846_, 0);
lean_dec(v_unused_1860_);
v___x_1852_ = v___x_1846_;
v_isShared_1853_ = v_isSharedCheck_1859_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_diag_1850_);
lean_inc(v_postponed_1849_);
lean_inc(v_zetaDeltaFVarIds_1848_);
lean_inc(v_cache_1847_);
lean_dec(v___x_1846_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1859_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_snd_1845_);
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_snd_1845_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_cache_1847_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_zetaDeltaFVarIds_1848_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_postponed_1849_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_diag_1850_);
v___x_1855_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_st_ref_put(v___y_1837_, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_fst_1844_);
return v___x_1857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1861_, v___y_1862_);
lean_dec(v___y_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1865_, v___y_1867_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1879_, lean_object* v_localInsts_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1879_, v_localInsts_1880_, v_x_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
v_a_1896_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1887_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1887_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1904_, lean_object* v_localInsts_1905_, lean_object* v_x_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1904_, v_localInsts_1905_, v_x_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1913_, lean_object* v_lctx_1914_, lean_object* v_localInsts_1915_, lean_object* v_x_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1914_, v_localInsts_1915_, v_x_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1923_, lean_object* v_lctx_1924_, lean_object* v_localInsts_1925_, lean_object* v_x_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1923_, v_lctx_1924_, v_localInsts_1925_, v_x_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1932_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1933_, lean_object* v_x_1934_){
_start:
{
uint8_t v___x_1935_; 
v___x_1935_ = lean_name_eq(v_x_1934_, v_matchDeclName_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1936_, lean_object* v_x_1937_){
_start:
{
uint8_t v_res_1938_; lean_object* v_r_1939_; 
v_res_1938_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1936_, v_x_1937_);
lean_dec(v_x_1937_);
lean_dec(v_matchDeclName_1936_);
v_r_1939_ = lean_box(v_res_1938_);
return v_r_1939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1940_, lean_object* v_a_1941_, lean_object* v_b_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_nat_dec_lt(v_a_1941_, v_upperBound_1940_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; 
lean_dec(v_a_1941_);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_b_1942_);
return v___x_1949_;
}
else
{
uint8_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = 0;
v___x_1951_ = l_Lean_Meta_introSubstEq(v_b_1942_, v___x_1950_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v_snd_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v_snd_1953_ = lean_ctor_get(v_a_1952_, 1);
lean_inc(v_snd_1953_);
lean_dec(v_a_1952_);
v___x_1954_ = lean_unsigned_to_nat(1u);
v___x_1955_ = lean_nat_add(v_a_1941_, v___x_1954_);
lean_dec(v_a_1941_);
v_a_1941_ = v___x_1955_;
v_b_1942_ = v_snd_1953_;
goto _start;
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec(v_a_1941_);
v_a_1957_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1951_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1951_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1965_, lean_object* v_a_1966_, lean_object* v_b_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1965_, v_a_1966_, v_b_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v_upperBound_1965_);
return v_res_1973_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1976_ = l_Lean_stringToMessageData(v___x_1975_);
return v___x_1976_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1979_ = l_Lean_stringToMessageData(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1980_, lean_object* v___f_1981_, lean_object* v_matchDeclName_1982_, lean_object* v___x_1983_, lean_object* v_heqNum_1984_, lean_object* v_heqPos_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1991_; lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2145_; 
v___x_1991_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1980_, v___y_1987_);
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2145_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2145_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_box(0);
v___x_1997_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1992_, v___x_1996_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2144_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2144_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2144_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; uint8_t v___y_2009_; lean_object* v_mvarId_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v_toCold_2066_; lean_object* v_options_2067_; lean_object* v_inheritedTraceOptions_2068_; uint8_t v_hasTrace_2069_; lean_object* v___x_2070_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; 
v_toCold_2066_ = lean_ctor_get(v___y_1988_, 0);
v_options_2067_ = lean_ctor_get(v_toCold_2066_, 2);
v_inheritedTraceOptions_2068_ = lean_ctor_get(v_toCold_2066_, 11);
v_hasTrace_2069_ = lean_ctor_get_uint8(v_options_2067_, sizeof(void*)*1);
v___x_2070_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2069_ == 0)
{
v___y_2072_ = v___y_1986_;
v___y_2073_ = v___y_1987_;
v___y_2074_ = v___y_1988_;
v___y_2075_ = v___y_1989_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2068_, v_options_2067_, v___x_2129_);
if (v___x_2130_ == 0)
{
v___y_2072_ = v___y_1986_;
v___y_2073_ = v___y_1987_;
v___y_2074_ = v___y_1988_;
v___y_2075_ = v___y_1989_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2131_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2132_ = l_Lean_Expr_mvarId_x21(v_a_1998_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2131_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2070_, v___x_2134_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_dec_ref_known(v___x_2135_, 1);
v___y_2072_ = v___y_1986_;
v___y_2073_ = v___y_1987_;
v___y_2074_ = v___y_1988_;
v___y_2075_ = v___y_1989_;
goto v___jp_2071_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_del_object(v___x_2000_);
lean_dec(v_a_1998_);
lean_del_object(v___x_1994_);
lean_dec(v_heqPos_1985_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
v___jp_2002_:
{
if (v___y_2009_ == 0)
{
lean_object* v___x_2010_; 
lean_dec_ref(v___y_2007_);
lean_del_object(v___x_2000_);
v___x_2010_ = l_Lean_MVarId_deltaTarget(v___y_2006_, v___f_1981_, v___y_2005_, v___y_2003_, v___y_2004_, v___y_2008_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = l_Lean_MVarId_heqOfEq(v_a_2011_, v___y_2005_, v___y_2003_, v___y_2004_, v___y_2008_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1982_, v_a_2013_, v___x_1983_, v___y_2005_, v___y_2003_, v___y_2004_, v___y_2008_);
lean_dec(v___x_1983_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2015_; 
lean_dec_ref_known(v___x_2014_, 1);
v___x_2015_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1998_, v___y_2003_);
return v___x_2015_;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_a_1998_);
v_a_2016_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2014_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_a_1998_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
v_a_2024_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2012_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2012_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_a_1998_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
v_a_2032_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2010_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2010_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v___x_2041_; 
lean_dec(v___y_2006_);
lean_dec(v_a_1998_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 1);
lean_ctor_set(v___x_2000_, 0, v___y_2007_);
v___x_2041_ = v___x_2000_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___y_2007_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
v___jp_2043_:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_MVarId_intros(v_mvarId_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v_snd_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v_snd_2051_ = lean_ctor_get(v_a_2050_, 1);
lean_inc_n(v_snd_2051_, 2);
lean_dec(v_a_2050_);
v___x_2052_ = 1;
v___x_2053_ = l_Lean_MVarId_refl(v_snd_2051_, v___x_2052_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v___x_2054_; 
lean_dec_ref_known(v___x_2053_, 1);
lean_dec(v_snd_2051_);
lean_del_object(v___x_2000_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v___x_2054_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1998_, v___y_2046_);
return v___x_2054_;
}
else
{
lean_object* v_a_2055_; uint8_t v___x_2056_; 
v_a_2055_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2056_ = l_Lean_Exception_isInterrupt(v_a_2055_);
if (v___x_2056_ == 0)
{
uint8_t v___x_2057_; 
lean_inc(v_a_2055_);
v___x_2057_ = l_Lean_Exception_isRuntime(v_a_2055_);
v___y_2003_ = v___y_2046_;
v___y_2004_ = v___y_2047_;
v___y_2005_ = v___y_2045_;
v___y_2006_ = v_snd_2051_;
v___y_2007_ = v_a_2055_;
v___y_2008_ = v___y_2048_;
v___y_2009_ = v___x_2057_;
goto v___jp_2002_;
}
else
{
v___y_2003_ = v___y_2046_;
v___y_2004_ = v___y_2047_;
v___y_2005_ = v___y_2045_;
v___y_2006_ = v_snd_2051_;
v___y_2007_ = v_a_2055_;
v___y_2008_ = v___y_2048_;
v___y_2009_ = v___x_2056_;
goto v___jp_2002_;
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_del_object(v___x_2000_);
lean_dec(v_a_1998_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v_a_2058_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2049_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2049_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
v___jp_2071_:
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = l_Lean_Expr_mvarId_x21(v_a_1998_);
v___x_2077_ = lean_nat_dec_lt(v___x_1983_, v_heqNum_1984_);
if (v___x_2077_ == 0)
{
lean_del_object(v___x_1994_);
lean_dec(v_heqPos_1985_);
v_mvarId_2044_ = v___x_2076_;
v___y_2045_ = v___y_2072_;
v___y_2046_ = v___y_2073_;
v___y_2047_ = v___y_2074_;
v___y_2048_ = v___y_2075_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_box(0);
v___x_2079_ = 0;
v___x_2080_ = l_Lean_Meta_introNCore(v___x_2076_, v_heqPos_1985_, v___x_2078_, v___x_2079_, v___x_2079_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v_snd_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2119_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v_snd_2082_ = lean_ctor_get(v_a_2081_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_a_2081_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v_a_2081_, 0);
lean_dec(v_unused_2120_);
v___x_2084_ = v_a_2081_;
v_isShared_2085_ = v_isSharedCheck_2119_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_snd_2082_);
lean_dec(v_a_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2119_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; 
lean_inc(v___x_1983_);
v___x_2086_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1984_, v___x_1983_, v_snd_2082_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_toCold_2087_; lean_object* v_options_2088_; uint8_t v_hasTrace_2089_; 
v_toCold_2087_ = lean_ctor_get(v___y_2074_, 0);
v_options_2088_ = lean_ctor_get(v_toCold_2087_, 2);
v_hasTrace_2089_ = lean_ctor_get_uint8(v_options_2088_, sizeof(void*)*1);
if (v_hasTrace_2089_ == 0)
{
lean_object* v_a_2090_; 
lean_del_object(v___x_2084_);
lean_del_object(v___x_1994_);
v_a_2090_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2086_, 1);
v_mvarId_2044_ = v_a_2090_;
v___y_2045_ = v___y_2072_;
v___y_2046_ = v___y_2073_;
v___y_2047_ = v___y_2074_;
v___y_2048_ = v___y_2075_;
goto v___jp_2043_;
}
else
{
lean_object* v_a_2091_; lean_object* v_inheritedTraceOptions_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_a_2091_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2086_, 1);
v_inheritedTraceOptions_2092_ = lean_ctor_get(v_toCold_2087_, 11);
v___x_2093_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2094_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2092_, v_options_2088_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_del_object(v___x_2084_);
lean_del_object(v___x_1994_);
v_mvarId_2044_ = v_a_2091_;
v___y_2045_ = v___y_2072_;
v___y_2046_ = v___y_2073_;
v___y_2047_ = v___y_2074_;
v___y_2048_ = v___y_2075_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2091_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set_tag(v___x_1994_, 1);
lean_ctor_set(v___x_1994_, 0, v_a_2091_);
v___x_2097_ = v___x_1994_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2091_);
v___x_2097_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2099_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 7);
lean_ctor_set(v___x_2084_, 1, v___x_2097_);
lean_ctor_set(v___x_2084_, 0, v___x_2095_);
v___x_2099_ = v___x_2084_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2070_, v___x_2099_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_dec_ref_known(v___x_2100_, 1);
v_mvarId_2044_ = v_a_2091_;
v___y_2045_ = v___y_2072_;
v___y_2046_ = v___y_2073_;
v___y_2047_ = v___y_2074_;
v___y_2048_ = v___y_2075_;
goto v___jp_2043_;
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec(v_a_2091_);
lean_del_object(v___x_2000_);
lean_dec(v_a_1998_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
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
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_del_object(v___x_2084_);
lean_del_object(v___x_2000_);
lean_dec(v_a_1998_);
lean_del_object(v___x_1994_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v_a_2111_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2086_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2086_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_del_object(v___x_2000_);
lean_dec(v_a_1998_);
lean_del_object(v___x_1994_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v_a_2121_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2080_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2080_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1994_);
lean_dec(v_heqPos_1985_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
return v___x_1997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2146_, lean_object* v___f_2147_, lean_object* v_matchDeclName_2148_, lean_object* v___x_2149_, lean_object* v_heqNum_2150_, lean_object* v_heqPos_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2146_, v___f_2147_, v_matchDeclName_2148_, v___x_2149_, v_heqNum_2150_, v_heqPos_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v_heqNum_2150_);
return v_res_2157_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2158_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_unsigned_to_nat(32u);
v___x_2162_ = lean_mk_empty_array_with_capacity(v___x_2161_);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2164_ = ((size_t)5ULL);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = lean_unsigned_to_nat(32u);
v___x_2167_ = lean_mk_empty_array_with_capacity(v___x_2166_);
v___x_2168_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2169_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___x_2167_);
lean_ctor_set(v___x_2169_, 2, v___x_2165_);
lean_ctor_set(v___x_2169_, 3, v___x_2165_);
lean_ctor_set_usize(v___x_2169_, 4, v___x_2164_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = lean_box(1);
v___x_2171_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2172_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
lean_ctor_set(v___x_2173_, 1, v___x_2171_);
lean_ctor_set(v___x_2173_, 2, v___x_2170_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2176_, lean_object* v_type_2177_, lean_object* v_heqPos_2178_, lean_object* v_heqNum_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v___f_2185_; lean_object* v___x_2186_; lean_object* v___f_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_inc(v_matchDeclName_2176_);
v___f_2185_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2185_, 0, v_matchDeclName_2176_);
v___x_2186_ = lean_unsigned_to_nat(0u);
v___f_2187_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 11, 6);
lean_closure_set(v___f_2187_, 0, v_type_2177_);
lean_closure_set(v___f_2187_, 1, v___f_2185_);
lean_closure_set(v___f_2187_, 2, v_matchDeclName_2176_);
lean_closure_set(v___f_2187_, 3, v___x_2186_);
lean_closure_set(v___f_2187_, 4, v_heqNum_2179_);
lean_closure_set(v___f_2187_, 5, v_heqPos_2178_);
v___x_2188_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2189_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2190_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2188_, v___x_2189_, v___f_2187_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2191_, lean_object* v_type_2192_, lean_object* v_heqPos_2193_, lean_object* v_heqNum_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2191_, v_type_2192_, v_heqPos_2193_, v_heqNum_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2201_, lean_object* v_inst_2202_, lean_object* v_R_2203_, lean_object* v_a_2204_, lean_object* v_b_2205_, lean_object* v_c_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2201_, v_a_2204_, v_b_2205_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2213_, lean_object* v_inst_2214_, lean_object* v_R_2215_, lean_object* v_a_2216_, lean_object* v_b_2217_, lean_object* v_c_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2213_, v_inst_2214_, v_R_2215_, v_a_2216_, v_b_2217_, v_c_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v_upperBound_2213_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2225_, lean_object* v_b_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
lean_inc(v___y_2230_);
lean_inc_ref(v___y_2229_);
lean_inc(v___y_2228_);
lean_inc_ref(v___y_2227_);
v___x_2232_ = lean_apply_6(v_k_2225_, v_b_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, lean_box(0));
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2233_, lean_object* v_b_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2233_, v_b_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2241_, uint8_t v_bi_2242_, lean_object* v_type_2243_, lean_object* v_k_2244_, uint8_t v_kind_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___f_2251_; lean_object* v___x_2252_; 
v___f_2251_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2251_, 0, v_k_2244_);
v___x_2252_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2241_, v_bi_2242_, v_type_2243_, v___f_2251_, v_kind_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
v_a_2261_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2252_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2252_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2269_, lean_object* v_bi_2270_, lean_object* v_type_2271_, lean_object* v_k_2272_, lean_object* v_kind_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
uint8_t v_bi_boxed_2279_; uint8_t v_kind_boxed_2280_; lean_object* v_res_2281_; 
v_bi_boxed_2279_ = lean_unbox(v_bi_2270_);
v_kind_boxed_2280_ = lean_unbox(v_kind_2273_);
v_res_2281_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2269_, v_bi_boxed_2279_, v_type_2271_, v_k_2272_, v_kind_boxed_2280_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2282_, lean_object* v_name_2283_, uint8_t v_bi_2284_, lean_object* v_type_2285_, lean_object* v_k_2286_, uint8_t v_kind_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2283_, v_bi_2284_, v_type_2285_, v_k_2286_, v_kind_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2294_, lean_object* v_name_2295_, lean_object* v_bi_2296_, lean_object* v_type_2297_, lean_object* v_k_2298_, lean_object* v_kind_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v_bi_boxed_2305_; uint8_t v_kind_boxed_2306_; lean_object* v_res_2307_; 
v_bi_boxed_2305_ = lean_unbox(v_bi_2296_);
v_kind_boxed_2306_ = lean_unbox(v_kind_2299_);
v_res_2307_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2294_, v_name_2295_, v_bi_boxed_2305_, v_type_2297_, v_k_2298_, v_kind_boxed_2306_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2308_, lean_object* v_altsNew_2309_, lean_object* v_discrs_2310_, lean_object* v_patterns_2311_, lean_object* v_alts_2312_, lean_object* v_k_2313_, lean_object* v_altNew_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2308_, v_altsNew_2309_, v_discrs_2310_, v_patterns_2311_, v_alts_2312_, v_k_2313_, v_altNew_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v_i_2308_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2321_, lean_object* v_patterns_2322_, lean_object* v_alts_2323_, lean_object* v_k_2324_, lean_object* v_i_2325_, lean_object* v_altsNew_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = lean_array_get_size(v_alts_2323_);
v___x_2333_ = lean_nat_dec_lt(v_i_2325_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; 
lean_dec(v_i_2325_);
lean_dec_ref(v_alts_2323_);
lean_dec_ref(v_patterns_2322_);
lean_dec_ref(v_discrs_2321_);
lean_inc(v_a_2330_);
lean_inc_ref(v_a_2329_);
lean_inc(v_a_2328_);
lean_inc_ref(v_a_2327_);
v___x_2334_ = lean_apply_6(v_k_2324_, v_altsNew_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, lean_box(0));
return v___x_2334_;
}
else
{
lean_object* v___f_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_inc_ref(v_alts_2323_);
lean_inc_ref(v_patterns_2322_);
lean_inc_ref(v_discrs_2321_);
lean_inc(v_i_2325_);
v___f_2335_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2335_, 0, v_i_2325_);
lean_closure_set(v___f_2335_, 1, v_altsNew_2326_);
lean_closure_set(v___f_2335_, 2, v_discrs_2321_);
lean_closure_set(v___f_2335_, 3, v_patterns_2322_);
lean_closure_set(v___f_2335_, 4, v_alts_2323_);
lean_closure_set(v___f_2335_, 5, v_k_2324_);
v___x_2336_ = lean_array_fget(v_alts_2323_, v_i_2325_);
lean_dec(v_i_2325_);
lean_dec_ref(v_alts_2323_);
v___x_2337_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2336_, v_a_2327_, v_a_2329_, v_a_2330_);
lean_dec(v___x_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_Lean_LocalDecl_type(v_a_2338_);
v___x_2340_ = l_Lean_Expr_replaceFVars(v___x_2339_, v_discrs_2321_, v_patterns_2322_);
lean_dec_ref(v_patterns_2322_);
lean_dec_ref(v_discrs_2321_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = l_Lean_LocalDecl_userName(v_a_2338_);
v___x_2342_ = l_Lean_LocalDecl_binderInfo(v_a_2338_);
lean_dec(v_a_2338_);
v___x_2343_ = 0;
v___x_2344_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2341_, v___x_2342_, v___x_2340_, v___f_2335_, v___x_2343_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
return v___x_2344_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v___f_2335_);
lean_dec_ref(v_patterns_2322_);
lean_dec_ref(v_discrs_2321_);
v_a_2345_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2337_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2337_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2353_, lean_object* v_altsNew_2354_, lean_object* v_discrs_2355_, lean_object* v_patterns_2356_, lean_object* v_alts_2357_, lean_object* v_k_2358_, lean_object* v_altNew_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2365_ = lean_unsigned_to_nat(1u);
v___x_2366_ = lean_nat_add(v_i_2353_, v___x_2365_);
v___x_2367_ = lean_array_push(v_altsNew_2354_, v_altNew_2359_);
v___x_2368_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2355_, v_patterns_2356_, v_alts_2357_, v_k_2358_, v___x_2366_, v___x_2367_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2369_, lean_object* v_patterns_2370_, lean_object* v_alts_2371_, lean_object* v_k_2372_, lean_object* v_i_2373_, lean_object* v_altsNew_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2369_, v_patterns_2370_, v_alts_2371_, v_k_2372_, v_i_2373_, v_altsNew_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2381_, lean_object* v_discrs_2382_, lean_object* v_patterns_2383_, lean_object* v_alts_2384_, lean_object* v_k_2385_, lean_object* v_i_2386_, lean_object* v_altsNew_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2382_, v_patterns_2383_, v_alts_2384_, v_k_2385_, v_i_2386_, v_altsNew_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2394_, lean_object* v_discrs_2395_, lean_object* v_patterns_2396_, lean_object* v_alts_2397_, lean_object* v_k_2398_, lean_object* v_i_2399_, lean_object* v_altsNew_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2394_, v_discrs_2395_, v_patterns_2396_, v_alts_2397_, v_k_2398_, v_i_2399_, v_altsNew_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2409_, lean_object* v_discrs_2410_, lean_object* v_patterns_2411_, lean_object* v_alts_2412_, lean_object* v_k_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2420_ = lean_nat_dec_eq(v_numDiscrEqs_2409_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2422_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2410_, v_patterns_2411_, v_alts_2412_, v_k_2413_, v___x_2419_, v___x_2421_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; 
lean_dec_ref(v_patterns_2411_);
lean_dec_ref(v_discrs_2410_);
lean_inc(v_a_2417_);
lean_inc_ref(v_a_2416_);
lean_inc(v_a_2415_);
lean_inc_ref(v_a_2414_);
v___x_2423_ = lean_apply_6(v_k_2413_, v_alts_2412_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, lean_box(0));
return v___x_2423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2424_, lean_object* v_discrs_2425_, lean_object* v_patterns_2426_, lean_object* v_alts_2427_, lean_object* v_k_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2424_, v_discrs_2425_, v_patterns_2426_, v_alts_2427_, v_k_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_numDiscrEqs_2424_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2435_, lean_object* v_numDiscrEqs_2436_, lean_object* v_discrs_2437_, lean_object* v_patterns_2438_, lean_object* v_alts_2439_, lean_object* v_k_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2436_, v_discrs_2437_, v_patterns_2438_, v_alts_2439_, v_k_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2447_, lean_object* v_numDiscrEqs_2448_, lean_object* v_discrs_2449_, lean_object* v_patterns_2450_, lean_object* v_alts_2451_, lean_object* v_k_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2447_, v_numDiscrEqs_2448_, v_discrs_2449_, v_patterns_2450_, v_alts_2451_, v_k_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_numDiscrEqs_2448_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(lean_object* v_declName_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___x_2462_; lean_object* v_env_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2462_ = lean_st_ref_get(v___y_2460_);
v_env_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc_ref(v_env_2463_);
lean_dec(v___x_2462_);
v___x_2464_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2463_, v_declName_2459_);
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg___boxed(lean_object* v_declName_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2466_, v___y_2467_);
lean_dec(v___y_2467_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_declName_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2470_, v___y_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___boxed(lean_object* v_declName_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v_declName_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___f_2491_; lean_object* v___x_14366__overap_2492_; lean_object* v___x_2493_; 
v___f_2491_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14366__overap_2492_ = lean_panic_fn_borrowed(v___f_2491_, v_msg_2485_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v___y_2487_);
lean_inc_ref(v___y_2486_);
v___x_2493_ = lean_apply_5(v___x_14366__overap_2492_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, lean_box(0));
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2501_, lean_object* v_b_2502_, lean_object* v_c_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; 
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
v___x_2509_ = lean_apply_7(v_k_2501_, v_b_2502_, v_c_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, lean_box(0));
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2510_, lean_object* v_b_2511_, lean_object* v_c_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2510_, v_b_2511_, v_c_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2519_, lean_object* v_k_2520_, uint8_t v_cleanupAnnotations_2521_, uint8_t v_whnfType_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v___f_2528_; lean_object* v___x_2529_; 
v___f_2528_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2528_, 0, v_k_2520_);
v___x_2529_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2519_, v___f_2528_, v_cleanupAnnotations_2521_, v_whnfType_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_a_2538_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2529_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2529_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2546_, lean_object* v_k_2547_, lean_object* v_cleanupAnnotations_2548_, lean_object* v_whnfType_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2555_; uint8_t v_whnfType_boxed_2556_; lean_object* v_res_2557_; 
v_cleanupAnnotations_boxed_2555_ = lean_unbox(v_cleanupAnnotations_2548_);
v_whnfType_boxed_2556_ = lean_unbox(v_whnfType_2549_);
v_res_2557_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2546_, v_k_2547_, v_cleanupAnnotations_boxed_2555_, v_whnfType_boxed_2556_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2558_, lean_object* v_type_2559_, lean_object* v_k_2560_, uint8_t v_cleanupAnnotations_2561_, uint8_t v_whnfType_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2559_, v_k_2560_, v_cleanupAnnotations_2561_, v_whnfType_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2569_, lean_object* v_type_2570_, lean_object* v_k_2571_, lean_object* v_cleanupAnnotations_2572_, lean_object* v_whnfType_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2579_; uint8_t v_whnfType_boxed_2580_; lean_object* v_res_2581_; 
v_cleanupAnnotations_boxed_2579_ = lean_unbox(v_cleanupAnnotations_2572_);
v_whnfType_boxed_2580_ = lean_unbox(v_whnfType_2573_);
v_res_2581_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2569_, v_type_2570_, v_k_2571_, v_cleanupAnnotations_boxed_2579_, v_whnfType_boxed_2580_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2582_, lean_object* v_splitterName_2583_, lean_object* v_matcherInput_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_matchType_2590_; lean_object* v_discrInfos_2591_; lean_object* v_lhss_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2612_; 
v_matchType_2590_ = lean_ctor_get(v_matcherInput_2584_, 1);
v_discrInfos_2591_ = lean_ctor_get(v_matcherInput_2584_, 2);
v_lhss_2592_ = lean_ctor_get(v_matcherInput_2584_, 3);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_matcherInput_2584_);
if (v_isSharedCheck_2612_ == 0)
{
lean_object* v_unused_2613_; lean_object* v_unused_2614_; 
v_unused_2613_ = lean_ctor_get(v_matcherInput_2584_, 4);
lean_dec(v_unused_2613_);
v_unused_2614_ = lean_ctor_get(v_matcherInput_2584_, 0);
lean_dec(v_unused_2614_);
v___x_2594_ = v_matcherInput_2584_;
v_isShared_2595_ = v_isSharedCheck_2612_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_lhss_2592_);
lean_inc(v_discrInfos_2591_);
lean_inc(v_matchType_2590_);
lean_dec(v_matcherInput_2584_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2612_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2596_, 0, v_overlaps_2582_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 4, v___x_2596_);
lean_ctor_set(v___x_2594_, 0, v_splitterName_2583_);
v___x_2598_ = v___x_2594_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_splitterName_2583_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_matchType_2590_);
lean_ctor_set(v_reuseFailAlloc_2611_, 2, v_discrInfos_2591_);
lean_ctor_set(v_reuseFailAlloc_2611_, 3, v_lhss_2592_);
lean_ctor_set(v_reuseFailAlloc_2611_, 4, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_Meta_Match_mkMatcher(v___x_2598_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v_addMatcher_2601_; lean_object* v___x_2602_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v_addMatcher_2601_ = lean_ctor_get(v_a_2600_, 3);
lean_inc_ref(v_addMatcher_2601_);
lean_dec(v_a_2600_);
lean_inc(v___y_2588_);
lean_inc_ref(v___y_2587_);
lean_inc(v___y_2586_);
lean_inc_ref(v___y_2585_);
v___x_2602_ = lean_apply_5(v_addMatcher_2601_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, lean_box(0));
return v___x_2602_;
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
v_a_2603_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2599_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2599_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2615_, lean_object* v_splitterName_2616_, lean_object* v_matcherInput_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2615_, v_splitterName_2616_, v_matcherInput_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
return v_res_2623_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2624_, lean_object* v_ys_2625_, lean_object* v_x_2626_){
_start:
{
lean_object* v_zero_2627_; uint8_t v_isZero_2628_; 
v_zero_2627_ = lean_unsigned_to_nat(0u);
v_isZero_2628_ = lean_nat_dec_eq(v_x_2626_, v_zero_2627_);
if (v_isZero_2628_ == 1)
{
lean_dec(v_x_2626_);
return v_isZero_2628_;
}
else
{
lean_object* v_one_2629_; lean_object* v_n_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v_one_2629_ = lean_unsigned_to_nat(1u);
v_n_2630_ = lean_nat_sub(v_x_2626_, v_one_2629_);
lean_dec(v_x_2626_);
v___x_2631_ = lean_array_fget_borrowed(v_xs_2624_, v_n_2630_);
v___x_2632_ = lean_array_fget_borrowed(v_ys_2625_, v_n_2630_);
v___x_2633_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2631_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_dec(v_n_2630_);
return v___x_2633_;
}
else
{
v_x_2626_ = v_n_2630_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2635_, lean_object* v_ys_2636_, lean_object* v_x_2637_){
_start:
{
uint8_t v_res_2638_; lean_object* v_r_2639_; 
v_res_2638_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2635_, v_ys_2636_, v_x_2637_);
lean_dec_ref(v_ys_2636_);
lean_dec_ref(v_xs_2635_);
v_r_2639_ = lean_box(v_res_2638_);
return v_r_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2640_, lean_object* v_b_2641_){
_start:
{
lean_object* v_array_2642_; lean_object* v_start_2643_; lean_object* v_stop_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2657_; 
v_array_2642_ = lean_ctor_get(v_a_2640_, 0);
v_start_2643_ = lean_ctor_get(v_a_2640_, 1);
v_stop_2644_ = lean_ctor_get(v_a_2640_, 2);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_a_2640_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2646_ = v_a_2640_;
v_isShared_2647_ = v_isSharedCheck_2657_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_stop_2644_);
lean_inc(v_start_2643_);
lean_inc(v_array_2642_);
lean_dec(v_a_2640_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2657_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
uint8_t v___x_2648_; 
v___x_2648_ = lean_nat_dec_lt(v_start_2643_, v_stop_2644_);
if (v___x_2648_ == 0)
{
lean_del_object(v___x_2646_);
lean_dec(v_stop_2644_);
lean_dec(v_start_2643_);
lean_dec_ref(v_array_2642_);
return v_b_2641_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2649_ = lean_unsigned_to_nat(1u);
v___x_2650_ = lean_nat_add(v_start_2643_, v___x_2649_);
lean_inc_ref(v_array_2642_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v___x_2650_);
v___x_2652_ = v___x_2646_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_array_2642_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_stop_2644_);
v___x_2652_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_array_fget(v_array_2642_, v_start_2643_);
lean_dec(v_start_2643_);
lean_dec_ref(v_array_2642_);
v___x_2654_ = lean_array_push(v_b_2641_, v___x_2653_);
v_a_2640_ = v___x_2652_;
v_b_2641_ = v___x_2654_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2658_, size_t v_sz_2659_, size_t v_i_2660_, lean_object* v_b_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
uint8_t v___x_2667_; 
v___x_2667_ = lean_usize_dec_lt(v_i_2660_, v_sz_2659_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_b_2661_);
return v___x_2668_;
}
else
{
lean_object* v_snd_2669_; lean_object* v_fst_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2722_; 
v_snd_2669_ = lean_ctor_get(v_b_2661_, 1);
v_fst_2670_ = lean_ctor_get(v_b_2661_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_b_2661_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2672_ = v_b_2661_;
v_isShared_2673_ = v_isSharedCheck_2722_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_snd_2669_);
lean_inc(v_fst_2670_);
lean_dec(v_b_2661_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2722_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v_array_2674_; lean_object* v_start_2675_; lean_object* v_stop_2676_; uint8_t v___x_2677_; 
v_array_2674_ = lean_ctor_get(v_snd_2669_, 0);
v_start_2675_ = lean_ctor_get(v_snd_2669_, 1);
v_stop_2676_ = lean_ctor_get(v_snd_2669_, 2);
v___x_2677_ = lean_nat_dec_lt(v_start_2675_, v_stop_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2679_; 
if (v_isShared_2673_ == 0)
{
v___x_2679_ = v___x_2672_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_fst_2670_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_snd_2669_);
v___x_2679_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2680_; 
v___x_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
return v___x_2680_;
}
}
else
{
lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2718_; 
lean_inc(v_stop_2676_);
lean_inc(v_start_2675_);
lean_inc_ref(v_array_2674_);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_snd_2669_);
if (v_isSharedCheck_2718_ == 0)
{
lean_object* v_unused_2719_; lean_object* v_unused_2720_; lean_object* v_unused_2721_; 
v_unused_2719_ = lean_ctor_get(v_snd_2669_, 2);
lean_dec(v_unused_2719_);
v_unused_2720_ = lean_ctor_get(v_snd_2669_, 1);
lean_dec(v_unused_2720_);
v_unused_2721_ = lean_ctor_get(v_snd_2669_, 0);
lean_dec(v_unused_2721_);
v___x_2683_ = v_snd_2669_;
v_isShared_2684_ = v_isSharedCheck_2718_;
goto v_resetjp_2682_;
}
else
{
lean_dec(v_snd_2669_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2718_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v_a_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v_a_2685_ = lean_array_uget_borrowed(v_as_2658_, v_i_2660_);
v___x_2686_ = lean_array_fget(v_array_2674_, v_start_2675_);
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_nat_add(v_start_2675_, v___x_2687_);
lean_dec(v_start_2675_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 1, v___x_2688_);
v___x_2690_ = v___x_2683_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_array_2674_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2717_, 2, v_stop_2676_);
v___x_2690_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; 
lean_inc(v_a_2685_);
v___x_2691_ = l_Lean_Meta_mkEqHEq(v_a_2685_, v___x_2686_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
v___x_2693_ = l_Lean_mkArrow(v_a_2692_, v_fst_2670_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2690_);
lean_ctor_set(v___x_2672_, 0, v_a_2694_);
v___x_2696_ = v___x_2672_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2690_);
v___x_2696_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
size_t v___x_2697_; size_t v___x_2698_; 
v___x_2697_ = ((size_t)1ULL);
v___x_2698_ = lean_usize_add(v_i_2660_, v___x_2697_);
v_i_2660_ = v___x_2698_;
v_b_2661_ = v___x_2696_;
goto _start;
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec_ref(v___x_2690_);
lean_del_object(v___x_2672_);
v_a_2701_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2693_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2693_);
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
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec_ref(v___x_2690_);
lean_del_object(v___x_2672_);
lean_dec(v_fst_2670_);
v_a_2709_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2691_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2691_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2723_, lean_object* v_sz_2724_, lean_object* v_i_2725_, lean_object* v_b_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
size_t v_sz_boxed_2732_; size_t v_i_boxed_2733_; lean_object* v_res_2734_; 
v_sz_boxed_2732_ = lean_unbox_usize(v_sz_2724_);
lean_dec(v_sz_2724_);
v_i_boxed_2733_ = lean_unbox_usize(v_i_2725_);
lean_dec(v_i_2725_);
v_res_2734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2723_, v_sz_boxed_2732_, v_i_boxed_2733_, v_b_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec_ref(v_as_2723_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2735_, lean_object* v___x_2736_, lean_object* v_as_2737_, size_t v_sz_2738_, size_t v_i_2739_, lean_object* v_b_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_a_2747_; uint8_t v___x_2751_; 
v___x_2751_ = lean_usize_dec_lt(v_i_2739_, v_sz_2738_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_b_2740_);
return v___x_2752_;
}
else
{
lean_object* v___x_2753_; lean_object* v_a_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2753_ = l_Lean_instInhabitedExpr;
v_a_2754_ = lean_array_uget_borrowed(v_as_2737_, v_i_2739_);
v___x_2755_ = lean_array_get_borrowed(v___x_2753_, v___x_2735_, v_a_2754_);
lean_inc(v___x_2755_);
v___x_2756_ = l_Lean_Meta_instantiateForall(v___x_2755_, v___x_2736_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2758_ = lean_array_get_size(v___x_2736_);
v___x_2759_ = l_Lean_Meta_Match_simpH_x3f(v_a_2757_, v___x_2758_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
if (lean_obj_tag(v_a_2760_) == 1)
{
lean_object* v_val_2761_; lean_object* v___x_2762_; 
v_val_2761_ = lean_ctor_get(v_a_2760_, 0);
lean_inc(v_val_2761_);
lean_dec_ref_known(v_a_2760_, 1);
v___x_2762_ = lean_array_push(v_b_2740_, v_val_2761_);
v_a_2747_ = v___x_2762_;
goto v___jp_2746_;
}
else
{
lean_dec(v_a_2760_);
v_a_2747_ = v_b_2740_;
goto v___jp_2746_;
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v_b_2740_);
v_a_2763_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2759_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2759_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec_ref(v_b_2740_);
v_a_2771_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2756_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2756_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
v___jp_2746_:
{
size_t v___x_2748_; size_t v___x_2749_; 
v___x_2748_ = ((size_t)1ULL);
v___x_2749_ = lean_usize_add(v_i_2739_, v___x_2748_);
v_i_2739_ = v___x_2749_;
v_b_2740_ = v_a_2747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2779_, lean_object* v___x_2780_, lean_object* v_as_2781_, lean_object* v_sz_2782_, lean_object* v_i_2783_, lean_object* v_b_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
size_t v_sz_boxed_2790_; size_t v_i_boxed_2791_; lean_object* v_res_2792_; 
v_sz_boxed_2790_ = lean_unbox_usize(v_sz_2782_);
lean_dec(v_sz_2782_);
v_i_boxed_2791_ = lean_unbox_usize(v_i_2783_);
lean_dec(v_i_2783_);
v_res_2792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2779_, v___x_2780_, v_as_2781_, v_sz_boxed_2790_, v_i_boxed_2791_, v_b_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec_ref(v_as_2781_);
lean_dec_ref(v___x_2780_);
lean_dec_ref(v___x_2779_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v___x_2796_, lean_object* v___x_2797_, lean_object* v___x_2798_, lean_object* v___x_2799_, lean_object* v___x_2800_, lean_object* v_rhsArgs_2801_, lean_object* v_a_2802_, lean_object* v_ys_2803_, uint8_t v___x_2804_, uint8_t v___x_2805_, uint8_t v___x_2806_, lean_object* v_matchDeclName_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v___x_2810_, lean_object* v___x_2811_, lean_object* v___x_2812_, lean_object* v_argMask_2813_, lean_object* v_a_2814_, lean_object* v_alts_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2821_ = lean_array_get_borrowed(v___x_2793_, v_alts_2815_, v_a_2794_);
v___x_2822_ = l_Lean_ConstantInfo_name(v_a_2795_);
v___x_2823_ = l_Lean_mkConst(v___x_2822_, v___x_2796_);
v___x_2824_ = l_Subarray_copy___redArg(v___x_2797_);
v___x_2825_ = lean_mk_empty_array_with_capacity(v___x_2798_);
v___x_2826_ = lean_array_push(v___x_2825_, v___x_2799_);
v___x_2827_ = l_Array_append___redArg(v___x_2824_, v___x_2826_);
lean_dec_ref(v___x_2826_);
lean_inc_ref(v___x_2827_);
v___x_2828_ = l_Array_append___redArg(v___x_2827_, v___x_2800_);
v___x_2829_ = l_Array_append___redArg(v___x_2828_, v_alts_2815_);
v___x_2830_ = l_Lean_mkAppN(v___x_2823_, v___x_2829_);
lean_dec_ref(v___x_2829_);
lean_inc(v___x_2821_);
v___x_2831_ = l_Lean_mkAppN(v___x_2821_, v_rhsArgs_2801_);
v___x_2832_ = l_Lean_Meta_mkEq(v___x_2830_, v___x_2831_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2834_ = l_Lean_mkArrowN(v_a_2802_, v_a_2833_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
v___x_2836_ = l_Array_append___redArg(v___x_2827_, v_ys_2803_);
v___x_2837_ = l_Array_append___redArg(v___x_2836_, v_alts_2815_);
v___x_2838_ = l_Lean_Meta_mkForallFVars(v___x_2837_, v_a_2835_, v___x_2804_, v___x_2805_, v___x_2805_, v___x_2806_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec_ref(v___x_2837_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2839_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2842_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc_n(v_a_2841_, 2);
lean_dec_ref_known(v___x_2840_, 1);
lean_inc(v___x_2808_);
v___x_2842_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2807_, v_a_2841_, v___x_2808_, v___x_2808_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2842_, 1);
lean_inc(v___x_2809_);
v___x_2844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2809_);
lean_ctor_set(v___x_2844_, 1, v___x_2810_);
lean_ctor_set(v___x_2844_, 2, v_a_2841_);
v___x_2845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2809_);
lean_ctor_set(v___x_2845_, 1, v___x_2811_);
v___x_2846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v_a_2843_);
lean_ctor_set(v___x_2846_, 2, v___x_2845_);
v___x_2847_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
v___x_2848_ = l_Lean_addDecl(v___x_2847_, v___x_2804_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2857_; 
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v___x_2848_, 0);
lean_dec(v_unused_2858_);
v___x_2850_ = v___x_2848_;
v_isShared_2851_ = v_isSharedCheck_2857_;
goto v_resetjp_2849_;
}
else
{
lean_dec(v___x_2848_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2857_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2812_);
lean_ctor_set(v___x_2852_, 1, v_argMask_2813_);
v___x_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2853_, 0, v_a_2814_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2853_);
v___x_2855_ = v___x_2850_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec_ref(v_a_2814_);
lean_dec_ref(v_argMask_2813_);
lean_dec_ref(v___x_2812_);
v_a_2859_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2848_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2848_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2814_);
lean_dec_ref(v_argMask_2813_);
lean_dec_ref(v___x_2812_);
lean_dec(v___x_2811_);
lean_dec(v___x_2810_);
lean_dec(v___x_2809_);
v_a_2867_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2842_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2842_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec_ref(v_a_2814_);
lean_dec_ref(v_argMask_2813_);
lean_dec_ref(v___x_2812_);
lean_dec(v___x_2811_);
lean_dec(v___x_2810_);
lean_dec(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec(v_matchDeclName_2807_);
v_a_2875_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2840_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2840_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec_ref(v_a_2814_);
lean_dec_ref(v_argMask_2813_);
lean_dec_ref(v___x_2812_);
lean_dec(v___x_2811_);
lean_dec(v___x_2810_);
lean_dec(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec(v_matchDeclName_2807_);
v_a_2883_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2838_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2838_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec_ref(v___x_2827_);
lean_dec_ref(v_a_2814_);
lean_dec_ref(v_argMask_2813_);
lean_dec_ref(v___x_2812_);
lean_dec(v___x_2811_);
lean_dec(v___x_2810_);
lean_dec(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec(v_matchDeclName_2807_);
v_a_2891_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2834_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2834_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec_ref(v___x_2827_);
lean_dec_ref(v_a_2814_);
lean_dec_ref(v_argMask_2813_);
lean_dec_ref(v___x_2812_);
lean_dec(v___x_2811_);
lean_dec(v___x_2810_);
lean_dec(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec(v_matchDeclName_2807_);
v_a_2899_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2832_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2832_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2907_ = _args[0];
lean_object* v_a_2908_ = _args[1];
lean_object* v_a_2909_ = _args[2];
lean_object* v___x_2910_ = _args[3];
lean_object* v___x_2911_ = _args[4];
lean_object* v___x_2912_ = _args[5];
lean_object* v___x_2913_ = _args[6];
lean_object* v___x_2914_ = _args[7];
lean_object* v_rhsArgs_2915_ = _args[8];
lean_object* v_a_2916_ = _args[9];
lean_object* v_ys_2917_ = _args[10];
lean_object* v___x_2918_ = _args[11];
lean_object* v___x_2919_ = _args[12];
lean_object* v___x_2920_ = _args[13];
lean_object* v_matchDeclName_2921_ = _args[14];
lean_object* v___x_2922_ = _args[15];
lean_object* v___x_2923_ = _args[16];
lean_object* v___x_2924_ = _args[17];
lean_object* v___x_2925_ = _args[18];
lean_object* v___x_2926_ = _args[19];
lean_object* v_argMask_2927_ = _args[20];
lean_object* v_a_2928_ = _args[21];
lean_object* v_alts_2929_ = _args[22];
lean_object* v___y_2930_ = _args[23];
lean_object* v___y_2931_ = _args[24];
lean_object* v___y_2932_ = _args[25];
lean_object* v___y_2933_ = _args[26];
lean_object* v___y_2934_ = _args[27];
_start:
{
uint8_t v___x_18504__boxed_2935_; uint8_t v___x_18505__boxed_2936_; uint8_t v___x_18506__boxed_2937_; lean_object* v_res_2938_; 
v___x_18504__boxed_2935_ = lean_unbox(v___x_2918_);
v___x_18505__boxed_2936_ = lean_unbox(v___x_2919_);
v___x_18506__boxed_2937_ = lean_unbox(v___x_2920_);
v_res_2938_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2907_, v_a_2908_, v_a_2909_, v___x_2910_, v___x_2911_, v___x_2912_, v___x_2913_, v___x_2914_, v_rhsArgs_2915_, v_a_2916_, v_ys_2917_, v___x_18504__boxed_2935_, v___x_18505__boxed_2936_, v___x_18506__boxed_2937_, v_matchDeclName_2921_, v___x_2922_, v___x_2923_, v___x_2924_, v___x_2925_, v___x_2926_, v_argMask_2927_, v_a_2928_, v_alts_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec_ref(v_alts_2929_);
lean_dec_ref(v_ys_2917_);
lean_dec_ref(v_a_2916_);
lean_dec_ref(v_rhsArgs_2915_);
lean_dec_ref(v___x_2914_);
lean_dec(v___x_2912_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v___x_2907_);
return v_res_2938_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2939_; lean_object* v_dummy_2940_; 
v___x_2939_ = lean_box(0);
v_dummy_2940_ = l_Lean_Expr_sort___override(v___x_2939_);
return v_dummy_2940_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = lean_box(0);
v___x_2945_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_2946_ = l_Lean_mkConst(v___x_2945_, v___x_2944_);
return v___x_2946_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_2949_ = l_Lean_stringToMessageData(v___x_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_2950_, lean_object* v_overlaps_2951_, lean_object* v_a_2952_, lean_object* v_fst_2953_, lean_object* v___x_2954_, lean_object* v___x_2955_, lean_object* v___x_2956_, uint8_t v___x_2957_, lean_object* v___x_2958_, lean_object* v_a_2959_, lean_object* v___x_2960_, lean_object* v___x_2961_, lean_object* v___x_2962_, lean_object* v_matchDeclName_2963_, lean_object* v___x_2964_, lean_object* v___x_2965_, lean_object* v___x_2966_, lean_object* v___x_2967_, lean_object* v___x_2968_, lean_object* v_ys_2969_, lean_object* v___eqs_2970_, lean_object* v_rhsArgs_2971_, lean_object* v_argMask_2972_, lean_object* v_altResultType_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_dummy_2979_; lean_object* v_nargs_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; size_t v_sz_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v_dummy_2979_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_2980_ = l_Lean_Expr_getAppNumArgs(v_altResultType_2973_);
lean_inc(v_nargs_2980_);
v___x_2981_ = lean_mk_array(v_nargs_2980_, v_dummy_2979_);
v___x_2982_ = lean_nat_sub(v_nargs_2980_, v___x_2950_);
lean_dec(v_nargs_2980_);
v___x_2983_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_2973_, v___x_2981_, v___x_2982_);
v___x_2984_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_2951_, v_a_2952_);
v_sz_2985_ = lean_array_size(v___x_2984_);
v___x_2986_ = ((size_t)0ULL);
lean_inc_ref(v___x_2954_);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_2953_, v___x_2983_, v___x_2984_, v_sz_2985_, v___x_2986_, v___x_2954_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec_ref(v___x_2984_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; uint8_t v___y_2994_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v_toCold_3047_; lean_object* v_options_3048_; uint8_t v_hasTrace_3049_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2987_, 1);
v_toCold_3047_ = lean_ctor_get(v___y_2976_, 0);
v_options_3048_ = lean_ctor_get(v_toCold_3047_, 2);
v_hasTrace_3049_ = lean_ctor_get_uint8(v_options_3048_, sizeof(void*)*1);
if (v_hasTrace_3049_ == 0)
{
v___y_3038_ = v___y_2974_;
v___y_3039_ = v___y_2975_;
v___y_3040_ = v___y_2976_;
v___y_3041_ = v___y_2977_;
goto v___jp_3037_;
}
else
{
lean_object* v_inheritedTraceOptions_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; 
v_inheritedTraceOptions_3050_ = lean_ctor_get(v_toCold_3047_, 11);
v___x_3051_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3052_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_3053_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3050_, v_options_3048_, v___x_3052_);
if (v___x_3053_ == 0)
{
v___y_3038_ = v___y_2974_;
v___y_3039_ = v___y_2975_;
v___y_3040_ = v___y_2976_;
v___y_3041_ = v___y_2977_;
goto v___jp_3037_;
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3054_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_2988_);
v___x_3055_ = lean_array_to_list(v_a_2988_);
v___x_3056_ = lean_box(0);
v___x_3057_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3055_, v___x_3056_);
v___x_3058_ = l_Lean_MessageData_ofList(v___x_3057_);
v___x_3059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3054_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3051_, v___x_3059_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_dec_ref_known(v___x_3060_, 1);
v___y_3038_ = v___y_2974_;
v___y_3039_ = v___y_2975_;
v___y_3040_ = v___y_2976_;
v___y_3041_ = v___y_2977_;
goto v___jp_3037_;
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v_a_2988_);
lean_dec_ref(v___x_2983_);
lean_dec_ref(v_argMask_2972_);
lean_dec_ref(v_rhsArgs_2971_);
lean_dec_ref(v_ys_2969_);
lean_dec_ref(v___x_2967_);
lean_dec(v___x_2966_);
lean_dec(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec(v_matchDeclName_2963_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v___x_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_a_2959_);
lean_dec_ref(v___x_2958_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v_a_2952_);
lean_dec(v___x_2950_);
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
v___jp_2989_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; size_t v_sz_3005_; lean_object* v___x_3006_; 
v___x_2995_ = lean_array_get_size(v_ys_2969_);
v___x_2996_ = lean_array_get_size(v_a_2988_);
v___x_2997_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2997_, 0, v___x_2995_);
lean_ctor_set(v___x_2997_, 1, v___x_2996_);
lean_ctor_set_uint8(v___x_2997_, sizeof(void*)*2, v___y_2994_);
v___x_2998_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2983_);
v___x_2999_ = l_Array_reverse___redArg(v___x_2983_);
v___x_3000_ = lean_array_get_size(v___x_2999_);
lean_inc(v___x_2955_);
v___x_3001_ = l_Array_toSubarray___redArg(v___x_2999_, v___x_2955_, v___x_3000_);
lean_inc_ref(v___x_2956_);
v___x_3002_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2956_, v___x_2954_);
v___x_3003_ = l_Array_reverse___redArg(v___x_3002_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_2998_);
lean_ctor_set(v___x_3004_, 1, v___x_3001_);
v_sz_3005_ = lean_array_size(v___x_3003_);
v___x_3006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3003_, v_sz_3005_, v___x_2986_, v___x_3004_, v___y_2993_, v___y_2991_, v___y_2990_, v___y_2992_);
lean_dec_ref(v___x_3003_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v_fst_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v_fst_3008_ = lean_ctor_get(v_a_3007_, 0);
lean_inc(v_fst_3008_);
lean_dec(v_a_3007_);
v___x_3009_ = l_Subarray_copy___redArg(v___x_2956_);
lean_inc_ref(v___x_3009_);
v___x_3010_ = l_Array_append___redArg(v___x_3009_, v_ys_2969_);
v___x_3011_ = 0;
v___x_3012_ = 1;
v___x_3013_ = l_Lean_Meta_mkForallFVars(v___x_3010_, v_fst_3008_, v___x_3011_, v___x_2957_, v___x_2957_, v___x_3012_, v___y_2993_, v___y_2991_, v___y_2990_, v___y_2992_);
lean_dec_ref(v___x_3010_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___f_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v___x_3015_ = lean_box(v___x_3011_);
v___x_3016_ = lean_box(v___x_2957_);
v___x_3017_ = lean_box(v___x_3012_);
lean_inc_ref(v___x_2983_);
v___f_3018_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_3018_, 0, v___x_2958_);
lean_closure_set(v___f_3018_, 1, v_a_2952_);
lean_closure_set(v___f_3018_, 2, v_a_2959_);
lean_closure_set(v___f_3018_, 3, v___x_2960_);
lean_closure_set(v___f_3018_, 4, v___x_2961_);
lean_closure_set(v___f_3018_, 5, v___x_2950_);
lean_closure_set(v___f_3018_, 6, v___x_2962_);
lean_closure_set(v___f_3018_, 7, v___x_2983_);
lean_closure_set(v___f_3018_, 8, v_rhsArgs_2971_);
lean_closure_set(v___f_3018_, 9, v_a_2988_);
lean_closure_set(v___f_3018_, 10, v_ys_2969_);
lean_closure_set(v___f_3018_, 11, v___x_3015_);
lean_closure_set(v___f_3018_, 12, v___x_3016_);
lean_closure_set(v___f_3018_, 13, v___x_3017_);
lean_closure_set(v___f_3018_, 14, v_matchDeclName_2963_);
lean_closure_set(v___f_3018_, 15, v___x_2955_);
lean_closure_set(v___f_3018_, 16, v___x_2964_);
lean_closure_set(v___f_3018_, 17, v___x_2965_);
lean_closure_set(v___f_3018_, 18, v___x_2966_);
lean_closure_set(v___f_3018_, 19, v___x_2997_);
lean_closure_set(v___f_3018_, 20, v_argMask_2972_);
lean_closure_set(v___f_3018_, 21, v_a_3014_);
v___x_3019_ = l_Subarray_copy___redArg(v___x_2967_);
v___x_3020_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2968_, v___x_3009_, v___x_2983_, v___x_3019_, v___f_3018_, v___y_2993_, v___y_2991_, v___y_2990_, v___y_2992_);
return v___x_3020_;
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref(v___x_3009_);
lean_dec_ref_known(v___x_2997_, 2);
lean_dec(v_a_2988_);
lean_dec_ref(v___x_2983_);
lean_dec_ref(v_argMask_2972_);
lean_dec_ref(v_rhsArgs_2971_);
lean_dec_ref(v_ys_2969_);
lean_dec_ref(v___x_2967_);
lean_dec(v___x_2966_);
lean_dec(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec(v_matchDeclName_2963_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v___x_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_a_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v___x_2955_);
lean_dec(v_a_2952_);
lean_dec(v___x_2950_);
v_a_3021_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3013_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3013_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref_known(v___x_2997_, 2);
lean_dec(v_a_2988_);
lean_dec_ref(v___x_2983_);
lean_dec_ref(v_argMask_2972_);
lean_dec_ref(v_rhsArgs_2971_);
lean_dec_ref(v_ys_2969_);
lean_dec_ref(v___x_2967_);
lean_dec(v___x_2966_);
lean_dec(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec(v_matchDeclName_2963_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v___x_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_a_2959_);
lean_dec_ref(v___x_2958_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec(v_a_2952_);
lean_dec(v___x_2950_);
v_a_3029_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3006_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3006_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
v___jp_3037_:
{
lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = lean_array_get_size(v_ys_2969_);
v___x_3043_ = lean_nat_dec_eq(v___x_3042_, v___x_2955_);
if (v___x_3043_ == 0)
{
v___y_2990_ = v___y_3040_;
v___y_2991_ = v___y_3039_;
v___y_2992_ = v___y_3041_;
v___y_2993_ = v___y_3038_;
v___y_2994_ = v___x_3043_;
goto v___jp_2989_;
}
else
{
lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3044_ = lean_array_get_size(v_a_2988_);
v___x_3045_ = lean_nat_dec_eq(v___x_3044_, v___x_2955_);
if (v___x_3045_ == 0)
{
v___y_2990_ = v___y_3040_;
v___y_2991_ = v___y_3039_;
v___y_2992_ = v___y_3041_;
v___y_2993_ = v___y_3038_;
v___y_2994_ = v___x_3045_;
goto v___jp_2989_;
}
else
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_nat_dec_eq(v___x_2968_, v___x_2955_);
v___y_2990_ = v___y_3040_;
v___y_2991_ = v___y_3039_;
v___y_2992_ = v___y_3041_;
v___y_2993_ = v___y_3038_;
v___y_2994_ = v___x_3046_;
goto v___jp_2989_;
}
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec_ref(v___x_2983_);
lean_dec_ref(v_argMask_2972_);
lean_dec_ref(v_rhsArgs_2971_);
lean_dec_ref(v_ys_2969_);
lean_dec_ref(v___x_2967_);
lean_dec(v___x_2966_);
lean_dec(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec(v_matchDeclName_2963_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v___x_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_a_2959_);
lean_dec_ref(v___x_2958_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v_a_2952_);
lean_dec(v___x_2950_);
v_a_3069_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_2987_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_2987_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3077_ = _args[0];
lean_object* v_overlaps_3078_ = _args[1];
lean_object* v_a_3079_ = _args[2];
lean_object* v_fst_3080_ = _args[3];
lean_object* v___x_3081_ = _args[4];
lean_object* v___x_3082_ = _args[5];
lean_object* v___x_3083_ = _args[6];
lean_object* v___x_3084_ = _args[7];
lean_object* v___x_3085_ = _args[8];
lean_object* v_a_3086_ = _args[9];
lean_object* v___x_3087_ = _args[10];
lean_object* v___x_3088_ = _args[11];
lean_object* v___x_3089_ = _args[12];
lean_object* v_matchDeclName_3090_ = _args[13];
lean_object* v___x_3091_ = _args[14];
lean_object* v___x_3092_ = _args[15];
lean_object* v___x_3093_ = _args[16];
lean_object* v___x_3094_ = _args[17];
lean_object* v___x_3095_ = _args[18];
lean_object* v_ys_3096_ = _args[19];
lean_object* v___eqs_3097_ = _args[20];
lean_object* v_rhsArgs_3098_ = _args[21];
lean_object* v_argMask_3099_ = _args[22];
lean_object* v_altResultType_3100_ = _args[23];
lean_object* v___y_3101_ = _args[24];
lean_object* v___y_3102_ = _args[25];
lean_object* v___y_3103_ = _args[26];
lean_object* v___y_3104_ = _args[27];
lean_object* v___y_3105_ = _args[28];
_start:
{
uint8_t v___x_18772__boxed_3106_; lean_object* v_res_3107_; 
v___x_18772__boxed_3106_ = lean_unbox(v___x_3084_);
v_res_3107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3077_, v_overlaps_3078_, v_a_3079_, v_fst_3080_, v___x_3081_, v___x_3082_, v___x_3083_, v___x_18772__boxed_3106_, v___x_3085_, v_a_3086_, v___x_3087_, v___x_3088_, v___x_3089_, v_matchDeclName_3090_, v___x_3091_, v___x_3092_, v___x_3093_, v___x_3094_, v___x_3095_, v_ys_3096_, v___eqs_3097_, v_rhsArgs_3098_, v_argMask_3099_, v_altResultType_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec_ref(v___eqs_3097_);
lean_dec(v___x_3095_);
lean_dec(v_fst_3080_);
lean_dec_ref(v_overlaps_3078_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3108_, lean_object* v_val_3109_, lean_object* v_baseName_3110_, lean_object* v___x_3111_, lean_object* v_a_3112_, lean_object* v___x_3113_, lean_object* v___x_3114_, lean_object* v___x_3115_, lean_object* v_matchDeclName_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v___x_3119_, lean_object* v_a_3120_, lean_object* v_b_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
uint8_t v___x_3127_; 
v___x_3127_ = lean_nat_dec_lt(v_a_3120_, v_upperBound_3108_);
if (v___x_3127_ == 0)
{
lean_object* v___x_3128_; 
lean_dec(v_a_3120_);
lean_dec(v___x_3119_);
lean_dec_ref(v___x_3118_);
lean_dec(v___x_3117_);
lean_dec(v_matchDeclName_3116_);
lean_dec_ref(v___x_3115_);
lean_dec_ref(v___x_3114_);
lean_dec(v___x_3113_);
lean_dec_ref(v_a_3112_);
lean_dec_ref(v___x_3111_);
lean_dec(v_baseName_3110_);
lean_dec_ref(v_val_3109_);
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v_b_3121_);
return v___x_3128_;
}
else
{
lean_object* v_snd_3129_; lean_object* v_snd_3130_; lean_object* v_snd_3131_; lean_object* v_fst_3132_; lean_object* v_fst_3133_; lean_object* v_fst_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3217_; 
v_snd_3129_ = lean_ctor_get(v_b_3121_, 1);
lean_inc(v_snd_3129_);
v_snd_3130_ = lean_ctor_get(v_snd_3129_, 1);
lean_inc(v_snd_3130_);
v_snd_3131_ = lean_ctor_get(v_snd_3130_, 1);
lean_inc(v_snd_3131_);
v_fst_3132_ = lean_ctor_get(v_b_3121_, 0);
lean_inc(v_fst_3132_);
lean_dec_ref(v_b_3121_);
v_fst_3133_ = lean_ctor_get(v_snd_3129_, 0);
lean_inc(v_fst_3133_);
lean_dec(v_snd_3129_);
v_fst_3134_ = lean_ctor_get(v_snd_3130_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v_snd_3130_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v_snd_3130_, 1);
lean_dec(v_unused_3218_);
v___x_3136_ = v_snd_3130_;
v_isShared_3137_ = v_isSharedCheck_3217_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_fst_3134_);
lean_dec(v_snd_3130_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3217_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v_fst_3138_; lean_object* v_snd_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3216_; 
v_fst_3138_ = lean_ctor_get(v_snd_3131_, 0);
v_snd_3139_ = lean_ctor_get(v_snd_3131_, 1);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_snd_3131_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3141_ = v_snd_3131_;
v_isShared_3142_ = v_isSharedCheck_3216_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_snd_3139_);
lean_inc(v_fst_3138_);
lean_dec(v_snd_3131_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3216_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v_altInfos_3143_; lean_object* v_overlaps_3144_; lean_object* v_start_3145_; lean_object* v_stop_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___f_3158_; lean_object* v___x_3159_; lean_object* v___y_3161_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v_altInfos_3143_ = lean_ctor_get(v_val_3109_, 2);
v_overlaps_3144_ = lean_ctor_get(v_val_3109_, 5);
v_start_3145_ = lean_ctor_get(v___x_3118_, 1);
v_stop_3146_ = lean_ctor_get(v___x_3118_, 2);
v___x_3147_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3148_ = l_Lean_instInhabitedExpr;
v___x_3149_ = lean_unsigned_to_nat(0u);
v___x_3150_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3151_ = lean_box(0);
v___x_3152_ = lean_unsigned_to_nat(1u);
v___x_3153_ = lean_array_get_borrowed(v___x_3147_, v_altInfos_3143_, v_a_3120_);
v___x_3154_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3110_);
v___x_3155_ = l_Lean_Name_str___override(v_baseName_3110_, v___x_3154_);
lean_inc(v_fst_3134_);
v___x_3156_ = lean_name_append_index_after(v___x_3155_, v_fst_3134_);
v___x_3157_ = lean_box(v___x_3127_);
lean_inc(v___x_3119_);
lean_inc_ref(v___x_3118_);
lean_inc(v___x_3117_);
lean_inc(v___x_3156_);
lean_inc(v_matchDeclName_3116_);
lean_inc_ref(v___x_3115_);
lean_inc_ref(v___x_3114_);
lean_inc(v___x_3113_);
lean_inc_ref(v_a_3112_);
lean_inc_ref(v___x_3111_);
lean_inc(v_fst_3133_);
lean_inc(v_a_3120_);
lean_inc_ref(v_overlaps_3144_);
v___f_3158_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3158_, 0, v___x_3152_);
lean_closure_set(v___f_3158_, 1, v_overlaps_3144_);
lean_closure_set(v___f_3158_, 2, v_a_3120_);
lean_closure_set(v___f_3158_, 3, v_fst_3133_);
lean_closure_set(v___f_3158_, 4, v___x_3150_);
lean_closure_set(v___f_3158_, 5, v___x_3149_);
lean_closure_set(v___f_3158_, 6, v___x_3111_);
lean_closure_set(v___f_3158_, 7, v___x_3157_);
lean_closure_set(v___f_3158_, 8, v___x_3148_);
lean_closure_set(v___f_3158_, 9, v_a_3112_);
lean_closure_set(v___f_3158_, 10, v___x_3113_);
lean_closure_set(v___f_3158_, 11, v___x_3114_);
lean_closure_set(v___f_3158_, 12, v___x_3115_);
lean_closure_set(v___f_3158_, 13, v_matchDeclName_3116_);
lean_closure_set(v___f_3158_, 14, v___x_3156_);
lean_closure_set(v___f_3158_, 15, v___x_3117_);
lean_closure_set(v___f_3158_, 16, v___x_3151_);
lean_closure_set(v___f_3158_, 17, v___x_3118_);
lean_closure_set(v___f_3158_, 18, v___x_3119_);
v___x_3159_ = lean_array_push(v_fst_3132_, v___x_3156_);
v___x_3212_ = lean_nat_sub(v_stop_3146_, v_start_3145_);
v___x_3213_ = lean_nat_dec_lt(v_a_3120_, v___x_3212_);
lean_dec(v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; 
v___x_3214_ = l_outOfBounds___redArg(v___x_3148_);
v___y_3161_ = v___x_3214_;
goto v___jp_3160_;
}
else
{
lean_object* v___x_3215_; 
v___x_3215_ = l_Subarray_get___redArg(v___x_3118_, v_a_3120_);
v___y_3161_ = v___x_3215_;
goto v___jp_3160_;
}
v___jp_3160_:
{
lean_object* v___x_3162_; 
lean_inc(v___y_3125_);
lean_inc_ref(v___y_3124_);
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
v___x_3162_ = lean_infer_type(v___y_3161_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
lean_inc(v___x_3119_);
lean_inc(v___x_3153_);
v___x_3164_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3163_, v___x_3153_, v___x_3119_, v___f_3158_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v_snd_3166_; lean_object* v_fst_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3195_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v_snd_3166_ = lean_ctor_get(v_a_3165_, 1);
v_fst_3167_ = lean_ctor_get(v_a_3165_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_a_3165_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3169_ = v_a_3165_;
v_isShared_3170_ = v_isSharedCheck_3195_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_snd_3166_);
lean_inc(v_fst_3167_);
lean_dec(v_a_3165_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3195_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v_fst_3171_; lean_object* v_snd_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3194_; 
v_fst_3171_ = lean_ctor_get(v_snd_3166_, 0);
v_snd_3172_ = lean_ctor_get(v_snd_3166_, 1);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_snd_3166_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3174_ = v_snd_3166_;
v_isShared_3175_ = v_isSharedCheck_3194_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_snd_3172_);
lean_inc(v_fst_3171_);
lean_dec(v_snd_3166_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3194_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3176_ = lean_array_push(v_fst_3133_, v_fst_3167_);
v___x_3177_ = lean_array_push(v_fst_3138_, v_fst_3171_);
v___x_3178_ = lean_array_push(v_snd_3139_, v_snd_3172_);
v___x_3179_ = lean_nat_add(v_fst_3134_, v___x_3152_);
lean_dec(v_fst_3134_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 1, v___x_3178_);
lean_ctor_set(v___x_3174_, 0, v___x_3177_);
v___x_3181_ = v___x_3174_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v___x_3178_);
v___x_3181_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3183_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 1, v___x_3181_);
lean_ctor_set(v___x_3169_, 0, v___x_3179_);
v___x_3183_ = v___x_3169_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3185_; 
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 1, v___x_3183_);
lean_ctor_set(v___x_3141_, 0, v___x_3176_);
v___x_3185_ = v___x_3141_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3187_; 
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 1, v___x_3185_);
lean_ctor_set(v___x_3136_, 0, v___x_3159_);
v___x_3187_ = v___x_3136_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_nat_add(v_a_3120_, v___x_3152_);
lean_dec(v_a_3120_);
v_a_3120_ = v___x_3188_;
v_b_3121_ = v___x_3187_;
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
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref(v___x_3159_);
lean_del_object(v___x_3141_);
lean_dec(v_snd_3139_);
lean_dec(v_fst_3138_);
lean_del_object(v___x_3136_);
lean_dec(v_fst_3134_);
lean_dec(v_fst_3133_);
lean_dec(v_a_3120_);
lean_dec(v___x_3119_);
lean_dec_ref(v___x_3118_);
lean_dec(v___x_3117_);
lean_dec(v_matchDeclName_3116_);
lean_dec_ref(v___x_3115_);
lean_dec_ref(v___x_3114_);
lean_dec(v___x_3113_);
lean_dec_ref(v_a_3112_);
lean_dec_ref(v___x_3111_);
lean_dec(v_baseName_3110_);
lean_dec_ref(v_val_3109_);
v_a_3196_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3164_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3164_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec_ref(v___x_3159_);
lean_dec_ref(v___f_3158_);
lean_del_object(v___x_3141_);
lean_dec(v_snd_3139_);
lean_dec(v_fst_3138_);
lean_del_object(v___x_3136_);
lean_dec(v_fst_3134_);
lean_dec(v_fst_3133_);
lean_dec(v_a_3120_);
lean_dec(v___x_3119_);
lean_dec_ref(v___x_3118_);
lean_dec(v___x_3117_);
lean_dec(v_matchDeclName_3116_);
lean_dec_ref(v___x_3115_);
lean_dec_ref(v___x_3114_);
lean_dec(v___x_3113_);
lean_dec_ref(v_a_3112_);
lean_dec_ref(v___x_3111_);
lean_dec(v_baseName_3110_);
lean_dec_ref(v_val_3109_);
v_a_3204_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3162_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3162_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
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
lean_object* v_upperBound_3219_ = _args[0];
lean_object* v_val_3220_ = _args[1];
lean_object* v_baseName_3221_ = _args[2];
lean_object* v___x_3222_ = _args[3];
lean_object* v_a_3223_ = _args[4];
lean_object* v___x_3224_ = _args[5];
lean_object* v___x_3225_ = _args[6];
lean_object* v___x_3226_ = _args[7];
lean_object* v_matchDeclName_3227_ = _args[8];
lean_object* v___x_3228_ = _args[9];
lean_object* v___x_3229_ = _args[10];
lean_object* v___x_3230_ = _args[11];
lean_object* v_a_3231_ = _args[12];
lean_object* v_b_3232_ = _args[13];
lean_object* v___y_3233_ = _args[14];
lean_object* v___y_3234_ = _args[15];
lean_object* v___y_3235_ = _args[16];
lean_object* v___y_3236_ = _args[17];
lean_object* v___y_3237_ = _args[18];
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3219_, v_val_3220_, v_baseName_3221_, v___x_3222_, v_a_3223_, v___x_3224_, v___x_3225_, v___x_3226_, v_matchDeclName_3227_, v___x_3228_, v___x_3229_, v___x_3230_, v_a_3231_, v_b_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v_upperBound_3219_);
return v_res_3238_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3242_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3243_ = lean_unsigned_to_nat(6u);
v___x_3244_ = lean_unsigned_to_nat(233u);
v___x_3245_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3246_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3247_ = l_mkPanicMessageWithDecl(v___x_3246_, v___x_3245_, v___x_3244_, v___x_3243_, v___x_3242_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3260_, lean_object* v_matchDeclName_3261_, lean_object* v_numParams_3262_, lean_object* v_val_3263_, lean_object* v___x_3264_, lean_object* v_numDiscrs_3265_, lean_object* v_baseName_3266_, lean_object* v_a_3267_, lean_object* v___x_3268_, lean_object* v___x_3269_, lean_object* v___x_3270_, lean_object* v_uElimPos_x3f_3271_, lean_object* v_discrInfos_3272_, lean_object* v_overlaps_3273_, lean_object* v___f_3274_, lean_object* v___x_3275_, lean_object* v_altInfos_3276_, lean_object* v_xs_3277_, lean_object* v___matchResultType_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; uint8_t v___y_3296_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v_lower_3304_; lean_object* v_upper_3305_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3262_);
lean_inc_ref(v_xs_3277_);
v___x_3300_ = l_Array_toSubarray___redArg(v_xs_3277_, v___x_3299_, v_numParams_3262_);
v___x_3301_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3263_);
v___x_3302_ = lean_array_get(v___x_3264_, v_xs_3277_, v___x_3301_);
lean_dec(v___x_3301_);
v___x_3358_ = lean_array_get_size(v_xs_3277_);
v___x_3359_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3263_);
v___x_3360_ = lean_nat_sub(v___x_3358_, v___x_3359_);
lean_dec(v___x_3359_);
v___x_3361_ = lean_nat_dec_le(v___x_3360_, v___x_3299_);
if (v___x_3361_ == 0)
{
v_lower_3304_ = v___x_3360_;
v_upper_3305_ = v___x_3358_;
goto v___jp_3303_;
}
else
{
lean_dec(v___x_3360_);
v_lower_3304_ = v___x_3299_;
v_upper_3305_ = v___x_3358_;
goto v___jp_3303_;
}
v___jp_3284_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3286_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3285_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
return v___x_3286_;
}
v___jp_3287_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3290_, 0, v___y_3288_);
lean_ctor_set(v___x_3290_, 1, v_splitterName_3260_);
lean_ctor_set(v___x_3290_, 2, v___y_3289_);
v___x_3291_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3261_, v___x_3290_, v___y_3282_);
return v___x_3291_;
}
v___jp_3292_:
{
lean_object* v___x_3297_; 
lean_inc(v_matchDeclName_3261_);
v___x_3297_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3261_, v___y_3296_, v___y_3294_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_dec_ref_known(v___x_3297_, 1);
v___y_3288_ = v___y_3293_;
v___y_3289_ = v___y_3295_;
goto v___jp_3287_;
}
else
{
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3293_);
lean_dec(v_matchDeclName_3261_);
lean_dec(v_splitterName_3260_);
return v___x_3297_;
}
}
v___jp_3303_:
{
lean_object* v___x_3306_; lean_object* v_start_3307_; lean_object* v_stop_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_inc_ref(v_xs_3277_);
v___x_3306_ = l_Array_toSubarray___redArg(v_xs_3277_, v_lower_3304_, v_upper_3305_);
v_start_3307_ = lean_ctor_get(v___x_3306_, 1);
v_stop_3308_ = lean_ctor_get(v___x_3306_, 2);
v___x_3309_ = lean_unsigned_to_nat(1u);
v___x_3310_ = lean_nat_add(v_numParams_3262_, v___x_3309_);
v___x_3311_ = lean_nat_add(v___x_3310_, v_numDiscrs_3265_);
v___x_3312_ = lean_nat_sub(v_stop_3308_, v_start_3307_);
v___x_3313_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3314_ = l_Array_toSubarray___redArg(v_xs_3277_, v___x_3310_, v___x_3311_);
lean_inc(v___x_3269_);
lean_inc(v_matchDeclName_3261_);
lean_inc(v___x_3268_);
v___x_3315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3312_, v_val_3263_, v_baseName_3266_, v___x_3314_, v_a_3267_, v___x_3268_, v___x_3300_, v___x_3302_, v_matchDeclName_3261_, v___x_3269_, v___x_3306_, v___x_3270_, v___x_3299_, v___x_3313_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___x_3312_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v_snd_3317_; lean_object* v_snd_3318_; lean_object* v_snd_3319_; lean_object* v_fst_3320_; lean_object* v_fst_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3348_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref_known(v___x_3315_, 1);
v_snd_3317_ = lean_ctor_get(v_a_3316_, 1);
v_snd_3318_ = lean_ctor_get(v_snd_3317_, 1);
v_snd_3319_ = lean_ctor_get(v_snd_3318_, 1);
lean_inc(v_snd_3319_);
v_fst_3320_ = lean_ctor_get(v_a_3316_, 0);
lean_inc(v_fst_3320_);
lean_dec(v_a_3316_);
v_fst_3321_ = lean_ctor_get(v_snd_3319_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v_snd_3319_);
if (v_isSharedCheck_3348_ == 0)
{
lean_object* v_unused_3349_; 
v_unused_3349_ = lean_ctor_get(v_snd_3319_, 1);
lean_dec(v_unused_3349_);
v___x_3323_ = v_snd_3319_;
v_isShared_3324_ = v_isSharedCheck_3348_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_fst_3321_);
lean_dec(v_snd_3319_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3348_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; uint8_t v___x_3326_; 
lean_inc_ref(v_overlaps_3273_);
lean_inc(v_fst_3321_);
v___x_3325_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3325_, 0, v_numParams_3262_);
lean_ctor_set(v___x_3325_, 1, v_numDiscrs_3265_);
lean_ctor_set(v___x_3325_, 2, v_fst_3321_);
lean_ctor_set(v___x_3325_, 3, v_uElimPos_x3f_3271_);
lean_ctor_set(v___x_3325_, 4, v_discrInfos_3272_);
lean_ctor_set(v___x_3325_, 5, v_overlaps_3273_);
v___x_3326_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3273_);
lean_dec_ref(v_overlaps_3273_);
if (v___x_3326_ == 0)
{
uint8_t v___x_3327_; 
lean_del_object(v___x_3323_);
lean_dec(v_fst_3321_);
lean_dec_ref(v___x_3275_);
lean_dec(v___x_3269_);
lean_dec(v___x_3268_);
v___x_3327_ = 1;
v___y_3293_ = v_fst_3320_;
v___y_3294_ = v___f_3274_;
v___y_3295_ = v___x_3325_;
v___y_3296_ = v___x_3327_;
goto v___jp_3292_;
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3329_ = lean_find_expr(v___x_3328_, v___x_3275_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
lean_dec_ref(v___f_3274_);
v___x_3330_ = lean_array_get_size(v_altInfos_3276_);
v___x_3331_ = lean_array_get_size(v_fst_3321_);
v___x_3332_ = lean_nat_dec_eq(v___x_3330_, v___x_3331_);
if (v___x_3332_ == 0)
{
lean_dec_ref_known(v___x_3325_, 6);
lean_del_object(v___x_3323_);
lean_dec(v_fst_3321_);
lean_dec(v_fst_3320_);
lean_dec_ref(v___x_3275_);
lean_dec(v___x_3269_);
lean_dec(v___x_3268_);
lean_dec(v_matchDeclName_3261_);
lean_dec(v_splitterName_3260_);
goto v___jp_3284_;
}
else
{
uint8_t v___x_3333_; 
v___x_3333_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3276_, v_fst_3321_, v___x_3330_);
lean_dec(v_fst_3321_);
if (v___x_3333_ == 0)
{
lean_dec_ref_known(v___x_3325_, 6);
lean_del_object(v___x_3323_);
lean_dec(v_fst_3320_);
lean_dec_ref(v___x_3275_);
lean_dec(v___x_3269_);
lean_dec(v___x_3268_);
lean_dec(v_matchDeclName_3261_);
lean_dec(v_splitterName_3260_);
goto v___jp_3284_;
}
else
{
uint8_t v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3340_; 
v___x_3334_ = 0;
lean_inc_n(v_splitterName_3260_, 2);
v___x_3335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3335_, 0, v_splitterName_3260_);
lean_ctor_set(v___x_3335_, 1, v___x_3269_);
lean_ctor_set(v___x_3335_, 2, v___x_3275_);
lean_inc(v_matchDeclName_3261_);
v___x_3336_ = l_Lean_mkConst(v_matchDeclName_3261_, v___x_3268_);
v___x_3337_ = lean_box(1);
v___x_3338_ = 1;
if (v_isShared_3324_ == 0)
{
lean_ctor_set_tag(v___x_3323_, 1);
lean_ctor_set(v___x_3323_, 1, v___x_3298_);
lean_ctor_set(v___x_3323_, 0, v_splitterName_3260_);
v___x_3340_ = v___x_3323_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_splitterName_3260_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v___x_3298_);
v___x_3340_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3341_, 0, v___x_3335_);
lean_ctor_set(v___x_3341_, 1, v___x_3336_);
lean_ctor_set(v___x_3341_, 2, v___x_3337_);
lean_ctor_set(v___x_3341_, 3, v___x_3340_);
lean_ctor_set_uint8(v___x_3341_, sizeof(void*)*4, v___x_3338_);
v___x_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
lean_inc_ref(v___x_3342_);
v___x_3343_ = l_Lean_addDecl(v___x_3342_, v___x_3334_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3343_) == 0)
{
uint8_t v___x_3344_; lean_object* v___x_3345_; 
lean_dec_ref_known(v___x_3343_, 1);
v___x_3344_ = 0;
lean_inc(v_splitterName_3260_);
v___x_3345_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3260_, v___x_3344_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v___x_3346_; 
lean_dec_ref_known(v___x_3345_, 1);
v___x_3346_ = l_Lean_compileDecl(v___x_3342_, v___x_3334_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_dec_ref_known(v___x_3346_, 1);
v___y_3288_ = v_fst_3320_;
v___y_3289_ = v___x_3325_;
goto v___jp_3287_;
}
else
{
lean_dec_ref_known(v___x_3325_, 6);
lean_dec(v_fst_3320_);
lean_dec(v_matchDeclName_3261_);
lean_dec(v_splitterName_3260_);
return v___x_3346_;
}
}
else
{
lean_dec_ref_known(v___x_3342_, 1);
lean_dec_ref_known(v___x_3325_, 6);
lean_dec(v_fst_3320_);
lean_dec(v_matchDeclName_3261_);
lean_dec(v_splitterName_3260_);
return v___x_3345_;
}
}
else
{
lean_dec_ref_known(v___x_3342_, 1);
lean_dec_ref_known(v___x_3325_, 6);
lean_dec(v_fst_3320_);
lean_dec(v_matchDeclName_3261_);
lean_dec(v_splitterName_3260_);
return v___x_3343_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3329_, 1);
lean_del_object(v___x_3323_);
lean_dec(v_fst_3321_);
lean_dec_ref(v___x_3275_);
lean_dec(v___x_3269_);
lean_dec(v___x_3268_);
v___y_3293_ = v_fst_3320_;
v___y_3294_ = v___f_3274_;
v___y_3295_ = v___x_3325_;
v___y_3296_ = v___x_3326_;
goto v___jp_3292_;
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec_ref(v___x_3275_);
lean_dec_ref(v___f_3274_);
lean_dec_ref(v_overlaps_3273_);
lean_dec_ref(v_discrInfos_3272_);
lean_dec(v_uElimPos_x3f_3271_);
lean_dec(v___x_3269_);
lean_dec(v___x_3268_);
lean_dec(v_numDiscrs_3265_);
lean_dec(v_numParams_3262_);
lean_dec(v_matchDeclName_3261_);
lean_dec(v_splitterName_3260_);
v_a_3350_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3315_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3315_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3362_ = _args[0];
lean_object* v_matchDeclName_3363_ = _args[1];
lean_object* v_numParams_3364_ = _args[2];
lean_object* v_val_3365_ = _args[3];
lean_object* v___x_3366_ = _args[4];
lean_object* v_numDiscrs_3367_ = _args[5];
lean_object* v_baseName_3368_ = _args[6];
lean_object* v_a_3369_ = _args[7];
lean_object* v___x_3370_ = _args[8];
lean_object* v___x_3371_ = _args[9];
lean_object* v___x_3372_ = _args[10];
lean_object* v_uElimPos_x3f_3373_ = _args[11];
lean_object* v_discrInfos_3374_ = _args[12];
lean_object* v_overlaps_3375_ = _args[13];
lean_object* v___f_3376_ = _args[14];
lean_object* v___x_3377_ = _args[15];
lean_object* v_altInfos_3378_ = _args[16];
lean_object* v_xs_3379_ = _args[17];
lean_object* v___matchResultType_3380_ = _args[18];
lean_object* v___y_3381_ = _args[19];
lean_object* v___y_3382_ = _args[20];
lean_object* v___y_3383_ = _args[21];
lean_object* v___y_3384_ = _args[22];
lean_object* v___y_3385_ = _args[23];
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3362_, v_matchDeclName_3363_, v_numParams_3364_, v_val_3365_, v___x_3366_, v_numDiscrs_3367_, v_baseName_3368_, v_a_3369_, v___x_3370_, v___x_3371_, v___x_3372_, v_uElimPos_x3f_3373_, v_discrInfos_3374_, v_overlaps_3375_, v___f_3376_, v___x_3377_, v_altInfos_3378_, v_xs_3379_, v___matchResultType_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec_ref(v___matchResultType_3380_);
lean_dec_ref(v_altInfos_3378_);
lean_dec_ref(v___x_3366_);
return v_res_3386_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3389_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3390_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3391_ = lean_unsigned_to_nat(0u);
v___x_3392_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
lean_ctor_set(v___x_3392_, 2, v___x_3391_);
lean_ctor_set(v___x_3392_, 3, v___x_3391_);
lean_ctor_set(v___x_3392_, 4, v___x_3390_);
lean_ctor_set(v___x_3392_, 5, v___x_3390_);
lean_ctor_set(v___x_3392_, 6, v___x_3390_);
lean_ctor_set(v___x_3392_, 7, v___x_3390_);
lean_ctor_set(v___x_3392_, 8, v___x_3390_);
lean_ctor_set(v___x_3392_, 9, v___x_3390_);
lean_ctor_set(v___x_3392_, 10, v___x_3390_);
lean_ctor_set(v___x_3392_, 11, v___x_3389_);
return v___x_3392_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3393_ = lean_box(1);
v___x_3394_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3395_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v___x_3394_);
lean_ctor_set(v___x_3396_, 2, v___x_3393_);
return v___x_3396_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3));
v___x_3399_ = l_Lean_stringToMessageData(v___x_3398_);
return v___x_3399_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_3402_ = l_Lean_stringToMessageData(v___x_3401_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_3405_ = l_Lean_stringToMessageData(v___x_3404_);
return v___x_3405_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_3408_ = l_Lean_stringToMessageData(v___x_3407_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_3411_ = l_Lean_stringToMessageData(v___x_3410_);
return v___x_3411_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_3414_ = l_Lean_stringToMessageData(v___x_3413_);
return v___x_3414_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_3417_ = l_Lean_stringToMessageData(v___x_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3418_, lean_object* v_declHint_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v_env_3424_; uint8_t v___x_3425_; 
v___x_3422_ = lean_box(0);
v___x_3423_ = lean_st_ref_get(v___y_3420_);
v_env_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc_ref(v_env_3424_);
lean_dec(v___x_3423_);
v___x_3425_ = l_Lean_Name_isAnonymous(v_declHint_3419_);
if (v___x_3425_ == 0)
{
uint8_t v_isExporting_3426_; 
v_isExporting_3426_ = lean_ctor_get_uint8(v_env_3424_, sizeof(void*)*13);
if (v_isExporting_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec_ref(v_env_3424_);
lean_dec(v_declHint_3419_);
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_msg_3418_);
return v___x_3427_;
}
else
{
lean_object* v___x_3428_; uint8_t v___x_3429_; 
lean_inc_ref(v_env_3424_);
v___x_3428_ = l_Lean_Environment_setExporting(v_env_3424_, v___x_3425_);
lean_inc(v_declHint_3419_);
lean_inc_ref(v___x_3428_);
v___x_3429_ = l_Lean_Environment_contains(v___x_3428_, v_declHint_3419_, v_isExporting_3426_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
lean_dec_ref(v___x_3428_);
lean_dec_ref(v_env_3424_);
lean_dec(v_declHint_3419_);
v___x_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3430_, 0, v_msg_3418_);
return v___x_3430_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v_c_3436_; lean_object* v___x_3437_; 
v___x_3431_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3432_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3433_ = l_Lean_Options_empty;
v___x_3434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3428_);
lean_ctor_set(v___x_3434_, 1, v___x_3431_);
lean_ctor_set(v___x_3434_, 2, v___x_3432_);
lean_ctor_set(v___x_3434_, 3, v___x_3433_);
lean_inc(v_declHint_3419_);
v___x_3435_ = l_Lean_MessageData_ofConstName(v_declHint_3419_, v___x_3425_);
v_c_3436_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3436_, 0, v___x_3434_);
lean_ctor_set(v_c_3436_, 1, v___x_3435_);
v___x_3437_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3424_, v_declHint_3419_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec_ref(v_env_3424_);
lean_dec(v_declHint_3419_);
v___x_3438_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
lean_ctor_set(v___x_3439_, 1, v_c_3436_);
v___x_3440_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_3441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3439_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = l_Lean_MessageData_note(v___x_3441_);
v___x_3443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3443_, 0, v_msg_3418_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
return v___x_3444_;
}
else
{
lean_object* v_val_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3479_; 
v_val_3445_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3447_ = v___x_3437_;
v_isShared_3448_ = v_isSharedCheck_3479_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_val_3445_);
lean_dec(v___x_3437_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3479_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v_moduleNames_3450_; lean_object* v_mod_3451_; uint8_t v___x_3452_; 
v___x_3449_ = l_Lean_Environment_header(v_env_3424_);
lean_dec_ref(v_env_3424_);
v_moduleNames_3450_ = lean_ctor_get(v___x_3449_, 4);
lean_inc_ref(v_moduleNames_3450_);
lean_dec_ref(v___x_3449_);
v_mod_3451_ = lean_array_get(v___x_3422_, v_moduleNames_3450_, v_val_3445_);
lean_dec(v_val_3445_);
lean_dec_ref(v_moduleNames_3450_);
v___x_3452_ = l_Lean_isPrivateName(v_declHint_3419_);
lean_dec(v_declHint_3419_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3453_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
lean_ctor_set(v___x_3454_, 1, v_c_3436_);
v___x_3455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = l_Lean_MessageData_ofName(v_mod_3451_);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3458_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = l_Lean_MessageData_note(v___x_3460_);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v_msg_3418_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set_tag(v___x_3447_, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3462_);
v___x_3464_ = v___x_3447_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3466_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
lean_ctor_set(v___x_3467_, 1, v_c_3436_);
v___x_3468_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_3469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3467_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = l_Lean_MessageData_ofName(v_mod_3451_);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3469_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Lean_MessageData_note(v___x_3473_);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v_msg_3418_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set_tag(v___x_3447_, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3475_);
v___x_3477_ = v___x_3447_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3480_; 
lean_dec_ref(v_env_3424_);
lean_dec(v_declHint_3419_);
v___x_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3480_, 0, v_msg_3418_);
return v___x_3480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3481_, lean_object* v_declHint_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3481_, v_declHint_3482_, v___y_3483_);
lean_dec(v___y_3483_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3486_, lean_object* v_declHint_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v___x_3493_; lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3503_; 
v___x_3493_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3486_, v_declHint_3487_, v___y_3491_);
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3503_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3503_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3498_ = l_Lean_unknownIdentifierMessageTag;
v___x_3499_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
lean_ctor_set(v___x_3499_, 1, v_a_3494_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3499_);
v___x_3501_ = v___x_3496_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3504_, lean_object* v_declHint_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3504_, v_declHint_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3512_, lean_object* v_msg_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v_toCold_3519_; lean_object* v_currRecDepth_3520_; lean_object* v_ref_3521_; uint16_t v_optionFlags_3522_; uint8_t v_suppressElabErrors_3523_; uint8_t v_isRecordingDeps_3524_; lean_object* v_ref_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v_toCold_3519_ = lean_ctor_get(v___y_3516_, 0);
v_currRecDepth_3520_ = lean_ctor_get(v___y_3516_, 1);
v_ref_3521_ = lean_ctor_get(v___y_3516_, 2);
v_optionFlags_3522_ = lean_ctor_get_uint16(v___y_3516_, sizeof(void*)*3);
v_suppressElabErrors_3523_ = lean_ctor_get_uint8(v___y_3516_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3524_ = lean_ctor_get_uint8(v___y_3516_, sizeof(void*)*3 + 3);
v_ref_3525_ = l_Lean_replaceRef(v_ref_3512_, v_ref_3521_);
lean_inc(v_currRecDepth_3520_);
lean_inc_ref(v_toCold_3519_);
v___x_3526_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3526_, 0, v_toCold_3519_);
lean_ctor_set(v___x_3526_, 1, v_currRecDepth_3520_);
lean_ctor_set(v___x_3526_, 2, v_ref_3525_);
lean_ctor_set_uint16(v___x_3526_, sizeof(void*)*3, v_optionFlags_3522_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*3 + 2, v_suppressElabErrors_3523_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*3 + 3, v_isRecordingDeps_3524_);
v___x_3527_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3513_, v___y_3514_, v___y_3515_, v___x_3526_, v___y_3517_);
lean_dec_ref_known(v___x_3526_, 3);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3528_, lean_object* v_msg_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3528_, v_msg_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v_ref_3528_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3536_, lean_object* v_msg_3537_, lean_object* v_declHint_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v___x_3544_; lean_object* v_a_3545_; lean_object* v___x_3546_; 
v___x_3544_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3537_, v_declHint_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref(v___x_3544_);
v___x_3546_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3536_, v_a_3545_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3547_, lean_object* v_msg_3548_, lean_object* v_declHint_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3547_, v_msg_3548_, v_declHint_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v_ref_3547_);
return v_res_3555_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3558_ = l_Lean_stringToMessageData(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3561_ = l_Lean_stringToMessageData(v___x_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3562_, lean_object* v_constName_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v___x_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3569_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3570_ = 0;
lean_inc(v_constName_3563_);
v___x_3571_ = l_Lean_MessageData_ofConstName(v_constName_3563_, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3569_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3572_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3562_, v___x_3574_, v_constName_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3576_, lean_object* v_constName_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3576_, v_constName_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v_ref_3576_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v_ref_3590_; lean_object* v___x_3591_; 
v_ref_3590_ = lean_ctor_get(v___y_3587_, 2);
v___x_3591_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3590_, v_constName_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v___x_3605_; lean_object* v_env_3606_; uint8_t v___x_3607_; lean_object* v___x_3608_; 
v___x_3605_ = lean_st_ref_get(v___y_3603_);
v_env_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc_ref(v_env_3606_);
lean_dec(v___x_3605_);
v___x_3607_ = 0;
lean_inc(v_constName_3599_);
v___x_3608_ = l_Lean_Environment_find_x3f(v_env_3606_, v_constName_3599_, v___x_3607_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
return v___x_3609_;
}
else
{
lean_object* v_val_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec(v_constName_3599_);
v_val_3610_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3608_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_val_3610_);
lean_dec(v___x_3608_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set_tag(v___x_3612_, 0);
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_val_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
if (lean_obj_tag(v_a_3625_) == 0)
{
lean_object* v___x_3627_; 
v___x_3627_ = l_List_reverse___redArg(v_a_3626_);
return v___x_3627_;
}
else
{
lean_object* v_head_3628_; lean_object* v_tail_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3638_; 
v_head_3628_ = lean_ctor_get(v_a_3625_, 0);
v_tail_3629_ = lean_ctor_get(v_a_3625_, 1);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_a_3625_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3631_ = v_a_3625_;
v_isShared_3632_ = v_isSharedCheck_3638_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_tail_3629_);
lean_inc(v_head_3628_);
lean_dec(v_a_3625_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3638_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3633_ = l_Lean_mkLevelParam(v_head_3628_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v_a_3626_);
lean_ctor_set(v___x_3631_, 0, v___x_3633_);
v___x_3635_ = v___x_3631_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3633_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_a_3626_);
v___x_3635_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
v_a_3625_ = v_tail_3629_;
v_a_3626_ = v___x_3635_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3641_ = l_Lean_stringToMessageData(v___x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3642_, lean_object* v_baseName_3643_, lean_object* v_splitterName_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v___x_3650_; uint8_t v_foApprox_3651_; uint8_t v_ctxApprox_3652_; uint8_t v_quasiPatternApprox_3653_; uint8_t v_constApprox_3654_; uint8_t v_isDefEqStuckEx_3655_; uint8_t v_unificationHints_3656_; uint8_t v_proofIrrelevance_3657_; uint8_t v_assignSyntheticOpaque_3658_; uint8_t v_offsetCnstrs_3659_; uint8_t v_transparency_3660_; uint8_t v_univApprox_3661_; uint8_t v_iota_3662_; uint8_t v_beta_3663_; uint8_t v_proj_3664_; uint8_t v_zeta_3665_; uint8_t v_zetaDelta_3666_; uint8_t v_zetaUnused_3667_; uint8_t v_zetaHave_3668_; uint8_t v_canUnfoldPredicateConfig_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3732_; 
v___x_3650_ = l_Lean_Meta_Context_config(v_a_3645_);
v_foApprox_3651_ = lean_ctor_get_uint8(v___x_3650_, 0);
v_ctxApprox_3652_ = lean_ctor_get_uint8(v___x_3650_, 1);
v_quasiPatternApprox_3653_ = lean_ctor_get_uint8(v___x_3650_, 2);
v_constApprox_3654_ = lean_ctor_get_uint8(v___x_3650_, 3);
v_isDefEqStuckEx_3655_ = lean_ctor_get_uint8(v___x_3650_, 4);
v_unificationHints_3656_ = lean_ctor_get_uint8(v___x_3650_, 5);
v_proofIrrelevance_3657_ = lean_ctor_get_uint8(v___x_3650_, 6);
v_assignSyntheticOpaque_3658_ = lean_ctor_get_uint8(v___x_3650_, 7);
v_offsetCnstrs_3659_ = lean_ctor_get_uint8(v___x_3650_, 8);
v_transparency_3660_ = lean_ctor_get_uint8(v___x_3650_, 9);
v_univApprox_3661_ = lean_ctor_get_uint8(v___x_3650_, 11);
v_iota_3662_ = lean_ctor_get_uint8(v___x_3650_, 12);
v_beta_3663_ = lean_ctor_get_uint8(v___x_3650_, 13);
v_proj_3664_ = lean_ctor_get_uint8(v___x_3650_, 14);
v_zeta_3665_ = lean_ctor_get_uint8(v___x_3650_, 15);
v_zetaDelta_3666_ = lean_ctor_get_uint8(v___x_3650_, 16);
v_zetaUnused_3667_ = lean_ctor_get_uint8(v___x_3650_, 17);
v_zetaHave_3668_ = lean_ctor_get_uint8(v___x_3650_, 18);
v_canUnfoldPredicateConfig_3669_ = lean_ctor_get_uint8(v___x_3650_, 19);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3671_ = v___x_3650_;
v_isShared_3672_ = v_isSharedCheck_3732_;
goto v_resetjp_3670_;
}
else
{
lean_dec(v___x_3650_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3732_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
uint8_t v_trackZetaDelta_3673_; lean_object* v_zetaDeltaSet_3674_; lean_object* v_lctx_3675_; lean_object* v_localInstances_3676_; lean_object* v_defEqCtx_x3f_3677_; lean_object* v_synthPendingDepth_3678_; lean_object* v_customCanUnfoldPredicate_x3f_3679_; uint8_t v_univApprox_3680_; uint8_t v_inTypeClassResolution_3681_; uint8_t v_cacheInferType_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3730_; 
v_trackZetaDelta_3673_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*7);
v_zetaDeltaSet_3674_ = lean_ctor_get(v_a_3645_, 1);
v_lctx_3675_ = lean_ctor_get(v_a_3645_, 2);
v_localInstances_3676_ = lean_ctor_get(v_a_3645_, 3);
v_defEqCtx_x3f_3677_ = lean_ctor_get(v_a_3645_, 4);
v_synthPendingDepth_3678_ = lean_ctor_get(v_a_3645_, 5);
v_customCanUnfoldPredicate_x3f_3679_ = lean_ctor_get(v_a_3645_, 6);
v_univApprox_3680_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3681_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*7 + 2);
v_cacheInferType_3682_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*7 + 3);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_a_3645_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; 
v_unused_3731_ = lean_ctor_get(v_a_3645_, 0);
lean_dec(v_unused_3731_);
v___x_3684_ = v_a_3645_;
v_isShared_3685_ = v_isSharedCheck_3730_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3679_);
lean_inc(v_synthPendingDepth_3678_);
lean_inc(v_defEqCtx_x3f_3677_);
lean_inc(v_localInstances_3676_);
lean_inc(v_lctx_3675_);
lean_inc(v_zetaDeltaSet_3674_);
lean_dec(v_a_3645_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3730_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
uint8_t v___x_3686_; lean_object* v___x_3688_; 
v___x_3686_ = 2;
if (v_isShared_3672_ == 0)
{
v___x_3688_ = v___x_3671_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 0, v_foApprox_3651_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 1, v_ctxApprox_3652_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 2, v_quasiPatternApprox_3653_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 3, v_constApprox_3654_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 4, v_isDefEqStuckEx_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 5, v_unificationHints_3656_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 6, v_proofIrrelevance_3657_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 7, v_assignSyntheticOpaque_3658_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 8, v_offsetCnstrs_3659_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 9, v_transparency_3660_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 11, v_univApprox_3661_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 12, v_iota_3662_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 13, v_beta_3663_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 14, v_proj_3664_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 15, v_zeta_3665_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 16, v_zetaDelta_3666_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 17, v_zetaUnused_3667_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 18, v_zetaHave_3668_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, 19, v_canUnfoldPredicateConfig_3669_);
v___x_3688_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
uint64_t v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
lean_ctor_set_uint8(v___x_3688_, 10, v___x_3686_);
v___x_3689_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3688_);
v___x_3690_ = l_Lean_instInhabitedExpr;
v___x_3691_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3691_, 0, v___x_3688_);
lean_ctor_set_uint64(v___x_3691_, sizeof(void*)*1, v___x_3689_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3691_);
v___x_3693_ = v___x_3684_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_zetaDeltaSet_3674_);
lean_ctor_set(v_reuseFailAlloc_3728_, 2, v_lctx_3675_);
lean_ctor_set(v_reuseFailAlloc_3728_, 3, v_localInstances_3676_);
lean_ctor_set(v_reuseFailAlloc_3728_, 4, v_defEqCtx_x3f_3677_);
lean_ctor_set(v_reuseFailAlloc_3728_, 5, v_synthPendingDepth_3678_);
lean_ctor_set(v_reuseFailAlloc_3728_, 6, v_customCanUnfoldPredicate_x3f_3679_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, sizeof(void*)*7, v_trackZetaDelta_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, sizeof(void*)*7 + 1, v_univApprox_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3681_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, sizeof(void*)*7 + 3, v_cacheInferType_3682_);
v___x_3693_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; 
lean_inc(v_matchDeclName_3642_);
v___x_3694_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3642_, v___x_3693_, v_a_3646_, v_a_3647_, v_a_3648_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v_a_3700_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
v___x_3696_ = l_Lean_ConstantInfo_levelParams(v_a_3695_);
v___x_3697_ = lean_box(0);
lean_inc(v___x_3696_);
v___x_3698_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v___x_3696_, v___x_3697_);
lean_inc(v_matchDeclName_3642_);
v___x_3699_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_3642_, v_a_3648_);
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
lean_dec_ref(v___x_3699_);
if (lean_obj_tag(v_a_3700_) == 1)
{
lean_object* v_val_3701_; lean_object* v_numParams_3702_; lean_object* v_numDiscrs_3703_; lean_object* v_altInfos_3704_; lean_object* v_uElimPos_x3f_3705_; lean_object* v_discrInfos_3706_; lean_object* v_overlaps_3707_; lean_object* v___f_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___f_3711_; uint8_t v___x_3712_; lean_object* v___x_3713_; 
v_val_3701_ = lean_ctor_get(v_a_3700_, 0);
lean_inc(v_val_3701_);
lean_dec_ref_known(v_a_3700_, 1);
v_numParams_3702_ = lean_ctor_get(v_val_3701_, 0);
lean_inc(v_numParams_3702_);
v_numDiscrs_3703_ = lean_ctor_get(v_val_3701_, 1);
lean_inc(v_numDiscrs_3703_);
v_altInfos_3704_ = lean_ctor_get(v_val_3701_, 2);
lean_inc_ref(v_altInfos_3704_);
v_uElimPos_x3f_3705_ = lean_ctor_get(v_val_3701_, 3);
lean_inc(v_uElimPos_x3f_3705_);
v_discrInfos_3706_ = lean_ctor_get(v_val_3701_, 4);
lean_inc_ref(v_discrInfos_3706_);
v_overlaps_3707_ = lean_ctor_get(v_val_3701_, 5);
lean_inc_ref_n(v_overlaps_3707_, 2);
lean_inc(v_splitterName_3644_);
v___f_3708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3708_, 0, v_overlaps_3707_);
lean_closure_set(v___f_3708_, 1, v_splitterName_3644_);
v___x_3709_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3706_);
v___x_3710_ = l_Lean_ConstantInfo_type(v_a_3695_);
lean_inc_ref(v___x_3710_);
v___f_3711_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3711_, 0, v_splitterName_3644_);
lean_closure_set(v___f_3711_, 1, v_matchDeclName_3642_);
lean_closure_set(v___f_3711_, 2, v_numParams_3702_);
lean_closure_set(v___f_3711_, 3, v_val_3701_);
lean_closure_set(v___f_3711_, 4, v___x_3690_);
lean_closure_set(v___f_3711_, 5, v_numDiscrs_3703_);
lean_closure_set(v___f_3711_, 6, v_baseName_3643_);
lean_closure_set(v___f_3711_, 7, v_a_3695_);
lean_closure_set(v___f_3711_, 8, v___x_3698_);
lean_closure_set(v___f_3711_, 9, v___x_3696_);
lean_closure_set(v___f_3711_, 10, v___x_3709_);
lean_closure_set(v___f_3711_, 11, v_uElimPos_x3f_3705_);
lean_closure_set(v___f_3711_, 12, v_discrInfos_3706_);
lean_closure_set(v___f_3711_, 13, v_overlaps_3707_);
lean_closure_set(v___f_3711_, 14, v___f_3708_);
lean_closure_set(v___f_3711_, 15, v___x_3710_);
lean_closure_set(v___f_3711_, 16, v_altInfos_3704_);
v___x_3712_ = 0;
v___x_3713_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3710_, v___f_3711_, v___x_3712_, v___x_3712_, v___x_3693_, v_a_3646_, v_a_3647_, v_a_3648_);
lean_dec_ref(v___x_3693_);
return v___x_3713_;
}
else
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
lean_dec(v_a_3700_);
lean_dec(v___x_3698_);
lean_dec(v___x_3696_);
lean_dec(v_a_3695_);
lean_dec(v_splitterName_3644_);
lean_dec(v_baseName_3643_);
v___x_3714_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3715_ = l_Lean_MessageData_ofName(v_matchDeclName_3642_);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3718_, v___x_3693_, v_a_3646_, v_a_3647_, v_a_3648_);
lean_dec_ref(v___x_3693_);
return v___x_3719_;
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref(v___x_3693_);
lean_dec(v_splitterName_3644_);
lean_dec(v_baseName_3643_);
lean_dec(v_matchDeclName_3642_);
v_a_3720_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3694_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3694_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3733_, lean_object* v_baseName_3734_, lean_object* v_splitterName_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3733_, v_baseName_3734_, v_splitterName_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
lean_dec(v_a_3737_);
return v_res_3741_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3742_, lean_object* v_ys_3743_, lean_object* v_hsz_3744_, lean_object* v_x_3745_, lean_object* v_x_3746_){
_start:
{
uint8_t v___x_3747_; 
v___x_3747_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3742_, v_ys_3743_, v_x_3745_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3748_, lean_object* v_ys_3749_, lean_object* v_hsz_3750_, lean_object* v_x_3751_, lean_object* v_x_3752_){
_start:
{
uint8_t v_res_3753_; lean_object* v_r_3754_; 
v_res_3753_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3748_, v_ys_3749_, v_hsz_3750_, v_x_3751_, v_x_3752_);
lean_dec_ref(v_ys_3749_);
lean_dec_ref(v_xs_3748_);
v_r_3754_ = lean_box(v_res_3753_);
return v_r_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3755_, lean_object* v_R_3756_, lean_object* v_a_3757_, lean_object* v_b_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3757_, v_b_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3760_, lean_object* v_val_3761_, lean_object* v_baseName_3762_, lean_object* v___x_3763_, lean_object* v_a_3764_, lean_object* v___x_3765_, lean_object* v___x_3766_, lean_object* v___x_3767_, lean_object* v_matchDeclName_3768_, lean_object* v___x_3769_, lean_object* v___x_3770_, lean_object* v___x_3771_, lean_object* v_inst_3772_, lean_object* v_R_3773_, lean_object* v_a_3774_, lean_object* v_b_3775_, lean_object* v_c_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3760_, v_val_3761_, v_baseName_3762_, v___x_3763_, v_a_3764_, v___x_3765_, v___x_3766_, v___x_3767_, v_matchDeclName_3768_, v___x_3769_, v___x_3770_, v___x_3771_, v_a_3774_, v_b_3775_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3783_ = _args[0];
lean_object* v_val_3784_ = _args[1];
lean_object* v_baseName_3785_ = _args[2];
lean_object* v___x_3786_ = _args[3];
lean_object* v_a_3787_ = _args[4];
lean_object* v___x_3788_ = _args[5];
lean_object* v___x_3789_ = _args[6];
lean_object* v___x_3790_ = _args[7];
lean_object* v_matchDeclName_3791_ = _args[8];
lean_object* v___x_3792_ = _args[9];
lean_object* v___x_3793_ = _args[10];
lean_object* v___x_3794_ = _args[11];
lean_object* v_inst_3795_ = _args[12];
lean_object* v_R_3796_ = _args[13];
lean_object* v_a_3797_ = _args[14];
lean_object* v_b_3798_ = _args[15];
lean_object* v_c_3799_ = _args[16];
lean_object* v___y_3800_ = _args[17];
lean_object* v___y_3801_ = _args[18];
lean_object* v___y_3802_ = _args[19];
lean_object* v___y_3803_ = _args[20];
lean_object* v___y_3804_ = _args[21];
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3783_, v_val_3784_, v_baseName_3785_, v___x_3786_, v_a_3787_, v___x_3788_, v___x_3789_, v___x_3790_, v_matchDeclName_3791_, v___x_3792_, v___x_3793_, v___x_3794_, v_inst_3795_, v_R_3796_, v_a_3797_, v_b_3798_, v_c_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v_upperBound_3783_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3806_, lean_object* v_constName_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; 
v___x_3813_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3814_, lean_object* v_constName_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3814_, v_constName_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3822_, lean_object* v_ref_3823_, lean_object* v_constName_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3823_, v_constName_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3831_, lean_object* v_ref_3832_, lean_object* v_constName_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3831_, v_ref_3832_, v_constName_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v_ref_3832_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3840_, lean_object* v_ref_3841_, lean_object* v_msg_3842_, lean_object* v_declHint_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3841_, v_msg_3842_, v_declHint_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3850_, lean_object* v_ref_3851_, lean_object* v_msg_3852_, lean_object* v_declHint_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3850_, v_ref_3851_, v_msg_3852_, v_declHint_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v_ref_3851_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3860_, lean_object* v_declHint_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3860_, v_declHint_3861_, v___y_3865_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3868_, lean_object* v_declHint_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3868_, v_declHint_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3876_, lean_object* v_ref_3877_, lean_object* v_msg_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3877_, v_msg_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3885_, lean_object* v_ref_3886_, lean_object* v_msg_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3885_, v_ref_3886_, v_msg_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v_ref_3886_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3894_, lean_object* v_vals_3895_, lean_object* v_i_3896_, lean_object* v_k_3897_){
_start:
{
lean_object* v___x_3898_; uint8_t v___x_3899_; 
v___x_3898_ = lean_array_get_size(v_keys_3894_);
v___x_3899_ = lean_nat_dec_lt(v_i_3896_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; 
lean_dec(v_i_3896_);
v___x_3900_ = lean_box(0);
return v___x_3900_;
}
else
{
lean_object* v_k_x27_3901_; uint8_t v___x_3902_; 
v_k_x27_3901_ = lean_array_fget_borrowed(v_keys_3894_, v_i_3896_);
v___x_3902_ = lean_name_eq(v_k_3897_, v_k_x27_3901_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_unsigned_to_nat(1u);
v___x_3904_ = lean_nat_add(v_i_3896_, v___x_3903_);
lean_dec(v_i_3896_);
v_i_3896_ = v___x_3904_;
goto _start;
}
else
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = lean_array_fget_borrowed(v_vals_3895_, v_i_3896_);
lean_dec(v_i_3896_);
lean_inc(v___x_3906_);
v___x_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
return v___x_3907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3908_, lean_object* v_vals_3909_, lean_object* v_i_3910_, lean_object* v_k_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3908_, v_vals_3909_, v_i_3910_, v_k_3911_);
lean_dec(v_k_3911_);
lean_dec_ref(v_vals_3909_);
lean_dec_ref(v_keys_3908_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3913_, size_t v_x_3914_, lean_object* v_x_3915_){
_start:
{
if (lean_obj_tag(v_x_3913_) == 0)
{
lean_object* v_es_3916_; lean_object* v___x_3917_; size_t v___x_3918_; size_t v___x_3919_; lean_object* v_j_3920_; lean_object* v___x_3921_; 
v_es_3916_ = lean_ctor_get(v_x_3913_, 0);
v___x_3917_ = lean_box(2);
v___x_3918_ = ((size_t)31ULL);
v___x_3919_ = lean_usize_land(v_x_3914_, v___x_3918_);
v_j_3920_ = lean_usize_to_nat(v___x_3919_);
v___x_3921_ = lean_array_get_borrowed(v___x_3917_, v_es_3916_, v_j_3920_);
lean_dec(v_j_3920_);
switch(lean_obj_tag(v___x_3921_))
{
case 0:
{
lean_object* v_key_3922_; lean_object* v_val_3923_; uint8_t v___x_3924_; 
v_key_3922_ = lean_ctor_get(v___x_3921_, 0);
v_val_3923_ = lean_ctor_get(v___x_3921_, 1);
v___x_3924_ = lean_name_eq(v_x_3915_, v_key_3922_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; 
v___x_3925_ = lean_box(0);
return v___x_3925_;
}
else
{
lean_object* v___x_3926_; 
lean_inc(v_val_3923_);
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v_val_3923_);
return v___x_3926_;
}
}
case 1:
{
lean_object* v_node_3927_; size_t v___x_3928_; size_t v___x_3929_; 
v_node_3927_ = lean_ctor_get(v___x_3921_, 0);
v___x_3928_ = ((size_t)5ULL);
v___x_3929_ = lean_usize_shift_right(v_x_3914_, v___x_3928_);
v_x_3913_ = v_node_3927_;
v_x_3914_ = v___x_3929_;
goto _start;
}
default: 
{
lean_object* v___x_3931_; 
v___x_3931_ = lean_box(0);
return v___x_3931_;
}
}
}
else
{
lean_object* v_ks_3932_; lean_object* v_vs_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_ks_3932_ = lean_ctor_get(v_x_3913_, 0);
v_vs_3933_ = lean_ctor_get(v_x_3913_, 1);
v___x_3934_ = lean_unsigned_to_nat(0u);
v___x_3935_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3932_, v_vs_3933_, v___x_3934_, v_x_3915_);
return v___x_3935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3936_, lean_object* v_x_3937_, lean_object* v_x_3938_){
_start:
{
size_t v_x_709__boxed_3939_; lean_object* v_res_3940_; 
v_x_709__boxed_3939_ = lean_unbox_usize(v_x_3937_);
lean_dec(v_x_3937_);
v_res_3940_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3936_, v_x_709__boxed_3939_, v_x_3938_);
lean_dec(v_x_3938_);
lean_dec_ref(v_x_3936_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3941_, lean_object* v_x_3942_){
_start:
{
uint64_t v___y_3944_; 
if (lean_obj_tag(v_x_3942_) == 0)
{
uint64_t v___x_3947_; 
v___x_3947_ = 1723ULL;
v___y_3944_ = v___x_3947_;
goto v___jp_3943_;
}
else
{
uint64_t v_hash_3948_; 
v_hash_3948_ = lean_ctor_get_uint64(v_x_3942_, sizeof(void*)*2);
v___y_3944_ = v_hash_3948_;
goto v___jp_3943_;
}
v___jp_3943_:
{
size_t v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = lean_uint64_to_usize(v___y_3944_);
v___x_3946_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3941_, v___x_3945_, v_x_3942_);
return v___x_3946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3949_, lean_object* v_x_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3949_, v_x_3950_);
lean_dec(v_x_3950_);
lean_dec_ref(v_x_3949_);
return v_res_3951_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3959_ = l_Lean_stringToMessageData(v___x_3958_);
return v___x_3959_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3962_ = l_Lean_stringToMessageData(v___x_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v_env_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3969_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_3970_ = lean_st_ref_get(v_a_3967_);
v_env_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc_ref(v_env_3971_);
lean_dec(v___x_3970_);
lean_inc_n(v_matchDeclName_3963_, 3);
v___x_3972_ = l_Lean_mkPrivateName(v_env_3971_, v_matchDeclName_3963_);
lean_dec_ref(v_env_3971_);
v___x_3973_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_3972_);
v___x_3974_ = l_Lean_Name_append(v___x_3972_, v___x_3973_);
lean_inc_n(v___x_3974_, 2);
v___x_3975_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_3975_, 0, v_matchDeclName_3963_);
lean_closure_set(v___x_3975_, 1, v___x_3972_);
lean_closure_set(v___x_3975_, 2, v___x_3974_);
v___x_3976_ = l_Lean_Meta_realizeConst(v_matchDeclName_3963_, v___x_3974_, v___x_3975_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_4005_; 
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4005_ == 0)
{
lean_object* v_unused_4006_; 
v_unused_4006_ = lean_ctor_get(v___x_3976_, 0);
lean_dec(v_unused_4006_);
v___x_3978_ = v___x_3976_;
v_isShared_3979_ = v_isSharedCheck_4005_;
goto v_resetjp_3977_;
}
else
{
lean_dec(v___x_3976_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_4005_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3980_; lean_object* v_env_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; lean_object* v_map_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_4003_; 
v___x_3980_ = lean_st_ref_get(v_a_3967_);
v_env_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc_ref(v_env_3981_);
lean_dec(v___x_3980_);
v___x_3982_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_3983_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_3984_ = 0;
v___x_3985_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3969_, v___x_3982_, v_env_3981_, v___x_3983_, v___x_3974_, v___x_3984_);
v_map_3986_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4003_ == 0)
{
lean_object* v_unused_4004_; 
v_unused_4004_ = lean_ctor_get(v___x_3985_, 1);
lean_dec(v_unused_4004_);
v___x_3988_ = v___x_3985_;
v_isShared_3989_ = v_isSharedCheck_4003_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_map_3986_);
lean_dec(v___x_3985_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_4003_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_3986_, v_matchDeclName_3963_);
lean_dec_ref(v_map_3986_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
lean_del_object(v___x_3978_);
v___x_3991_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_3992_ = l_Lean_MessageData_ofName(v_matchDeclName_3963_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set_tag(v___x_3988_, 7);
lean_ctor_set(v___x_3988_, 1, v___x_3992_);
lean_ctor_set(v___x_3988_, 0, v___x_3991_);
v___x_3994_ = v___x_3988_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3991_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3995_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_3996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3994_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3996_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
lean_dec(v_a_3967_);
lean_dec_ref(v_a_3966_);
lean_dec(v_a_3965_);
lean_dec_ref(v_a_3964_);
return v___x_3997_;
}
}
else
{
lean_object* v_val_3999_; lean_object* v___x_4001_; 
lean_del_object(v___x_3988_);
lean_dec(v_a_3967_);
lean_dec_ref(v_a_3966_);
lean_dec(v_a_3965_);
lean_dec_ref(v_a_3964_);
lean_dec(v_matchDeclName_3963_);
v_val_3999_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_val_3999_);
lean_dec_ref_known(v___x_3990_, 1);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v_val_3999_);
v___x_4001_ = v___x_3978_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_val_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec(v___x_3974_);
lean_dec(v_a_3967_);
lean_dec_ref(v_a_3966_);
lean_dec(v_a_3965_);
lean_dec_ref(v_a_3964_);
lean_dec(v_matchDeclName_3963_);
v_a_4007_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3976_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3976_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = lean_get_match_equations_for(v_matchDeclName_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4022_, lean_object* v_x_4023_, lean_object* v_x_4024_){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4023_, v_x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4026_, lean_object* v_x_4027_, lean_object* v_x_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4026_, v_x_4027_, v_x_4028_);
lean_dec(v_x_4028_);
lean_dec_ref(v_x_4027_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4030_, lean_object* v_x_4031_, size_t v_x_4032_, lean_object* v_x_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4031_, v_x_4032_, v_x_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4035_, lean_object* v_x_4036_, lean_object* v_x_4037_, lean_object* v_x_4038_){
_start:
{
size_t v_x_903__boxed_4039_; lean_object* v_res_4040_; 
v_x_903__boxed_4039_ = lean_unbox_usize(v_x_4037_);
lean_dec(v_x_4037_);
v_res_4040_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4035_, v_x_4036_, v_x_903__boxed_4039_, v_x_4038_);
lean_dec(v_x_4038_);
lean_dec_ref(v_x_4036_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4041_, lean_object* v_keys_4042_, lean_object* v_vals_4043_, lean_object* v_heq_4044_, lean_object* v_i_4045_, lean_object* v_k_4046_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4042_, v_vals_4043_, v_i_4045_, v_k_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4048_, lean_object* v_keys_4049_, lean_object* v_vals_4050_, lean_object* v_heq_4051_, lean_object* v_i_4052_, lean_object* v_k_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4048_, v_keys_4049_, v_vals_4050_, v_heq_4051_, v_i_4052_, v_k_4053_);
lean_dec(v_k_4053_);
lean_dec_ref(v_vals_4050_);
lean_dec_ref(v_keys_4049_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4055_, lean_object* v_k_4056_, uint8_t v_cleanupAnnotations_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___f_4063_; uint8_t v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___f_4063_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4063_, 0, v_k_4056_);
v___x_4064_ = 0;
v___x_4065_ = lean_box(0);
v___x_4066_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4064_, v___x_4065_, v_type_4055_, v___f_4063_, v_cleanupAnnotations_4057_, v___x_4064_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4066_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4066_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
v_a_4075_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4066_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4066_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4083_, lean_object* v_k_4084_, lean_object* v_cleanupAnnotations_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4091_; lean_object* v_res_4092_; 
v_cleanupAnnotations_boxed_4091_ = lean_unbox(v_cleanupAnnotations_4085_);
v_res_4092_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4083_, v_k_4084_, v_cleanupAnnotations_boxed_4091_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4093_, lean_object* v_type_4094_, lean_object* v_k_4095_, uint8_t v_cleanupAnnotations_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4094_, v_k_4095_, v_cleanupAnnotations_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4103_, lean_object* v_type_4104_, lean_object* v_k_4105_, lean_object* v_cleanupAnnotations_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4112_; lean_object* v_res_4113_; 
v_cleanupAnnotations_boxed_4112_ = lean_unbox(v_cleanupAnnotations_4106_);
v_res_4113_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4103_, v_type_4104_, v_k_4105_, v_cleanupAnnotations_boxed_4112_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_msg_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___f_4120_; lean_object* v___x_18841__overap_4121_; lean_object* v___x_4122_; 
v___f_4120_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_18841__overap_4121_ = lean_panic_fn_borrowed(v___f_4120_, v_msg_4114_);
lean_inc(v___y_4118_);
lean_inc_ref(v___y_4117_);
lean_inc(v___y_4116_);
lean_inc_ref(v___y_4115_);
v___x_4122_ = lean_apply_5(v___x_18841__overap_4121_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, lean_box(0));
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_msg_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_msg_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4130_){
_start:
{
uint8_t v_foApprox_4131_; uint8_t v_ctxApprox_4132_; uint8_t v_quasiPatternApprox_4133_; uint8_t v_constApprox_4134_; uint8_t v_isDefEqStuckEx_4135_; uint8_t v_unificationHints_4136_; uint8_t v_proofIrrelevance_4137_; uint8_t v_assignSyntheticOpaque_4138_; uint8_t v_offsetCnstrs_4139_; uint8_t v_transparency_4140_; uint8_t v_univApprox_4141_; uint8_t v_iota_4142_; uint8_t v_beta_4143_; uint8_t v_proj_4144_; uint8_t v_zeta_4145_; uint8_t v_zetaDelta_4146_; uint8_t v_zetaUnused_4147_; uint8_t v_zetaHave_4148_; uint8_t v_canUnfoldPredicateConfig_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4157_; 
v_foApprox_4131_ = lean_ctor_get_uint8(v_c_4130_, 0);
v_ctxApprox_4132_ = lean_ctor_get_uint8(v_c_4130_, 1);
v_quasiPatternApprox_4133_ = lean_ctor_get_uint8(v_c_4130_, 2);
v_constApprox_4134_ = lean_ctor_get_uint8(v_c_4130_, 3);
v_isDefEqStuckEx_4135_ = lean_ctor_get_uint8(v_c_4130_, 4);
v_unificationHints_4136_ = lean_ctor_get_uint8(v_c_4130_, 5);
v_proofIrrelevance_4137_ = lean_ctor_get_uint8(v_c_4130_, 6);
v_assignSyntheticOpaque_4138_ = lean_ctor_get_uint8(v_c_4130_, 7);
v_offsetCnstrs_4139_ = lean_ctor_get_uint8(v_c_4130_, 8);
v_transparency_4140_ = lean_ctor_get_uint8(v_c_4130_, 9);
v_univApprox_4141_ = lean_ctor_get_uint8(v_c_4130_, 11);
v_iota_4142_ = lean_ctor_get_uint8(v_c_4130_, 12);
v_beta_4143_ = lean_ctor_get_uint8(v_c_4130_, 13);
v_proj_4144_ = lean_ctor_get_uint8(v_c_4130_, 14);
v_zeta_4145_ = lean_ctor_get_uint8(v_c_4130_, 15);
v_zetaDelta_4146_ = lean_ctor_get_uint8(v_c_4130_, 16);
v_zetaUnused_4147_ = lean_ctor_get_uint8(v_c_4130_, 17);
v_zetaHave_4148_ = lean_ctor_get_uint8(v_c_4130_, 18);
v_canUnfoldPredicateConfig_4149_ = lean_ctor_get_uint8(v_c_4130_, 19);
v_isSharedCheck_4157_ = !lean_is_exclusive(v_c_4130_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4151_ = v_c_4130_;
v_isShared_4152_ = v_isSharedCheck_4157_;
goto v_resetjp_4150_;
}
else
{
lean_dec(v_c_4130_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4157_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
uint8_t v___x_4153_; lean_object* v___x_4155_; 
v___x_4153_ = 2;
if (v_isShared_4152_ == 0)
{
v___x_4155_ = v___x_4151_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 0, v_foApprox_4131_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 1, v_ctxApprox_4132_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 2, v_quasiPatternApprox_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 3, v_constApprox_4134_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 4, v_isDefEqStuckEx_4135_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 5, v_unificationHints_4136_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 6, v_proofIrrelevance_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 7, v_assignSyntheticOpaque_4138_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 8, v_offsetCnstrs_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 9, v_transparency_4140_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 11, v_univApprox_4141_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 12, v_iota_4142_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 13, v_beta_4143_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 14, v_proj_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 15, v_zeta_4145_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 16, v_zetaDelta_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 17, v_zetaUnused_4147_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 18, v_zetaHave_4148_);
lean_ctor_set_uint8(v_reuseFailAlloc_4156_, 19, v_canUnfoldPredicateConfig_4149_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
lean_ctor_set_uint8(v___x_4155_, 10, v___x_4153_);
return v___x_4155_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4158_, lean_object* v_t_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_dummy_4165_; lean_object* v_nargs_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v_dummy_4165_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4166_ = l_Lean_Expr_getAppNumArgs(v_t_4159_);
lean_inc(v_nargs_4166_);
v___x_4167_ = lean_mk_array(v_nargs_4166_, v_dummy_4165_);
v___x_4168_ = lean_unsigned_to_nat(1u);
v___x_4169_ = lean_nat_sub(v_nargs_4166_, v___x_4168_);
lean_dec(v_nargs_4166_);
v___x_4170_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4159_, v___x_4167_, v___x_4169_);
v___x_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4172_, lean_object* v_t_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4172_, v_t_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec_ref(v_x_4172_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4180_, lean_object* v_x_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v_snd_4180_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4188_, lean_object* v_x_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4188_, v_x_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec_ref(v_x_4189_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4196_, size_t v_i_4197_, lean_object* v_bs_4198_){
_start:
{
uint8_t v___x_4199_; 
v___x_4199_ = lean_usize_dec_lt(v_i_4197_, v_sz_4196_);
if (v___x_4199_ == 0)
{
return v_bs_4198_;
}
else
{
lean_object* v_v_4200_; lean_object* v_fst_4201_; lean_object* v_snd_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4216_; 
v_v_4200_ = lean_array_uget(v_bs_4198_, v_i_4197_);
v_fst_4201_ = lean_ctor_get(v_v_4200_, 0);
v_snd_4202_ = lean_ctor_get(v_v_4200_, 1);
v_isSharedCheck_4216_ = !lean_is_exclusive(v_v_4200_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4204_ = v_v_4200_;
v_isShared_4205_ = v_isSharedCheck_4216_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_snd_4202_);
lean_inc(v_fst_4201_);
lean_dec(v_v_4200_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4216_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4206_; lean_object* v_bs_x27_4207_; lean_object* v___f_4208_; lean_object* v___x_4210_; 
v___x_4206_ = lean_unsigned_to_nat(0u);
v_bs_x27_4207_ = lean_array_uset(v_bs_4198_, v_i_4197_, v___x_4206_);
v___f_4208_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4208_, 0, v_snd_4202_);
if (v_isShared_4205_ == 0)
{
lean_ctor_set(v___x_4204_, 1, v___f_4208_);
v___x_4210_ = v___x_4204_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_fst_4201_);
lean_ctor_set(v_reuseFailAlloc_4215_, 1, v___f_4208_);
v___x_4210_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
size_t v___x_4211_; size_t v___x_4212_; lean_object* v___x_4213_; 
v___x_4211_ = ((size_t)1ULL);
v___x_4212_ = lean_usize_add(v_i_4197_, v___x_4211_);
v___x_4213_ = lean_array_uset(v_bs_x27_4207_, v_i_4197_, v___x_4210_);
v_i_4197_ = v___x_4212_;
v_bs_4198_ = v___x_4213_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4217_, lean_object* v_i_4218_, lean_object* v_bs_4219_){
_start:
{
size_t v_sz_boxed_4220_; size_t v_i_boxed_4221_; lean_object* v_res_4222_; 
v_sz_boxed_4220_ = lean_unbox_usize(v_sz_4217_);
lean_dec(v_sz_4217_);
v_i_boxed_4221_ = lean_unbox_usize(v_i_4218_);
lean_dec(v_i_4218_);
v_res_4222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4220_, v_i_boxed_4221_, v_bs_4219_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4223_, size_t v_i_4224_, lean_object* v_bs_4225_){
_start:
{
uint8_t v___x_4226_; 
v___x_4226_ = lean_usize_dec_lt(v_i_4224_, v_sz_4223_);
if (v___x_4226_ == 0)
{
return v_bs_4225_;
}
else
{
lean_object* v_v_4227_; lean_object* v_fst_4228_; lean_object* v_snd_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4245_; 
v_v_4227_ = lean_array_uget(v_bs_4225_, v_i_4224_);
v_fst_4228_ = lean_ctor_get(v_v_4227_, 0);
v_snd_4229_ = lean_ctor_get(v_v_4227_, 1);
v_isSharedCheck_4245_ = !lean_is_exclusive(v_v_4227_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4231_ = v_v_4227_;
v_isShared_4232_ = v_isSharedCheck_4245_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_snd_4229_);
lean_inc(v_fst_4228_);
lean_dec(v_v_4227_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4245_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4233_; lean_object* v_bs_x27_4234_; uint8_t v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4238_; 
v___x_4233_ = lean_unsigned_to_nat(0u);
v_bs_x27_4234_ = lean_array_uset(v_bs_4225_, v_i_4224_, v___x_4233_);
v___x_4235_ = 0;
v___x_4236_ = lean_box(v___x_4235_);
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v___x_4236_);
v___x_4238_ = v___x_4231_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4236_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v_snd_4229_);
v___x_4238_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
lean_object* v___x_4239_; size_t v___x_4240_; size_t v___x_4241_; lean_object* v___x_4242_; 
v___x_4239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4239_, 0, v_fst_4228_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = ((size_t)1ULL);
v___x_4241_ = lean_usize_add(v_i_4224_, v___x_4240_);
v___x_4242_ = lean_array_uset(v_bs_x27_4234_, v_i_4224_, v___x_4239_);
v_i_4224_ = v___x_4241_;
v_bs_4225_ = v___x_4242_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4246_, lean_object* v_i_4247_, lean_object* v_bs_4248_){
_start:
{
size_t v_sz_boxed_4249_; size_t v_i_boxed_4250_; lean_object* v_res_4251_; 
v_sz_boxed_4249_ = lean_unbox_usize(v_sz_4246_);
lean_dec(v_sz_4246_);
v_i_boxed_4250_ = lean_unbox_usize(v_i_4247_);
lean_dec(v_i_4247_);
v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4249_, v_i_boxed_4250_, v_bs_4248_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4252_, lean_object* v___x_4253_, lean_object* v_a_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_20547__overap_4260_; lean_object* v___x_4261_; 
v___x_20547__overap_4260_ = l_instInhabitedOfMonad___redArg(v___x_4252_, v___x_4253_);
lean_inc(v___y_4258_);
lean_inc_ref(v___y_4257_);
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
v___x_4261_ = lean_apply_5(v___x_20547__overap_4260_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, lean_box(0));
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v_a_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4262_, v___x_4263_, v_a_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec_ref(v_a_4264_);
return v_res_4270_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_instMonadEIO___redArg();
return v___x_4271_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4273_ = l_StateRefT_x27_instMonad___redArg(v___x_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4278_, lean_object* v_declInfos_4279_, lean_object* v_k_4280_, lean_object* v_kind_4281_, lean_object* v_x_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
uint8_t v_kind_boxed_4288_; lean_object* v_res_4289_; 
v_kind_boxed_4288_ = lean_unbox(v_kind_4281_);
v_res_4289_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4278_, v_declInfos_4279_, v_k_4280_, v_kind_boxed_4288_, v_x_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4290_, lean_object* v_k_4291_, uint8_t v_kind_4292_, lean_object* v_acc_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; lean_object* v_toApplicative_4300_; lean_object* v_toFunctor_4301_; lean_object* v_toSeq_4302_; lean_object* v_toSeqLeft_4303_; lean_object* v_toSeqRight_4304_; lean_object* v___f_4305_; lean_object* v___f_4306_; lean_object* v___f_4307_; lean_object* v___f_4308_; lean_object* v___x_4309_; lean_object* v___f_4310_; lean_object* v___f_4311_; lean_object* v___f_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v_toApplicative_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4366_; 
v___x_4299_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4300_ = lean_ctor_get(v___x_4299_, 0);
v_toFunctor_4301_ = lean_ctor_get(v_toApplicative_4300_, 0);
v_toSeq_4302_ = lean_ctor_get(v_toApplicative_4300_, 2);
v_toSeqLeft_4303_ = lean_ctor_get(v_toApplicative_4300_, 3);
v_toSeqRight_4304_ = lean_ctor_get(v_toApplicative_4300_, 4);
v___f_4305_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4306_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4301_, 2);
v___f_4307_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4307_, 0, v_toFunctor_4301_);
v___f_4308_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4308_, 0, v_toFunctor_4301_);
v___x_4309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___f_4307_);
lean_ctor_set(v___x_4309_, 1, v___f_4308_);
lean_inc(v_toSeqRight_4304_);
v___f_4310_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4310_, 0, v_toSeqRight_4304_);
lean_inc(v_toSeqLeft_4303_);
v___f_4311_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4311_, 0, v_toSeqLeft_4303_);
lean_inc(v_toSeq_4302_);
v___f_4312_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4312_, 0, v_toSeq_4302_);
v___x_4313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4309_);
lean_ctor_set(v___x_4313_, 1, v___f_4305_);
lean_ctor_set(v___x_4313_, 2, v___f_4312_);
lean_ctor_set(v___x_4313_, 3, v___f_4311_);
lean_ctor_set(v___x_4313_, 4, v___f_4310_);
v___x_4314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
lean_ctor_set(v___x_4314_, 1, v___f_4306_);
v___x_4315_ = l_StateRefT_x27_instMonad___redArg(v___x_4314_);
v_toApplicative_4316_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4366_ == 0)
{
lean_object* v_unused_4367_; 
v_unused_4367_ = lean_ctor_get(v___x_4315_, 1);
lean_dec(v_unused_4367_);
v___x_4318_ = v___x_4315_;
v_isShared_4319_ = v_isSharedCheck_4366_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_toApplicative_4316_);
lean_dec(v___x_4315_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4366_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v_toFunctor_4320_; lean_object* v_toSeq_4321_; lean_object* v_toSeqLeft_4322_; lean_object* v_toSeqRight_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4364_; 
v_toFunctor_4320_ = lean_ctor_get(v_toApplicative_4316_, 0);
v_toSeq_4321_ = lean_ctor_get(v_toApplicative_4316_, 2);
v_toSeqLeft_4322_ = lean_ctor_get(v_toApplicative_4316_, 3);
v_toSeqRight_4323_ = lean_ctor_get(v_toApplicative_4316_, 4);
v_isSharedCheck_4364_ = !lean_is_exclusive(v_toApplicative_4316_);
if (v_isSharedCheck_4364_ == 0)
{
lean_object* v_unused_4365_; 
v_unused_4365_ = lean_ctor_get(v_toApplicative_4316_, 1);
lean_dec(v_unused_4365_);
v___x_4325_ = v_toApplicative_4316_;
v_isShared_4326_ = v_isSharedCheck_4364_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_toSeqRight_4323_);
lean_inc(v_toSeqLeft_4322_);
lean_inc(v_toSeq_4321_);
lean_inc(v_toFunctor_4320_);
lean_dec(v_toApplicative_4316_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4364_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___f_4327_; lean_object* v___f_4328_; lean_object* v___f_4329_; lean_object* v___f_4330_; lean_object* v___x_4331_; lean_object* v___f_4332_; lean_object* v___f_4333_; lean_object* v___f_4334_; lean_object* v___x_4336_; 
v___f_4327_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4328_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4320_);
v___f_4329_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4329_, 0, v_toFunctor_4320_);
v___f_4330_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4330_, 0, v_toFunctor_4320_);
v___x_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___f_4329_);
lean_ctor_set(v___x_4331_, 1, v___f_4330_);
v___f_4332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4332_, 0, v_toSeqRight_4323_);
v___f_4333_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4333_, 0, v_toSeqLeft_4322_);
v___f_4334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4334_, 0, v_toSeq_4321_);
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 4, v___f_4332_);
lean_ctor_set(v___x_4325_, 3, v___f_4333_);
lean_ctor_set(v___x_4325_, 2, v___f_4334_);
lean_ctor_set(v___x_4325_, 1, v___f_4327_);
lean_ctor_set(v___x_4325_, 0, v___x_4331_);
v___x_4336_ = v___x_4325_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4331_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v___f_4327_);
lean_ctor_set(v_reuseFailAlloc_4363_, 2, v___f_4334_);
lean_ctor_set(v_reuseFailAlloc_4363_, 3, v___f_4333_);
lean_ctor_set(v_reuseFailAlloc_4363_, 4, v___f_4332_);
v___x_4336_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
lean_object* v___x_4338_; 
if (v_isShared_4319_ == 0)
{
lean_ctor_set(v___x_4318_, 1, v___f_4328_);
lean_ctor_set(v___x_4318_, 0, v___x_4336_);
v___x_4338_ = v___x_4318_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4336_);
lean_ctor_set(v_reuseFailAlloc_4362_, 1, v___f_4328_);
v___x_4338_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4339_ = lean_array_get_size(v_acc_4293_);
v___x_4340_ = lean_array_get_size(v_declInfos_4290_);
v___x_4341_ = lean_nat_dec_lt(v___x_4339_, v___x_4340_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4342_; 
lean_dec_ref(v___x_4338_);
lean_dec_ref(v_declInfos_4290_);
lean_inc(v___y_4297_);
lean_inc_ref(v___y_4296_);
lean_inc(v___y_4295_);
lean_inc_ref(v___y_4294_);
v___x_4342_ = lean_apply_6(v_k_4291_, v_acc_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, lean_box(0));
return v___x_4342_;
}
else
{
lean_object* v___x_4343_; uint8_t v___x_4344_; lean_object* v___x_4345_; lean_object* v___f_4346_; lean_object* v___f_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v_snd_4352_; lean_object* v_fst_4353_; lean_object* v_fst_4354_; lean_object* v_snd_4355_; lean_object* v___x_4356_; lean_object* v___f_4357_; lean_object* v___x_4358_; 
v___x_4343_ = lean_box(0);
v___x_4344_ = 0;
v___x_4345_ = l_Lean_instInhabitedExpr;
v___f_4346_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4346_, 0, v___x_4338_);
lean_closure_set(v___f_4346_, 1, v___x_4345_);
v___f_4347_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4347_, 0, v___f_4346_);
v___x_4348_ = lean_box(v___x_4344_);
v___x_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4348_);
lean_ctor_set(v___x_4349_, 1, v___f_4347_);
v___x_4350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4343_);
lean_ctor_set(v___x_4350_, 1, v___x_4349_);
v___x_4351_ = lean_array_get(v___x_4350_, v_declInfos_4290_, v___x_4339_);
lean_dec_ref_known(v___x_4350_, 2);
v_snd_4352_ = lean_ctor_get(v___x_4351_, 1);
lean_inc(v_snd_4352_);
v_fst_4353_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_fst_4353_);
lean_dec(v___x_4351_);
v_fst_4354_ = lean_ctor_get(v_snd_4352_, 0);
lean_inc(v_fst_4354_);
v_snd_4355_ = lean_ctor_get(v_snd_4352_, 1);
lean_inc(v_snd_4355_);
lean_dec(v_snd_4352_);
v___x_4356_ = lean_box(v_kind_4292_);
lean_inc_ref(v_acc_4293_);
v___f_4357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4357_, 0, v_acc_4293_);
lean_closure_set(v___f_4357_, 1, v_declInfos_4290_);
lean_closure_set(v___f_4357_, 2, v_k_4291_);
lean_closure_set(v___f_4357_, 3, v___x_4356_);
lean_inc(v___y_4297_);
lean_inc_ref(v___y_4296_);
lean_inc(v___y_4295_);
lean_inc_ref(v___y_4294_);
v___x_4358_ = lean_apply_6(v_snd_4355_, v_acc_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, lean_box(0));
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; uint8_t v___x_4360_; lean_object* v___x_4361_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
v___x_4360_ = lean_unbox(v_fst_4354_);
lean_dec(v_fst_4354_);
v___x_4361_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4353_, v___x_4360_, v_a_4359_, v___f_4357_, v_kind_4292_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
return v___x_4361_;
}
else
{
lean_dec_ref(v___f_4357_);
lean_dec(v_fst_4354_);
lean_dec(v_fst_4353_);
return v___x_4358_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4368_, lean_object* v_declInfos_4369_, lean_object* v_k_4370_, uint8_t v_kind_4371_, lean_object* v_x_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4378_ = lean_array_push(v_acc_4368_, v_x_4372_);
v___x_4379_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4369_, v_k_4370_, v_kind_4371_, v___x_4378_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4380_, lean_object* v_k_4381_, lean_object* v_kind_4382_, lean_object* v_acc_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
uint8_t v_kind_boxed_4389_; lean_object* v_res_4390_; 
v_kind_boxed_4389_ = lean_unbox(v_kind_4382_);
v_res_4390_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4380_, v_k_4381_, v_kind_boxed_4389_, v_acc_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4391_, lean_object* v_k_4392_, uint8_t v_kind_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4399_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4400_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4391_, v_k_4392_, v_kind_4393_, v___x_4399_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4401_, lean_object* v_k_4402_, lean_object* v_kind_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
uint8_t v_kind_boxed_4409_; lean_object* v_res_4410_; 
v_kind_boxed_4409_ = lean_unbox(v_kind_4403_);
v_res_4410_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4401_, v_k_4402_, v_kind_boxed_4409_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4411_, lean_object* v_k_4412_, uint8_t v_kind_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
size_t v_sz_4419_; size_t v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v_sz_4419_ = lean_array_size(v_declInfos_4411_);
v___x_4420_ = ((size_t)0ULL);
v___x_4421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4419_, v___x_4420_, v_declInfos_4411_);
v___x_4422_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4421_, v_k_4412_, v_kind_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4423_, lean_object* v_k_4424_, lean_object* v_kind_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
uint8_t v_kind_boxed_4431_; lean_object* v_res_4432_; 
v_kind_boxed_4431_ = lean_unbox(v_kind_4425_);
v_res_4432_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4423_, v_k_4424_, v_kind_boxed_4431_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4433_, lean_object* v_k_4434_, uint8_t v_kind_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
size_t v_sz_4441_; size_t v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v_sz_4441_ = lean_array_size(v_declInfos_4433_);
v___x_4442_ = ((size_t)0ULL);
v___x_4443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4441_, v___x_4442_, v_declInfos_4433_);
v___x_4444_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4443_, v_k_4434_, v_kind_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4445_, lean_object* v_k_4446_, lean_object* v_kind_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
uint8_t v_kind_boxed_4453_; lean_object* v_res_4454_; 
v_kind_boxed_4453_ = lean_unbox(v_kind_4447_);
v_res_4454_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4445_, v_k_4446_, v_kind_boxed_4453_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(lean_object* v_a_4458_, lean_object* v_b_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_array_4465_; lean_object* v_start_4466_; lean_object* v_stop_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4525_; 
v_array_4465_ = lean_ctor_get(v_a_4458_, 0);
v_start_4466_ = lean_ctor_get(v_a_4458_, 1);
v_stop_4467_ = lean_ctor_get(v_a_4458_, 2);
v_isSharedCheck_4525_ = !lean_is_exclusive(v_a_4458_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4469_ = v_a_4458_;
v_isShared_4470_ = v_isSharedCheck_4525_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_stop_4467_);
lean_inc(v_start_4466_);
lean_inc(v_array_4465_);
lean_dec(v_a_4458_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4525_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
uint8_t v___x_4471_; 
v___x_4471_ = lean_nat_dec_lt(v_start_4466_, v_stop_4467_);
if (v___x_4471_ == 0)
{
lean_object* v___x_4472_; 
lean_del_object(v___x_4469_);
lean_dec(v_stop_4467_);
lean_dec(v_start_4466_);
lean_dec_ref(v_array_4465_);
v___x_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4472_, 0, v_b_4459_);
return v___x_4472_;
}
else
{
lean_object* v_snd_4473_; lean_object* v_fst_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4524_; 
v_snd_4473_ = lean_ctor_get(v_b_4459_, 1);
v_fst_4474_ = lean_ctor_get(v_b_4459_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v_b_4459_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4476_ = v_b_4459_;
v_isShared_4477_ = v_isSharedCheck_4524_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_snd_4473_);
lean_inc(v_fst_4474_);
lean_dec(v_b_4459_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4524_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v_array_4478_; lean_object* v_start_4479_; lean_object* v_stop_4480_; uint8_t v___x_4481_; 
v_array_4478_ = lean_ctor_get(v_snd_4473_, 0);
v_start_4479_ = lean_ctor_get(v_snd_4473_, 1);
v_stop_4480_ = lean_ctor_get(v_snd_4473_, 2);
v___x_4481_ = lean_nat_dec_lt(v_start_4479_, v_stop_4480_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4483_; 
lean_del_object(v___x_4469_);
lean_dec(v_stop_4467_);
lean_dec(v_start_4466_);
lean_dec_ref(v_array_4465_);
if (v_isShared_4477_ == 0)
{
v___x_4483_ = v___x_4476_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_fst_4474_);
lean_ctor_set(v_reuseFailAlloc_4485_, 1, v_snd_4473_);
v___x_4483_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; 
v___x_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
return v___x_4484_;
}
}
else
{
lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4520_; 
lean_inc(v_stop_4480_);
lean_inc(v_start_4479_);
lean_inc_ref(v_array_4478_);
v_isSharedCheck_4520_ = !lean_is_exclusive(v_snd_4473_);
if (v_isSharedCheck_4520_ == 0)
{
lean_object* v_unused_4521_; lean_object* v_unused_4522_; lean_object* v_unused_4523_; 
v_unused_4521_ = lean_ctor_get(v_snd_4473_, 2);
lean_dec(v_unused_4521_);
v_unused_4522_ = lean_ctor_get(v_snd_4473_, 1);
lean_dec(v_unused_4522_);
v_unused_4523_ = lean_ctor_get(v_snd_4473_, 0);
lean_dec(v_unused_4523_);
v___x_4487_ = v_snd_4473_;
v_isShared_4488_ = v_isSharedCheck_4520_;
goto v_resetjp_4486_;
}
else
{
lean_dec(v_snd_4473_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4520_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4492_; 
v___x_4489_ = lean_unsigned_to_nat(1u);
v___x_4490_ = lean_nat_add(v_start_4466_, v___x_4489_);
lean_inc_ref(v_array_4465_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 2, v_stop_4467_);
lean_ctor_set(v___x_4487_, 1, v___x_4490_);
lean_ctor_set(v___x_4487_, 0, v_array_4465_);
v___x_4492_ = v___x_4487_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_array_4465_);
lean_ctor_set(v_reuseFailAlloc_4519_, 1, v___x_4490_);
lean_ctor_set(v_reuseFailAlloc_4519_, 2, v_stop_4467_);
v___x_4492_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4497_; 
v___x_4493_ = lean_array_fget(v_array_4465_, v_start_4466_);
lean_dec(v_start_4466_);
lean_dec_ref(v_array_4465_);
v___x_4494_ = lean_array_fget(v_array_4478_, v_start_4479_);
v___x_4495_ = lean_nat_add(v_start_4479_, v___x_4489_);
lean_dec(v_start_4479_);
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 2, v_stop_4480_);
lean_ctor_set(v___x_4469_, 1, v___x_4495_);
lean_ctor_set(v___x_4469_, 0, v_array_4478_);
v___x_4497_ = v___x_4469_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_array_4478_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v___x_4495_);
lean_ctor_set(v_reuseFailAlloc_4518_, 2, v_stop_4480_);
v___x_4497_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
lean_object* v___x_4498_; 
v___x_4498_ = l_Lean_Meta_mkEqHEq(v___x_4493_, v___x_4494_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4505_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref_known(v___x_4498_, 1);
v___x_4500_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__1));
v___x_4501_ = lean_array_get_size(v_fst_4474_);
v___x_4502_ = lean_nat_add(v___x_4501_, v___x_4489_);
v___x_4503_ = lean_name_append_index_after(v___x_4500_, v___x_4502_);
if (v_isShared_4477_ == 0)
{
lean_ctor_set(v___x_4476_, 1, v_a_4499_);
lean_ctor_set(v___x_4476_, 0, v___x_4503_);
v___x_4505_ = v___x_4476_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4503_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v_a_4499_);
v___x_4505_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = lean_array_push(v_fst_4474_, v___x_4505_);
v___x_4507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
lean_ctor_set(v___x_4507_, 1, v___x_4497_);
v_a_4458_ = v___x_4492_;
v_b_4459_ = v___x_4507_;
goto _start;
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_dec_ref(v___x_4497_);
lean_dec_ref(v___x_4492_);
lean_del_object(v___x_4476_);
lean_dec(v_fst_4474_);
v_a_4510_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4498_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4498_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___boxed(lean_object* v_a_4526_, lean_object* v_b_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_4526_, v_b_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v___x_4534_, lean_object* v_a_4535_, lean_object* v___x_4536_, lean_object* v_as_4537_, size_t v_sz_4538_, size_t v_i_4539_, lean_object* v_b_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v_a_4547_; uint8_t v___x_4551_; 
v___x_4551_ = lean_usize_dec_lt(v_i_4539_, v_sz_4538_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; 
lean_dec(v___x_4536_);
v___x_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4552_, 0, v_b_4540_);
return v___x_4552_;
}
else
{
lean_object* v___x_4553_; lean_object* v_a_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4553_ = l_Lean_instInhabitedExpr;
v_a_4554_ = lean_array_uget_borrowed(v_as_4537_, v_i_4539_);
v___x_4555_ = lean_array_get_borrowed(v___x_4553_, v___x_4534_, v_a_4554_);
lean_inc(v___x_4555_);
v___x_4556_ = l_Lean_Meta_instantiateForall(v___x_4555_, v_a_4535_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; lean_object* v___x_4558_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_a_4557_);
lean_dec_ref_known(v___x_4556_, 1);
lean_inc(v___x_4536_);
v___x_4558_ = l_Lean_Meta_Match_simpH_x3f(v_a_4557_, v___x_4536_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_a_4559_);
lean_dec_ref_known(v___x_4558_, 1);
if (lean_obj_tag(v_a_4559_) == 1)
{
lean_object* v_val_4560_; lean_object* v___x_4561_; 
v_val_4560_ = lean_ctor_get(v_a_4559_, 0);
lean_inc(v_val_4560_);
lean_dec_ref_known(v_a_4559_, 1);
v___x_4561_ = lean_array_push(v_b_4540_, v_val_4560_);
v_a_4547_ = v___x_4561_;
goto v___jp_4546_;
}
else
{
lean_dec(v_a_4559_);
v_a_4547_ = v_b_4540_;
goto v___jp_4546_;
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec_ref(v_b_4540_);
lean_dec(v___x_4536_);
v_a_4562_ = lean_ctor_get(v___x_4558_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4558_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4558_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
lean_dec_ref(v_b_4540_);
lean_dec(v___x_4536_);
v_a_4570_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4556_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4556_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
v___jp_4546_:
{
size_t v___x_4548_; size_t v___x_4549_; 
v___x_4548_ = ((size_t)1ULL);
v___x_4549_ = lean_usize_add(v_i_4539_, v___x_4548_);
v_i_4539_ = v___x_4549_;
v_b_4540_ = v_a_4547_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v___x_4578_, lean_object* v_a_4579_, lean_object* v___x_4580_, lean_object* v_as_4581_, lean_object* v_sz_4582_, lean_object* v_i_4583_, lean_object* v_b_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
size_t v_sz_boxed_4590_; size_t v_i_boxed_4591_; lean_object* v_res_4592_; 
v_sz_boxed_4590_ = lean_unbox_usize(v_sz_4582_);
lean_dec(v_sz_4582_);
v_i_boxed_4591_ = lean_unbox_usize(v_i_4583_);
lean_dec(v_i_4583_);
v_res_4592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4578_, v_a_4579_, v___x_4580_, v_as_4581_, v_sz_boxed_4590_, v_i_boxed_4591_, v_b_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec_ref(v_as_4581_);
lean_dec_ref(v_a_4579_);
lean_dec_ref(v___x_4578_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4593_, lean_object* v_args_4594_, lean_object* v___x_4595_, lean_object* v_overlaps_4596_, lean_object* v_a_4597_, lean_object* v_fst_4598_, lean_object* v_a_4599_, lean_object* v___x_4600_, lean_object* v___x_4601_, lean_object* v___x_4602_, lean_object* v___x_4603_, lean_object* v_altVars_4604_, uint8_t v___x_4605_, uint8_t v___x_4606_, lean_object* v_a_4607_, lean_object* v___x_4608_, lean_object* v___x_4609_, lean_object* v___x_4610_, lean_object* v___x_4611_, lean_object* v___x_4612_, lean_object* v___x_4613_, lean_object* v___x_4614_, lean_object* v_matchDeclName_4615_, lean_object* v___x_4616_, lean_object* v___x_4617_, lean_object* v___x_4618_, lean_object* v_heqs_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4625_ = l_Lean_mkAppN(v___y_4593_, v_args_4594_);
lean_inc_ref(v_heqs_4619_);
v___x_4626_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4625_, v_heqs_4619_, v___x_4595_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4628_; size_t v_sz_4629_; size_t v___x_4630_; lean_object* v___x_4631_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
lean_inc(v_a_4627_);
lean_dec_ref_known(v___x_4626_, 1);
v___x_4628_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4596_, v_a_4597_);
v_sz_4629_ = lean_array_size(v___x_4628_);
v___x_4630_ = ((size_t)0ULL);
lean_inc_ref(v___x_4601_);
v___x_4631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_fst_4598_, v_a_4599_, v___x_4600_, v___x_4628_, v_sz_4629_, v___x_4630_, v___x_4601_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
lean_dec_ref(v___x_4628_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; lean_object* v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; lean_object* v_toCold_4744_; lean_object* v_options_4745_; uint8_t v_hasTrace_4746_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
lean_dec_ref_known(v___x_4631_, 1);
v_toCold_4744_ = lean_ctor_get(v___y_4622_, 0);
v_options_4745_ = lean_ctor_get(v_toCold_4744_, 2);
v_hasTrace_4746_ = lean_ctor_get_uint8(v_options_4745_, sizeof(void*)*1);
if (v_hasTrace_4746_ == 0)
{
v___y_4634_ = v___y_4620_;
v___y_4635_ = v___y_4621_;
v___y_4636_ = v___y_4622_;
v___y_4637_ = v___y_4623_;
goto v___jp_4633_;
}
else
{
lean_object* v_inheritedTraceOptions_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; uint8_t v___x_4750_; 
v_inheritedTraceOptions_4747_ = lean_ctor_get(v_toCold_4744_, 11);
v___x_4748_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4749_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4747_, v_options_4745_, v___x_4749_);
if (v___x_4750_ == 0)
{
v___y_4634_ = v___y_4620_;
v___y_4635_ = v___y_4621_;
v___y_4636_ = v___y_4622_;
v___y_4637_ = v___y_4623_;
goto v___jp_4633_;
}
else
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4751_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4632_);
v___x_4752_ = lean_array_to_list(v_a_4632_);
v___x_4753_ = lean_box(0);
v___x_4754_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4752_, v___x_4753_);
v___x_4755_ = l_Lean_MessageData_ofList(v___x_4754_);
v___x_4756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4751_);
lean_ctor_set(v___x_4756_, 1, v___x_4755_);
v___x_4757_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4748_, v___x_4756_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_dec_ref_known(v___x_4757_, 1);
v___y_4634_ = v___y_4620_;
v___y_4635_ = v___y_4621_;
v___y_4636_ = v___y_4622_;
v___y_4637_ = v___y_4623_;
goto v___jp_4633_;
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
lean_dec(v_a_4632_);
lean_dec(v_a_4627_);
lean_dec_ref(v_heqs_4619_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
lean_dec(v_matchDeclName_4615_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4611_);
lean_dec_ref(v___x_4609_);
lean_dec(v___x_4608_);
lean_dec_ref(v___x_4603_);
lean_dec(v___x_4602_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v_a_4599_);
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4757_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4757_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4763_; 
if (v_isShared_4761_ == 0)
{
v___x_4763_ = v___x_4760_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
}
v___jp_4633_:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; size_t v_sz_4645_; lean_object* v___x_4646_; 
v___x_4638_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4639_ = l_Array_reverse___redArg(v_a_4599_);
v___x_4640_ = lean_array_get_size(v___x_4639_);
v___x_4641_ = l_Array_toSubarray___redArg(v___x_4639_, v___x_4602_, v___x_4640_);
lean_inc_ref(v___x_4603_);
v___x_4642_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4603_, v___x_4601_);
v___x_4643_ = l_Array_reverse___redArg(v___x_4642_);
v___x_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4638_);
lean_ctor_set(v___x_4644_, 1, v___x_4641_);
v_sz_4645_ = lean_array_size(v___x_4643_);
v___x_4646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4643_, v_sz_4645_, v___x_4630_, v___x_4644_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
lean_dec_ref(v___x_4643_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v_fst_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4734_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
lean_dec_ref_known(v___x_4646_, 1);
v_fst_4648_ = lean_ctor_get(v_a_4647_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v_a_4647_);
if (v_isSharedCheck_4734_ == 0)
{
lean_object* v_unused_4735_; 
v_unused_4735_ = lean_ctor_get(v_a_4647_, 1);
lean_dec(v_unused_4735_);
v___x_4650_ = v_a_4647_;
v_isShared_4651_ = v_isSharedCheck_4734_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_fst_4648_);
lean_dec(v_a_4647_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4734_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; uint8_t v___x_4654_; lean_object* v___x_4655_; 
v___x_4652_ = l_Subarray_copy___redArg(v___x_4603_);
lean_inc_ref(v___x_4652_);
v___x_4653_ = l_Array_append___redArg(v___x_4652_, v_altVars_4604_);
v___x_4654_ = 1;
v___x_4655_ = l_Lean_Meta_mkForallFVars(v___x_4653_, v_fst_4648_, v___x_4605_, v___x_4606_, v___x_4606_, v___x_4654_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
lean_dec_ref(v___x_4653_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_a_4656_);
lean_dec_ref_known(v___x_4655_, 1);
v___x_4657_ = l_Lean_ConstantInfo_name(v_a_4607_);
v___x_4658_ = l_Lean_mkConst(v___x_4657_, v___x_4608_);
lean_inc_ref(v___x_4609_);
v___x_4659_ = l_Subarray_copy___redArg(v___x_4609_);
v___x_4660_ = lean_mk_empty_array_with_capacity(v___x_4610_);
v___x_4661_ = lean_array_push(v___x_4660_, v___x_4611_);
v___x_4662_ = l_Array_append___redArg(v___x_4659_, v___x_4661_);
lean_dec_ref(v___x_4661_);
v___x_4663_ = l_Array_append___redArg(v___x_4662_, v___x_4652_);
lean_dec_ref(v___x_4652_);
v___x_4664_ = l_Subarray_copy___redArg(v___x_4612_);
v___x_4665_ = l_Array_append___redArg(v___x_4663_, v___x_4664_);
lean_dec_ref(v___x_4664_);
v___x_4666_ = l_Lean_mkAppN(v___x_4658_, v___x_4665_);
v___x_4667_ = l_Lean_Meta_mkHEq(v___x_4666_, v_a_4627_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4669_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref_known(v___x_4667_, 1);
v___x_4669_ = l_Lean_mkArrowN(v_a_4632_, v_a_4668_, v___y_4636_, v___y_4637_);
lean_dec(v_a_4632_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref_known(v___x_4669_, 1);
v___x_4671_ = l_Array_append___redArg(v___x_4665_, v_altVars_4604_);
v___x_4672_ = l_Array_append___redArg(v___x_4671_, v_heqs_4619_);
v___x_4673_ = l_Lean_Meta_mkForallFVars(v___x_4672_, v_a_4670_, v___x_4605_, v___x_4606_, v___x_4606_, v___x_4654_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
lean_dec_ref(v___x_4672_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v___x_4675_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_a_4674_);
lean_dec_ref_known(v___x_4673_, 1);
v___x_4675_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4674_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4733_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4678_ = v___x_4675_;
v_isShared_4679_ = v_isSharedCheck_4733_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4733_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v_start_4680_; lean_object* v_stop_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4731_; 
v_start_4680_ = lean_ctor_get(v___x_4609_, 1);
v_stop_4681_ = lean_ctor_get(v___x_4609_, 2);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; 
v_unused_4732_ = lean_ctor_get(v___x_4609_, 0);
lean_dec(v_unused_4732_);
v___x_4683_ = v___x_4609_;
v_isShared_4684_ = v_isSharedCheck_4731_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_stop_4681_);
lean_inc(v_start_4680_);
lean_dec(v___x_4609_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4731_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4685_ = lean_nat_sub(v_stop_4681_, v_start_4680_);
lean_dec(v_start_4680_);
lean_dec(v_stop_4681_);
v___x_4686_ = lean_nat_add(v___x_4685_, v___x_4610_);
lean_dec(v___x_4685_);
v___x_4687_ = lean_nat_add(v___x_4686_, v___x_4613_);
lean_dec(v___x_4686_);
v___x_4688_ = lean_nat_add(v___x_4687_, v___x_4614_);
lean_dec(v___x_4687_);
v___x_4689_ = lean_array_get_size(v_altVars_4604_);
v___x_4690_ = lean_nat_add(v___x_4688_, v___x_4689_);
lean_dec(v___x_4688_);
v___x_4691_ = lean_array_get_size(v_heqs_4619_);
lean_dec_ref(v_heqs_4619_);
lean_inc(v_a_4676_);
v___x_4692_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4615_, v_a_4676_, v___x_4690_, v___x_4691_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4730_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4695_ = v___x_4692_;
v_isShared_4696_ = v_isSharedCheck_4730_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4692_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4730_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4697_; lean_object* v_env_4698_; uint8_t v___x_4699_; 
v___x_4697_ = lean_st_ref_get(v___y_4637_);
v_env_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc_ref(v_env_4698_);
lean_dec(v___x_4697_);
lean_inc(v___x_4616_);
v___x_4699_ = l_Lean_Environment_contains(v_env_4698_, v___x_4616_, v___x_4606_);
if (v___x_4699_ == 0)
{
lean_object* v___x_4701_; 
lean_del_object(v___x_4695_);
lean_inc(v___x_4616_);
if (v_isShared_4684_ == 0)
{
lean_ctor_set(v___x_4683_, 2, v_a_4676_);
lean_ctor_set(v___x_4683_, 1, v___x_4617_);
lean_ctor_set(v___x_4683_, 0, v___x_4616_);
v___x_4701_ = v___x_4683_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4616_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v___x_4617_);
lean_ctor_set(v_reuseFailAlloc_4726_, 2, v_a_4676_);
v___x_4701_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
lean_object* v___x_4703_; 
if (v_isShared_4651_ == 0)
{
lean_ctor_set_tag(v___x_4650_, 1);
lean_ctor_set(v___x_4650_, 1, v___x_4618_);
lean_ctor_set(v___x_4650_, 0, v___x_4616_);
v___x_4703_ = v___x_4650_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v___x_4616_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v___x_4618_);
v___x_4703_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
lean_object* v___x_4704_; lean_object* v___x_4706_; 
v___x_4704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4701_);
lean_ctor_set(v___x_4704_, 1, v_a_4693_);
lean_ctor_set(v___x_4704_, 2, v___x_4703_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set_tag(v___x_4678_, 2);
lean_ctor_set(v___x_4678_, 0, v___x_4704_);
v___x_4706_ = v___x_4678_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4704_);
v___x_4706_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
lean_object* v___x_4707_; 
v___x_4707_ = l_Lean_addDecl(v___x_4706_, v___x_4605_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v___x_4709_; uint8_t v_isShared_4710_; uint8_t v_isSharedCheck_4714_; 
v_isSharedCheck_4714_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4714_ == 0)
{
lean_object* v_unused_4715_; 
v_unused_4715_ = lean_ctor_get(v___x_4707_, 0);
lean_dec(v_unused_4715_);
v___x_4709_ = v___x_4707_;
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
else
{
lean_dec(v___x_4707_);
v___x_4709_ = lean_box(0);
v_isShared_4710_ = v_isSharedCheck_4714_;
goto v_resetjp_4708_;
}
v_resetjp_4708_:
{
lean_object* v___x_4712_; 
if (v_isShared_4710_ == 0)
{
lean_ctor_set(v___x_4709_, 0, v_a_4656_);
v___x_4712_ = v___x_4709_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4656_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
else
{
lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4723_; 
lean_dec(v_a_4656_);
v_a_4716_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4718_ = v___x_4707_;
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v___x_4707_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4721_; 
if (v_isShared_4719_ == 0)
{
v___x_4721_ = v___x_4718_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4716_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4728_; 
lean_dec(v_a_4693_);
lean_del_object(v___x_4683_);
lean_del_object(v___x_4678_);
lean_dec(v_a_4676_);
lean_del_object(v___x_4650_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
if (v_isShared_4696_ == 0)
{
lean_ctor_set(v___x_4695_, 0, v_a_4656_);
v___x_4728_ = v___x_4695_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_a_4656_);
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
else
{
lean_del_object(v___x_4683_);
lean_del_object(v___x_4678_);
lean_dec(v_a_4676_);
lean_dec(v_a_4656_);
lean_del_object(v___x_4650_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
return v___x_4692_;
}
}
}
}
else
{
lean_dec(v_a_4656_);
lean_del_object(v___x_4650_);
lean_dec_ref(v_heqs_4619_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
lean_dec(v_matchDeclName_4615_);
lean_dec_ref(v___x_4609_);
return v___x_4675_;
}
}
else
{
lean_dec(v_a_4656_);
lean_del_object(v___x_4650_);
lean_dec_ref(v_heqs_4619_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
lean_dec(v_matchDeclName_4615_);
lean_dec_ref(v___x_4609_);
return v___x_4673_;
}
}
else
{
lean_dec_ref(v___x_4665_);
lean_dec(v_a_4656_);
lean_del_object(v___x_4650_);
lean_dec_ref(v_heqs_4619_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
lean_dec(v_matchDeclName_4615_);
lean_dec_ref(v___x_4609_);
return v___x_4669_;
}
}
else
{
lean_dec_ref(v___x_4665_);
lean_dec(v_a_4656_);
lean_del_object(v___x_4650_);
lean_dec(v_a_4632_);
lean_dec_ref(v_heqs_4619_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
lean_dec(v_matchDeclName_4615_);
lean_dec_ref(v___x_4609_);
return v___x_4667_;
}
}
else
{
lean_dec_ref(v___x_4652_);
lean_del_object(v___x_4650_);
lean_dec(v_a_4632_);
lean_dec(v_a_4627_);
lean_dec_ref(v_heqs_4619_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
lean_dec(v_matchDeclName_4615_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4611_);
lean_dec_ref(v___x_4609_);
lean_dec(v___x_4608_);
return v___x_4655_;
}
}
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4743_; 
lean_dec(v_a_4632_);
lean_dec(v_a_4627_);
lean_dec_ref(v_heqs_4619_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
lean_dec(v_matchDeclName_4615_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4611_);
lean_dec_ref(v___x_4609_);
lean_dec(v___x_4608_);
lean_dec_ref(v___x_4603_);
v_a_4736_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4738_ = v___x_4646_;
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4646_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4741_; 
if (v_isShared_4739_ == 0)
{
v___x_4741_ = v___x_4738_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_a_4736_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
lean_dec(v_a_4627_);
lean_dec_ref(v_heqs_4619_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
lean_dec(v_matchDeclName_4615_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4611_);
lean_dec_ref(v___x_4609_);
lean_dec(v___x_4608_);
lean_dec_ref(v___x_4603_);
lean_dec(v___x_4602_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v_a_4599_);
v_a_4766_ = lean_ctor_get(v___x_4631_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4631_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4631_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4619_);
lean_dec(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
lean_dec(v_matchDeclName_4615_);
lean_dec_ref(v___x_4612_);
lean_dec_ref(v___x_4611_);
lean_dec_ref(v___x_4609_);
lean_dec(v___x_4608_);
lean_dec_ref(v___x_4603_);
lean_dec(v___x_4602_);
lean_dec_ref(v___x_4601_);
lean_dec(v___x_4600_);
lean_dec_ref(v_a_4599_);
return v___x_4626_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4774_ = _args[0];
lean_object* v_args_4775_ = _args[1];
lean_object* v___x_4776_ = _args[2];
lean_object* v_overlaps_4777_ = _args[3];
lean_object* v_a_4778_ = _args[4];
lean_object* v_fst_4779_ = _args[5];
lean_object* v_a_4780_ = _args[6];
lean_object* v___x_4781_ = _args[7];
lean_object* v___x_4782_ = _args[8];
lean_object* v___x_4783_ = _args[9];
lean_object* v___x_4784_ = _args[10];
lean_object* v_altVars_4785_ = _args[11];
lean_object* v___x_4786_ = _args[12];
lean_object* v___x_4787_ = _args[13];
lean_object* v_a_4788_ = _args[14];
lean_object* v___x_4789_ = _args[15];
lean_object* v___x_4790_ = _args[16];
lean_object* v___x_4791_ = _args[17];
lean_object* v___x_4792_ = _args[18];
lean_object* v___x_4793_ = _args[19];
lean_object* v___x_4794_ = _args[20];
lean_object* v___x_4795_ = _args[21];
lean_object* v_matchDeclName_4796_ = _args[22];
lean_object* v___x_4797_ = _args[23];
lean_object* v___x_4798_ = _args[24];
lean_object* v___x_4799_ = _args[25];
lean_object* v_heqs_4800_ = _args[26];
lean_object* v___y_4801_ = _args[27];
lean_object* v___y_4802_ = _args[28];
lean_object* v___y_4803_ = _args[29];
lean_object* v___y_4804_ = _args[30];
lean_object* v___y_4805_ = _args[31];
_start:
{
uint8_t v___x_21290__boxed_4806_; uint8_t v___x_21291__boxed_4807_; lean_object* v_res_4808_; 
v___x_21290__boxed_4806_ = lean_unbox(v___x_4786_);
v___x_21291__boxed_4807_ = lean_unbox(v___x_4787_);
v_res_4808_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4774_, v_args_4775_, v___x_4776_, v_overlaps_4777_, v_a_4778_, v_fst_4779_, v_a_4780_, v___x_4781_, v___x_4782_, v___x_4783_, v___x_4784_, v_altVars_4785_, v___x_21290__boxed_4806_, v___x_21291__boxed_4807_, v_a_4788_, v___x_4789_, v___x_4790_, v___x_4791_, v___x_4792_, v___x_4793_, v___x_4794_, v___x_4795_, v_matchDeclName_4796_, v___x_4797_, v___x_4798_, v___x_4799_, v_heqs_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec(v___x_4795_);
lean_dec(v___x_4794_);
lean_dec(v___x_4791_);
lean_dec_ref(v_a_4788_);
lean_dec_ref(v_altVars_4785_);
lean_dec(v_fst_4779_);
lean_dec(v_a_4778_);
lean_dec_ref(v_overlaps_4777_);
lean_dec_ref(v_args_4775_);
return v_res_4808_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4811_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4812_ = lean_unsigned_to_nat(8u);
v___x_4813_ = lean_unsigned_to_nat(295u);
v___x_4814_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4815_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4816_ = l_mkPanicMessageWithDecl(v___x_4815_, v___x_4814_, v___x_4813_, v___x_4812_, v___x_4811_);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4817_, lean_object* v___x_4818_, lean_object* v___y_4819_, lean_object* v___x_4820_, lean_object* v_overlaps_4821_, lean_object* v_a_4822_, lean_object* v_fst_4823_, lean_object* v___x_4824_, lean_object* v___x_4825_, uint8_t v___x_4826_, lean_object* v_a_4827_, lean_object* v___x_4828_, lean_object* v___x_4829_, lean_object* v___x_4830_, lean_object* v___x_4831_, lean_object* v___x_4832_, lean_object* v___x_4833_, lean_object* v_matchDeclName_4834_, lean_object* v___x_4835_, lean_object* v___x_4836_, lean_object* v___x_4837_, lean_object* v_altVars_4838_, lean_object* v_args_4839_, lean_object* v___mask_4840_, lean_object* v_altResultType_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
uint8_t v___x_4847_; lean_object* v___x_4848_; 
v___x_4847_ = 0;
v___x_4848_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4841_, v___f_4817_, v___x_4847_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v_start_4850_; lean_object* v_stop_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; uint8_t v___x_4854_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_a_4849_);
lean_dec_ref_known(v___x_4848_, 1);
v_start_4850_ = lean_ctor_get(v___x_4818_, 1);
v_stop_4851_ = lean_ctor_get(v___x_4818_, 2);
v___x_4852_ = lean_array_get_size(v_a_4849_);
v___x_4853_ = lean_nat_sub(v_stop_4851_, v_start_4850_);
v___x_4854_ = lean_nat_dec_eq(v___x_4852_, v___x_4853_);
if (v___x_4854_ == 0)
{
lean_object* v___x_4855_; lean_object* v___x_4856_; 
lean_dec(v___x_4853_);
lean_dec(v_a_4849_);
lean_dec_ref(v_args_4839_);
lean_dec_ref(v_altVars_4838_);
lean_dec(v___x_4837_);
lean_dec(v___x_4836_);
lean_dec(v___x_4835_);
lean_dec(v_matchDeclName_4834_);
lean_dec(v___x_4833_);
lean_dec_ref(v___x_4832_);
lean_dec_ref(v___x_4831_);
lean_dec(v___x_4830_);
lean_dec_ref(v___x_4829_);
lean_dec(v___x_4828_);
lean_dec_ref(v_a_4827_);
lean_dec(v___x_4825_);
lean_dec_ref(v___x_4824_);
lean_dec(v_fst_4823_);
lean_dec(v_a_4822_);
lean_dec_ref(v_overlaps_4821_);
lean_dec(v___x_4820_);
lean_dec_ref(v___y_4819_);
lean_dec_ref(v___x_4818_);
v___x_4855_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4856_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v___x_4855_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
return v___x_4856_;
}
else
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___f_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4857_ = lean_box(v___x_4847_);
v___x_4858_ = lean_box(v___x_4826_);
lean_inc_ref(v___x_4818_);
lean_inc(v___x_4825_);
lean_inc(v_a_4849_);
v___f_4859_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4859_, 0, v___y_4819_);
lean_closure_set(v___f_4859_, 1, v_args_4839_);
lean_closure_set(v___f_4859_, 2, v___x_4820_);
lean_closure_set(v___f_4859_, 3, v_overlaps_4821_);
lean_closure_set(v___f_4859_, 4, v_a_4822_);
lean_closure_set(v___f_4859_, 5, v_fst_4823_);
lean_closure_set(v___f_4859_, 6, v_a_4849_);
lean_closure_set(v___f_4859_, 7, v___x_4852_);
lean_closure_set(v___f_4859_, 8, v___x_4824_);
lean_closure_set(v___f_4859_, 9, v___x_4825_);
lean_closure_set(v___f_4859_, 10, v___x_4818_);
lean_closure_set(v___f_4859_, 11, v_altVars_4838_);
lean_closure_set(v___f_4859_, 12, v___x_4857_);
lean_closure_set(v___f_4859_, 13, v___x_4858_);
lean_closure_set(v___f_4859_, 14, v_a_4827_);
lean_closure_set(v___f_4859_, 15, v___x_4828_);
lean_closure_set(v___f_4859_, 16, v___x_4829_);
lean_closure_set(v___f_4859_, 17, v___x_4830_);
lean_closure_set(v___f_4859_, 18, v___x_4831_);
lean_closure_set(v___f_4859_, 19, v___x_4832_);
lean_closure_set(v___f_4859_, 20, v___x_4853_);
lean_closure_set(v___f_4859_, 21, v___x_4833_);
lean_closure_set(v___f_4859_, 22, v_matchDeclName_4834_);
lean_closure_set(v___f_4859_, 23, v___x_4835_);
lean_closure_set(v___f_4859_, 24, v___x_4836_);
lean_closure_set(v___f_4859_, 25, v___x_4837_);
v___x_4860_ = lean_mk_empty_array_with_capacity(v___x_4825_);
v___x_4861_ = l_Array_toSubarray___redArg(v_a_4849_, v___x_4825_, v___x_4852_);
v___x_4862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4860_);
lean_ctor_set(v___x_4862_, 1, v___x_4861_);
v___x_4863_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v___x_4818_, v___x_4862_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v_fst_4865_; uint8_t v___x_4866_; lean_object* v___x_4867_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v_fst_4865_ = lean_ctor_get(v_a_4864_, 0);
lean_inc(v_fst_4865_);
lean_dec(v_a_4864_);
v___x_4866_ = 0;
v___x_4867_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4865_, v___f_4859_, v___x_4866_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
return v___x_4867_;
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
lean_dec_ref(v___f_4859_);
v_a_4868_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4863_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4863_);
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
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
lean_dec_ref(v_args_4839_);
lean_dec_ref(v_altVars_4838_);
lean_dec(v___x_4837_);
lean_dec(v___x_4836_);
lean_dec(v___x_4835_);
lean_dec(v_matchDeclName_4834_);
lean_dec(v___x_4833_);
lean_dec_ref(v___x_4832_);
lean_dec_ref(v___x_4831_);
lean_dec(v___x_4830_);
lean_dec_ref(v___x_4829_);
lean_dec(v___x_4828_);
lean_dec_ref(v_a_4827_);
lean_dec(v___x_4825_);
lean_dec_ref(v___x_4824_);
lean_dec(v_fst_4823_);
lean_dec(v_a_4822_);
lean_dec_ref(v_overlaps_4821_);
lean_dec(v___x_4820_);
lean_dec_ref(v___y_4819_);
lean_dec_ref(v___x_4818_);
v_a_4876_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4848_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4848_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4884_ = _args[0];
lean_object* v___x_4885_ = _args[1];
lean_object* v___y_4886_ = _args[2];
lean_object* v___x_4887_ = _args[3];
lean_object* v_overlaps_4888_ = _args[4];
lean_object* v_a_4889_ = _args[5];
lean_object* v_fst_4890_ = _args[6];
lean_object* v___x_4891_ = _args[7];
lean_object* v___x_4892_ = _args[8];
lean_object* v___x_4893_ = _args[9];
lean_object* v_a_4894_ = _args[10];
lean_object* v___x_4895_ = _args[11];
lean_object* v___x_4896_ = _args[12];
lean_object* v___x_4897_ = _args[13];
lean_object* v___x_4898_ = _args[14];
lean_object* v___x_4899_ = _args[15];
lean_object* v___x_4900_ = _args[16];
lean_object* v_matchDeclName_4901_ = _args[17];
lean_object* v___x_4902_ = _args[18];
lean_object* v___x_4903_ = _args[19];
lean_object* v___x_4904_ = _args[20];
lean_object* v_altVars_4905_ = _args[21];
lean_object* v_args_4906_ = _args[22];
lean_object* v___mask_4907_ = _args[23];
lean_object* v_altResultType_4908_ = _args[24];
lean_object* v___y_4909_ = _args[25];
lean_object* v___y_4910_ = _args[26];
lean_object* v___y_4911_ = _args[27];
lean_object* v___y_4912_ = _args[28];
lean_object* v___y_4913_ = _args[29];
_start:
{
uint8_t v___x_21677__boxed_4914_; lean_object* v_res_4915_; 
v___x_21677__boxed_4914_ = lean_unbox(v___x_4893_);
v_res_4915_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4884_, v___x_4885_, v___y_4886_, v___x_4887_, v_overlaps_4888_, v_a_4889_, v_fst_4890_, v___x_4891_, v___x_4892_, v___x_21677__boxed_4914_, v_a_4894_, v___x_4895_, v___x_4896_, v___x_4897_, v___x_4898_, v___x_4899_, v___x_4900_, v_matchDeclName_4901_, v___x_4902_, v___x_4903_, v___x_4904_, v_altVars_4905_, v_args_4906_, v___mask_4907_, v_altResultType_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
lean_dec_ref(v___mask_4907_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4917_, lean_object* v_val_4918_, lean_object* v_matchDeclName_4919_, lean_object* v___x_4920_, lean_object* v___x_4921_, lean_object* v_a_4922_, lean_object* v___x_4923_, lean_object* v___x_4924_, lean_object* v___x_4925_, lean_object* v___x_4926_, lean_object* v___x_4927_, lean_object* v___x_4928_, lean_object* v_a_4929_, lean_object* v_b_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_){
_start:
{
uint8_t v___x_4936_; 
v___x_4936_ = lean_nat_dec_lt(v_a_4929_, v_upperBound_4917_);
if (v___x_4936_ == 0)
{
lean_object* v___x_4937_; 
lean_dec(v_a_4929_);
lean_dec(v___x_4928_);
lean_dec(v___x_4927_);
lean_dec_ref(v___x_4926_);
lean_dec_ref(v___x_4925_);
lean_dec_ref(v___x_4924_);
lean_dec(v___x_4923_);
lean_dec_ref(v_a_4922_);
lean_dec(v___x_4921_);
lean_dec_ref(v___x_4920_);
lean_dec(v_matchDeclName_4919_);
lean_dec_ref(v_val_4918_);
v___x_4937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4937_, 0, v_b_4930_);
return v___x_4937_;
}
else
{
lean_object* v_snd_4938_; lean_object* v_fst_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_5003_; 
v_snd_4938_ = lean_ctor_get(v_b_4930_, 1);
v_fst_4939_ = lean_ctor_get(v_b_4930_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v_b_4930_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4941_ = v_b_4930_;
v_isShared_4942_ = v_isSharedCheck_5003_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_snd_4938_);
lean_inc(v_fst_4939_);
lean_dec(v_b_4930_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_5003_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v_fst_4943_; lean_object* v_snd_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_5002_; 
v_fst_4943_ = lean_ctor_get(v_snd_4938_, 0);
v_snd_4944_ = lean_ctor_get(v_snd_4938_, 1);
v_isSharedCheck_5002_ = !lean_is_exclusive(v_snd_4938_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4946_ = v_snd_4938_;
v_isShared_4947_ = v_isSharedCheck_5002_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_snd_4944_);
lean_inc(v_fst_4943_);
lean_dec(v_snd_4938_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_5002_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v_altInfos_4948_; lean_object* v_overlaps_4949_; lean_object* v_start_4950_; lean_object* v_stop_4951_; lean_object* v___f_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___y_4964_; lean_object* v___x_4997_; uint8_t v___x_4998_; 
v_altInfos_4948_ = lean_ctor_get(v_val_4918_, 2);
v_overlaps_4949_ = lean_ctor_get(v_val_4918_, 5);
v_start_4950_ = lean_ctor_get(v___x_4926_, 1);
v_stop_4951_ = lean_ctor_get(v___x_4926_, 2);
v___f_4952_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4953_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4954_ = lean_unsigned_to_nat(0u);
v___x_4955_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4956_ = lean_unsigned_to_nat(1u);
v___x_4957_ = lean_box(0);
v___x_4958_ = lean_array_get_borrowed(v___x_4953_, v_altInfos_4948_, v_a_4929_);
v___x_4959_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4919_);
v___x_4960_ = l_Lean_Name_str___override(v_matchDeclName_4919_, v___x_4959_);
lean_inc(v_snd_4944_);
v___x_4961_ = lean_name_append_index_after(v___x_4960_, v_snd_4944_);
lean_inc(v___x_4961_);
v___x_4962_ = lean_array_push(v_fst_4939_, v___x_4961_);
v___x_4997_ = lean_nat_sub(v_stop_4951_, v_start_4950_);
v___x_4998_ = lean_nat_dec_lt(v_a_4929_, v___x_4997_);
lean_dec(v___x_4997_);
if (v___x_4998_ == 0)
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4999_ = l_Lean_instInhabitedExpr;
v___x_5000_ = l_outOfBounds___redArg(v___x_4999_);
v___y_4964_ = v___x_5000_;
goto v___jp_4963_;
}
else
{
lean_object* v___x_5001_; 
v___x_5001_ = l_Subarray_get___redArg(v___x_4926_, v_a_4929_);
v___y_4964_ = v___x_5001_;
goto v___jp_4963_;
}
v___jp_4963_:
{
lean_object* v___x_4965_; lean_object* v___f_4966_; lean_object* v___x_4967_; 
v___x_4965_ = lean_box(v___x_4936_);
lean_inc(v___x_4928_);
lean_inc(v_matchDeclName_4919_);
lean_inc(v___x_4927_);
lean_inc_ref(v___x_4926_);
lean_inc_ref(v___x_4925_);
lean_inc_ref(v___x_4924_);
lean_inc(v___x_4923_);
lean_inc_ref(v_a_4922_);
lean_inc(v_fst_4943_);
lean_inc(v_a_4929_);
lean_inc_ref(v_overlaps_4949_);
lean_inc(v___x_4921_);
lean_inc_ref(v___y_4964_);
lean_inc_ref(v___x_4920_);
v___f_4966_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 30, 21);
lean_closure_set(v___f_4966_, 0, v___f_4952_);
lean_closure_set(v___f_4966_, 1, v___x_4920_);
lean_closure_set(v___f_4966_, 2, v___y_4964_);
lean_closure_set(v___f_4966_, 3, v___x_4921_);
lean_closure_set(v___f_4966_, 4, v_overlaps_4949_);
lean_closure_set(v___f_4966_, 5, v_a_4929_);
lean_closure_set(v___f_4966_, 6, v_fst_4943_);
lean_closure_set(v___f_4966_, 7, v___x_4955_);
lean_closure_set(v___f_4966_, 8, v___x_4954_);
lean_closure_set(v___f_4966_, 9, v___x_4965_);
lean_closure_set(v___f_4966_, 10, v_a_4922_);
lean_closure_set(v___f_4966_, 11, v___x_4923_);
lean_closure_set(v___f_4966_, 12, v___x_4924_);
lean_closure_set(v___f_4966_, 13, v___x_4956_);
lean_closure_set(v___f_4966_, 14, v___x_4925_);
lean_closure_set(v___f_4966_, 15, v___x_4926_);
lean_closure_set(v___f_4966_, 16, v___x_4927_);
lean_closure_set(v___f_4966_, 17, v_matchDeclName_4919_);
lean_closure_set(v___f_4966_, 18, v___x_4961_);
lean_closure_set(v___f_4966_, 19, v___x_4928_);
lean_closure_set(v___f_4966_, 20, v___x_4957_);
lean_inc(v___y_4934_);
lean_inc_ref(v___y_4933_);
lean_inc(v___y_4932_);
lean_inc_ref(v___y_4931_);
v___x_4967_ = lean_infer_type(v___y_4964_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4969_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_a_4968_);
lean_dec_ref_known(v___x_4967_, 1);
lean_inc(v___x_4958_);
v___x_4969_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4968_, v___x_4958_, v___f_4966_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
if (lean_obj_tag(v___x_4969_) == 0)
{
lean_object* v_a_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4974_; 
v_a_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_a_4970_);
lean_dec_ref_known(v___x_4969_, 1);
v___x_4971_ = lean_array_push(v_fst_4943_, v_a_4970_);
v___x_4972_ = lean_nat_add(v_snd_4944_, v___x_4956_);
lean_dec(v_snd_4944_);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 1, v___x_4972_);
lean_ctor_set(v___x_4946_, 0, v___x_4971_);
v___x_4974_ = v___x_4946_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4971_);
lean_ctor_set(v_reuseFailAlloc_4980_, 1, v___x_4972_);
v___x_4974_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
lean_object* v___x_4976_; 
if (v_isShared_4942_ == 0)
{
lean_ctor_set(v___x_4941_, 1, v___x_4974_);
lean_ctor_set(v___x_4941_, 0, v___x_4962_);
v___x_4976_ = v___x_4941_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v___x_4962_);
lean_ctor_set(v_reuseFailAlloc_4979_, 1, v___x_4974_);
v___x_4976_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
lean_object* v___x_4977_; 
v___x_4977_ = lean_nat_add(v_a_4929_, v___x_4956_);
lean_dec(v_a_4929_);
v_a_4929_ = v___x_4977_;
v_b_4930_ = v___x_4976_;
goto _start;
}
}
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
lean_dec_ref(v___x_4962_);
lean_del_object(v___x_4946_);
lean_dec(v_snd_4944_);
lean_dec(v_fst_4943_);
lean_del_object(v___x_4941_);
lean_dec(v_a_4929_);
lean_dec(v___x_4928_);
lean_dec(v___x_4927_);
lean_dec_ref(v___x_4926_);
lean_dec_ref(v___x_4925_);
lean_dec_ref(v___x_4924_);
lean_dec(v___x_4923_);
lean_dec_ref(v_a_4922_);
lean_dec(v___x_4921_);
lean_dec_ref(v___x_4920_);
lean_dec(v_matchDeclName_4919_);
lean_dec_ref(v_val_4918_);
v_a_4981_ = lean_ctor_get(v___x_4969_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4969_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4969_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4969_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
else
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
lean_dec_ref(v___f_4966_);
lean_dec_ref(v___x_4962_);
lean_del_object(v___x_4946_);
lean_dec(v_snd_4944_);
lean_dec(v_fst_4943_);
lean_del_object(v___x_4941_);
lean_dec(v_a_4929_);
lean_dec(v___x_4928_);
lean_dec(v___x_4927_);
lean_dec_ref(v___x_4926_);
lean_dec_ref(v___x_4925_);
lean_dec_ref(v___x_4924_);
lean_dec(v___x_4923_);
lean_dec_ref(v_a_4922_);
lean_dec(v___x_4921_);
lean_dec_ref(v___x_4920_);
lean_dec(v_matchDeclName_4919_);
lean_dec_ref(v_val_4918_);
v_a_4989_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v___x_4967_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4967_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5004_ = _args[0];
lean_object* v_val_5005_ = _args[1];
lean_object* v_matchDeclName_5006_ = _args[2];
lean_object* v___x_5007_ = _args[3];
lean_object* v___x_5008_ = _args[4];
lean_object* v_a_5009_ = _args[5];
lean_object* v___x_5010_ = _args[6];
lean_object* v___x_5011_ = _args[7];
lean_object* v___x_5012_ = _args[8];
lean_object* v___x_5013_ = _args[9];
lean_object* v___x_5014_ = _args[10];
lean_object* v___x_5015_ = _args[11];
lean_object* v_a_5016_ = _args[12];
lean_object* v_b_5017_ = _args[13];
lean_object* v___y_5018_ = _args[14];
lean_object* v___y_5019_ = _args[15];
lean_object* v___y_5020_ = _args[16];
lean_object* v___y_5021_ = _args[17];
lean_object* v___y_5022_ = _args[18];
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5004_, v_val_5005_, v_matchDeclName_5006_, v___x_5007_, v___x_5008_, v_a_5009_, v___x_5010_, v___x_5011_, v___x_5012_, v___x_5013_, v___x_5014_, v___x_5015_, v_a_5016_, v_b_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v_upperBound_5004_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5030_, lean_object* v___x_5031_, lean_object* v_matchDeclName_5032_, lean_object* v___x_5033_, lean_object* v_a_5034_, lean_object* v___x_5035_, lean_object* v___x_5036_, lean_object* v_xs_5037_, lean_object* v___matchResultType_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v_numParams_5044_; lean_object* v_numDiscrs_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v_lower_5051_; lean_object* v_upper_5052_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; uint8_t v___x_5083_; 
v_numParams_5044_ = lean_ctor_get(v_val_5030_, 0);
v_numDiscrs_5045_ = lean_ctor_get(v_val_5030_, 1);
v___x_5046_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5044_);
lean_inc_ref(v_xs_5037_);
v___x_5047_ = l_Array_toSubarray___redArg(v_xs_5037_, v___x_5046_, v_numParams_5044_);
v___x_5048_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5030_);
v___x_5049_ = lean_array_get(v___x_5031_, v_xs_5037_, v___x_5048_);
lean_dec(v___x_5048_);
v___x_5080_ = lean_array_get_size(v_xs_5037_);
v___x_5081_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5030_);
v___x_5082_ = lean_nat_sub(v___x_5080_, v___x_5081_);
lean_dec(v___x_5081_);
v___x_5083_ = lean_nat_dec_le(v___x_5082_, v___x_5046_);
if (v___x_5083_ == 0)
{
v_lower_5051_ = v___x_5082_;
v_upper_5052_ = v___x_5080_;
goto v___jp_5050_;
}
else
{
lean_dec(v___x_5082_);
v_lower_5051_ = v___x_5046_;
v_upper_5052_ = v___x_5080_;
goto v___jp_5050_;
}
v___jp_5050_:
{
lean_object* v___x_5053_; lean_object* v_start_5054_; lean_object* v_stop_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
lean_inc_ref(v_xs_5037_);
v___x_5053_ = l_Array_toSubarray___redArg(v_xs_5037_, v_lower_5051_, v_upper_5052_);
v_start_5054_ = lean_ctor_get(v___x_5053_, 1);
v_stop_5055_ = lean_ctor_get(v___x_5053_, 2);
v___x_5056_ = lean_unsigned_to_nat(1u);
v___x_5057_ = lean_nat_add(v_numParams_5044_, v___x_5056_);
v___x_5058_ = lean_nat_add(v___x_5057_, v_numDiscrs_5045_);
v___x_5059_ = lean_nat_sub(v_stop_5055_, v_start_5054_);
v___x_5060_ = l_Array_toSubarray___redArg(v_xs_5037_, v___x_5057_, v___x_5058_);
v___x_5061_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5059_);
v___x_5062_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5059_, v_val_5030_, v_matchDeclName_5032_, v___x_5060_, v___x_5033_, v_a_5034_, v___x_5035_, v___x_5047_, v___x_5049_, v___x_5053_, v___x_5059_, v___x_5036_, v___x_5046_, v___x_5061_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
lean_dec(v___x_5059_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5070_; 
v_isSharedCheck_5070_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5070_ == 0)
{
lean_object* v_unused_5071_; 
v_unused_5071_ = lean_ctor_get(v___x_5062_, 0);
lean_dec(v_unused_5071_);
v___x_5064_ = v___x_5062_;
v_isShared_5065_ = v_isSharedCheck_5070_;
goto v_resetjp_5063_;
}
else
{
lean_dec(v___x_5062_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5070_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5066_; lean_object* v___x_5068_; 
v___x_5066_ = lean_box(0);
if (v_isShared_5065_ == 0)
{
lean_ctor_set(v___x_5064_, 0, v___x_5066_);
v___x_5068_ = v___x_5064_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5069_; 
v_reuseFailAlloc_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5066_);
v___x_5068_ = v_reuseFailAlloc_5069_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
return v___x_5068_;
}
}
}
else
{
lean_object* v_a_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5079_; 
v_a_5072_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5074_ = v___x_5062_;
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_a_5072_);
lean_dec(v___x_5062_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5079_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5077_; 
if (v_isShared_5075_ == 0)
{
v___x_5077_ = v___x_5074_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5084_, lean_object* v___x_5085_, lean_object* v_matchDeclName_5086_, lean_object* v___x_5087_, lean_object* v_a_5088_, lean_object* v___x_5089_, lean_object* v___x_5090_, lean_object* v_xs_5091_, lean_object* v___matchResultType_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5084_, v___x_5085_, v_matchDeclName_5086_, v___x_5087_, v_a_5088_, v___x_5089_, v___x_5090_, v_xs_5091_, v___matchResultType_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_);
lean_dec(v___y_5096_);
lean_dec_ref(v___y_5095_);
lean_dec(v___y_5094_);
lean_dec_ref(v___y_5093_);
lean_dec_ref(v___matchResultType_5092_);
lean_dec_ref(v___x_5085_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_){
_start:
{
uint8_t v_trackZetaDelta_5105_; lean_object* v_zetaDeltaSet_5106_; lean_object* v_lctx_5107_; lean_object* v_localInstances_5108_; lean_object* v_defEqCtx_x3f_5109_; lean_object* v_synthPendingDepth_5110_; lean_object* v_customCanUnfoldPredicate_x3f_5111_; uint8_t v_univApprox_5112_; uint8_t v_inTypeClassResolution_5113_; uint8_t v_cacheInferType_5114_; lean_object* v___x_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5158_; 
v_trackZetaDelta_5105_ = lean_ctor_get_uint8(v_a_5100_, sizeof(void*)*7);
v_zetaDeltaSet_5106_ = lean_ctor_get(v_a_5100_, 1);
lean_inc(v_zetaDeltaSet_5106_);
v_lctx_5107_ = lean_ctor_get(v_a_5100_, 2);
lean_inc_ref(v_lctx_5107_);
v_localInstances_5108_ = lean_ctor_get(v_a_5100_, 3);
lean_inc_ref(v_localInstances_5108_);
v_defEqCtx_x3f_5109_ = lean_ctor_get(v_a_5100_, 4);
lean_inc(v_defEqCtx_x3f_5109_);
v_synthPendingDepth_5110_ = lean_ctor_get(v_a_5100_, 5);
lean_inc(v_synthPendingDepth_5110_);
v_customCanUnfoldPredicate_x3f_5111_ = lean_ctor_get(v_a_5100_, 6);
lean_inc(v_customCanUnfoldPredicate_x3f_5111_);
v_univApprox_5112_ = lean_ctor_get_uint8(v_a_5100_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5113_ = lean_ctor_get_uint8(v_a_5100_, sizeof(void*)*7 + 2);
v_cacheInferType_5114_ = lean_ctor_get_uint8(v_a_5100_, sizeof(void*)*7 + 3);
v___x_5115_ = l_Lean_Meta_Context_config(v_a_5100_);
v_isSharedCheck_5158_ = !lean_is_exclusive(v_a_5100_);
if (v_isSharedCheck_5158_ == 0)
{
lean_object* v_unused_5159_; lean_object* v_unused_5160_; lean_object* v_unused_5161_; lean_object* v_unused_5162_; lean_object* v_unused_5163_; lean_object* v_unused_5164_; lean_object* v_unused_5165_; 
v_unused_5159_ = lean_ctor_get(v_a_5100_, 6);
lean_dec(v_unused_5159_);
v_unused_5160_ = lean_ctor_get(v_a_5100_, 5);
lean_dec(v_unused_5160_);
v_unused_5161_ = lean_ctor_get(v_a_5100_, 4);
lean_dec(v_unused_5161_);
v_unused_5162_ = lean_ctor_get(v_a_5100_, 3);
lean_dec(v_unused_5162_);
v_unused_5163_ = lean_ctor_get(v_a_5100_, 2);
lean_dec(v_unused_5163_);
v_unused_5164_ = lean_ctor_get(v_a_5100_, 1);
lean_dec(v_unused_5164_);
v_unused_5165_ = lean_ctor_get(v_a_5100_, 0);
lean_dec(v_unused_5165_);
v___x_5117_ = v_a_5100_;
v_isShared_5118_ = v_isSharedCheck_5158_;
goto v_resetjp_5116_;
}
else
{
lean_dec(v_a_5100_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5158_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5119_; uint64_t v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5124_; 
v___x_5119_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5115_);
v___x_5120_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5119_);
v___x_5121_ = l_Lean_instInhabitedExpr;
v___x_5122_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5122_, 0, v___x_5119_);
lean_ctor_set_uint64(v___x_5122_, sizeof(void*)*1, v___x_5120_);
lean_inc(v_customCanUnfoldPredicate_x3f_5111_);
lean_inc(v_synthPendingDepth_5110_);
lean_inc(v_defEqCtx_x3f_5109_);
lean_inc_ref(v_localInstances_5108_);
lean_inc_ref(v_lctx_5107_);
lean_inc(v_zetaDeltaSet_5106_);
if (v_isShared_5118_ == 0)
{
lean_ctor_set(v___x_5117_, 0, v___x_5122_);
v___x_5124_ = v___x_5117_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5122_);
lean_ctor_set(v_reuseFailAlloc_5157_, 1, v_zetaDeltaSet_5106_);
lean_ctor_set(v_reuseFailAlloc_5157_, 2, v_lctx_5107_);
lean_ctor_set(v_reuseFailAlloc_5157_, 3, v_localInstances_5108_);
lean_ctor_set(v_reuseFailAlloc_5157_, 4, v_defEqCtx_x3f_5109_);
lean_ctor_set(v_reuseFailAlloc_5157_, 5, v_synthPendingDepth_5110_);
lean_ctor_set(v_reuseFailAlloc_5157_, 6, v_customCanUnfoldPredicate_x3f_5111_);
lean_ctor_set_uint8(v_reuseFailAlloc_5157_, sizeof(void*)*7, v_trackZetaDelta_5105_);
lean_ctor_set_uint8(v_reuseFailAlloc_5157_, sizeof(void*)*7 + 1, v_univApprox_5112_);
lean_ctor_set_uint8(v_reuseFailAlloc_5157_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5113_);
lean_ctor_set_uint8(v_reuseFailAlloc_5157_, sizeof(void*)*7 + 3, v_cacheInferType_5114_);
v___x_5124_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
lean_object* v___x_5125_; lean_object* v___x_5126_; uint64_t v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5125_ = l_Lean_Meta_Context_config(v___x_5124_);
lean_dec_ref(v___x_5124_);
v___x_5126_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5125_);
v___x_5127_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5126_);
v___x_5128_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5128_, 0, v___x_5126_);
lean_ctor_set_uint64(v___x_5128_, sizeof(void*)*1, v___x_5127_);
v___x_5129_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
lean_ctor_set(v___x_5129_, 1, v_zetaDeltaSet_5106_);
lean_ctor_set(v___x_5129_, 2, v_lctx_5107_);
lean_ctor_set(v___x_5129_, 3, v_localInstances_5108_);
lean_ctor_set(v___x_5129_, 4, v_defEqCtx_x3f_5109_);
lean_ctor_set(v___x_5129_, 5, v_synthPendingDepth_5110_);
lean_ctor_set(v___x_5129_, 6, v_customCanUnfoldPredicate_x3f_5111_);
lean_ctor_set_uint8(v___x_5129_, sizeof(void*)*7, v_trackZetaDelta_5105_);
lean_ctor_set_uint8(v___x_5129_, sizeof(void*)*7 + 1, v_univApprox_5112_);
lean_ctor_set_uint8(v___x_5129_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5113_);
lean_ctor_set_uint8(v___x_5129_, sizeof(void*)*7 + 3, v_cacheInferType_5114_);
lean_inc(v_matchDeclName_5099_);
v___x_5130_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5099_, v___x_5129_, v_a_5101_, v_a_5102_, v_a_5103_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v_a_5136_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
lean_dec_ref_known(v___x_5130_, 1);
v___x_5132_ = l_Lean_ConstantInfo_levelParams(v_a_5131_);
v___x_5133_ = lean_box(0);
lean_inc(v___x_5132_);
v___x_5134_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v___x_5132_, v___x_5133_);
lean_inc(v_matchDeclName_5099_);
v___x_5135_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_5099_, v_a_5103_);
v_a_5136_ = lean_ctor_get(v___x_5135_, 0);
lean_inc(v_a_5136_);
lean_dec_ref(v___x_5135_);
if (lean_obj_tag(v_a_5136_) == 1)
{
lean_object* v_val_5137_; lean_object* v___x_5138_; lean_object* v___f_5139_; lean_object* v___x_5140_; uint8_t v___x_5141_; lean_object* v___x_5142_; 
v_val_5137_ = lean_ctor_get(v_a_5136_, 0);
lean_inc(v_val_5137_);
lean_dec_ref_known(v_a_5136_, 1);
v___x_5138_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5137_);
lean_inc(v_a_5131_);
v___f_5139_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5139_, 0, v_val_5137_);
lean_closure_set(v___f_5139_, 1, v___x_5121_);
lean_closure_set(v___f_5139_, 2, v_matchDeclName_5099_);
lean_closure_set(v___f_5139_, 3, v___x_5138_);
lean_closure_set(v___f_5139_, 4, v_a_5131_);
lean_closure_set(v___f_5139_, 5, v___x_5134_);
lean_closure_set(v___f_5139_, 6, v___x_5132_);
v___x_5140_ = l_Lean_ConstantInfo_type(v_a_5131_);
lean_dec(v_a_5131_);
v___x_5141_ = 0;
v___x_5142_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5140_, v___f_5139_, v___x_5141_, v___x_5141_, v___x_5129_, v_a_5101_, v_a_5102_, v_a_5103_);
lean_dec_ref_known(v___x_5129_, 7);
return v___x_5142_;
}
else
{
lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
lean_dec(v_a_5136_);
lean_dec(v___x_5134_);
lean_dec(v___x_5132_);
lean_dec(v_a_5131_);
v___x_5143_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5144_ = l_Lean_MessageData_ofName(v_matchDeclName_5099_);
v___x_5145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5143_);
lean_ctor_set(v___x_5145_, 1, v___x_5144_);
v___x_5146_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5147_, 0, v___x_5145_);
lean_ctor_set(v___x_5147_, 1, v___x_5146_);
v___x_5148_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5147_, v___x_5129_, v_a_5101_, v_a_5102_, v_a_5103_);
lean_dec_ref_known(v___x_5129_, 7);
return v___x_5148_;
}
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
lean_dec_ref_known(v___x_5129_, 7);
lean_dec(v_matchDeclName_5099_);
v_a_5149_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5130_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5130_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_){
_start:
{
lean_object* v_res_5172_; 
v_res_5172_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5166_, v_a_5167_, v_a_5168_, v_a_5169_, v_a_5170_);
lean_dec(v_a_5170_);
lean_dec_ref(v_a_5169_);
lean_dec(v_a_5168_);
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v_inst_5173_, lean_object* v_R_5174_, lean_object* v_a_5175_, lean_object* v_b_5176_, lean_object* v_c_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
lean_object* v___x_5183_; 
v___x_5183_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_5175_, v_b_5176_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
return v___x_5183_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v_inst_5184_, lean_object* v_R_5185_, lean_object* v_a_5186_, lean_object* v_b_5187_, lean_object* v_c_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_inst_5184_, v_R_5185_, v_a_5186_, v_b_5187_, v_c_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_);
lean_dec(v___y_5192_);
lean_dec_ref(v___y_5191_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5195_, lean_object* v_val_5196_, lean_object* v_matchDeclName_5197_, lean_object* v___x_5198_, lean_object* v___x_5199_, lean_object* v_a_5200_, lean_object* v___x_5201_, lean_object* v___x_5202_, lean_object* v___x_5203_, lean_object* v___x_5204_, lean_object* v___x_5205_, lean_object* v___x_5206_, lean_object* v_inst_5207_, lean_object* v_R_5208_, lean_object* v_a_5209_, lean_object* v_b_5210_, lean_object* v_c_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
lean_object* v___x_5217_; 
v___x_5217_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5195_, v_val_5196_, v_matchDeclName_5197_, v___x_5198_, v___x_5199_, v_a_5200_, v___x_5201_, v___x_5202_, v___x_5203_, v___x_5204_, v___x_5205_, v___x_5206_, v_a_5209_, v_b_5210_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5218_ = _args[0];
lean_object* v_val_5219_ = _args[1];
lean_object* v_matchDeclName_5220_ = _args[2];
lean_object* v___x_5221_ = _args[3];
lean_object* v___x_5222_ = _args[4];
lean_object* v_a_5223_ = _args[5];
lean_object* v___x_5224_ = _args[6];
lean_object* v___x_5225_ = _args[7];
lean_object* v___x_5226_ = _args[8];
lean_object* v___x_5227_ = _args[9];
lean_object* v___x_5228_ = _args[10];
lean_object* v___x_5229_ = _args[11];
lean_object* v_inst_5230_ = _args[12];
lean_object* v_R_5231_ = _args[13];
lean_object* v_a_5232_ = _args[14];
lean_object* v_b_5233_ = _args[15];
lean_object* v_c_5234_ = _args[16];
lean_object* v___y_5235_ = _args[17];
lean_object* v___y_5236_ = _args[18];
lean_object* v___y_5237_ = _args[19];
lean_object* v___y_5238_ = _args[20];
lean_object* v___y_5239_ = _args[21];
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5218_, v_val_5219_, v_matchDeclName_5220_, v___x_5221_, v___x_5222_, v_a_5223_, v___x_5224_, v___x_5225_, v___x_5226_, v___x_5227_, v___x_5228_, v___x_5229_, v_inst_5230_, v_R_5231_, v_a_5232_, v_b_5233_, v_c_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_);
lean_dec(v___y_5238_);
lean_dec_ref(v___y_5237_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
lean_dec(v_upperBound_5218_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5241_, lean_object* v_matchDeclName_5242_, lean_object* v_a_5243_, lean_object* v_b_5244_){
_start:
{
uint8_t v___x_5246_; 
v___x_5246_ = lean_nat_dec_lt(v_a_5243_, v_upperBound_5241_);
if (v___x_5246_ == 0)
{
lean_object* v___x_5247_; 
lean_dec(v_a_5243_);
lean_dec(v_matchDeclName_5242_);
v___x_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5247_, 0, v_b_5244_);
return v___x_5247_;
}
else
{
lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; 
v___x_5248_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5242_);
v___x_5249_ = l_Lean_Name_str___override(v_matchDeclName_5242_, v___x_5248_);
v___x_5250_ = lean_unsigned_to_nat(1u);
v___x_5251_ = lean_nat_add(v_a_5243_, v___x_5250_);
lean_dec(v_a_5243_);
lean_inc(v___x_5251_);
v___x_5252_ = lean_name_append_index_after(v___x_5249_, v___x_5251_);
v___x_5253_ = lean_array_push(v_b_5244_, v___x_5252_);
v_a_5243_ = v___x_5251_;
v_b_5244_ = v___x_5253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5255_, lean_object* v_matchDeclName_5256_, lean_object* v_a_5257_, lean_object* v_b_5258_, lean_object* v___y_5259_){
_start:
{
lean_object* v_res_5260_; 
v_res_5260_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5255_, v_matchDeclName_5256_, v_a_5257_, v_b_5258_);
lean_dec(v_upperBound_5255_);
return v_res_5260_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_){
_start:
{
lean_object* v___x_5267_; lean_object* v_firstEqnName_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
v___x_5267_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5261_, 3);
v_firstEqnName_5268_ = l_Lean_Name_str___override(v_matchDeclName_5261_, v___x_5267_);
v___x_5269_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5269_, 0, v_matchDeclName_5261_);
v___x_5270_ = l_Lean_Meta_realizeConst(v_matchDeclName_5261_, v_firstEqnName_5268_, v___x_5269_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_);
if (lean_obj_tag(v___x_5270_) == 0)
{
lean_object* v___x_5271_; lean_object* v_a_5272_; 
lean_dec_ref_known(v___x_5270_, 1);
lean_inc(v_matchDeclName_5261_);
v___x_5271_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_5261_, v_a_5265_);
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
lean_inc(v_a_5272_);
lean_dec_ref(v___x_5271_);
if (lean_obj_tag(v_a_5272_) == 1)
{
lean_object* v_val_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; 
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
v_val_5273_ = lean_ctor_get(v_a_5272_, 0);
lean_inc(v_val_5273_);
lean_dec_ref_known(v_a_5272_, 1);
v___x_5274_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5273_);
lean_dec(v_val_5273_);
v___x_5275_ = lean_unsigned_to_nat(0u);
v___x_5276_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5277_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5274_, v_matchDeclName_5261_, v___x_5275_, v___x_5276_);
lean_dec(v___x_5274_);
return v___x_5277_;
}
else
{
lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
lean_dec(v_a_5272_);
v___x_5278_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5279_ = l_Lean_MessageData_ofName(v_matchDeclName_5261_);
v___x_5280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5278_);
lean_ctor_set(v___x_5280_, 1, v___x_5279_);
v___x_5281_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5282_, 0, v___x_5280_);
lean_ctor_set(v___x_5282_, 1, v___x_5281_);
v___x_5283_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5282_, v_a_5262_, v_a_5263_, v_a_5264_, v_a_5265_);
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
return v___x_5283_;
}
}
else
{
lean_object* v_a_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5291_; 
lean_dec(v_a_5265_);
lean_dec_ref(v_a_5264_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec(v_matchDeclName_5261_);
v_a_5284_ = lean_ctor_get(v___x_5270_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5270_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5286_ = v___x_5270_;
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_a_5284_);
lean_dec(v___x_5270_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5291_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5289_; 
if (v_isShared_5287_ == 0)
{
v___x_5289_ = v___x_5286_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
v___x_5289_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
return v___x_5289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_){
_start:
{
lean_object* v_res_5298_; 
v_res_5298_ = lean_get_congr_match_equations_for(v_matchDeclName_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5299_, lean_object* v_matchDeclName_5300_, lean_object* v_inst_5301_, lean_object* v_R_5302_, lean_object* v_a_5303_, lean_object* v_b_5304_, lean_object* v_c_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_){
_start:
{
lean_object* v___x_5311_; 
v___x_5311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5299_, v_matchDeclName_5300_, v_a_5303_, v_b_5304_);
return v___x_5311_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5312_, lean_object* v_matchDeclName_5313_, lean_object* v_inst_5314_, lean_object* v_R_5315_, lean_object* v_a_5316_, lean_object* v_b_5317_, lean_object* v_c_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v_res_5324_; 
v_res_5324_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5312_, v_matchDeclName_5313_, v_inst_5314_, v_R_5315_, v_a_5316_, v_b_5317_, v_c_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec(v_upperBound_5312_);
return v_res_5324_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; 
v___x_5375_ = lean_unsigned_to_nat(3248161880u);
v___x_5376_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5377_ = l_Lean_Name_num___override(v___x_5376_, v___x_5375_);
return v___x_5377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; 
v___x_5379_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5380_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5381_ = l_Lean_Name_str___override(v___x_5380_, v___x_5379_);
return v___x_5381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; 
v___x_5383_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5384_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5385_ = l_Lean_Name_str___override(v___x_5384_, v___x_5383_);
return v___x_5385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5386_ = lean_unsigned_to_nat(2u);
v___x_5387_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5388_ = l_Lean_Name_num___override(v___x_5387_, v___x_5386_);
return v___x_5388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5390_; uint8_t v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5390_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5391_ = 0;
v___x_5392_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5393_ = l_Lean_registerTraceClass(v___x_5390_, v___x_5391_, v___x_5392_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5396_, lean_object* v_n_5397_){
_start:
{
if (lean_obj_tag(v_n_5397_) == 1)
{
lean_object* v_pre_5398_; lean_object* v_str_5399_; uint8_t v___y_5401_; uint8_t v___x_5407_; 
v_pre_5398_ = lean_ctor_get(v_n_5397_, 0);
lean_inc(v_pre_5398_);
v_str_5399_ = lean_ctor_get(v_n_5397_, 1);
lean_inc_ref_n(v_str_5399_, 2);
lean_dec_ref_known(v_n_5397_, 2);
v___x_5407_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5399_);
if (v___x_5407_ == 0)
{
lean_object* v___x_5408_; uint8_t v___x_5409_; 
v___x_5408_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5409_ = lean_string_dec_eq(v_str_5399_, v___x_5408_);
lean_dec_ref(v_str_5399_);
v___y_5401_ = v___x_5409_;
goto v___jp_5400_;
}
else
{
lean_dec_ref(v_str_5399_);
v___y_5401_ = v___x_5407_;
goto v___jp_5400_;
}
v___jp_5400_:
{
if (v___y_5401_ == 0)
{
lean_object* v___x_5402_; 
lean_dec(v_pre_5398_);
lean_dec_ref(v_env_5396_);
v___x_5402_ = lean_box(0);
return v___x_5402_;
}
else
{
lean_object* v___x_5403_; 
v___x_5403_ = l_Lean_privateToUserName_x3f(v_pre_5398_);
if (lean_obj_tag(v___x_5403_) == 0)
{
lean_dec_ref(v_env_5396_);
return v___x_5403_;
}
else
{
lean_object* v_val_5404_; uint8_t v___x_5405_; 
v_val_5404_ = lean_ctor_get(v___x_5403_, 0);
lean_inc(v_val_5404_);
v___x_5405_ = l_Lean_Meta_isMatcherCore(v_env_5396_, v_val_5404_);
if (v___x_5405_ == 0)
{
lean_object* v___x_5406_; 
lean_dec_ref_known(v___x_5403_, 1);
v___x_5406_ = lean_box(0);
return v___x_5406_;
}
else
{
return v___x_5403_;
}
}
}
}
}
else
{
lean_object* v___x_5410_; 
lean_dec(v_n_5397_);
lean_dec_ref(v_env_5396_);
v___x_5410_ = lean_box(0);
return v___x_5410_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5411_, lean_object* v_x2_5412_){
_start:
{
lean_object* v___x_5413_; 
v___x_5413_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5411_, v_x2_5412_);
if (lean_obj_tag(v___x_5413_) == 0)
{
uint8_t v___x_5414_; 
v___x_5414_ = 0;
return v___x_5414_;
}
else
{
uint8_t v___x_5415_; 
lean_dec_ref_known(v___x_5413_, 1);
v___x_5415_ = 1;
return v___x_5415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5416_, lean_object* v_x2_5417_){
_start:
{
uint8_t v_res_5418_; lean_object* v_r_5419_; 
v_res_5418_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5416_, v_x2_5417_);
v_r_5419_ = lean_box(v_res_5418_);
return v_r_5419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5422_; lean_object* v___x_5423_; 
v___f_5422_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5423_ = l_Lean_registerReservedNamePredicate(v___f_5422_);
return v___x_5423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5424_){
_start:
{
lean_object* v_res_5425_; 
v_res_5425_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5425_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5432_; uint64_t v___x_5433_; 
v___x_5432_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5433_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5432_);
return v___x_5433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; 
v___x_5434_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5435_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5436_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5436_, 0, v___x_5435_);
lean_ctor_set_uint64(v___x_5436_, sizeof(void*)*1, v___x_5434_);
return v___x_5436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; 
v___x_5439_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5440_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5441_ = lean_unsigned_to_nat(0u);
v___x_5442_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5442_, 0, v___x_5441_);
lean_ctor_set(v___x_5442_, 1, v___x_5441_);
lean_ctor_set(v___x_5442_, 2, v___x_5441_);
lean_ctor_set(v___x_5442_, 3, v___x_5441_);
lean_ctor_set(v___x_5442_, 4, v___x_5440_);
lean_ctor_set(v___x_5442_, 5, v___x_5440_);
lean_ctor_set(v___x_5442_, 6, v___x_5440_);
lean_ctor_set(v___x_5442_, 7, v___x_5440_);
lean_ctor_set(v___x_5442_, 8, v___x_5440_);
lean_ctor_set(v___x_5442_, 9, v___x_5440_);
lean_ctor_set(v___x_5442_, 10, v___x_5440_);
lean_ctor_set(v___x_5442_, 11, v___x_5439_);
return v___x_5442_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5443_; lean_object* v___x_5444_; 
v___x_5443_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5444_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5444_, 0, v___x_5443_);
lean_ctor_set(v___x_5444_, 1, v___x_5443_);
lean_ctor_set(v___x_5444_, 2, v___x_5443_);
lean_ctor_set(v___x_5444_, 3, v___x_5443_);
lean_ctor_set(v___x_5444_, 4, v___x_5443_);
lean_ctor_set(v___x_5444_, 5, v___x_5443_);
return v___x_5444_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5445_; lean_object* v___x_5446_; 
v___x_5445_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5446_, 0, v___x_5445_);
lean_ctor_set(v___x_5446_, 1, v___x_5445_);
lean_ctor_set(v___x_5446_, 2, v___x_5445_);
lean_ctor_set(v___x_5446_, 3, v___x_5445_);
lean_ctor_set(v___x_5446_, 4, v___x_5445_);
return v___x_5446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5447_, lean_object* v_name_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v___x_5452_; lean_object* v_env_5453_; lean_object* v___x_5454_; 
v___x_5452_ = lean_st_ref_get(v___y_5450_);
v_env_5453_ = lean_ctor_get(v___x_5452_, 0);
lean_inc_ref(v_env_5453_);
lean_dec(v___x_5452_);
v___x_5454_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5453_, v_name_5448_);
if (lean_obj_tag(v___x_5454_) == 1)
{
lean_object* v_val_5455_; uint8_t v___x_5456_; uint8_t v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; 
v_val_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_val_5455_);
lean_dec_ref_known(v___x_5454_, 1);
v___x_5456_ = 0;
v___x_5457_ = 1;
v___x_5458_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5459_ = lean_unsigned_to_nat(0u);
v___x_5460_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5461_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5462_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5463_ = lean_box(0);
lean_inc(v___x_5447_);
v___x_5464_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5464_, 0, v___x_5458_);
lean_ctor_set(v___x_5464_, 1, v___x_5447_);
lean_ctor_set(v___x_5464_, 2, v___x_5461_);
lean_ctor_set(v___x_5464_, 3, v___x_5462_);
lean_ctor_set(v___x_5464_, 4, v___x_5463_);
lean_ctor_set(v___x_5464_, 5, v___x_5459_);
lean_ctor_set(v___x_5464_, 6, v___x_5463_);
lean_ctor_set_uint8(v___x_5464_, sizeof(void*)*7, v___x_5456_);
lean_ctor_set_uint8(v___x_5464_, sizeof(void*)*7 + 1, v___x_5456_);
lean_ctor_set_uint8(v___x_5464_, sizeof(void*)*7 + 2, v___x_5456_);
lean_ctor_set_uint8(v___x_5464_, sizeof(void*)*7 + 3, v___x_5457_);
v___x_5465_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5466_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5467_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5468_, 0, v___x_5465_);
lean_ctor_set(v___x_5468_, 1, v___x_5466_);
lean_ctor_set(v___x_5468_, 2, v___x_5447_);
lean_ctor_set(v___x_5468_, 3, v___x_5460_);
lean_ctor_set(v___x_5468_, 4, v___x_5467_);
v___x_5469_ = lean_st_mk_ref(v___x_5468_);
lean_inc(v___y_5450_);
lean_inc_ref(v___y_5449_);
lean_inc(v___x_5469_);
v___x_5470_ = lean_get_match_equations_for(v_val_5455_, v___x_5464_, v___x_5469_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5470_) == 0)
{
lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5479_; 
v_isSharedCheck_5479_ = !lean_is_exclusive(v___x_5470_);
if (v_isSharedCheck_5479_ == 0)
{
lean_object* v_unused_5480_; 
v_unused_5480_ = lean_ctor_get(v___x_5470_, 0);
lean_dec(v_unused_5480_);
v___x_5472_ = v___x_5470_;
v_isShared_5473_ = v_isSharedCheck_5479_;
goto v_resetjp_5471_;
}
else
{
lean_dec(v___x_5470_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5479_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5477_; 
v___x_5474_ = lean_st_ref_get(v___x_5469_);
lean_dec(v___x_5469_);
lean_dec(v___x_5474_);
v___x_5475_ = lean_box(v___x_5457_);
if (v_isShared_5473_ == 0)
{
lean_ctor_set(v___x_5472_, 0, v___x_5475_);
v___x_5477_ = v___x_5472_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v___x_5475_);
v___x_5477_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
return v___x_5477_;
}
}
}
else
{
lean_dec(v___x_5469_);
if (lean_obj_tag(v___x_5470_) == 0)
{
lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5488_; 
v_isSharedCheck_5488_ = !lean_is_exclusive(v___x_5470_);
if (v_isSharedCheck_5488_ == 0)
{
lean_object* v_unused_5489_; 
v_unused_5489_ = lean_ctor_get(v___x_5470_, 0);
lean_dec(v_unused_5489_);
v___x_5482_ = v___x_5470_;
v_isShared_5483_ = v_isSharedCheck_5488_;
goto v_resetjp_5481_;
}
else
{
lean_dec(v___x_5470_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5488_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5484_; lean_object* v___x_5486_; 
v___x_5484_ = lean_box(v___x_5457_);
if (v_isShared_5483_ == 0)
{
lean_ctor_set_tag(v___x_5482_, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5484_);
v___x_5486_ = v___x_5482_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v___x_5484_);
v___x_5486_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
return v___x_5486_;
}
}
}
else
{
lean_object* v_a_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5497_; 
v_a_5490_ = lean_ctor_get(v___x_5470_, 0);
v_isSharedCheck_5497_ = !lean_is_exclusive(v___x_5470_);
if (v_isSharedCheck_5497_ == 0)
{
v___x_5492_ = v___x_5470_;
v_isShared_5493_ = v_isSharedCheck_5497_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_a_5490_);
lean_dec(v___x_5470_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5497_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v___x_5495_; 
if (v_isShared_5493_ == 0)
{
v___x_5495_ = v___x_5492_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v_a_5490_);
v___x_5495_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5494_;
}
v_reusejp_5494_:
{
return v___x_5495_;
}
}
}
}
}
else
{
uint8_t v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; 
lean_dec(v___x_5454_);
lean_dec(v___x_5447_);
v___x_5498_ = 0;
v___x_5499_ = lean_box(v___x_5498_);
v___x_5500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5500_, 0, v___x_5499_);
return v___x_5500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5501_, lean_object* v_name_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_){
_start:
{
lean_object* v_res_5506_; 
v_res_5506_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5501_, v_name_5502_, v___y_5503_, v___y_5504_);
lean_dec(v___y_5504_);
lean_dec_ref(v___y_5503_);
return v_res_5506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5510_; lean_object* v___x_5511_; 
v___f_5510_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5511_ = l_Lean_registerReservedNameAction(v___f_5510_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5512_){
_start:
{
lean_object* v_res_5513_; 
v_res_5513_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5514_, lean_object* v_n_5515_){
_start:
{
if (lean_obj_tag(v_n_5515_) == 1)
{
lean_object* v_pre_5516_; lean_object* v_str_5517_; uint8_t v___x_5518_; 
v_pre_5516_ = lean_ctor_get(v_n_5515_, 0);
lean_inc(v_pre_5516_);
v_str_5517_ = lean_ctor_get(v_n_5515_, 1);
lean_inc_ref(v_str_5517_);
lean_dec_ref_known(v_n_5515_, 2);
v___x_5518_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5517_);
if (v___x_5518_ == 0)
{
lean_object* v___x_5519_; 
lean_dec(v_pre_5516_);
lean_dec_ref(v_env_5514_);
v___x_5519_ = lean_box(0);
return v___x_5519_;
}
else
{
uint8_t v___x_5520_; 
lean_inc(v_pre_5516_);
v___x_5520_ = l_Lean_Meta_isMatcherCore(v_env_5514_, v_pre_5516_);
if (v___x_5520_ == 0)
{
lean_object* v___x_5521_; 
lean_dec(v_pre_5516_);
v___x_5521_ = lean_box(0);
return v___x_5521_;
}
else
{
lean_object* v___x_5522_; 
v___x_5522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5522_, 0, v_pre_5516_);
return v___x_5522_;
}
}
}
else
{
lean_object* v___x_5523_; 
lean_dec(v_n_5515_);
lean_dec_ref(v_env_5514_);
v___x_5523_ = lean_box(0);
return v___x_5523_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5524_, lean_object* v_x2_5525_){
_start:
{
lean_object* v___x_5526_; 
v___x_5526_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5524_, v_x2_5525_);
if (lean_obj_tag(v___x_5526_) == 0)
{
uint8_t v___x_5527_; 
v___x_5527_ = 0;
return v___x_5527_;
}
else
{
uint8_t v___x_5528_; 
lean_dec_ref_known(v___x_5526_, 1);
v___x_5528_ = 1;
return v___x_5528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5529_, lean_object* v_x2_5530_){
_start:
{
uint8_t v_res_5531_; lean_object* v_r_5532_; 
v_res_5531_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5529_, v_x2_5530_);
v_r_5532_ = lean_box(v_res_5531_);
return v_r_5532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5535_; lean_object* v___x_5536_; 
v___f_5535_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5536_ = l_Lean_registerReservedNamePredicate(v___f_5535_);
return v___x_5536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5537_){
_start:
{
lean_object* v_res_5538_; 
v_res_5538_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5539_, lean_object* v_name_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_){
_start:
{
lean_object* v___x_5544_; lean_object* v_env_5545_; lean_object* v___x_5546_; 
v___x_5544_ = lean_st_ref_get(v___y_5542_);
v_env_5545_ = lean_ctor_get(v___x_5544_, 0);
lean_inc_ref(v_env_5545_);
lean_dec(v___x_5544_);
v___x_5546_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5545_, v_name_5540_);
if (lean_obj_tag(v___x_5546_) == 1)
{
lean_object* v_val_5547_; uint8_t v___x_5548_; uint8_t v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; 
v_val_5547_ = lean_ctor_get(v___x_5546_, 0);
lean_inc(v_val_5547_);
lean_dec_ref_known(v___x_5546_, 1);
v___x_5548_ = 0;
v___x_5549_ = 1;
v___x_5550_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5551_ = lean_unsigned_to_nat(32u);
v___x_5552_ = lean_mk_empty_array_with_capacity(v___x_5551_);
lean_dec_ref(v___x_5552_);
v___x_5553_ = lean_unsigned_to_nat(0u);
v___x_5554_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5555_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5556_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5557_ = lean_box(0);
lean_inc(v___x_5539_);
v___x_5558_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5558_, 0, v___x_5550_);
lean_ctor_set(v___x_5558_, 1, v___x_5539_);
lean_ctor_set(v___x_5558_, 2, v___x_5555_);
lean_ctor_set(v___x_5558_, 3, v___x_5556_);
lean_ctor_set(v___x_5558_, 4, v___x_5557_);
lean_ctor_set(v___x_5558_, 5, v___x_5553_);
lean_ctor_set(v___x_5558_, 6, v___x_5557_);
lean_ctor_set_uint8(v___x_5558_, sizeof(void*)*7, v___x_5548_);
lean_ctor_set_uint8(v___x_5558_, sizeof(void*)*7 + 1, v___x_5548_);
lean_ctor_set_uint8(v___x_5558_, sizeof(void*)*7 + 2, v___x_5548_);
lean_ctor_set_uint8(v___x_5558_, sizeof(void*)*7 + 3, v___x_5549_);
v___x_5559_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5560_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5561_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5562_, 0, v___x_5559_);
lean_ctor_set(v___x_5562_, 1, v___x_5560_);
lean_ctor_set(v___x_5562_, 2, v___x_5539_);
lean_ctor_set(v___x_5562_, 3, v___x_5554_);
lean_ctor_set(v___x_5562_, 4, v___x_5561_);
v___x_5563_ = lean_st_mk_ref(v___x_5562_);
lean_inc(v___y_5542_);
lean_inc_ref(v___y_5541_);
lean_inc(v___x_5563_);
v___x_5564_ = lean_get_congr_match_equations_for(v_val_5547_, v___x_5558_, v___x_5563_, v___y_5541_, v___y_5542_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5573_; 
v_isSharedCheck_5573_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5573_ == 0)
{
lean_object* v_unused_5574_; 
v_unused_5574_ = lean_ctor_get(v___x_5564_, 0);
lean_dec(v_unused_5574_);
v___x_5566_ = v___x_5564_;
v_isShared_5567_ = v_isSharedCheck_5573_;
goto v_resetjp_5565_;
}
else
{
lean_dec(v___x_5564_);
v___x_5566_ = lean_box(0);
v_isShared_5567_ = v_isSharedCheck_5573_;
goto v_resetjp_5565_;
}
v_resetjp_5565_:
{
lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5571_; 
v___x_5568_ = lean_st_ref_get(v___x_5563_);
lean_dec(v___x_5563_);
lean_dec(v___x_5568_);
v___x_5569_ = lean_box(v___x_5549_);
if (v_isShared_5567_ == 0)
{
lean_ctor_set(v___x_5566_, 0, v___x_5569_);
v___x_5571_ = v___x_5566_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v___x_5569_);
v___x_5571_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
return v___x_5571_;
}
}
}
else
{
lean_dec(v___x_5563_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5582_; 
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5582_ == 0)
{
lean_object* v_unused_5583_; 
v_unused_5583_ = lean_ctor_get(v___x_5564_, 0);
lean_dec(v_unused_5583_);
v___x_5576_ = v___x_5564_;
v_isShared_5577_ = v_isSharedCheck_5582_;
goto v_resetjp_5575_;
}
else
{
lean_dec(v___x_5564_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5582_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5578_; lean_object* v___x_5580_; 
v___x_5578_ = lean_box(v___x_5549_);
if (v_isShared_5577_ == 0)
{
lean_ctor_set_tag(v___x_5576_, 0);
lean_ctor_set(v___x_5576_, 0, v___x_5578_);
v___x_5580_ = v___x_5576_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v___x_5578_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
else
{
lean_object* v_a_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5591_; 
v_a_5584_ = lean_ctor_get(v___x_5564_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5586_ = v___x_5564_;
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_a_5584_);
lean_dec(v___x_5564_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5589_; 
if (v_isShared_5587_ == 0)
{
v___x_5589_ = v___x_5586_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_a_5584_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
return v___x_5589_;
}
}
}
}
}
else
{
uint8_t v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; 
lean_dec(v___x_5546_);
lean_dec(v___x_5539_);
v___x_5592_ = 0;
v___x_5593_ = lean_box(v___x_5592_);
v___x_5594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5594_, 0, v___x_5593_);
return v___x_5594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5595_, lean_object* v_name_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_){
_start:
{
lean_object* v_res_5600_; 
v_res_5600_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5595_, v_name_5596_, v___y_5597_, v___y_5598_);
lean_dec(v___y_5598_);
lean_dec_ref(v___y_5597_);
return v_res_5600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5604_; lean_object* v___x_5605_; 
v___f_5604_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5605_ = l_Lean_registerReservedNameAction(v___f_5604_);
return v___x_5605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5606_){
_start:
{
lean_object* v_res_5607_; 
v_res_5607_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5607_;
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
