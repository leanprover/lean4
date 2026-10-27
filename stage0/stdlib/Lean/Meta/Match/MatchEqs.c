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
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_MVarId_heqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_casesOnStuckLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpIfTarget(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_whnfCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6_value;
static const lean_array_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(16) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpIf failed"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchEqs"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(250, 1, 225, 180, 135, 246, 184, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(142, 18, 82, 91, 15, 164, 75, 57)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "proveCondEqThm.go "};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__19;
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
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_value)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6_value)}};
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
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__0_value)}};
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
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 7, 62, 187, 210, 164, 110, 59)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "MatchEqs"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__7_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 108, 58, 118, 141, 255, 162, 173)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__7_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__7_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__8_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__7_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(89, 143, 139, 150, 26, 209, 69, 100)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__8_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__8_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__9_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__8_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 19, 205, 36, 112, 108, 199, 19)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__9_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__9_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__10_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__9_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(64, 18, 131, 232, 118, 16, 218, 224)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__10_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__10_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__11_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__10_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(149, 136, 49, 102, 95, 126, 100, 58)}};
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
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__17_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__16_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(140, 51, 94, 245, 163, 3, 190, 52)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__17_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__17_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__18_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__17_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(81, 118, 58, 117, 110, 34, 2, 117)}};
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
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1389_ = l_Lean_stringToMessageData(v___x_1388_);
return v___x_1389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17(void){
_start:
{
lean_object* v_cls_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v_cls_1400_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
v___x_1401_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16));
v___x_1402_ = l_Lean_Name_append(v___x_1401_, v_cls_1400_);
return v___x_1402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__19(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18));
v___x_1405_ = l_Lean_stringToMessageData(v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1406_, lean_object* v_mvarId_1407_, lean_object* v_depth_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v_a_1419_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v_a_1435_; lean_object* v___y_1492_; lean_object* v___y_1493_; uint8_t v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v_a_1499_; lean_object* v___y_1537_; lean_object* v___y_1538_; uint8_t v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v_toCold_1725_; lean_object* v_currRecDepth_1726_; lean_object* v_ref_1727_; uint16_t v_optionFlags_1728_; uint8_t v_suppressElabErrors_1729_; uint8_t v_checkDeprecated_1730_; uint8_t v_isRecordingDeps_1731_; lean_object* v_options_1732_; lean_object* v_maxRecDepth_1733_; lean_object* v_inheritedTraceOptions_1734_; lean_object* v_cls_1735_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_toCold_1725_ = lean_ctor_get(v_a_1411_, 0);
v_currRecDepth_1726_ = lean_ctor_get(v_a_1411_, 1);
v_ref_1727_ = lean_ctor_get(v_a_1411_, 2);
v_optionFlags_1728_ = lean_ctor_get_uint16(v_a_1411_, sizeof(void*)*3);
v_suppressElabErrors_1729_ = lean_ctor_get_uint8(v_a_1411_, sizeof(void*)*3 + 2);
v_checkDeprecated_1730_ = lean_ctor_get_uint8(v_a_1411_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1731_ = lean_ctor_get_uint8(v_a_1411_, sizeof(void*)*3 + 4);
v_options_1732_ = lean_ctor_get(v_toCold_1725_, 2);
v_maxRecDepth_1733_ = lean_ctor_get(v_toCold_1725_, 3);
v_inheritedTraceOptions_1734_ = lean_ctor_get(v_toCold_1725_, 11);
v_cls_1735_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_nat_dec_eq(v_maxRecDepth_1733_, v___x_1747_);
if (v___x_1748_ == 0)
{
uint8_t v___x_1749_; 
v___x_1749_ = lean_nat_dec_eq(v_currRecDepth_1726_, v_maxRecDepth_1733_);
if (v___x_1749_ == 0)
{
goto v___jp_1736_;
}
else
{
lean_object* v___x_1750_; 
lean_dec(v_mvarId_1407_);
lean_dec(v_matchDeclName_1406_);
lean_inc(v_ref_1727_);
v___x_1750_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1727_);
return v___x_1750_;
}
}
else
{
goto v___jp_1736_;
}
v___jp_1414_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = lean_array_get_size(v_a_1419_);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_nat_dec_lt(v___x_1420_, v___x_1421_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; 
lean_dec_ref(v_a_1419_);
lean_dec_ref(v___y_1417_);
lean_dec(v_matchDeclName_1406_);
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
return v___x_1424_;
}
else
{
size_t v___x_1425_; size_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = ((size_t)0ULL);
v___x_1426_ = lean_usize_of_nat(v___x_1421_);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1408_, v_matchDeclName_1406_, v_a_1419_, v___x_1425_, v___x_1426_, v___x_1422_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec_ref(v_a_1419_);
return v___x_1427_;
}
}
v___jp_1428_:
{
uint8_t v___x_1436_; 
v___x_1436_ = l_Lean_Exception_isInterrupt(v_a_1435_);
if (v___x_1436_ == 0)
{
uint8_t v___x_1437_; 
lean_inc_ref(v_a_1435_);
v___x_1437_ = l_Lean_Exception_isRuntime(v_a_1435_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; 
lean_dec_ref(v_a_1435_);
v___x_1438_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1434_, v___y_1431_, v___y_1433_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v___x_1439_; 
lean_dec_ref_known(v___x_1438_, 1);
v___x_1439_ = l_Lean_Meta_saveState___redArg(v___y_1431_, v___y_1433_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
lean_inc(v___y_1429_);
v___x_1441_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; 
lean_dec(v_a_1440_);
lean_dec(v___y_1429_);
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___y_1415_ = v___y_1430_;
v___y_1416_ = v___y_1431_;
v___y_1417_ = v___y_1432_;
v___y_1418_ = v___y_1433_;
v_a_1419_ = v_a_1442_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1480_; 
v_a_1443_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1445_ = v___x_1441_;
v_isShared_1446_ = v_isSharedCheck_1480_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1441_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1480_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
uint8_t v___x_1447_; 
v___x_1447_ = l_Lean_Exception_isInterrupt(v_a_1443_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; 
lean_inc(v_a_1443_);
v___x_1448_ = l_Lean_Exception_isRuntime(v_a_1443_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_del_object(v___x_1445_);
lean_dec(v_a_1443_);
v___x_1449_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1440_, v___y_1431_, v___y_1433_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1472_; 
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v___x_1449_, 0);
lean_dec(v_unused_1473_);
v___x_1451_ = v___x_1449_;
v_isShared_1452_ = v_isSharedCheck_1472_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v___x_1449_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1472_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1453_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1406_);
v___x_1454_ = l_Lean_MessageData_ofName(v_matchDeclName_1406_);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set_tag(v___x_1451_, 1);
lean_ctor_set(v___x_1451_, 0, v___y_1429_);
v___x_1459_ = v___x_1451_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___y_1429_);
v___x_1459_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1457_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1460_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___y_1415_ = v___y_1430_;
v___y_1416_ = v___y_1431_;
v___y_1417_ = v___y_1432_;
v___y_1418_ = v___y_1433_;
v_a_1419_ = v_a_1462_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v___y_1432_);
lean_dec(v_matchDeclName_1406_);
v_a_1463_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1461_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1461_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1429_);
lean_dec(v_matchDeclName_1406_);
return v___x_1449_;
}
}
else
{
lean_object* v___x_1475_; 
lean_dec(v_a_1440_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1429_);
lean_dec(v_matchDeclName_1406_);
if (v_isShared_1446_ == 0)
{
v___x_1475_ = v___x_1445_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1443_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
lean_object* v___x_1478_; 
lean_dec(v_a_1440_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1429_);
lean_dec(v_matchDeclName_1406_);
if (v_isShared_1446_ == 0)
{
v___x_1478_ = v___x_1445_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1443_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1429_);
lean_dec(v_matchDeclName_1406_);
v_a_1481_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1439_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1439_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1429_);
lean_dec(v_matchDeclName_1406_);
return v___x_1438_;
}
}
else
{
lean_object* v___x_1489_; 
lean_dec_ref(v___y_1434_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1429_);
lean_dec(v_matchDeclName_1406_);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_a_1435_);
return v___x_1489_;
}
}
else
{
lean_object* v___x_1490_; 
lean_dec_ref(v___y_1434_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1429_);
lean_dec(v_matchDeclName_1406_);
v___x_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_a_1435_);
return v___x_1490_;
}
}
v___jp_1491_:
{
uint8_t v___x_1500_; 
v___x_1500_ = l_Lean_Exception_isInterrupt(v_a_1499_);
if (v___x_1500_ == 0)
{
uint8_t v___x_1501_; 
lean_inc_ref(v_a_1499_);
v___x_1501_ = l_Lean_Exception_isRuntime(v_a_1499_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_dec_ref(v_a_1499_);
v___x_1502_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1497_, v___y_1495_, v___y_1498_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref_known(v___x_1502_, 1);
v___x_1503_ = lean_box(0);
v___x_1504_ = l_Lean_Meta_saveState___redArg(v___y_1495_, v___y_1498_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1506_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
lean_inc(v___y_1492_);
v___x_1506_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1492_, v___x_1503_, v___y_1494_, v___y_1493_, v___y_1495_, v___y_1496_, v___y_1498_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
if (lean_obj_tag(v_a_1507_) == 1)
{
lean_object* v_val_1508_; lean_object* v_fst_1509_; lean_object* v_snd_1510_; lean_object* v_mvarId_1511_; lean_object* v_fvarId_1512_; lean_object* v___x_1513_; 
v_val_1508_ = lean_ctor_get(v_a_1507_, 0);
lean_inc(v_val_1508_);
lean_dec_ref_known(v_a_1507_, 1);
v_fst_1509_ = lean_ctor_get(v_val_1508_, 0);
lean_inc(v_fst_1509_);
v_snd_1510_ = lean_ctor_get(v_val_1508_, 1);
lean_inc(v_snd_1510_);
lean_dec(v_val_1508_);
v_mvarId_1511_ = lean_ctor_get(v_fst_1509_, 0);
lean_inc(v_mvarId_1511_);
v_fvarId_1512_ = lean_ctor_get(v_fst_1509_, 1);
lean_inc(v_fvarId_1512_);
lean_dec(v_fst_1509_);
v___x_1513_ = l_Lean_Meta_trySubst(v_mvarId_1511_, v_fvarId_1512_, v___y_1493_, v___y_1495_, v___y_1496_, v___y_1498_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v_mvarId_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v_a_1505_);
lean_dec(v___y_1492_);
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v_mvarId_1515_ = lean_ctor_get(v_snd_1510_, 0);
lean_inc(v_mvarId_1515_);
lean_dec(v_snd_1510_);
v___x_1516_ = lean_unsigned_to_nat(2u);
v___x_1517_ = lean_mk_empty_array_with_capacity(v___x_1516_);
v___x_1518_ = lean_array_push(v___x_1517_, v_a_1514_);
v___x_1519_ = lean_array_push(v___x_1518_, v_mvarId_1515_);
v___y_1415_ = v___y_1493_;
v___y_1416_ = v___y_1495_;
v___y_1417_ = v___y_1496_;
v___y_1418_ = v___y_1498_;
v_a_1419_ = v___x_1519_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1520_; 
lean_dec(v_snd_1510_);
v_a_1520_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1513_, 1);
v___y_1429_ = v___y_1492_;
v___y_1430_ = v___y_1493_;
v___y_1431_ = v___y_1495_;
v___y_1432_ = v___y_1496_;
v___y_1433_ = v___y_1498_;
v___y_1434_ = v_a_1505_;
v_a_1435_ = v_a_1520_;
goto v___jp_1428_;
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec(v_a_1507_);
v___x_1521_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1522_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1521_, v___y_1493_, v___y_1495_, v___y_1496_, v___y_1498_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; 
lean_dec(v_a_1505_);
lean_dec(v___y_1492_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___y_1415_ = v___y_1493_;
v___y_1416_ = v___y_1495_;
v___y_1417_ = v___y_1496_;
v___y_1418_ = v___y_1498_;
v_a_1419_ = v_a_1523_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1524_; 
v_a_1524_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1522_, 1);
v___y_1429_ = v___y_1492_;
v___y_1430_ = v___y_1493_;
v___y_1431_ = v___y_1495_;
v___y_1432_ = v___y_1496_;
v___y_1433_ = v___y_1498_;
v___y_1434_ = v_a_1505_;
v_a_1435_ = v_a_1524_;
goto v___jp_1428_;
}
}
}
else
{
lean_object* v_a_1525_; 
v_a_1525_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1506_, 1);
v___y_1429_ = v___y_1492_;
v___y_1430_ = v___y_1493_;
v___y_1431_ = v___y_1495_;
v___y_1432_ = v___y_1496_;
v___y_1433_ = v___y_1498_;
v___y_1434_ = v_a_1505_;
v_a_1435_ = v_a_1525_;
goto v___jp_1428_;
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1492_);
lean_dec(v_matchDeclName_1406_);
v_a_1526_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1504_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1504_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1492_);
lean_dec(v_matchDeclName_1406_);
return v___x_1502_;
}
}
else
{
lean_object* v___x_1534_; 
lean_dec_ref(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1492_);
lean_dec(v_matchDeclName_1406_);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_a_1499_);
return v___x_1534_;
}
}
else
{
lean_object* v___x_1535_; 
lean_dec_ref(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1492_);
lean_dec(v_matchDeclName_1406_);
v___x_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1499_);
return v___x_1535_;
}
}
v___jp_1536_:
{
if (lean_obj_tag(v___y_1544_) == 0)
{
lean_object* v_a_1545_; 
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1537_);
v_a_1545_ = lean_ctor_get(v___y_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___y_1544_, 1);
v___y_1415_ = v___y_1538_;
v___y_1416_ = v___y_1540_;
v___y_1417_ = v___y_1542_;
v___y_1418_ = v___y_1543_;
v_a_1419_ = v_a_1545_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1546_; 
v_a_1546_ = lean_ctor_get(v___y_1544_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___y_1544_, 1);
v___y_1492_ = v___y_1537_;
v___y_1493_ = v___y_1538_;
v___y_1494_ = v___y_1539_;
v___y_1495_ = v___y_1540_;
v___y_1496_ = v___y_1542_;
v___y_1497_ = v___y_1541_;
v___y_1498_ = v___y_1543_;
v_a_1499_ = v_a_1546_;
goto v___jp_1491_;
}
}
v___jp_1547_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1553_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1407_, v___x_1552_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = 1;
v___x_1556_ = l_Lean_Meta_saveState___redArg(v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
lean_inc(v_a_1554_);
v___x_1558_ = l_Lean_MVarId_refl(v_a_1554_, v___x_1555_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1559_; 
lean_dec_ref_known(v___x_1558_, 1);
lean_dec(v_a_1557_);
lean_dec(v_a_1554_);
v___x_1559_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7));
v___y_1415_ = v___y_1548_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1550_;
v___y_1418_ = v___y_1551_;
v_a_1419_ = v___x_1559_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1560_; uint8_t v___x_1561_; 
v_a_1560_ = lean_ctor_get(v___x_1558_, 0);
v___x_1561_ = l_Lean_Exception_isInterrupt(v_a_1560_);
if (v___x_1561_ == 0)
{
uint8_t v___x_1562_; 
lean_inc(v_a_1560_);
v___x_1562_ = l_Lean_Exception_isRuntime(v_a_1560_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; 
lean_dec_ref_known(v___x_1558_, 1);
v___x_1563_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1557_, v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec_ref_known(v___x_1563_, 1);
v___x_1564_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_1565_ = l_Lean_Meta_saveState___redArg(v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
lean_inc(v_a_1554_);
v___x_1567_ = l_Lean_MVarId_contradiction(v_a_1554_, v___x_1564_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1568_; 
lean_dec_ref_known(v___x_1567_, 1);
lean_dec(v_a_1566_);
lean_dec(v_a_1554_);
v___x_1568_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7));
v___y_1415_ = v___y_1548_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1550_;
v___y_1418_ = v___y_1551_;
v_a_1419_ = v___x_1568_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1569_; uint8_t v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1567_, 0);
v___x_1570_ = l_Lean_Exception_isInterrupt(v_a_1569_);
if (v___x_1570_ == 0)
{
uint8_t v___x_1571_; 
lean_inc(v_a_1569_);
v___x_1571_ = l_Lean_Exception_isRuntime(v_a_1569_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_dec_ref_known(v___x_1567_, 1);
v___x_1572_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1566_, v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; 
lean_dec_ref_known(v___x_1572_, 1);
v___x_1573_ = l_Lean_Meta_saveState___redArg(v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1575_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
lean_inc(v_a_1554_);
v___x_1575_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_a_1554_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v_a_1574_);
lean_dec(v_a_1554_);
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1577_ = lean_unsigned_to_nat(1u);
v___x_1578_ = lean_mk_empty_array_with_capacity(v___x_1577_);
v___x_1579_ = lean_array_push(v___x_1578_, v_a_1576_);
v___y_1415_ = v___y_1548_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1550_;
v___y_1418_ = v___y_1551_;
v_a_1419_ = v___x_1579_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1692_; 
v_a_1580_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1582_ = v___x_1575_;
v_isShared_1583_ = v_isSharedCheck_1692_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1575_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1692_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
uint8_t v___x_1584_; 
v___x_1584_ = l_Lean_Exception_isInterrupt(v_a_1580_);
if (v___x_1584_ == 0)
{
uint8_t v___x_1585_; 
lean_inc(v_a_1580_);
v___x_1585_ = l_Lean_Exception_isRuntime(v_a_1580_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; 
lean_del_object(v___x_1582_);
lean_dec(v_a_1580_);
v___x_1586_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1574_, v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref_known(v___x_1586_, 1);
v___x_1587_ = l_Lean_Meta_saveState___redArg(v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
lean_inc(v_a_1554_);
v___x_1589_ = l_Lean_Meta_casesOnStuckLHS(v_a_1554_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; 
lean_dec(v_a_1588_);
lean_dec(v_a_1554_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___y_1415_ = v___y_1548_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1550_;
v___y_1418_ = v___y_1551_;
v_a_1419_ = v_a_1590_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1677_; 
v_a_1591_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1593_ = v___x_1589_;
v_isShared_1594_ = v_isSharedCheck_1677_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1589_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1677_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
uint8_t v___x_1595_; 
v___x_1595_ = l_Lean_Exception_isInterrupt(v_a_1591_);
if (v___x_1595_ == 0)
{
uint8_t v___x_1596_; 
lean_inc(v_a_1591_);
v___x_1596_ = l_Lean_Exception_isRuntime(v_a_1591_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; 
lean_del_object(v___x_1593_);
lean_dec(v_a_1591_);
v___x_1597_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1588_, v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v___x_1598_; 
lean_dec_ref_known(v___x_1597_, 1);
v___x_1598_ = l_Lean_Meta_saveState___redArg(v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
lean_inc(v_a_1554_);
v___x_1600_ = l_Lean_Meta_reduceSparseCasesOn(v_a_1554_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; 
lean_dec(v_a_1599_);
lean_dec(v_a_1554_);
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v___y_1415_ = v___y_1548_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1550_;
v___y_1418_ = v___y_1551_;
v_a_1419_ = v_a_1601_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1662_; 
v_a_1602_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1604_ = v___x_1600_;
v_isShared_1605_ = v_isSharedCheck_1662_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1600_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1662_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Lean_Exception_isInterrupt(v_a_1602_);
if (v___x_1606_ == 0)
{
uint8_t v___x_1607_; 
lean_inc(v_a_1602_);
v___x_1607_ = l_Lean_Exception_isRuntime(v_a_1602_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_del_object(v___x_1604_);
lean_dec(v_a_1602_);
v___x_1608_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1599_, v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref_known(v___x_1608_, 1);
v___x_1609_ = l_Lean_Meta_saveState___redArg(v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
lean_inc(v_a_1554_);
v___x_1611_ = l_Lean_Meta_splitSparseCasesOn(v_a_1554_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; 
lean_dec(v_a_1610_);
lean_dec(v_a_1554_);
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___y_1415_ = v___y_1548_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1550_;
v___y_1418_ = v___y_1551_;
v_a_1419_ = v_a_1612_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1647_; 
v_a_1613_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1615_ = v___x_1611_;
v_isShared_1616_ = v_isSharedCheck_1647_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1611_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1647_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
uint8_t v___x_1617_; 
v___x_1617_ = l_Lean_Exception_isInterrupt(v_a_1613_);
if (v___x_1617_ == 0)
{
uint8_t v___x_1618_; 
lean_inc(v_a_1613_);
v___x_1618_ = l_Lean_Exception_isRuntime(v_a_1613_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_del_object(v___x_1615_);
lean_dec(v_a_1613_);
v___x_1619_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1610_, v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v___x_1620_; 
lean_dec_ref_known(v___x_1619_, 1);
v___x_1620_ = l_Lean_Meta_saveState___redArg(v___y_1549_, v___y_1551_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
lean_inc(v_a_1554_);
v___x_1622_ = l_Lean_Meta_simpIfTarget(v_a_1554_, v___x_1555_, v___x_1555_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; uint8_t v___x_1624_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1624_ = l_Lean_instBEqMVarId_beq(v_a_1623_, v_a_1554_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_box(0);
v___x_1626_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1623_, v___x_1625_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
v___y_1537_ = v_a_1554_;
v___y_1538_ = v___y_1548_;
v___y_1539_ = v___x_1555_;
v___y_1540_ = v___y_1549_;
v___y_1541_ = v_a_1621_;
v___y_1542_ = v___y_1550_;
v___y_1543_ = v___y_1551_;
v___y_1544_ = v___x_1626_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10);
v___x_1628_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1627_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1630_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1623_, v_a_1629_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
v___y_1537_ = v_a_1554_;
v___y_1538_ = v___y_1548_;
v___y_1539_ = v___x_1555_;
v___y_1540_ = v___y_1549_;
v___y_1541_ = v_a_1621_;
v___y_1542_ = v___y_1550_;
v___y_1543_ = v___y_1551_;
v___y_1544_ = v___x_1630_;
goto v___jp_1536_;
}
else
{
lean_object* v_a_1631_; 
lean_dec(v_a_1623_);
v_a_1631_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1628_, 1);
v___y_1492_ = v_a_1554_;
v___y_1493_ = v___y_1548_;
v___y_1494_ = v___x_1555_;
v___y_1495_ = v___y_1549_;
v___y_1496_ = v___y_1550_;
v___y_1497_ = v_a_1621_;
v___y_1498_ = v___y_1551_;
v_a_1499_ = v_a_1631_;
goto v___jp_1491_;
}
}
}
else
{
lean_object* v_a_1632_; 
v_a_1632_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1622_, 1);
v___y_1492_ = v_a_1554_;
v___y_1493_ = v___y_1548_;
v___y_1494_ = v___x_1555_;
v___y_1495_ = v___y_1549_;
v___y_1496_ = v___y_1550_;
v___y_1497_ = v_a_1621_;
v___y_1498_ = v___y_1551_;
v_a_1499_ = v_a_1632_;
goto v___jp_1491_;
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
v_a_1633_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1620_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1620_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
return v___x_1619_;
}
}
else
{
lean_object* v___x_1642_; 
lean_dec(v_a_1610_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
if (v_isShared_1616_ == 0)
{
v___x_1642_ = v___x_1615_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1613_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
lean_object* v___x_1645_; 
lean_dec(v_a_1610_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
if (v_isShared_1616_ == 0)
{
v___x_1645_ = v___x_1615_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1613_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
v_a_1648_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1609_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1609_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
return v___x_1608_;
}
}
else
{
lean_object* v___x_1657_; 
lean_dec(v_a_1599_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
if (v_isShared_1605_ == 0)
{
v___x_1657_ = v___x_1604_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1602_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_object* v___x_1660_; 
lean_dec(v_a_1599_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
if (v_isShared_1605_ == 0)
{
v___x_1660_ = v___x_1604_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1602_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
v_a_1663_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1598_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1598_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
return v___x_1597_;
}
}
else
{
lean_object* v___x_1672_; 
lean_dec(v_a_1588_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
if (v_isShared_1594_ == 0)
{
v___x_1672_ = v___x_1593_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1591_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
else
{
lean_object* v___x_1675_; 
lean_dec(v_a_1588_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
if (v_isShared_1594_ == 0)
{
v___x_1675_ = v___x_1593_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1591_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
v_a_1678_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1587_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1587_);
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
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
return v___x_1586_;
}
}
else
{
lean_object* v___x_1687_; 
lean_dec(v_a_1574_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
if (v_isShared_1583_ == 0)
{
v___x_1687_ = v___x_1582_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1580_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
else
{
lean_object* v___x_1690_; 
lean_dec(v_a_1574_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
if (v_isShared_1583_ == 0)
{
v___x_1690_ = v___x_1582_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1580_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
v_a_1693_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1573_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1573_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
return v___x_1572_;
}
}
else
{
lean_dec(v_a_1566_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
return v___x_1567_;
}
}
else
{
lean_dec(v_a_1566_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
return v___x_1567_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
v_a_1701_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1565_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1565_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
return v___x_1563_;
}
}
else
{
lean_dec(v_a_1557_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
return v___x_1558_;
}
}
else
{
lean_dec(v_a_1557_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
return v___x_1558_;
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
v_a_1709_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1556_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1556_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v___y_1550_);
lean_dec(v_matchDeclName_1406_);
v_a_1717_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1553_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1553_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
v___jp_1736_:
{
uint8_t v_hasTrace_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_hasTrace_1737_ = lean_ctor_get_uint8(v_options_1732_, sizeof(void*)*1);
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_currRecDepth_1726_, v___x_1738_);
lean_inc(v_ref_1727_);
lean_inc_ref(v_toCold_1725_);
v___x_1740_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1740_, 0, v_toCold_1725_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
lean_ctor_set(v___x_1740_, 2, v_ref_1727_);
lean_ctor_set_uint16(v___x_1740_, sizeof(void*)*3, v_optionFlags_1728_);
lean_ctor_set_uint8(v___x_1740_, sizeof(void*)*3 + 2, v_suppressElabErrors_1729_);
lean_ctor_set_uint8(v___x_1740_, sizeof(void*)*3 + 3, v_checkDeprecated_1730_);
lean_ctor_set_uint8(v___x_1740_, sizeof(void*)*3 + 4, v_isRecordingDeps_1731_);
if (v_hasTrace_1737_ == 0)
{
v___y_1548_ = v_a_1409_;
v___y_1549_ = v_a_1410_;
v___y_1550_ = v___x_1740_;
v___y_1551_ = v_a_1412_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17);
v___x_1742_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1734_, v_options_1732_, v___x_1741_);
if (v___x_1742_ == 0)
{
v___y_1548_ = v_a_1409_;
v___y_1549_ = v_a_1410_;
v___y_1550_ = v___x_1740_;
v___y_1551_ = v_a_1412_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1743_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__19, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__19_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__19);
lean_inc(v_mvarId_1407_);
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_mvarId_1407_);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1735_, v___x_1745_, v_a_1409_, v_a_1410_, v___x_1740_, v_a_1412_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_dec_ref_known(v___x_1746_, 1);
v___y_1548_ = v_a_1409_;
v___y_1549_ = v_a_1410_;
v___y_1550_ = v___x_1740_;
v___y_1551_ = v_a_1412_;
goto v___jp_1547_;
}
else
{
lean_dec_ref_known(v___x_1740_, 3);
lean_dec(v_mvarId_1407_);
lean_dec(v_matchDeclName_1406_);
return v___x_1746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1751_, lean_object* v_matchDeclName_1752_, lean_object* v_as_1753_, size_t v_i_1754_, size_t v_stop_1755_, lean_object* v_b_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_usize_dec_eq(v_i_1754_, v_stop_1755_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1763_ = lean_array_uget_borrowed(v_as_1753_, v_i_1754_);
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = lean_nat_add(v_depth_1751_, v___x_1764_);
lean_inc(v___x_1763_);
lean_inc(v_matchDeclName_1752_);
v___x_1766_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1752_, v___x_1763_, v___x_1765_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___x_1765_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; size_t v___x_1768_; size_t v___x_1769_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = ((size_t)1ULL);
v___x_1769_ = lean_usize_add(v_i_1754_, v___x_1768_);
v_i_1754_ = v___x_1769_;
v_b_1756_ = v_a_1767_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1752_);
return v___x_1766_;
}
}
else
{
lean_object* v___x_1771_; 
lean_dec(v_matchDeclName_1752_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_b_1756_);
return v___x_1771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1772_, lean_object* v_matchDeclName_1773_, lean_object* v_as_1774_, lean_object* v_i_1775_, lean_object* v_stop_1776_, lean_object* v_b_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
size_t v_i_boxed_1783_; size_t v_stop_boxed_1784_; lean_object* v_res_1785_; 
v_i_boxed_1783_ = lean_unbox_usize(v_i_1775_);
lean_dec(v_i_1775_);
v_stop_boxed_1784_ = lean_unbox_usize(v_stop_1776_);
lean_dec(v_stop_1776_);
v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1772_, v_matchDeclName_1773_, v_as_1774_, v_i_boxed_1783_, v_stop_boxed_1784_, v_b_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v_as_1774_);
lean_dec(v_depth_1772_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1786_, lean_object* v_mvarId_1787_, lean_object* v_depth_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1786_, v_mvarId_1787_, v_depth_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
lean_dec(v_depth_1788_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1795_, lean_object* v___y_1796_){
_start:
{
uint8_t v___x_1798_; 
v___x_1798_ = l_Lean_Expr_hasMVar(v_e_1795_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v_e_1795_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; lean_object* v_mctx_1801_; lean_object* v___x_1802_; lean_object* v_fst_1803_; lean_object* v_snd_1804_; lean_object* v___x_1805_; lean_object* v_cache_1806_; lean_object* v_zetaDeltaFVarIds_1807_; lean_object* v_postponed_1808_; lean_object* v_diag_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1818_; 
v___x_1800_ = lean_st_ref_get(v___y_1796_);
v_mctx_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc_ref(v_mctx_1801_);
lean_dec(v___x_1800_);
v___x_1802_ = l_Lean_instantiateMVarsCore(v_mctx_1801_, v_e_1795_);
v_fst_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_fst_1803_);
v_snd_1804_ = lean_ctor_get(v___x_1802_, 1);
lean_inc(v_snd_1804_);
lean_dec_ref(v___x_1802_);
v___x_1805_ = lean_st_ref_take(v___y_1796_);
v_cache_1806_ = lean_ctor_get(v___x_1805_, 1);
v_zetaDeltaFVarIds_1807_ = lean_ctor_get(v___x_1805_, 2);
v_postponed_1808_ = lean_ctor_get(v___x_1805_, 3);
v_diag_1809_ = lean_ctor_get(v___x_1805_, 4);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v___x_1805_, 0);
lean_dec(v_unused_1819_);
v___x_1811_ = v___x_1805_;
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_diag_1809_);
lean_inc(v_postponed_1808_);
lean_inc(v_zetaDeltaFVarIds_1807_);
lean_inc(v_cache_1806_);
lean_dec(v___x_1805_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v_snd_1804_);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_snd_1804_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_cache_1806_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_zetaDeltaFVarIds_1807_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_postponed_1808_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_diag_1809_);
v___x_1814_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_st_ref_put(v___y_1796_, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v_fst_1803_);
return v___x_1816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1820_, v___y_1821_);
lean_dec(v___y_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1824_, v___y_1826_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1838_, lean_object* v_localInsts_1839_, lean_object* v_x_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1838_, v_localInsts_1839_, v_x_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_a_1855_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1846_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1846_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1863_, lean_object* v_localInsts_1864_, lean_object* v_x_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1863_, v_localInsts_1864_, v_x_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1872_, lean_object* v_lctx_1873_, lean_object* v_localInsts_1874_, lean_object* v_x_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1873_, v_localInsts_1874_, v_x_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1882_, lean_object* v_lctx_1883_, lean_object* v_localInsts_1884_, lean_object* v_x_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1882_, v_lctx_1883_, v_localInsts_1884_, v_x_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1891_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1892_, lean_object* v_x_1893_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_name_eq(v_x_1893_, v_matchDeclName_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1895_, lean_object* v_x_1896_){
_start:
{
uint8_t v_res_1897_; lean_object* v_r_1898_; 
v_res_1897_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1895_, v_x_1896_);
lean_dec(v_x_1896_);
lean_dec(v_matchDeclName_1895_);
v_r_1898_ = lean_box(v_res_1897_);
return v_r_1898_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1899_, lean_object* v_a_1900_, lean_object* v_b_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_nat_dec_lt(v_a_1900_, v_upperBound_1899_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; 
lean_dec(v_a_1900_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v_b_1901_);
return v___x_1908_;
}
else
{
uint8_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = 0;
v___x_1910_ = l_Lean_Meta_introSubstEq(v_b_1901_, v___x_1909_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v_snd_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v_snd_1912_ = lean_ctor_get(v_a_1911_, 1);
lean_inc(v_snd_1912_);
lean_dec(v_a_1911_);
v___x_1913_ = lean_unsigned_to_nat(1u);
v___x_1914_ = lean_nat_add(v_a_1900_, v___x_1913_);
lean_dec(v_a_1900_);
v_a_1900_ = v___x_1914_;
v_b_1901_ = v_snd_1912_;
goto _start;
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1900_);
v_a_1916_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1910_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1910_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1924_, lean_object* v_a_1925_, lean_object* v_b_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1924_, v_a_1925_, v_b_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v_upperBound_1924_);
return v_res_1932_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1935_ = l_Lean_stringToMessageData(v___x_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1938_ = l_Lean_stringToMessageData(v___x_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1939_, lean_object* v___f_1940_, lean_object* v_matchDeclName_1941_, lean_object* v___x_1942_, lean_object* v_heqNum_1943_, lean_object* v_heqPos_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_2105_; 
v___x_1950_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1939_, v___y_1946_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_2105_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_2105_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_box(0);
v___x_1956_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1951_, v___x_1955_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2104_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_2104_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2104_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v_mvarId_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v_toCold_2024_; lean_object* v_options_2025_; lean_object* v_inheritedTraceOptions_2026_; uint8_t v_hasTrace_2027_; lean_object* v___x_2028_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; 
v_toCold_2024_ = lean_ctor_get(v___y_1947_, 0);
v_options_2025_ = lean_ctor_get(v_toCold_2024_, 2);
v_inheritedTraceOptions_2026_ = lean_ctor_get(v_toCold_2024_, 11);
v_hasTrace_2027_ = lean_ctor_get_uint8(v_options_2025_, sizeof(void*)*1);
v___x_2028_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
if (v_hasTrace_2027_ == 0)
{
lean_del_object(v___x_1953_);
v___y_2030_ = v___y_1945_;
v___y_2031_ = v___y_1946_;
v___y_2032_ = v___y_1947_;
v___y_2033_ = v___y_1948_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17);
v___x_2088_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2026_, v_options_2025_, v___x_2087_);
if (v___x_2088_ == 0)
{
lean_del_object(v___x_1953_);
v___y_2030_ = v___y_1945_;
v___y_2031_ = v___y_1946_;
v___y_2032_ = v___y_1947_;
v___y_2033_ = v___y_1948_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2089_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2090_ = l_Lean_Expr_mvarId_x21(v_a_1957_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set_tag(v___x_1953_, 1);
lean_ctor_set(v___x_1953_, 0, v___x_2090_);
v___x_2092_ = v___x_1953_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2089_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2028_, v___x_2093_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_dec_ref_known(v___x_2094_, 1);
v___y_2030_ = v___y_1945_;
v___y_2031_ = v___y_1946_;
v___y_2032_ = v___y_1947_;
v___y_2033_ = v___y_1948_;
goto v___jp_2029_;
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_del_object(v___x_1959_);
lean_dec(v_a_1957_);
lean_dec(v_heqPos_1944_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
lean_dec_ref(v___f_1940_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
}
v___jp_1961_:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_MVarId_intros(v_mvarId_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v_snd_1969_; uint8_t v___x_1970_; lean_object* v___x_1971_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v_snd_1969_ = lean_ctor_get(v_a_1968_, 1);
lean_inc_n(v_snd_1969_, 2);
lean_dec(v_a_1968_);
v___x_1970_ = 1;
v___x_1971_ = l_Lean_MVarId_refl(v_snd_1969_, v___x_1970_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v___x_1972_; 
lean_dec_ref_known(v___x_1971_, 1);
lean_dec(v_snd_1969_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
lean_dec_ref(v___f_1940_);
v___x_1972_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1957_, v___y_1964_);
return v___x_1972_;
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2015_; 
v_a_1973_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1975_ = v___x_1971_;
v_isShared_1976_ = v_isSharedCheck_2015_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1971_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2015_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
uint8_t v___x_1977_; 
v___x_1977_ = l_Lean_Exception_isInterrupt(v_a_1973_);
if (v___x_1977_ == 0)
{
uint8_t v___x_1978_; 
lean_inc(v_a_1973_);
v___x_1978_ = l_Lean_Exception_isRuntime(v_a_1973_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_del_object(v___x_1975_);
lean_dec(v_a_1973_);
v___x_1979_ = l_Lean_MVarId_deltaTarget(v_snd_1969_, v___f_1940_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1981_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v___x_1981_ = l_Lean_MVarId_heqOfEq(v_a_1980_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1983_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1941_, v_a_1982_, v___x_1942_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___x_1942_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v___x_1984_; 
lean_dec_ref_known(v___x_1983_, 1);
v___x_1984_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1957_, v___y_1964_);
return v___x_1984_;
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_a_1957_);
v_a_1985_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1983_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1983_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec(v_a_1957_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
v_a_1993_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1981_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1981_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_a_1957_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
v_a_2001_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1979_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1979_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v___x_2010_; 
lean_dec(v_snd_1969_);
lean_dec(v_a_1957_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
lean_dec_ref(v___f_1940_);
if (v_isShared_1976_ == 0)
{
v___x_2010_ = v___x_1975_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_1973_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
else
{
lean_object* v___x_2013_; 
lean_dec(v_snd_1969_);
lean_dec(v_a_1957_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
lean_dec_ref(v___f_1940_);
if (v_isShared_1976_ == 0)
{
v___x_2013_ = v___x_1975_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_1973_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_a_1957_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
lean_dec_ref(v___f_1940_);
v_a_2016_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1967_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1967_);
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
v___jp_2029_:
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = l_Lean_Expr_mvarId_x21(v_a_1957_);
v___x_2035_ = lean_nat_dec_lt(v___x_1942_, v_heqNum_1943_);
if (v___x_2035_ == 0)
{
lean_del_object(v___x_1959_);
lean_dec(v_heqPos_1944_);
v_mvarId_1962_ = v___x_2034_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
v___y_1966_ = v___y_2033_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_box(0);
v___x_2037_ = 0;
v___x_2038_ = l_Lean_Meta_introNCore(v___x_2034_, v_heqPos_1944_, v___x_2036_, v___x_2037_, v___x_2037_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v_snd_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2077_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v_snd_2040_ = lean_ctor_get(v_a_2039_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_a_2039_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; 
v_unused_2078_ = lean_ctor_get(v_a_2039_, 0);
lean_dec(v_unused_2078_);
v___x_2042_ = v_a_2039_;
v_isShared_2043_ = v_isSharedCheck_2077_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_snd_2040_);
lean_dec(v_a_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2077_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; 
lean_inc(v___x_1942_);
v___x_2044_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1943_, v___x_1942_, v_snd_2040_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_toCold_2045_; lean_object* v_options_2046_; uint8_t v_hasTrace_2047_; 
v_toCold_2045_ = lean_ctor_get(v___y_2032_, 0);
v_options_2046_ = lean_ctor_get(v_toCold_2045_, 2);
v_hasTrace_2047_ = lean_ctor_get_uint8(v_options_2046_, sizeof(void*)*1);
if (v_hasTrace_2047_ == 0)
{
lean_object* v_a_2048_; 
lean_del_object(v___x_2042_);
lean_del_object(v___x_1959_);
v_a_2048_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2044_, 1);
v_mvarId_1962_ = v_a_2048_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
v___y_1966_ = v___y_2033_;
goto v___jp_1961_;
}
else
{
lean_object* v_a_2049_; lean_object* v_inheritedTraceOptions_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
v_a_2049_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2044_, 1);
v_inheritedTraceOptions_2050_ = lean_ctor_get(v_toCold_2045_, 11);
v___x_2051_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17);
v___x_2052_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2050_, v_options_2046_, v___x_2051_);
if (v___x_2052_ == 0)
{
lean_del_object(v___x_2042_);
lean_del_object(v___x_1959_);
v_mvarId_1962_ = v_a_2049_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
v___y_1966_ = v___y_2033_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2049_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 1);
lean_ctor_set(v___x_1959_, 0, v_a_2049_);
v___x_2055_ = v___x_1959_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2049_);
v___x_2055_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2057_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 7);
lean_ctor_set(v___x_2042_, 1, v___x_2055_);
lean_ctor_set(v___x_2042_, 0, v___x_2053_);
v___x_2057_ = v___x_2042_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2028_, v___x_2057_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_dec_ref_known(v___x_2058_, 1);
v_mvarId_1962_ = v_a_2049_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
v___y_1966_ = v___y_2033_;
goto v___jp_1961_;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_a_2049_);
lean_dec(v_a_1957_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
lean_dec_ref(v___f_1940_);
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
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
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_del_object(v___x_2042_);
lean_del_object(v___x_1959_);
lean_dec(v_a_1957_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
lean_dec_ref(v___f_1940_);
v_a_2069_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2044_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2044_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_del_object(v___x_1959_);
lean_dec(v_a_1957_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
lean_dec_ref(v___f_1940_);
v_a_2079_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2038_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2038_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1953_);
lean_dec(v_heqPos_1944_);
lean_dec(v___x_1942_);
lean_dec(v_matchDeclName_1941_);
lean_dec_ref(v___f_1940_);
return v___x_1956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2106_, lean_object* v___f_2107_, lean_object* v_matchDeclName_2108_, lean_object* v___x_2109_, lean_object* v_heqNum_2110_, lean_object* v_heqPos_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2106_, v___f_2107_, v_matchDeclName_2108_, v___x_2109_, v_heqNum_2110_, v_heqPos_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v_heqNum_2110_);
return v_res_2117_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_unsigned_to_nat(32u);
v___x_2122_ = lean_mk_empty_array_with_capacity(v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2124_ = ((size_t)5ULL);
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = lean_unsigned_to_nat(32u);
v___x_2127_ = lean_mk_empty_array_with_capacity(v___x_2126_);
v___x_2128_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2129_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v___x_2127_);
lean_ctor_set(v___x_2129_, 2, v___x_2125_);
lean_ctor_set(v___x_2129_, 3, v___x_2125_);
lean_ctor_set_usize(v___x_2129_, 4, v___x_2124_);
return v___x_2129_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = lean_box(1);
v___x_2131_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2132_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v___x_2131_);
lean_ctor_set(v___x_2133_, 2, v___x_2130_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2136_, lean_object* v_type_2137_, lean_object* v_heqPos_2138_, lean_object* v_heqNum_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v___f_2145_; lean_object* v___x_2146_; lean_object* v___f_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_inc(v_matchDeclName_2136_);
v___f_2145_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2145_, 0, v_matchDeclName_2136_);
v___x_2146_ = lean_unsigned_to_nat(0u);
v___f_2147_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 11, 6);
lean_closure_set(v___f_2147_, 0, v_type_2137_);
lean_closure_set(v___f_2147_, 1, v___f_2145_);
lean_closure_set(v___f_2147_, 2, v_matchDeclName_2136_);
lean_closure_set(v___f_2147_, 3, v___x_2146_);
lean_closure_set(v___f_2147_, 4, v_heqNum_2139_);
lean_closure_set(v___f_2147_, 5, v_heqPos_2138_);
v___x_2148_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2149_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2150_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2148_, v___x_2149_, v___f_2147_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2151_, lean_object* v_type_2152_, lean_object* v_heqPos_2153_, lean_object* v_heqNum_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2151_, v_type_2152_, v_heqPos_2153_, v_heqNum_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2161_, lean_object* v_inst_2162_, lean_object* v_R_2163_, lean_object* v_a_2164_, lean_object* v_b_2165_, lean_object* v_c_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2161_, v_a_2164_, v_b_2165_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2173_, lean_object* v_inst_2174_, lean_object* v_R_2175_, lean_object* v_a_2176_, lean_object* v_b_2177_, lean_object* v_c_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2173_, v_inst_2174_, v_R_2175_, v_a_2176_, v_b_2177_, v_c_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v_upperBound_2173_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2185_, lean_object* v_b_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___x_2192_; 
lean_inc(v___y_2190_);
lean_inc_ref(v___y_2189_);
lean_inc(v___y_2188_);
lean_inc_ref(v___y_2187_);
v___x_2192_ = lean_apply_6(v_k_2185_, v_b_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, lean_box(0));
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2193_, lean_object* v_b_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2193_, v_b_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2201_, uint8_t v_bi_2202_, lean_object* v_type_2203_, lean_object* v_k_2204_, uint8_t v_kind_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___f_2211_; lean_object* v___x_2212_; 
v___f_2211_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2211_, 0, v_k_2204_);
v___x_2212_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2201_, v_bi_2202_, v_type_2203_, v___f_2211_, v_kind_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
v_a_2221_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2212_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2212_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2229_, lean_object* v_bi_2230_, lean_object* v_type_2231_, lean_object* v_k_2232_, lean_object* v_kind_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
uint8_t v_bi_boxed_2239_; uint8_t v_kind_boxed_2240_; lean_object* v_res_2241_; 
v_bi_boxed_2239_ = lean_unbox(v_bi_2230_);
v_kind_boxed_2240_ = lean_unbox(v_kind_2233_);
v_res_2241_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2229_, v_bi_boxed_2239_, v_type_2231_, v_k_2232_, v_kind_boxed_2240_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2242_, lean_object* v_name_2243_, uint8_t v_bi_2244_, lean_object* v_type_2245_, lean_object* v_k_2246_, uint8_t v_kind_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2243_, v_bi_2244_, v_type_2245_, v_k_2246_, v_kind_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2254_, lean_object* v_name_2255_, lean_object* v_bi_2256_, lean_object* v_type_2257_, lean_object* v_k_2258_, lean_object* v_kind_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
uint8_t v_bi_boxed_2265_; uint8_t v_kind_boxed_2266_; lean_object* v_res_2267_; 
v_bi_boxed_2265_ = lean_unbox(v_bi_2256_);
v_kind_boxed_2266_ = lean_unbox(v_kind_2259_);
v_res_2267_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2254_, v_name_2255_, v_bi_boxed_2265_, v_type_2257_, v_k_2258_, v_kind_boxed_2266_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2268_, lean_object* v_altsNew_2269_, lean_object* v_discrs_2270_, lean_object* v_patterns_2271_, lean_object* v_alts_2272_, lean_object* v_k_2273_, lean_object* v_altNew_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2268_, v_altsNew_2269_, v_discrs_2270_, v_patterns_2271_, v_alts_2272_, v_k_2273_, v_altNew_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v_i_2268_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2281_, lean_object* v_patterns_2282_, lean_object* v_alts_2283_, lean_object* v_k_2284_, lean_object* v_i_2285_, lean_object* v_altsNew_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v___x_2292_; uint8_t v___x_2293_; 
v___x_2292_ = lean_array_get_size(v_alts_2283_);
v___x_2293_ = lean_nat_dec_lt(v_i_2285_, v___x_2292_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; 
lean_dec(v_i_2285_);
lean_dec_ref(v_alts_2283_);
lean_dec_ref(v_patterns_2282_);
lean_dec_ref(v_discrs_2281_);
lean_inc(v_a_2290_);
lean_inc_ref(v_a_2289_);
lean_inc(v_a_2288_);
lean_inc_ref(v_a_2287_);
v___x_2294_ = lean_apply_6(v_k_2284_, v_altsNew_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, lean_box(0));
return v___x_2294_;
}
else
{
lean_object* v___f_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_inc_ref(v_alts_2283_);
lean_inc_ref(v_patterns_2282_);
lean_inc_ref(v_discrs_2281_);
lean_inc(v_i_2285_);
v___f_2295_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2295_, 0, v_i_2285_);
lean_closure_set(v___f_2295_, 1, v_altsNew_2286_);
lean_closure_set(v___f_2295_, 2, v_discrs_2281_);
lean_closure_set(v___f_2295_, 3, v_patterns_2282_);
lean_closure_set(v___f_2295_, 4, v_alts_2283_);
lean_closure_set(v___f_2295_, 5, v_k_2284_);
v___x_2296_ = lean_array_fget(v_alts_2283_, v_i_2285_);
lean_dec(v_i_2285_);
lean_dec_ref(v_alts_2283_);
v___x_2297_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2296_, v_a_2287_, v_a_2289_, v_a_2290_);
lean_dec(v___x_2296_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = l_Lean_LocalDecl_type(v_a_2298_);
v___x_2300_ = l_Lean_Expr_replaceFVars(v___x_2299_, v_discrs_2281_, v_patterns_2282_);
lean_dec_ref(v_patterns_2282_);
lean_dec_ref(v_discrs_2281_);
lean_dec_ref(v___x_2299_);
v___x_2301_ = l_Lean_LocalDecl_userName(v_a_2298_);
v___x_2302_ = l_Lean_LocalDecl_binderInfo(v_a_2298_);
lean_dec(v_a_2298_);
v___x_2303_ = 0;
v___x_2304_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2301_, v___x_2302_, v___x_2300_, v___f_2295_, v___x_2303_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
return v___x_2304_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v___f_2295_);
lean_dec_ref(v_patterns_2282_);
lean_dec_ref(v_discrs_2281_);
v_a_2305_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2297_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2297_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2313_, lean_object* v_altsNew_2314_, lean_object* v_discrs_2315_, lean_object* v_patterns_2316_, lean_object* v_alts_2317_, lean_object* v_k_2318_, lean_object* v_altNew_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2325_ = lean_unsigned_to_nat(1u);
v___x_2326_ = lean_nat_add(v_i_2313_, v___x_2325_);
v___x_2327_ = lean_array_push(v_altsNew_2314_, v_altNew_2319_);
v___x_2328_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2315_, v_patterns_2316_, v_alts_2317_, v_k_2318_, v___x_2326_, v___x_2327_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2329_, lean_object* v_patterns_2330_, lean_object* v_alts_2331_, lean_object* v_k_2332_, lean_object* v_i_2333_, lean_object* v_altsNew_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2329_, v_patterns_2330_, v_alts_2331_, v_k_2332_, v_i_2333_, v_altsNew_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2341_, lean_object* v_discrs_2342_, lean_object* v_patterns_2343_, lean_object* v_alts_2344_, lean_object* v_k_2345_, lean_object* v_i_2346_, lean_object* v_altsNew_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2342_, v_patterns_2343_, v_alts_2344_, v_k_2345_, v_i_2346_, v_altsNew_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2354_, lean_object* v_discrs_2355_, lean_object* v_patterns_2356_, lean_object* v_alts_2357_, lean_object* v_k_2358_, lean_object* v_i_2359_, lean_object* v_altsNew_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2354_, v_discrs_2355_, v_patterns_2356_, v_alts_2357_, v_k_2358_, v_i_2359_, v_altsNew_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2369_, lean_object* v_discrs_2370_, lean_object* v_patterns_2371_, lean_object* v_alts_2372_, lean_object* v_k_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = lean_nat_dec_eq(v_numDiscrEqs_2369_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2382_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2370_, v_patterns_2371_, v_alts_2372_, v_k_2373_, v___x_2379_, v___x_2381_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
return v___x_2382_;
}
else
{
lean_object* v___x_2383_; 
lean_dec_ref(v_patterns_2371_);
lean_dec_ref(v_discrs_2370_);
lean_inc(v_a_2377_);
lean_inc_ref(v_a_2376_);
lean_inc(v_a_2375_);
lean_inc_ref(v_a_2374_);
v___x_2383_ = lean_apply_6(v_k_2373_, v_alts_2372_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, lean_box(0));
return v___x_2383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2384_, lean_object* v_discrs_2385_, lean_object* v_patterns_2386_, lean_object* v_alts_2387_, lean_object* v_k_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2384_, v_discrs_2385_, v_patterns_2386_, v_alts_2387_, v_k_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_numDiscrEqs_2384_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2395_, lean_object* v_numDiscrEqs_2396_, lean_object* v_discrs_2397_, lean_object* v_patterns_2398_, lean_object* v_alts_2399_, lean_object* v_k_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2396_, v_discrs_2397_, v_patterns_2398_, v_alts_2399_, v_k_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2407_, lean_object* v_numDiscrEqs_2408_, lean_object* v_discrs_2409_, lean_object* v_patterns_2410_, lean_object* v_alts_2411_, lean_object* v_k_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2407_, v_numDiscrEqs_2408_, v_discrs_2409_, v_patterns_2410_, v_alts_2411_, v_k_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_numDiscrEqs_2408_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(lean_object* v_declName_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v_env_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2422_ = lean_st_ref_get(v___y_2420_);
v_env_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc_ref(v_env_2423_);
lean_dec(v___x_2422_);
v___x_2424_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2423_, v_declName_2419_);
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg___boxed(lean_object* v_declName_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2426_, v___y_2427_);
lean_dec(v___y_2427_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_declName_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2430_, v___y_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___boxed(lean_object* v_declName_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v_declName_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___f_2451_; lean_object* v___x_14372__overap_2452_; lean_object* v___x_2453_; 
v___f_2451_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14372__overap_2452_ = lean_panic_fn_borrowed(v___f_2451_, v_msg_2445_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
lean_inc(v___y_2447_);
lean_inc_ref(v___y_2446_);
v___x_2453_ = lean_apply_5(v___x_14372__overap_2452_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, lean_box(0));
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2461_, lean_object* v_b_2462_, lean_object* v_c_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v___x_2469_; 
lean_inc(v___y_2467_);
lean_inc_ref(v___y_2466_);
lean_inc(v___y_2465_);
lean_inc_ref(v___y_2464_);
v___x_2469_ = lean_apply_7(v_k_2461_, v_b_2462_, v_c_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, lean_box(0));
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2470_, lean_object* v_b_2471_, lean_object* v_c_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2470_, v_b_2471_, v_c_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2479_, lean_object* v_k_2480_, uint8_t v_cleanupAnnotations_2481_, uint8_t v_whnfType_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___f_2488_; lean_object* v___x_2489_; 
v___f_2488_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2488_, 0, v_k_2480_);
v___x_2489_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2479_, v___f_2488_, v_cleanupAnnotations_2481_, v_whnfType_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v_a_2498_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2489_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2489_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2506_, lean_object* v_k_2507_, lean_object* v_cleanupAnnotations_2508_, lean_object* v_whnfType_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2515_; uint8_t v_whnfType_boxed_2516_; lean_object* v_res_2517_; 
v_cleanupAnnotations_boxed_2515_ = lean_unbox(v_cleanupAnnotations_2508_);
v_whnfType_boxed_2516_ = lean_unbox(v_whnfType_2509_);
v_res_2517_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2506_, v_k_2507_, v_cleanupAnnotations_boxed_2515_, v_whnfType_boxed_2516_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2518_, lean_object* v_type_2519_, lean_object* v_k_2520_, uint8_t v_cleanupAnnotations_2521_, uint8_t v_whnfType_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2519_, v_k_2520_, v_cleanupAnnotations_2521_, v_whnfType_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2529_, lean_object* v_type_2530_, lean_object* v_k_2531_, lean_object* v_cleanupAnnotations_2532_, lean_object* v_whnfType_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2539_; uint8_t v_whnfType_boxed_2540_; lean_object* v_res_2541_; 
v_cleanupAnnotations_boxed_2539_ = lean_unbox(v_cleanupAnnotations_2532_);
v_whnfType_boxed_2540_ = lean_unbox(v_whnfType_2533_);
v_res_2541_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2529_, v_type_2530_, v_k_2531_, v_cleanupAnnotations_boxed_2539_, v_whnfType_boxed_2540_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2542_, lean_object* v_splitterName_2543_, lean_object* v_matcherInput_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_matchType_2550_; lean_object* v_discrInfos_2551_; lean_object* v_lhss_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2572_; 
v_matchType_2550_ = lean_ctor_get(v_matcherInput_2544_, 1);
v_discrInfos_2551_ = lean_ctor_get(v_matcherInput_2544_, 2);
v_lhss_2552_ = lean_ctor_get(v_matcherInput_2544_, 3);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_matcherInput_2544_);
if (v_isSharedCheck_2572_ == 0)
{
lean_object* v_unused_2573_; lean_object* v_unused_2574_; 
v_unused_2573_ = lean_ctor_get(v_matcherInput_2544_, 4);
lean_dec(v_unused_2573_);
v_unused_2574_ = lean_ctor_get(v_matcherInput_2544_, 0);
lean_dec(v_unused_2574_);
v___x_2554_ = v_matcherInput_2544_;
v_isShared_2555_ = v_isSharedCheck_2572_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_lhss_2552_);
lean_inc(v_discrInfos_2551_);
lean_inc(v_matchType_2550_);
lean_dec(v_matcherInput_2544_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2572_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_overlaps_2542_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 4, v___x_2556_);
lean_ctor_set(v___x_2554_, 0, v_splitterName_2543_);
v___x_2558_ = v___x_2554_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_splitterName_2543_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_matchType_2550_);
lean_ctor_set(v_reuseFailAlloc_2571_, 2, v_discrInfos_2551_);
lean_ctor_set(v_reuseFailAlloc_2571_, 3, v_lhss_2552_);
lean_ctor_set(v_reuseFailAlloc_2571_, 4, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Meta_Match_mkMatcher(v___x_2558_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v_addMatcher_2561_; lean_object* v___x_2562_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v_addMatcher_2561_ = lean_ctor_get(v_a_2560_, 3);
lean_inc_ref(v_addMatcher_2561_);
lean_dec(v_a_2560_);
lean_inc(v___y_2548_);
lean_inc_ref(v___y_2547_);
lean_inc(v___y_2546_);
lean_inc_ref(v___y_2545_);
v___x_2562_ = lean_apply_5(v_addMatcher_2561_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, lean_box(0));
return v___x_2562_;
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_a_2563_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2559_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2559_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2575_, lean_object* v_splitterName_2576_, lean_object* v_matcherInput_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2575_, v_splitterName_2576_, v_matcherInput_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2583_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2584_, lean_object* v_ys_2585_, lean_object* v_x_2586_){
_start:
{
lean_object* v_zero_2587_; uint8_t v_isZero_2588_; 
v_zero_2587_ = lean_unsigned_to_nat(0u);
v_isZero_2588_ = lean_nat_dec_eq(v_x_2586_, v_zero_2587_);
if (v_isZero_2588_ == 1)
{
lean_dec(v_x_2586_);
return v_isZero_2588_;
}
else
{
lean_object* v_one_2589_; lean_object* v_n_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v_one_2589_ = lean_unsigned_to_nat(1u);
v_n_2590_ = lean_nat_sub(v_x_2586_, v_one_2589_);
lean_dec(v_x_2586_);
v___x_2591_ = lean_array_fget_borrowed(v_xs_2584_, v_n_2590_);
v___x_2592_ = lean_array_fget_borrowed(v_ys_2585_, v_n_2590_);
v___x_2593_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2591_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_dec(v_n_2590_);
return v___x_2593_;
}
else
{
v_x_2586_ = v_n_2590_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2595_, lean_object* v_ys_2596_, lean_object* v_x_2597_){
_start:
{
uint8_t v_res_2598_; lean_object* v_r_2599_; 
v_res_2598_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2595_, v_ys_2596_, v_x_2597_);
lean_dec_ref(v_ys_2596_);
lean_dec_ref(v_xs_2595_);
v_r_2599_ = lean_box(v_res_2598_);
return v_r_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2600_, lean_object* v_b_2601_){
_start:
{
lean_object* v_array_2602_; lean_object* v_start_2603_; lean_object* v_stop_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2617_; 
v_array_2602_ = lean_ctor_get(v_a_2600_, 0);
v_start_2603_ = lean_ctor_get(v_a_2600_, 1);
v_stop_2604_ = lean_ctor_get(v_a_2600_, 2);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_a_2600_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2606_ = v_a_2600_;
v_isShared_2607_ = v_isSharedCheck_2617_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_stop_2604_);
lean_inc(v_start_2603_);
lean_inc(v_array_2602_);
lean_dec(v_a_2600_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2617_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_nat_dec_lt(v_start_2603_, v_stop_2604_);
if (v___x_2608_ == 0)
{
lean_del_object(v___x_2606_);
lean_dec(v_stop_2604_);
lean_dec(v_start_2603_);
lean_dec_ref(v_array_2602_);
return v_b_2601_;
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2609_ = lean_unsigned_to_nat(1u);
v___x_2610_ = lean_nat_add(v_start_2603_, v___x_2609_);
lean_inc_ref(v_array_2602_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 1, v___x_2610_);
v___x_2612_ = v___x_2606_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_array_2602_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_stop_2604_);
v___x_2612_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_array_fget(v_array_2602_, v_start_2603_);
lean_dec(v_start_2603_);
lean_dec_ref(v_array_2602_);
v___x_2614_ = lean_array_push(v_b_2601_, v___x_2613_);
v_a_2600_ = v___x_2612_;
v_b_2601_ = v___x_2614_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2618_, size_t v_sz_2619_, size_t v_i_2620_, lean_object* v_b_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
uint8_t v___x_2627_; 
v___x_2627_ = lean_usize_dec_lt(v_i_2620_, v_sz_2619_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
v___x_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2628_, 0, v_b_2621_);
return v___x_2628_;
}
else
{
lean_object* v_snd_2629_; lean_object* v_fst_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2682_; 
v_snd_2629_ = lean_ctor_get(v_b_2621_, 1);
v_fst_2630_ = lean_ctor_get(v_b_2621_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_b_2621_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2632_ = v_b_2621_;
v_isShared_2633_ = v_isSharedCheck_2682_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_snd_2629_);
lean_inc(v_fst_2630_);
lean_dec(v_b_2621_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2682_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v_array_2634_; lean_object* v_start_2635_; lean_object* v_stop_2636_; uint8_t v___x_2637_; 
v_array_2634_ = lean_ctor_get(v_snd_2629_, 0);
v_start_2635_ = lean_ctor_get(v_snd_2629_, 1);
v_stop_2636_ = lean_ctor_get(v_snd_2629_, 2);
v___x_2637_ = lean_nat_dec_lt(v_start_2635_, v_stop_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2639_; 
if (v_isShared_2633_ == 0)
{
v___x_2639_ = v___x_2632_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_fst_2630_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_snd_2629_);
v___x_2639_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
else
{
lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2678_; 
lean_inc(v_stop_2636_);
lean_inc(v_start_2635_);
lean_inc_ref(v_array_2634_);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_snd_2629_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; lean_object* v_unused_2680_; lean_object* v_unused_2681_; 
v_unused_2679_ = lean_ctor_get(v_snd_2629_, 2);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_snd_2629_, 1);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_snd_2629_, 0);
lean_dec(v_unused_2681_);
v___x_2643_ = v_snd_2629_;
v_isShared_2644_ = v_isSharedCheck_2678_;
goto v_resetjp_2642_;
}
else
{
lean_dec(v_snd_2629_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2678_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v_a_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v_a_2645_ = lean_array_uget_borrowed(v_as_2618_, v_i_2620_);
v___x_2646_ = lean_array_fget(v_array_2634_, v_start_2635_);
v___x_2647_ = lean_unsigned_to_nat(1u);
v___x_2648_ = lean_nat_add(v_start_2635_, v___x_2647_);
lean_dec(v_start_2635_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 1, v___x_2648_);
v___x_2650_ = v___x_2643_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_array_2634_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_stop_2636_);
v___x_2650_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; 
lean_inc(v_a_2645_);
v___x_2651_ = l_Lean_Meta_mkEqHEq(v_a_2645_, v___x_2646_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2653_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v___x_2653_ = l_Lean_mkArrow(v_a_2652_, v_fst_2630_, v___y_2624_, v___y_2625_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2653_, 1);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 1, v___x_2650_);
lean_ctor_set(v___x_2632_, 0, v_a_2654_);
v___x_2656_ = v___x_2632_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2650_);
v___x_2656_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
size_t v___x_2657_; size_t v___x_2658_; 
v___x_2657_ = ((size_t)1ULL);
v___x_2658_ = lean_usize_add(v_i_2620_, v___x_2657_);
v_i_2620_ = v___x_2658_;
v_b_2621_ = v___x_2656_;
goto _start;
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec_ref(v___x_2650_);
lean_del_object(v___x_2632_);
v_a_2661_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2653_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2653_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec_ref(v___x_2650_);
lean_del_object(v___x_2632_);
lean_dec(v_fst_2630_);
v_a_2669_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2651_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2651_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2683_, lean_object* v_sz_2684_, lean_object* v_i_2685_, lean_object* v_b_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
size_t v_sz_boxed_2692_; size_t v_i_boxed_2693_; lean_object* v_res_2694_; 
v_sz_boxed_2692_ = lean_unbox_usize(v_sz_2684_);
lean_dec(v_sz_2684_);
v_i_boxed_2693_ = lean_unbox_usize(v_i_2685_);
lean_dec(v_i_2685_);
v_res_2694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2683_, v_sz_boxed_2692_, v_i_boxed_2693_, v_b_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec_ref(v_as_2683_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2695_, lean_object* v___x_2696_, lean_object* v_as_2697_, size_t v_sz_2698_, size_t v_i_2699_, lean_object* v_b_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_a_2707_; uint8_t v___x_2711_; 
v___x_2711_ = lean_usize_dec_lt(v_i_2699_, v_sz_2698_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2712_, 0, v_b_2700_);
return v___x_2712_;
}
else
{
lean_object* v___x_2713_; lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2713_ = l_Lean_instInhabitedExpr;
v_a_2714_ = lean_array_uget_borrowed(v_as_2697_, v_i_2699_);
v___x_2715_ = lean_array_get_borrowed(v___x_2713_, v___x_2695_, v_a_2714_);
lean_inc(v___x_2715_);
v___x_2716_ = l_Lean_Meta_instantiateForall(v___x_2715_, v___x_2696_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2718_ = lean_array_get_size(v___x_2696_);
v___x_2719_ = l_Lean_Meta_Match_simpH_x3f(v_a_2717_, v___x_2718_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
if (lean_obj_tag(v_a_2720_) == 1)
{
lean_object* v_val_2721_; lean_object* v___x_2722_; 
v_val_2721_ = lean_ctor_get(v_a_2720_, 0);
lean_inc(v_val_2721_);
lean_dec_ref_known(v_a_2720_, 1);
v___x_2722_ = lean_array_push(v_b_2700_, v_val_2721_);
v_a_2707_ = v___x_2722_;
goto v___jp_2706_;
}
else
{
lean_dec(v_a_2720_);
v_a_2707_ = v_b_2700_;
goto v___jp_2706_;
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec_ref(v_b_2700_);
v_a_2723_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2719_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2719_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec_ref(v_b_2700_);
v_a_2731_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2716_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2716_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
v___jp_2706_:
{
size_t v___x_2708_; size_t v___x_2709_; 
v___x_2708_ = ((size_t)1ULL);
v___x_2709_ = lean_usize_add(v_i_2699_, v___x_2708_);
v_i_2699_ = v___x_2709_;
v_b_2700_ = v_a_2707_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2739_, lean_object* v___x_2740_, lean_object* v_as_2741_, lean_object* v_sz_2742_, lean_object* v_i_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
size_t v_sz_boxed_2750_; size_t v_i_boxed_2751_; lean_object* v_res_2752_; 
v_sz_boxed_2750_ = lean_unbox_usize(v_sz_2742_);
lean_dec(v_sz_2742_);
v_i_boxed_2751_ = lean_unbox_usize(v_i_2743_);
lean_dec(v_i_2743_);
v_res_2752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2739_, v___x_2740_, v_as_2741_, v_sz_boxed_2750_, v_i_boxed_2751_, v_b_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec_ref(v_as_2741_);
lean_dec_ref(v___x_2740_);
lean_dec_ref(v___x_2739_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v___x_2756_, lean_object* v___x_2757_, lean_object* v___x_2758_, lean_object* v___x_2759_, lean_object* v___x_2760_, lean_object* v_rhsArgs_2761_, lean_object* v_a_2762_, lean_object* v_ys_2763_, uint8_t v___x_2764_, uint8_t v___x_2765_, uint8_t v___x_2766_, lean_object* v_matchDeclName_2767_, lean_object* v___x_2768_, lean_object* v___x_2769_, lean_object* v___x_2770_, lean_object* v___x_2771_, lean_object* v___x_2772_, lean_object* v_argMask_2773_, lean_object* v_a_2774_, lean_object* v_alts_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2781_ = lean_array_get_borrowed(v___x_2753_, v_alts_2775_, v_a_2754_);
v___x_2782_ = l_Lean_ConstantInfo_name(v_a_2755_);
v___x_2783_ = l_Lean_mkConst(v___x_2782_, v___x_2756_);
v___x_2784_ = l_Subarray_copy___redArg(v___x_2757_);
v___x_2785_ = lean_mk_empty_array_with_capacity(v___x_2758_);
v___x_2786_ = lean_array_push(v___x_2785_, v___x_2759_);
v___x_2787_ = l_Array_append___redArg(v___x_2784_, v___x_2786_);
lean_dec_ref(v___x_2786_);
lean_inc_ref(v___x_2787_);
v___x_2788_ = l_Array_append___redArg(v___x_2787_, v___x_2760_);
v___x_2789_ = l_Array_append___redArg(v___x_2788_, v_alts_2775_);
v___x_2790_ = l_Lean_mkAppN(v___x_2783_, v___x_2789_);
lean_dec_ref(v___x_2789_);
lean_inc(v___x_2781_);
v___x_2791_ = l_Lean_mkAppN(v___x_2781_, v_rhsArgs_2761_);
v___x_2792_ = l_Lean_Meta_mkEq(v___x_2790_, v___x_2791_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v___x_2794_ = l_Lean_mkArrowN(v_a_2762_, v_a_2793_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
v___x_2796_ = l_Array_append___redArg(v___x_2787_, v_ys_2763_);
v___x_2797_ = l_Array_append___redArg(v___x_2796_, v_alts_2775_);
v___x_2798_ = l_Lean_Meta_mkForallFVars(v___x_2797_, v_a_2795_, v___x_2764_, v___x_2765_, v___x_2765_, v___x_2766_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec_ref(v___x_2797_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2800_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2798_, 1);
v___x_2800_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2799_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2802_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc_n(v_a_2801_, 2);
lean_dec_ref_known(v___x_2800_, 1);
lean_inc(v___x_2768_);
v___x_2802_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2767_, v_a_2801_, v___x_2768_, v___x_2768_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
lean_inc(v___x_2769_);
v___x_2804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2769_);
lean_ctor_set(v___x_2804_, 1, v___x_2770_);
lean_ctor_set(v___x_2804_, 2, v_a_2801_);
v___x_2805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2769_);
lean_ctor_set(v___x_2805_, 1, v___x_2771_);
v___x_2806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v_a_2803_);
lean_ctor_set(v___x_2806_, 2, v___x_2805_);
v___x_2807_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
v___x_2808_ = l_Lean_addDecl(v___x_2807_, v___x_2764_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2817_; 
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v___x_2808_, 0);
lean_dec(v_unused_2818_);
v___x_2810_ = v___x_2808_;
v_isShared_2811_ = v_isSharedCheck_2817_;
goto v_resetjp_2809_;
}
else
{
lean_dec(v___x_2808_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2817_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2772_);
lean_ctor_set(v___x_2812_, 1, v_argMask_2773_);
v___x_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2813_, 0, v_a_2774_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 0, v___x_2813_);
v___x_2815_ = v___x_2810_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v_a_2774_);
lean_dec_ref(v_argMask_2773_);
lean_dec_ref(v___x_2772_);
v_a_2819_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2808_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2808_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2774_);
lean_dec_ref(v_argMask_2773_);
lean_dec_ref(v___x_2772_);
lean_dec(v___x_2771_);
lean_dec(v___x_2770_);
lean_dec(v___x_2769_);
v_a_2827_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2802_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2802_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec_ref(v_a_2774_);
lean_dec_ref(v_argMask_2773_);
lean_dec_ref(v___x_2772_);
lean_dec(v___x_2771_);
lean_dec(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec(v_matchDeclName_2767_);
v_a_2835_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2800_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2800_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v_a_2774_);
lean_dec_ref(v_argMask_2773_);
lean_dec_ref(v___x_2772_);
lean_dec(v___x_2771_);
lean_dec(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec(v_matchDeclName_2767_);
v_a_2843_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2798_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2798_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec_ref(v___x_2787_);
lean_dec_ref(v_a_2774_);
lean_dec_ref(v_argMask_2773_);
lean_dec_ref(v___x_2772_);
lean_dec(v___x_2771_);
lean_dec(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec(v_matchDeclName_2767_);
v_a_2851_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2794_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2794_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec_ref(v___x_2787_);
lean_dec_ref(v_a_2774_);
lean_dec_ref(v_argMask_2773_);
lean_dec_ref(v___x_2772_);
lean_dec(v___x_2771_);
lean_dec(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec(v_matchDeclName_2767_);
v_a_2859_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2792_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2792_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2867_ = _args[0];
lean_object* v_a_2868_ = _args[1];
lean_object* v_a_2869_ = _args[2];
lean_object* v___x_2870_ = _args[3];
lean_object* v___x_2871_ = _args[4];
lean_object* v___x_2872_ = _args[5];
lean_object* v___x_2873_ = _args[6];
lean_object* v___x_2874_ = _args[7];
lean_object* v_rhsArgs_2875_ = _args[8];
lean_object* v_a_2876_ = _args[9];
lean_object* v_ys_2877_ = _args[10];
lean_object* v___x_2878_ = _args[11];
lean_object* v___x_2879_ = _args[12];
lean_object* v___x_2880_ = _args[13];
lean_object* v_matchDeclName_2881_ = _args[14];
lean_object* v___x_2882_ = _args[15];
lean_object* v___x_2883_ = _args[16];
lean_object* v___x_2884_ = _args[17];
lean_object* v___x_2885_ = _args[18];
lean_object* v___x_2886_ = _args[19];
lean_object* v_argMask_2887_ = _args[20];
lean_object* v_a_2888_ = _args[21];
lean_object* v_alts_2889_ = _args[22];
lean_object* v___y_2890_ = _args[23];
lean_object* v___y_2891_ = _args[24];
lean_object* v___y_2892_ = _args[25];
lean_object* v___y_2893_ = _args[26];
lean_object* v___y_2894_ = _args[27];
_start:
{
uint8_t v___x_18527__boxed_2895_; uint8_t v___x_18528__boxed_2896_; uint8_t v___x_18529__boxed_2897_; lean_object* v_res_2898_; 
v___x_18527__boxed_2895_ = lean_unbox(v___x_2878_);
v___x_18528__boxed_2896_ = lean_unbox(v___x_2879_);
v___x_18529__boxed_2897_ = lean_unbox(v___x_2880_);
v_res_2898_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2867_, v_a_2868_, v_a_2869_, v___x_2870_, v___x_2871_, v___x_2872_, v___x_2873_, v___x_2874_, v_rhsArgs_2875_, v_a_2876_, v_ys_2877_, v___x_18527__boxed_2895_, v___x_18528__boxed_2896_, v___x_18529__boxed_2897_, v_matchDeclName_2881_, v___x_2882_, v___x_2883_, v___x_2884_, v___x_2885_, v___x_2886_, v_argMask_2887_, v_a_2888_, v_alts_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v_alts_2889_);
lean_dec_ref(v_ys_2877_);
lean_dec_ref(v_a_2876_);
lean_dec_ref(v_rhsArgs_2875_);
lean_dec_ref(v___x_2874_);
lean_dec(v___x_2872_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v___x_2867_);
return v_res_2898_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2899_; lean_object* v_dummy_2900_; 
v___x_2899_ = lean_box(0);
v_dummy_2900_ = l_Lean_Expr_sort___override(v___x_2899_);
return v_dummy_2900_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2904_ = lean_box(0);
v___x_2905_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_2906_ = l_Lean_mkConst(v___x_2905_, v___x_2904_);
return v___x_2906_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_2909_ = l_Lean_stringToMessageData(v___x_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_2910_, lean_object* v_overlaps_2911_, lean_object* v_a_2912_, lean_object* v_fst_2913_, lean_object* v___x_2914_, lean_object* v___x_2915_, lean_object* v___x_2916_, uint8_t v___x_2917_, lean_object* v___x_2918_, lean_object* v_a_2919_, lean_object* v___x_2920_, lean_object* v___x_2921_, lean_object* v___x_2922_, lean_object* v_matchDeclName_2923_, lean_object* v___x_2924_, lean_object* v___x_2925_, lean_object* v___x_2926_, lean_object* v___x_2927_, lean_object* v___x_2928_, lean_object* v_ys_2929_, lean_object* v___eqs_2930_, lean_object* v_rhsArgs_2931_, lean_object* v_argMask_2932_, lean_object* v_altResultType_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_dummy_2939_; lean_object* v_nargs_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; size_t v_sz_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v_dummy_2939_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_2940_ = l_Lean_Expr_getAppNumArgs(v_altResultType_2933_);
lean_inc(v_nargs_2940_);
v___x_2941_ = lean_mk_array(v_nargs_2940_, v_dummy_2939_);
v___x_2942_ = lean_nat_sub(v_nargs_2940_, v___x_2910_);
lean_dec(v_nargs_2940_);
v___x_2943_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_2933_, v___x_2941_, v___x_2942_);
v___x_2944_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_2911_, v_a_2912_);
v_sz_2945_ = lean_array_size(v___x_2944_);
v___x_2946_ = ((size_t)0ULL);
lean_inc_ref(v___x_2914_);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_2913_, v___x_2943_, v___x_2944_, v_sz_2945_, v___x_2946_, v___x_2914_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec_ref(v___x_2944_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; uint8_t v___y_2954_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v_toCold_3007_; lean_object* v_options_3008_; uint8_t v_hasTrace_3009_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v_toCold_3007_ = lean_ctor_get(v___y_2936_, 0);
v_options_3008_ = lean_ctor_get(v_toCold_3007_, 2);
v_hasTrace_3009_ = lean_ctor_get_uint8(v_options_3008_, sizeof(void*)*1);
if (v_hasTrace_3009_ == 0)
{
v___y_2998_ = v___y_2934_;
v___y_2999_ = v___y_2935_;
v___y_3000_ = v___y_2936_;
v___y_3001_ = v___y_2937_;
goto v___jp_2997_;
}
else
{
lean_object* v_inheritedTraceOptions_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v_inheritedTraceOptions_3010_ = lean_ctor_get(v_toCold_3007_, 11);
v___x_3011_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
v___x_3012_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17);
v___x_3013_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3010_, v_options_3008_, v___x_3012_);
if (v___x_3013_ == 0)
{
v___y_2998_ = v___y_2934_;
v___y_2999_ = v___y_2935_;
v___y_3000_ = v___y_2936_;
v___y_3001_ = v___y_2937_;
goto v___jp_2997_;
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3014_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_2948_);
v___x_3015_ = lean_array_to_list(v_a_2948_);
v___x_3016_ = lean_box(0);
v___x_3017_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3015_, v___x_3016_);
v___x_3018_ = l_Lean_MessageData_ofList(v___x_3017_);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3014_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3011_, v___x_3019_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_dec_ref_known(v___x_3020_, 1);
v___y_2998_ = v___y_2934_;
v___y_2999_ = v___y_2935_;
v___y_3000_ = v___y_2936_;
v___y_3001_ = v___y_2937_;
goto v___jp_2997_;
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v_a_2948_);
lean_dec_ref(v___x_2943_);
lean_dec_ref(v_argMask_2932_);
lean_dec_ref(v_rhsArgs_2931_);
lean_dec_ref(v_ys_2929_);
lean_dec_ref(v___x_2927_);
lean_dec(v___x_2926_);
lean_dec(v___x_2925_);
lean_dec(v___x_2924_);
lean_dec(v_matchDeclName_2923_);
lean_dec_ref(v___x_2922_);
lean_dec_ref(v___x_2921_);
lean_dec(v___x_2920_);
lean_dec_ref(v_a_2919_);
lean_dec_ref(v___x_2918_);
lean_dec_ref(v___x_2916_);
lean_dec(v___x_2915_);
lean_dec_ref(v___x_2914_);
lean_dec(v_a_2912_);
lean_dec(v___x_2910_);
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3020_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
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
}
v___jp_2949_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; size_t v_sz_2965_; lean_object* v___x_2966_; 
v___x_2955_ = lean_array_get_size(v_ys_2929_);
v___x_2956_ = lean_array_get_size(v_a_2948_);
v___x_2957_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
lean_ctor_set_uint8(v___x_2957_, sizeof(void*)*2, v___y_2954_);
v___x_2958_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2943_);
v___x_2959_ = l_Array_reverse___redArg(v___x_2943_);
v___x_2960_ = lean_array_get_size(v___x_2959_);
lean_inc(v___x_2915_);
v___x_2961_ = l_Array_toSubarray___redArg(v___x_2959_, v___x_2915_, v___x_2960_);
lean_inc_ref(v___x_2916_);
v___x_2962_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2916_, v___x_2914_);
v___x_2963_ = l_Array_reverse___redArg(v___x_2962_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2958_);
lean_ctor_set(v___x_2964_, 1, v___x_2961_);
v_sz_2965_ = lean_array_size(v___x_2963_);
v___x_2966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_2963_, v_sz_2965_, v___x_2946_, v___x_2964_, v___y_2950_, v___y_2952_, v___y_2953_, v___y_2951_);
lean_dec_ref(v___x_2963_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v_fst_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; uint8_t v___x_2972_; lean_object* v___x_2973_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v_fst_2968_ = lean_ctor_get(v_a_2967_, 0);
lean_inc(v_fst_2968_);
lean_dec(v_a_2967_);
v___x_2969_ = l_Subarray_copy___redArg(v___x_2916_);
lean_inc_ref(v___x_2969_);
v___x_2970_ = l_Array_append___redArg(v___x_2969_, v_ys_2929_);
v___x_2971_ = 0;
v___x_2972_ = 1;
v___x_2973_ = l_Lean_Meta_mkForallFVars(v___x_2970_, v_fst_2968_, v___x_2971_, v___x_2917_, v___x_2917_, v___x_2972_, v___y_2950_, v___y_2952_, v___y_2953_, v___y_2951_);
lean_dec_ref(v___x_2970_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___f_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___x_2973_, 1);
v___x_2975_ = lean_box(v___x_2971_);
v___x_2976_ = lean_box(v___x_2917_);
v___x_2977_ = lean_box(v___x_2972_);
lean_inc_ref(v___x_2943_);
v___f_2978_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_2978_, 0, v___x_2918_);
lean_closure_set(v___f_2978_, 1, v_a_2912_);
lean_closure_set(v___f_2978_, 2, v_a_2919_);
lean_closure_set(v___f_2978_, 3, v___x_2920_);
lean_closure_set(v___f_2978_, 4, v___x_2921_);
lean_closure_set(v___f_2978_, 5, v___x_2910_);
lean_closure_set(v___f_2978_, 6, v___x_2922_);
lean_closure_set(v___f_2978_, 7, v___x_2943_);
lean_closure_set(v___f_2978_, 8, v_rhsArgs_2931_);
lean_closure_set(v___f_2978_, 9, v_a_2948_);
lean_closure_set(v___f_2978_, 10, v_ys_2929_);
lean_closure_set(v___f_2978_, 11, v___x_2975_);
lean_closure_set(v___f_2978_, 12, v___x_2976_);
lean_closure_set(v___f_2978_, 13, v___x_2977_);
lean_closure_set(v___f_2978_, 14, v_matchDeclName_2923_);
lean_closure_set(v___f_2978_, 15, v___x_2915_);
lean_closure_set(v___f_2978_, 16, v___x_2924_);
lean_closure_set(v___f_2978_, 17, v___x_2925_);
lean_closure_set(v___f_2978_, 18, v___x_2926_);
lean_closure_set(v___f_2978_, 19, v___x_2957_);
lean_closure_set(v___f_2978_, 20, v_argMask_2932_);
lean_closure_set(v___f_2978_, 21, v_a_2974_);
v___x_2979_ = l_Subarray_copy___redArg(v___x_2927_);
v___x_2980_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2928_, v___x_2969_, v___x_2943_, v___x_2979_, v___f_2978_, v___y_2950_, v___y_2952_, v___y_2953_, v___y_2951_);
return v___x_2980_;
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v___x_2969_);
lean_dec_ref_known(v___x_2957_, 2);
lean_dec(v_a_2948_);
lean_dec_ref(v___x_2943_);
lean_dec_ref(v_argMask_2932_);
lean_dec_ref(v_rhsArgs_2931_);
lean_dec_ref(v_ys_2929_);
lean_dec_ref(v___x_2927_);
lean_dec(v___x_2926_);
lean_dec(v___x_2925_);
lean_dec(v___x_2924_);
lean_dec(v_matchDeclName_2923_);
lean_dec_ref(v___x_2922_);
lean_dec_ref(v___x_2921_);
lean_dec(v___x_2920_);
lean_dec_ref(v_a_2919_);
lean_dec_ref(v___x_2918_);
lean_dec(v___x_2915_);
lean_dec(v_a_2912_);
lean_dec(v___x_2910_);
v_a_2981_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2973_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2973_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref_known(v___x_2957_, 2);
lean_dec(v_a_2948_);
lean_dec_ref(v___x_2943_);
lean_dec_ref(v_argMask_2932_);
lean_dec_ref(v_rhsArgs_2931_);
lean_dec_ref(v_ys_2929_);
lean_dec_ref(v___x_2927_);
lean_dec(v___x_2926_);
lean_dec(v___x_2925_);
lean_dec(v___x_2924_);
lean_dec(v_matchDeclName_2923_);
lean_dec_ref(v___x_2922_);
lean_dec_ref(v___x_2921_);
lean_dec(v___x_2920_);
lean_dec_ref(v_a_2919_);
lean_dec_ref(v___x_2918_);
lean_dec_ref(v___x_2916_);
lean_dec(v___x_2915_);
lean_dec(v_a_2912_);
lean_dec(v___x_2910_);
v_a_2989_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2966_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2966_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
v___jp_2997_:
{
lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3002_ = lean_array_get_size(v_ys_2929_);
v___x_3003_ = lean_nat_dec_eq(v___x_3002_, v___x_2915_);
if (v___x_3003_ == 0)
{
v___y_2950_ = v___y_2998_;
v___y_2951_ = v___y_3001_;
v___y_2952_ = v___y_2999_;
v___y_2953_ = v___y_3000_;
v___y_2954_ = v___x_3003_;
goto v___jp_2949_;
}
else
{
lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = lean_array_get_size(v_a_2948_);
v___x_3005_ = lean_nat_dec_eq(v___x_3004_, v___x_2915_);
if (v___x_3005_ == 0)
{
v___y_2950_ = v___y_2998_;
v___y_2951_ = v___y_3001_;
v___y_2952_ = v___y_2999_;
v___y_2953_ = v___y_3000_;
v___y_2954_ = v___x_3005_;
goto v___jp_2949_;
}
else
{
uint8_t v___x_3006_; 
v___x_3006_ = lean_nat_dec_eq(v___x_2928_, v___x_2915_);
v___y_2950_ = v___y_2998_;
v___y_2951_ = v___y_3001_;
v___y_2952_ = v___y_2999_;
v___y_2953_ = v___y_3000_;
v___y_2954_ = v___x_3006_;
goto v___jp_2949_;
}
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref(v___x_2943_);
lean_dec_ref(v_argMask_2932_);
lean_dec_ref(v_rhsArgs_2931_);
lean_dec_ref(v_ys_2929_);
lean_dec_ref(v___x_2927_);
lean_dec(v___x_2926_);
lean_dec(v___x_2925_);
lean_dec(v___x_2924_);
lean_dec(v_matchDeclName_2923_);
lean_dec_ref(v___x_2922_);
lean_dec_ref(v___x_2921_);
lean_dec(v___x_2920_);
lean_dec_ref(v_a_2919_);
lean_dec_ref(v___x_2918_);
lean_dec_ref(v___x_2916_);
lean_dec(v___x_2915_);
lean_dec_ref(v___x_2914_);
lean_dec(v_a_2912_);
lean_dec(v___x_2910_);
v_a_3029_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_2947_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_2947_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3037_ = _args[0];
lean_object* v_overlaps_3038_ = _args[1];
lean_object* v_a_3039_ = _args[2];
lean_object* v_fst_3040_ = _args[3];
lean_object* v___x_3041_ = _args[4];
lean_object* v___x_3042_ = _args[5];
lean_object* v___x_3043_ = _args[6];
lean_object* v___x_3044_ = _args[7];
lean_object* v___x_3045_ = _args[8];
lean_object* v_a_3046_ = _args[9];
lean_object* v___x_3047_ = _args[10];
lean_object* v___x_3048_ = _args[11];
lean_object* v___x_3049_ = _args[12];
lean_object* v_matchDeclName_3050_ = _args[13];
lean_object* v___x_3051_ = _args[14];
lean_object* v___x_3052_ = _args[15];
lean_object* v___x_3053_ = _args[16];
lean_object* v___x_3054_ = _args[17];
lean_object* v___x_3055_ = _args[18];
lean_object* v_ys_3056_ = _args[19];
lean_object* v___eqs_3057_ = _args[20];
lean_object* v_rhsArgs_3058_ = _args[21];
lean_object* v_argMask_3059_ = _args[22];
lean_object* v_altResultType_3060_ = _args[23];
lean_object* v___y_3061_ = _args[24];
lean_object* v___y_3062_ = _args[25];
lean_object* v___y_3063_ = _args[26];
lean_object* v___y_3064_ = _args[27];
lean_object* v___y_3065_ = _args[28];
_start:
{
uint8_t v___x_18795__boxed_3066_; lean_object* v_res_3067_; 
v___x_18795__boxed_3066_ = lean_unbox(v___x_3044_);
v_res_3067_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3037_, v_overlaps_3038_, v_a_3039_, v_fst_3040_, v___x_3041_, v___x_3042_, v___x_3043_, v___x_18795__boxed_3066_, v___x_3045_, v_a_3046_, v___x_3047_, v___x_3048_, v___x_3049_, v_matchDeclName_3050_, v___x_3051_, v___x_3052_, v___x_3053_, v___x_3054_, v___x_3055_, v_ys_3056_, v___eqs_3057_, v_rhsArgs_3058_, v_argMask_3059_, v_altResultType_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec_ref(v___eqs_3057_);
lean_dec(v___x_3055_);
lean_dec(v_fst_3040_);
lean_dec_ref(v_overlaps_3038_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3068_, lean_object* v_val_3069_, lean_object* v_baseName_3070_, lean_object* v___x_3071_, lean_object* v_a_3072_, lean_object* v___x_3073_, lean_object* v___x_3074_, lean_object* v___x_3075_, lean_object* v_matchDeclName_3076_, lean_object* v___x_3077_, lean_object* v___x_3078_, lean_object* v___x_3079_, lean_object* v_a_3080_, lean_object* v_b_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
uint8_t v___x_3087_; 
v___x_3087_ = lean_nat_dec_lt(v_a_3080_, v_upperBound_3068_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; 
lean_dec(v_a_3080_);
lean_dec(v___x_3079_);
lean_dec_ref(v___x_3078_);
lean_dec(v___x_3077_);
lean_dec(v_matchDeclName_3076_);
lean_dec_ref(v___x_3075_);
lean_dec_ref(v___x_3074_);
lean_dec(v___x_3073_);
lean_dec_ref(v_a_3072_);
lean_dec_ref(v___x_3071_);
lean_dec(v_baseName_3070_);
lean_dec_ref(v_val_3069_);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_b_3081_);
return v___x_3088_;
}
else
{
lean_object* v_snd_3089_; lean_object* v_snd_3090_; lean_object* v_snd_3091_; lean_object* v_fst_3092_; lean_object* v_fst_3093_; lean_object* v_fst_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3177_; 
v_snd_3089_ = lean_ctor_get(v_b_3081_, 1);
lean_inc(v_snd_3089_);
v_snd_3090_ = lean_ctor_get(v_snd_3089_, 1);
lean_inc(v_snd_3090_);
v_snd_3091_ = lean_ctor_get(v_snd_3090_, 1);
lean_inc(v_snd_3091_);
v_fst_3092_ = lean_ctor_get(v_b_3081_, 0);
lean_inc(v_fst_3092_);
lean_dec_ref(v_b_3081_);
v_fst_3093_ = lean_ctor_get(v_snd_3089_, 0);
lean_inc(v_fst_3093_);
lean_dec(v_snd_3089_);
v_fst_3094_ = lean_ctor_get(v_snd_3090_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_snd_3090_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v_snd_3090_, 1);
lean_dec(v_unused_3178_);
v___x_3096_ = v_snd_3090_;
v_isShared_3097_ = v_isSharedCheck_3177_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_fst_3094_);
lean_dec(v_snd_3090_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3177_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_fst_3098_; lean_object* v_snd_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3176_; 
v_fst_3098_ = lean_ctor_get(v_snd_3091_, 0);
v_snd_3099_ = lean_ctor_get(v_snd_3091_, 1);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_snd_3091_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3101_ = v_snd_3091_;
v_isShared_3102_ = v_isSharedCheck_3176_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_snd_3099_);
lean_inc(v_fst_3098_);
lean_dec(v_snd_3091_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3176_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v_altInfos_3103_; lean_object* v_overlaps_3104_; lean_object* v_start_3105_; lean_object* v_stop_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___f_3118_; lean_object* v___x_3119_; lean_object* v___y_3121_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
v_altInfos_3103_ = lean_ctor_get(v_val_3069_, 2);
v_overlaps_3104_ = lean_ctor_get(v_val_3069_, 5);
v_start_3105_ = lean_ctor_get(v___x_3078_, 1);
v_stop_3106_ = lean_ctor_get(v___x_3078_, 2);
v___x_3107_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3108_ = l_Lean_instInhabitedExpr;
v___x_3109_ = lean_unsigned_to_nat(0u);
v___x_3110_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3111_ = lean_box(0);
v___x_3112_ = lean_unsigned_to_nat(1u);
v___x_3113_ = lean_array_get_borrowed(v___x_3107_, v_altInfos_3103_, v_a_3080_);
v___x_3114_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3070_);
v___x_3115_ = l_Lean_Name_str___override(v_baseName_3070_, v___x_3114_);
lean_inc(v_fst_3094_);
v___x_3116_ = lean_name_append_index_after(v___x_3115_, v_fst_3094_);
v___x_3117_ = lean_box(v___x_3087_);
lean_inc(v___x_3079_);
lean_inc_ref(v___x_3078_);
lean_inc(v___x_3077_);
lean_inc(v___x_3116_);
lean_inc(v_matchDeclName_3076_);
lean_inc_ref(v___x_3075_);
lean_inc_ref(v___x_3074_);
lean_inc(v___x_3073_);
lean_inc_ref(v_a_3072_);
lean_inc_ref(v___x_3071_);
lean_inc(v_fst_3093_);
lean_inc(v_a_3080_);
lean_inc_ref(v_overlaps_3104_);
v___f_3118_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3118_, 0, v___x_3112_);
lean_closure_set(v___f_3118_, 1, v_overlaps_3104_);
lean_closure_set(v___f_3118_, 2, v_a_3080_);
lean_closure_set(v___f_3118_, 3, v_fst_3093_);
lean_closure_set(v___f_3118_, 4, v___x_3110_);
lean_closure_set(v___f_3118_, 5, v___x_3109_);
lean_closure_set(v___f_3118_, 6, v___x_3071_);
lean_closure_set(v___f_3118_, 7, v___x_3117_);
lean_closure_set(v___f_3118_, 8, v___x_3108_);
lean_closure_set(v___f_3118_, 9, v_a_3072_);
lean_closure_set(v___f_3118_, 10, v___x_3073_);
lean_closure_set(v___f_3118_, 11, v___x_3074_);
lean_closure_set(v___f_3118_, 12, v___x_3075_);
lean_closure_set(v___f_3118_, 13, v_matchDeclName_3076_);
lean_closure_set(v___f_3118_, 14, v___x_3116_);
lean_closure_set(v___f_3118_, 15, v___x_3077_);
lean_closure_set(v___f_3118_, 16, v___x_3111_);
lean_closure_set(v___f_3118_, 17, v___x_3078_);
lean_closure_set(v___f_3118_, 18, v___x_3079_);
v___x_3119_ = lean_array_push(v_fst_3092_, v___x_3116_);
v___x_3172_ = lean_nat_sub(v_stop_3106_, v_start_3105_);
v___x_3173_ = lean_nat_dec_lt(v_a_3080_, v___x_3172_);
lean_dec(v___x_3172_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; 
v___x_3174_ = l_outOfBounds___redArg(v___x_3108_);
v___y_3121_ = v___x_3174_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Subarray_get___redArg(v___x_3078_, v_a_3080_);
v___y_3121_ = v___x_3175_;
goto v___jp_3120_;
}
v___jp_3120_:
{
lean_object* v___x_3122_; 
lean_inc(v___y_3085_);
lean_inc_ref(v___y_3084_);
lean_inc(v___y_3083_);
lean_inc_ref(v___y_3082_);
v___x_3122_ = lean_infer_type(v___y_3121_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3124_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___x_3122_, 1);
lean_inc(v___x_3079_);
lean_inc(v___x_3113_);
v___x_3124_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3123_, v___x_3113_, v___x_3079_, v___f_3118_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; lean_object* v_snd_3126_; lean_object* v_fst_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3155_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref_known(v___x_3124_, 1);
v_snd_3126_ = lean_ctor_get(v_a_3125_, 1);
v_fst_3127_ = lean_ctor_get(v_a_3125_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_a_3125_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3129_ = v_a_3125_;
v_isShared_3130_ = v_isSharedCheck_3155_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_snd_3126_);
lean_inc(v_fst_3127_);
lean_dec(v_a_3125_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3155_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v_fst_3131_; lean_object* v_snd_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3154_; 
v_fst_3131_ = lean_ctor_get(v_snd_3126_, 0);
v_snd_3132_ = lean_ctor_get(v_snd_3126_, 1);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_snd_3126_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3134_ = v_snd_3126_;
v_isShared_3135_ = v_isSharedCheck_3154_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_snd_3132_);
lean_inc(v_fst_3131_);
lean_dec(v_snd_3126_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3154_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3136_ = lean_array_push(v_fst_3093_, v_fst_3127_);
v___x_3137_ = lean_array_push(v_fst_3098_, v_fst_3131_);
v___x_3138_ = lean_array_push(v_snd_3099_, v_snd_3132_);
v___x_3139_ = lean_nat_add(v_fst_3094_, v___x_3112_);
lean_dec(v_fst_3094_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 1, v___x_3138_);
lean_ctor_set(v___x_3134_, 0, v___x_3137_);
v___x_3141_ = v___x_3134_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v___x_3138_);
v___x_3141_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3143_; 
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 1, v___x_3141_);
lean_ctor_set(v___x_3129_, 0, v___x_3139_);
v___x_3143_ = v___x_3129_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
lean_object* v___x_3145_; 
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 1, v___x_3143_);
lean_ctor_set(v___x_3101_, 0, v___x_3136_);
v___x_3145_ = v___x_3101_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3147_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 1, v___x_3145_);
lean_ctor_set(v___x_3096_, 0, v___x_3119_);
v___x_3147_ = v___x_3096_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_nat_add(v_a_3080_, v___x_3112_);
lean_dec(v_a_3080_);
v_a_3080_ = v___x_3148_;
v_b_3081_ = v___x_3147_;
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
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v___x_3119_);
lean_del_object(v___x_3101_);
lean_dec(v_snd_3099_);
lean_dec(v_fst_3098_);
lean_del_object(v___x_3096_);
lean_dec(v_fst_3094_);
lean_dec(v_fst_3093_);
lean_dec(v_a_3080_);
lean_dec(v___x_3079_);
lean_dec_ref(v___x_3078_);
lean_dec(v___x_3077_);
lean_dec(v_matchDeclName_3076_);
lean_dec_ref(v___x_3075_);
lean_dec_ref(v___x_3074_);
lean_dec(v___x_3073_);
lean_dec_ref(v_a_3072_);
lean_dec_ref(v___x_3071_);
lean_dec(v_baseName_3070_);
lean_dec_ref(v_val_3069_);
v_a_3156_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3124_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3124_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref(v___x_3119_);
lean_dec_ref(v___f_3118_);
lean_del_object(v___x_3101_);
lean_dec(v_snd_3099_);
lean_dec(v_fst_3098_);
lean_del_object(v___x_3096_);
lean_dec(v_fst_3094_);
lean_dec(v_fst_3093_);
lean_dec(v_a_3080_);
lean_dec(v___x_3079_);
lean_dec_ref(v___x_3078_);
lean_dec(v___x_3077_);
lean_dec(v_matchDeclName_3076_);
lean_dec_ref(v___x_3075_);
lean_dec_ref(v___x_3074_);
lean_dec(v___x_3073_);
lean_dec_ref(v_a_3072_);
lean_dec_ref(v___x_3071_);
lean_dec(v_baseName_3070_);
lean_dec_ref(v_val_3069_);
v_a_3164_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3122_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3122_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
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
lean_object* v_upperBound_3179_ = _args[0];
lean_object* v_val_3180_ = _args[1];
lean_object* v_baseName_3181_ = _args[2];
lean_object* v___x_3182_ = _args[3];
lean_object* v_a_3183_ = _args[4];
lean_object* v___x_3184_ = _args[5];
lean_object* v___x_3185_ = _args[6];
lean_object* v___x_3186_ = _args[7];
lean_object* v_matchDeclName_3187_ = _args[8];
lean_object* v___x_3188_ = _args[9];
lean_object* v___x_3189_ = _args[10];
lean_object* v___x_3190_ = _args[11];
lean_object* v_a_3191_ = _args[12];
lean_object* v_b_3192_ = _args[13];
lean_object* v___y_3193_ = _args[14];
lean_object* v___y_3194_ = _args[15];
lean_object* v___y_3195_ = _args[16];
lean_object* v___y_3196_ = _args[17];
lean_object* v___y_3197_ = _args[18];
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3179_, v_val_3180_, v_baseName_3181_, v___x_3182_, v_a_3183_, v___x_3184_, v___x_3185_, v___x_3186_, v_matchDeclName_3187_, v___x_3188_, v___x_3189_, v___x_3190_, v_a_3191_, v_b_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v_upperBound_3179_);
return v_res_3198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3202_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3203_ = lean_unsigned_to_nat(6u);
v___x_3204_ = lean_unsigned_to_nat(233u);
v___x_3205_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3206_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3207_ = l_mkPanicMessageWithDecl(v___x_3206_, v___x_3205_, v___x_3204_, v___x_3203_, v___x_3202_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3220_, lean_object* v_matchDeclName_3221_, lean_object* v_numParams_3222_, lean_object* v_val_3223_, lean_object* v___x_3224_, lean_object* v_numDiscrs_3225_, lean_object* v_baseName_3226_, lean_object* v_a_3227_, lean_object* v___x_3228_, lean_object* v___x_3229_, lean_object* v___x_3230_, lean_object* v_uElimPos_x3f_3231_, lean_object* v_discrInfos_3232_, lean_object* v_overlaps_3233_, lean_object* v___f_3234_, lean_object* v___x_3235_, lean_object* v_altInfos_3236_, lean_object* v_xs_3237_, lean_object* v___matchResultType_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; uint8_t v___y_3256_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v_lower_3264_; lean_object* v_upper_3265_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3258_ = lean_box(0);
v___x_3259_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3222_);
lean_inc_ref(v_xs_3237_);
v___x_3260_ = l_Array_toSubarray___redArg(v_xs_3237_, v___x_3259_, v_numParams_3222_);
v___x_3261_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3223_);
v___x_3262_ = lean_array_get(v___x_3224_, v_xs_3237_, v___x_3261_);
lean_dec(v___x_3261_);
v___x_3318_ = lean_array_get_size(v_xs_3237_);
v___x_3319_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3223_);
v___x_3320_ = lean_nat_sub(v___x_3318_, v___x_3319_);
lean_dec(v___x_3319_);
v___x_3321_ = lean_nat_dec_le(v___x_3320_, v___x_3259_);
if (v___x_3321_ == 0)
{
v_lower_3264_ = v___x_3320_;
v_upper_3265_ = v___x_3318_;
goto v___jp_3263_;
}
else
{
lean_dec(v___x_3320_);
v_lower_3264_ = v___x_3259_;
v_upper_3265_ = v___x_3318_;
goto v___jp_3263_;
}
v___jp_3244_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3246_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3245_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
return v___x_3246_;
}
v___jp_3247_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3250_, 0, v___y_3248_);
lean_ctor_set(v___x_3250_, 1, v_splitterName_3220_);
lean_ctor_set(v___x_3250_, 2, v___y_3249_);
v___x_3251_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3221_, v___x_3250_, v___y_3242_);
return v___x_3251_;
}
v___jp_3252_:
{
lean_object* v___x_3257_; 
lean_inc(v_matchDeclName_3221_);
v___x_3257_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3221_, v___y_3256_, v___y_3253_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_dec_ref_known(v___x_3257_, 1);
v___y_3248_ = v___y_3254_;
v___y_3249_ = v___y_3255_;
goto v___jp_3247_;
}
else
{
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec(v_matchDeclName_3221_);
lean_dec(v_splitterName_3220_);
return v___x_3257_;
}
}
v___jp_3263_:
{
lean_object* v___x_3266_; lean_object* v_start_3267_; lean_object* v_stop_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_inc_ref(v_xs_3237_);
v___x_3266_ = l_Array_toSubarray___redArg(v_xs_3237_, v_lower_3264_, v_upper_3265_);
v_start_3267_ = lean_ctor_get(v___x_3266_, 1);
v_stop_3268_ = lean_ctor_get(v___x_3266_, 2);
v___x_3269_ = lean_unsigned_to_nat(1u);
v___x_3270_ = lean_nat_add(v_numParams_3222_, v___x_3269_);
v___x_3271_ = lean_nat_add(v___x_3270_, v_numDiscrs_3225_);
v___x_3272_ = lean_nat_sub(v_stop_3268_, v_start_3267_);
v___x_3273_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3274_ = l_Array_toSubarray___redArg(v_xs_3237_, v___x_3270_, v___x_3271_);
lean_inc(v___x_3229_);
lean_inc(v_matchDeclName_3221_);
lean_inc(v___x_3228_);
v___x_3275_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3272_, v_val_3223_, v_baseName_3226_, v___x_3274_, v_a_3227_, v___x_3228_, v___x_3260_, v___x_3262_, v_matchDeclName_3221_, v___x_3229_, v___x_3266_, v___x_3230_, v___x_3259_, v___x_3273_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
lean_dec(v___x_3272_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v_snd_3277_; lean_object* v_snd_3278_; lean_object* v_snd_3279_; lean_object* v_fst_3280_; lean_object* v_fst_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3308_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3275_, 1);
v_snd_3277_ = lean_ctor_get(v_a_3276_, 1);
v_snd_3278_ = lean_ctor_get(v_snd_3277_, 1);
v_snd_3279_ = lean_ctor_get(v_snd_3278_, 1);
lean_inc(v_snd_3279_);
v_fst_3280_ = lean_ctor_get(v_a_3276_, 0);
lean_inc(v_fst_3280_);
lean_dec(v_a_3276_);
v_fst_3281_ = lean_ctor_get(v_snd_3279_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_snd_3279_);
if (v_isSharedCheck_3308_ == 0)
{
lean_object* v_unused_3309_; 
v_unused_3309_ = lean_ctor_get(v_snd_3279_, 1);
lean_dec(v_unused_3309_);
v___x_3283_ = v_snd_3279_;
v_isShared_3284_ = v_isSharedCheck_3308_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_fst_3281_);
lean_dec(v_snd_3279_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3308_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; uint8_t v___x_3286_; 
lean_inc_ref(v_overlaps_3233_);
lean_inc(v_fst_3281_);
v___x_3285_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3285_, 0, v_numParams_3222_);
lean_ctor_set(v___x_3285_, 1, v_numDiscrs_3225_);
lean_ctor_set(v___x_3285_, 2, v_fst_3281_);
lean_ctor_set(v___x_3285_, 3, v_uElimPos_x3f_3231_);
lean_ctor_set(v___x_3285_, 4, v_discrInfos_3232_);
lean_ctor_set(v___x_3285_, 5, v_overlaps_3233_);
v___x_3286_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3233_);
lean_dec_ref(v_overlaps_3233_);
if (v___x_3286_ == 0)
{
uint8_t v___x_3287_; 
lean_del_object(v___x_3283_);
lean_dec(v_fst_3281_);
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3229_);
lean_dec(v___x_3228_);
v___x_3287_ = 1;
v___y_3253_ = v___f_3234_;
v___y_3254_ = v_fst_3280_;
v___y_3255_ = v___x_3285_;
v___y_3256_ = v___x_3287_;
goto v___jp_3252_;
}
else
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3289_ = lean_find_expr(v___x_3288_, v___x_3235_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v___x_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
lean_dec_ref(v___f_3234_);
v___x_3290_ = lean_array_get_size(v_altInfos_3236_);
v___x_3291_ = lean_array_get_size(v_fst_3281_);
v___x_3292_ = lean_nat_dec_eq(v___x_3290_, v___x_3291_);
if (v___x_3292_ == 0)
{
lean_dec_ref_known(v___x_3285_, 6);
lean_del_object(v___x_3283_);
lean_dec(v_fst_3281_);
lean_dec(v_fst_3280_);
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3229_);
lean_dec(v___x_3228_);
lean_dec(v_matchDeclName_3221_);
lean_dec(v_splitterName_3220_);
goto v___jp_3244_;
}
else
{
uint8_t v___x_3293_; 
v___x_3293_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3236_, v_fst_3281_, v___x_3290_);
lean_dec(v_fst_3281_);
if (v___x_3293_ == 0)
{
lean_dec_ref_known(v___x_3285_, 6);
lean_del_object(v___x_3283_);
lean_dec(v_fst_3280_);
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3229_);
lean_dec(v___x_3228_);
lean_dec(v_matchDeclName_3221_);
lean_dec(v_splitterName_3220_);
goto v___jp_3244_;
}
else
{
uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3300_; 
v___x_3294_ = 0;
lean_inc_n(v_splitterName_3220_, 2);
v___x_3295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3295_, 0, v_splitterName_3220_);
lean_ctor_set(v___x_3295_, 1, v___x_3229_);
lean_ctor_set(v___x_3295_, 2, v___x_3235_);
lean_inc(v_matchDeclName_3221_);
v___x_3296_ = l_Lean_mkConst(v_matchDeclName_3221_, v___x_3228_);
v___x_3297_ = lean_box(1);
v___x_3298_ = 1;
if (v_isShared_3284_ == 0)
{
lean_ctor_set_tag(v___x_3283_, 1);
lean_ctor_set(v___x_3283_, 1, v___x_3258_);
lean_ctor_set(v___x_3283_, 0, v_splitterName_3220_);
v___x_3300_ = v___x_3283_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_splitterName_3220_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v___x_3258_);
v___x_3300_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3301_, 0, v___x_3295_);
lean_ctor_set(v___x_3301_, 1, v___x_3296_);
lean_ctor_set(v___x_3301_, 2, v___x_3297_);
lean_ctor_set(v___x_3301_, 3, v___x_3300_);
lean_ctor_set_uint8(v___x_3301_, sizeof(void*)*4, v___x_3298_);
v___x_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_inc_ref(v___x_3302_);
v___x_3303_ = l_Lean_addDecl(v___x_3302_, v___x_3294_, v___y_3241_, v___y_3242_);
if (lean_obj_tag(v___x_3303_) == 0)
{
uint8_t v___x_3304_; lean_object* v___x_3305_; 
lean_dec_ref_known(v___x_3303_, 1);
v___x_3304_ = 0;
lean_inc(v_splitterName_3220_);
v___x_3305_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3220_, v___x_3304_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v___x_3306_; 
lean_dec_ref_known(v___x_3305_, 1);
v___x_3306_ = l_Lean_compileDecl(v___x_3302_, v___x_3294_, v___y_3241_, v___y_3242_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_dec_ref_known(v___x_3306_, 1);
v___y_3248_ = v_fst_3280_;
v___y_3249_ = v___x_3285_;
goto v___jp_3247_;
}
else
{
lean_dec_ref_known(v___x_3285_, 6);
lean_dec(v_fst_3280_);
lean_dec(v_matchDeclName_3221_);
lean_dec(v_splitterName_3220_);
return v___x_3306_;
}
}
else
{
lean_dec_ref_known(v___x_3302_, 1);
lean_dec_ref_known(v___x_3285_, 6);
lean_dec(v_fst_3280_);
lean_dec(v_matchDeclName_3221_);
lean_dec(v_splitterName_3220_);
return v___x_3305_;
}
}
else
{
lean_dec_ref_known(v___x_3302_, 1);
lean_dec_ref_known(v___x_3285_, 6);
lean_dec(v_fst_3280_);
lean_dec(v_matchDeclName_3221_);
lean_dec(v_splitterName_3220_);
return v___x_3303_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3289_, 1);
lean_del_object(v___x_3283_);
lean_dec(v_fst_3281_);
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3229_);
lean_dec(v___x_3228_);
v___y_3253_ = v___f_3234_;
v___y_3254_ = v_fst_3280_;
v___y_3255_ = v___x_3285_;
v___y_3256_ = v___x_3286_;
goto v___jp_3252_;
}
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec_ref(v___x_3235_);
lean_dec_ref(v___f_3234_);
lean_dec_ref(v_overlaps_3233_);
lean_dec_ref(v_discrInfos_3232_);
lean_dec(v_uElimPos_x3f_3231_);
lean_dec(v___x_3229_);
lean_dec(v___x_3228_);
lean_dec(v_numDiscrs_3225_);
lean_dec(v_numParams_3222_);
lean_dec(v_matchDeclName_3221_);
lean_dec(v_splitterName_3220_);
v_a_3310_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3275_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3275_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3322_ = _args[0];
lean_object* v_matchDeclName_3323_ = _args[1];
lean_object* v_numParams_3324_ = _args[2];
lean_object* v_val_3325_ = _args[3];
lean_object* v___x_3326_ = _args[4];
lean_object* v_numDiscrs_3327_ = _args[5];
lean_object* v_baseName_3328_ = _args[6];
lean_object* v_a_3329_ = _args[7];
lean_object* v___x_3330_ = _args[8];
lean_object* v___x_3331_ = _args[9];
lean_object* v___x_3332_ = _args[10];
lean_object* v_uElimPos_x3f_3333_ = _args[11];
lean_object* v_discrInfos_3334_ = _args[12];
lean_object* v_overlaps_3335_ = _args[13];
lean_object* v___f_3336_ = _args[14];
lean_object* v___x_3337_ = _args[15];
lean_object* v_altInfos_3338_ = _args[16];
lean_object* v_xs_3339_ = _args[17];
lean_object* v___matchResultType_3340_ = _args[18];
lean_object* v___y_3341_ = _args[19];
lean_object* v___y_3342_ = _args[20];
lean_object* v___y_3343_ = _args[21];
lean_object* v___y_3344_ = _args[22];
lean_object* v___y_3345_ = _args[23];
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3322_, v_matchDeclName_3323_, v_numParams_3324_, v_val_3325_, v___x_3326_, v_numDiscrs_3327_, v_baseName_3328_, v_a_3329_, v___x_3330_, v___x_3331_, v___x_3332_, v_uElimPos_x3f_3333_, v_discrInfos_3334_, v_overlaps_3335_, v___f_3336_, v___x_3337_, v_altInfos_3338_, v_xs_3339_, v___matchResultType_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec_ref(v___matchResultType_3340_);
lean_dec_ref(v_altInfos_3338_);
lean_dec_ref(v___x_3326_);
return v_res_3346_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
return v___x_3348_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3349_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3350_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3351_ = lean_unsigned_to_nat(0u);
v___x_3352_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
lean_ctor_set(v___x_3352_, 2, v___x_3351_);
lean_ctor_set(v___x_3352_, 3, v___x_3351_);
lean_ctor_set(v___x_3352_, 4, v___x_3350_);
lean_ctor_set(v___x_3352_, 5, v___x_3350_);
lean_ctor_set(v___x_3352_, 6, v___x_3350_);
lean_ctor_set(v___x_3352_, 7, v___x_3350_);
lean_ctor_set(v___x_3352_, 8, v___x_3350_);
lean_ctor_set(v___x_3352_, 9, v___x_3350_);
lean_ctor_set(v___x_3352_, 10, v___x_3350_);
lean_ctor_set(v___x_3352_, 11, v___x_3349_);
return v___x_3352_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3353_ = lean_box(1);
v___x_3354_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3355_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
lean_ctor_set(v___x_3356_, 1, v___x_3354_);
lean_ctor_set(v___x_3356_, 2, v___x_3353_);
return v___x_3356_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3));
v___x_3359_ = l_Lean_stringToMessageData(v___x_3358_);
return v___x_3359_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_3362_ = l_Lean_stringToMessageData(v___x_3361_);
return v___x_3362_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_3365_ = l_Lean_stringToMessageData(v___x_3364_);
return v___x_3365_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_3368_ = l_Lean_stringToMessageData(v___x_3367_);
return v___x_3368_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_3371_ = l_Lean_stringToMessageData(v___x_3370_);
return v___x_3371_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_3374_ = l_Lean_stringToMessageData(v___x_3373_);
return v___x_3374_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_3377_ = l_Lean_stringToMessageData(v___x_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3378_, lean_object* v_declHint_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v_env_3384_; uint8_t v___x_3385_; 
v___x_3382_ = lean_box(0);
v___x_3383_ = lean_st_ref_get(v___y_3380_);
v_env_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc_ref(v_env_3384_);
lean_dec(v___x_3383_);
v___x_3385_ = l_Lean_Name_isAnonymous(v_declHint_3379_);
if (v___x_3385_ == 0)
{
uint8_t v_isExporting_3386_; 
v_isExporting_3386_ = lean_ctor_get_uint8(v_env_3384_, sizeof(void*)*13);
if (v_isExporting_3386_ == 0)
{
lean_object* v___x_3387_; 
lean_dec_ref(v_env_3384_);
lean_dec(v_declHint_3379_);
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v_msg_3378_);
return v___x_3387_;
}
else
{
lean_object* v___x_3388_; uint8_t v___x_3389_; 
lean_inc_ref(v_env_3384_);
v___x_3388_ = l_Lean_Environment_setExporting(v_env_3384_, v___x_3385_);
lean_inc(v_declHint_3379_);
lean_inc_ref(v___x_3388_);
v___x_3389_ = l_Lean_Environment_contains(v___x_3388_, v_declHint_3379_, v_isExporting_3386_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; 
lean_dec_ref(v___x_3388_);
lean_dec_ref(v_env_3384_);
lean_dec(v_declHint_3379_);
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v_msg_3378_);
return v___x_3390_;
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v_c_3396_; lean_object* v___x_3397_; 
v___x_3391_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3392_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3393_ = l_Lean_Options_empty;
lean_inc_ref(v___x_3388_);
v___x_3394_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3388_);
lean_ctor_set(v___x_3394_, 1, v___x_3391_);
lean_ctor_set(v___x_3394_, 2, v___x_3392_);
lean_ctor_set(v___x_3394_, 3, v___x_3393_);
lean_inc(v_declHint_3379_);
v___x_3395_ = l_Lean_MessageData_ofConstName(v_declHint_3379_, v___x_3385_);
v_c_3396_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3396_, 0, v___x_3394_);
lean_ctor_set(v_c_3396_, 1, v___x_3395_);
v___x_3397_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3388_, v_declHint_3379_);
lean_dec_ref(v___x_3388_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
lean_dec_ref(v_env_3384_);
lean_dec(v_declHint_3379_);
v___x_3398_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
lean_ctor_set(v___x_3399_, 1, v_c_3396_);
v___x_3400_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_3401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = l_Lean_MessageData_note(v___x_3401_);
v___x_3403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3403_, 0, v_msg_3378_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
return v___x_3404_;
}
else
{
lean_object* v_val_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3439_; 
v_val_3405_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3407_ = v___x_3397_;
v_isShared_3408_ = v_isSharedCheck_3439_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_val_3405_);
lean_dec(v___x_3397_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3439_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3409_; lean_object* v_moduleNames_3410_; lean_object* v_mod_3411_; uint8_t v___x_3412_; 
v___x_3409_ = l_Lean_Environment_header(v_env_3384_);
lean_dec_ref(v_env_3384_);
v_moduleNames_3410_ = lean_ctor_get(v___x_3409_, 4);
lean_inc_ref(v_moduleNames_3410_);
lean_dec_ref(v___x_3409_);
v_mod_3411_ = lean_array_get(v___x_3382_, v_moduleNames_3410_, v_val_3405_);
lean_dec(v_val_3405_);
lean_dec_ref(v_moduleNames_3410_);
v___x_3412_ = l_Lean_isPrivateName(v_declHint_3379_);
lean_dec(v_declHint_3379_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3413_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_3414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set(v___x_3414_, 1, v_c_3396_);
v___x_3415_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3414_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = l_Lean_MessageData_ofName(v_mod_3411_);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = l_Lean_MessageData_note(v___x_3420_);
v___x_3422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3422_, 0, v_msg_3378_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set_tag(v___x_3407_, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3422_);
v___x_3424_ = v___x_3407_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3426_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_3427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v_c_3396_);
v___x_3428_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = l_Lean_MessageData_ofName(v_mod_3411_);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = l_Lean_MessageData_note(v___x_3433_);
v___x_3435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3435_, 0, v_msg_3378_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set_tag(v___x_3407_, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3435_);
v___x_3437_ = v___x_3407_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3440_; 
lean_dec_ref(v_env_3384_);
lean_dec(v_declHint_3379_);
v___x_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3440_, 0, v_msg_3378_);
return v___x_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3441_, lean_object* v_declHint_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3441_, v_declHint_3442_, v___y_3443_);
lean_dec(v___y_3443_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3446_, lean_object* v_declHint_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v___x_3453_; lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3463_; 
v___x_3453_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3446_, v_declHint_3447_, v___y_3451_);
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3456_ = v___x_3453_;
v_isShared_3457_ = v_isSharedCheck_3463_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3463_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3458_ = l_Lean_unknownIdentifierMessageTag;
v___x_3459_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v_a_3454_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3459_);
v___x_3461_ = v___x_3456_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3464_, lean_object* v_declHint_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3464_, v_declHint_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3472_, lean_object* v_msg_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_toCold_3479_; lean_object* v_currRecDepth_3480_; lean_object* v_ref_3481_; uint16_t v_optionFlags_3482_; uint8_t v_suppressElabErrors_3483_; uint8_t v_checkDeprecated_3484_; uint8_t v_isRecordingDeps_3485_; lean_object* v_ref_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_toCold_3479_ = lean_ctor_get(v___y_3476_, 0);
v_currRecDepth_3480_ = lean_ctor_get(v___y_3476_, 1);
v_ref_3481_ = lean_ctor_get(v___y_3476_, 2);
v_optionFlags_3482_ = lean_ctor_get_uint16(v___y_3476_, sizeof(void*)*3);
v_suppressElabErrors_3483_ = lean_ctor_get_uint8(v___y_3476_, sizeof(void*)*3 + 2);
v_checkDeprecated_3484_ = lean_ctor_get_uint8(v___y_3476_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3485_ = lean_ctor_get_uint8(v___y_3476_, sizeof(void*)*3 + 4);
v_ref_3486_ = l_Lean_replaceRef(v_ref_3472_, v_ref_3481_);
lean_inc(v_currRecDepth_3480_);
lean_inc_ref(v_toCold_3479_);
v___x_3487_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3487_, 0, v_toCold_3479_);
lean_ctor_set(v___x_3487_, 1, v_currRecDepth_3480_);
lean_ctor_set(v___x_3487_, 2, v_ref_3486_);
lean_ctor_set_uint16(v___x_3487_, sizeof(void*)*3, v_optionFlags_3482_);
lean_ctor_set_uint8(v___x_3487_, sizeof(void*)*3 + 2, v_suppressElabErrors_3483_);
lean_ctor_set_uint8(v___x_3487_, sizeof(void*)*3 + 3, v_checkDeprecated_3484_);
lean_ctor_set_uint8(v___x_3487_, sizeof(void*)*3 + 4, v_isRecordingDeps_3485_);
v___x_3488_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3473_, v___y_3474_, v___y_3475_, v___x_3487_, v___y_3477_);
lean_dec_ref_known(v___x_3487_, 3);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3489_, lean_object* v_msg_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3489_, v_msg_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v_ref_3489_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3497_, lean_object* v_msg_3498_, lean_object* v_declHint_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v___x_3505_; lean_object* v_a_3506_; lean_object* v___x_3507_; 
v___x_3505_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3498_, v_declHint_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref(v___x_3505_);
v___x_3507_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3497_, v_a_3506_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3508_, lean_object* v_msg_3509_, lean_object* v_declHint_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3508_, v_msg_3509_, v_declHint_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v_ref_3508_);
return v_res_3516_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3519_ = l_Lean_stringToMessageData(v___x_3518_);
return v___x_3519_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3522_ = l_Lean_stringToMessageData(v___x_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3523_, lean_object* v_constName_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3530_; uint8_t v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3530_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3531_ = 0;
lean_inc(v_constName_3524_);
v___x_3532_ = l_Lean_MessageData_ofConstName(v_constName_3524_, v___x_3531_);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3530_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3523_, v___x_3535_, v_constName_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3537_, lean_object* v_constName_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3537_, v_constName_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v_ref_3537_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_ref_3551_; lean_object* v___x_3552_; 
v_ref_3551_ = lean_ctor_get(v___y_3548_, 2);
v___x_3552_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3551_, v_constName_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3566_; lean_object* v_env_3567_; uint8_t v___x_3568_; lean_object* v___x_3569_; 
v___x_3566_ = lean_st_ref_get(v___y_3564_);
v_env_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc_ref(v_env_3567_);
lean_dec(v___x_3566_);
v___x_3568_ = 0;
lean_inc(v_constName_3560_);
v___x_3569_ = l_Lean_Environment_find_x3f(v_env_3567_, v_constName_3560_, v___x_3568_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
return v___x_3570_;
}
else
{
lean_object* v_val_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec(v_constName_3560_);
v_val_3571_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3569_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_val_3571_);
lean_dec(v___x_3569_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set_tag(v___x_3573_, 0);
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_val_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_a_3586_, lean_object* v_a_3587_){
_start:
{
if (lean_obj_tag(v_a_3586_) == 0)
{
lean_object* v___x_3588_; 
v___x_3588_ = l_List_reverse___redArg(v_a_3587_);
return v___x_3588_;
}
else
{
lean_object* v_head_3589_; lean_object* v_tail_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3599_; 
v_head_3589_ = lean_ctor_get(v_a_3586_, 0);
v_tail_3590_ = lean_ctor_get(v_a_3586_, 1);
v_isSharedCheck_3599_ = !lean_is_exclusive(v_a_3586_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3592_ = v_a_3586_;
v_isShared_3593_ = v_isSharedCheck_3599_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_tail_3590_);
lean_inc(v_head_3589_);
lean_dec(v_a_3586_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3599_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3594_ = l_Lean_mkLevelParam(v_head_3589_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 1, v_a_3587_);
lean_ctor_set(v___x_3592_, 0, v___x_3594_);
v___x_3596_ = v___x_3592_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3594_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_a_3587_);
v___x_3596_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
v_a_3586_ = v_tail_3590_;
v_a_3587_ = v___x_3596_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3602_ = l_Lean_stringToMessageData(v___x_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3603_, lean_object* v_baseName_3604_, lean_object* v_splitterName_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_){
_start:
{
lean_object* v___x_3611_; uint8_t v_foApprox_3612_; uint8_t v_ctxApprox_3613_; uint8_t v_quasiPatternApprox_3614_; uint8_t v_constApprox_3615_; uint8_t v_isDefEqStuckEx_3616_; uint8_t v_unificationHints_3617_; uint8_t v_proofIrrelevance_3618_; uint8_t v_assignSyntheticOpaque_3619_; uint8_t v_offsetCnstrs_3620_; uint8_t v_transparency_3621_; uint8_t v_univApprox_3622_; uint8_t v_iota_3623_; uint8_t v_beta_3624_; uint8_t v_proj_3625_; uint8_t v_zeta_3626_; uint8_t v_zetaDelta_3627_; uint8_t v_zetaUnused_3628_; uint8_t v_zetaHave_3629_; uint8_t v_canUnfoldPredicateConfig_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3693_; 
v___x_3611_ = l_Lean_Meta_Context_config(v_a_3606_);
v_foApprox_3612_ = lean_ctor_get_uint8(v___x_3611_, 0);
v_ctxApprox_3613_ = lean_ctor_get_uint8(v___x_3611_, 1);
v_quasiPatternApprox_3614_ = lean_ctor_get_uint8(v___x_3611_, 2);
v_constApprox_3615_ = lean_ctor_get_uint8(v___x_3611_, 3);
v_isDefEqStuckEx_3616_ = lean_ctor_get_uint8(v___x_3611_, 4);
v_unificationHints_3617_ = lean_ctor_get_uint8(v___x_3611_, 5);
v_proofIrrelevance_3618_ = lean_ctor_get_uint8(v___x_3611_, 6);
v_assignSyntheticOpaque_3619_ = lean_ctor_get_uint8(v___x_3611_, 7);
v_offsetCnstrs_3620_ = lean_ctor_get_uint8(v___x_3611_, 8);
v_transparency_3621_ = lean_ctor_get_uint8(v___x_3611_, 9);
v_univApprox_3622_ = lean_ctor_get_uint8(v___x_3611_, 11);
v_iota_3623_ = lean_ctor_get_uint8(v___x_3611_, 12);
v_beta_3624_ = lean_ctor_get_uint8(v___x_3611_, 13);
v_proj_3625_ = lean_ctor_get_uint8(v___x_3611_, 14);
v_zeta_3626_ = lean_ctor_get_uint8(v___x_3611_, 15);
v_zetaDelta_3627_ = lean_ctor_get_uint8(v___x_3611_, 16);
v_zetaUnused_3628_ = lean_ctor_get_uint8(v___x_3611_, 17);
v_zetaHave_3629_ = lean_ctor_get_uint8(v___x_3611_, 18);
v_canUnfoldPredicateConfig_3630_ = lean_ctor_get_uint8(v___x_3611_, 19);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3632_ = v___x_3611_;
v_isShared_3633_ = v_isSharedCheck_3693_;
goto v_resetjp_3631_;
}
else
{
lean_dec(v___x_3611_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3693_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
uint8_t v_trackZetaDelta_3634_; lean_object* v_zetaDeltaSet_3635_; lean_object* v_lctx_3636_; lean_object* v_localInstances_3637_; lean_object* v_defEqCtx_x3f_3638_; lean_object* v_synthPendingDepth_3639_; lean_object* v_customCanUnfoldPredicate_x3f_3640_; uint8_t v_univApprox_3641_; uint8_t v_inTypeClassResolution_3642_; uint8_t v_cacheInferType_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3691_; 
v_trackZetaDelta_3634_ = lean_ctor_get_uint8(v_a_3606_, sizeof(void*)*7);
v_zetaDeltaSet_3635_ = lean_ctor_get(v_a_3606_, 1);
v_lctx_3636_ = lean_ctor_get(v_a_3606_, 2);
v_localInstances_3637_ = lean_ctor_get(v_a_3606_, 3);
v_defEqCtx_x3f_3638_ = lean_ctor_get(v_a_3606_, 4);
v_synthPendingDepth_3639_ = lean_ctor_get(v_a_3606_, 5);
v_customCanUnfoldPredicate_x3f_3640_ = lean_ctor_get(v_a_3606_, 6);
v_univApprox_3641_ = lean_ctor_get_uint8(v_a_3606_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3642_ = lean_ctor_get_uint8(v_a_3606_, sizeof(void*)*7 + 2);
v_cacheInferType_3643_ = lean_ctor_get_uint8(v_a_3606_, sizeof(void*)*7 + 3);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_a_3606_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; 
v_unused_3692_ = lean_ctor_get(v_a_3606_, 0);
lean_dec(v_unused_3692_);
v___x_3645_ = v_a_3606_;
v_isShared_3646_ = v_isSharedCheck_3691_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3640_);
lean_inc(v_synthPendingDepth_3639_);
lean_inc(v_defEqCtx_x3f_3638_);
lean_inc(v_localInstances_3637_);
lean_inc(v_lctx_3636_);
lean_inc(v_zetaDeltaSet_3635_);
lean_dec(v_a_3606_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3691_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
uint8_t v___x_3647_; lean_object* v___x_3649_; 
v___x_3647_ = 2;
if (v_isShared_3633_ == 0)
{
v___x_3649_ = v___x_3632_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 0, v_foApprox_3612_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 1, v_ctxApprox_3613_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 2, v_quasiPatternApprox_3614_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 3, v_constApprox_3615_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 4, v_isDefEqStuckEx_3616_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 5, v_unificationHints_3617_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 6, v_proofIrrelevance_3618_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 7, v_assignSyntheticOpaque_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 8, v_offsetCnstrs_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 9, v_transparency_3621_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 11, v_univApprox_3622_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 12, v_iota_3623_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 13, v_beta_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 14, v_proj_3625_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 15, v_zeta_3626_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 16, v_zetaDelta_3627_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 17, v_zetaUnused_3628_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 18, v_zetaHave_3629_);
lean_ctor_set_uint8(v_reuseFailAlloc_3690_, 19, v_canUnfoldPredicateConfig_3630_);
v___x_3649_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
uint64_t v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
lean_ctor_set_uint8(v___x_3649_, 10, v___x_3647_);
v___x_3650_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3649_);
v___x_3651_ = l_Lean_instInhabitedExpr;
v___x_3652_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3652_, 0, v___x_3649_);
lean_ctor_set_uint64(v___x_3652_, sizeof(void*)*1, v___x_3650_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3652_);
v___x_3654_ = v___x_3645_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_zetaDeltaSet_3635_);
lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_lctx_3636_);
lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_localInstances_3637_);
lean_ctor_set(v_reuseFailAlloc_3689_, 4, v_defEqCtx_x3f_3638_);
lean_ctor_set(v_reuseFailAlloc_3689_, 5, v_synthPendingDepth_3639_);
lean_ctor_set(v_reuseFailAlloc_3689_, 6, v_customCanUnfoldPredicate_x3f_3640_);
lean_ctor_set_uint8(v_reuseFailAlloc_3689_, sizeof(void*)*7, v_trackZetaDelta_3634_);
lean_ctor_set_uint8(v_reuseFailAlloc_3689_, sizeof(void*)*7 + 1, v_univApprox_3641_);
lean_ctor_set_uint8(v_reuseFailAlloc_3689_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3642_);
lean_ctor_set_uint8(v_reuseFailAlloc_3689_, sizeof(void*)*7 + 3, v_cacheInferType_3643_);
v___x_3654_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; 
lean_inc(v_matchDeclName_3603_);
v___x_3655_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3603_, v___x_3654_, v_a_3607_, v_a_3608_, v_a_3609_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v_a_3661_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3655_, 1);
v___x_3657_ = l_Lean_ConstantInfo_levelParams(v_a_3656_);
v___x_3658_ = lean_box(0);
lean_inc(v___x_3657_);
v___x_3659_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v___x_3657_, v___x_3658_);
lean_inc(v_matchDeclName_3603_);
v___x_3660_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_3603_, v_a_3609_);
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref(v___x_3660_);
if (lean_obj_tag(v_a_3661_) == 1)
{
lean_object* v_val_3662_; lean_object* v_numParams_3663_; lean_object* v_numDiscrs_3664_; lean_object* v_altInfos_3665_; lean_object* v_uElimPos_x3f_3666_; lean_object* v_discrInfos_3667_; lean_object* v_overlaps_3668_; lean_object* v___f_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___f_3672_; uint8_t v___x_3673_; lean_object* v___x_3674_; 
v_val_3662_ = lean_ctor_get(v_a_3661_, 0);
lean_inc(v_val_3662_);
lean_dec_ref_known(v_a_3661_, 1);
v_numParams_3663_ = lean_ctor_get(v_val_3662_, 0);
lean_inc(v_numParams_3663_);
v_numDiscrs_3664_ = lean_ctor_get(v_val_3662_, 1);
lean_inc(v_numDiscrs_3664_);
v_altInfos_3665_ = lean_ctor_get(v_val_3662_, 2);
lean_inc_ref(v_altInfos_3665_);
v_uElimPos_x3f_3666_ = lean_ctor_get(v_val_3662_, 3);
lean_inc(v_uElimPos_x3f_3666_);
v_discrInfos_3667_ = lean_ctor_get(v_val_3662_, 4);
lean_inc_ref(v_discrInfos_3667_);
v_overlaps_3668_ = lean_ctor_get(v_val_3662_, 5);
lean_inc_ref_n(v_overlaps_3668_, 2);
lean_inc(v_splitterName_3605_);
v___f_3669_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3669_, 0, v_overlaps_3668_);
lean_closure_set(v___f_3669_, 1, v_splitterName_3605_);
v___x_3670_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3667_);
v___x_3671_ = l_Lean_ConstantInfo_type(v_a_3656_);
lean_inc_ref(v___x_3671_);
v___f_3672_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3672_, 0, v_splitterName_3605_);
lean_closure_set(v___f_3672_, 1, v_matchDeclName_3603_);
lean_closure_set(v___f_3672_, 2, v_numParams_3663_);
lean_closure_set(v___f_3672_, 3, v_val_3662_);
lean_closure_set(v___f_3672_, 4, v___x_3651_);
lean_closure_set(v___f_3672_, 5, v_numDiscrs_3664_);
lean_closure_set(v___f_3672_, 6, v_baseName_3604_);
lean_closure_set(v___f_3672_, 7, v_a_3656_);
lean_closure_set(v___f_3672_, 8, v___x_3659_);
lean_closure_set(v___f_3672_, 9, v___x_3657_);
lean_closure_set(v___f_3672_, 10, v___x_3670_);
lean_closure_set(v___f_3672_, 11, v_uElimPos_x3f_3666_);
lean_closure_set(v___f_3672_, 12, v_discrInfos_3667_);
lean_closure_set(v___f_3672_, 13, v_overlaps_3668_);
lean_closure_set(v___f_3672_, 14, v___f_3669_);
lean_closure_set(v___f_3672_, 15, v___x_3671_);
lean_closure_set(v___f_3672_, 16, v_altInfos_3665_);
v___x_3673_ = 0;
v___x_3674_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3671_, v___f_3672_, v___x_3673_, v___x_3673_, v___x_3654_, v_a_3607_, v_a_3608_, v_a_3609_);
lean_dec_ref(v___x_3654_);
return v___x_3674_;
}
else
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
lean_dec(v_a_3661_);
lean_dec(v___x_3659_);
lean_dec(v___x_3657_);
lean_dec(v_a_3656_);
lean_dec(v_splitterName_3605_);
lean_dec(v_baseName_3604_);
v___x_3675_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3676_ = l_Lean_MessageData_ofName(v_matchDeclName_3603_);
v___x_3677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3675_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___x_3678_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3677_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3679_, v___x_3654_, v_a_3607_, v_a_3608_, v_a_3609_);
lean_dec_ref(v___x_3654_);
return v___x_3680_;
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v___x_3654_);
lean_dec(v_splitterName_3605_);
lean_dec(v_baseName_3604_);
lean_dec(v_matchDeclName_3603_);
v_a_3681_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3655_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3655_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3694_, lean_object* v_baseName_3695_, lean_object* v_splitterName_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3694_, v_baseName_3695_, v_splitterName_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
lean_dec(v_a_3700_);
lean_dec_ref(v_a_3699_);
lean_dec(v_a_3698_);
return v_res_3702_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3703_, lean_object* v_ys_3704_, lean_object* v_hsz_3705_, lean_object* v_x_3706_, lean_object* v_x_3707_){
_start:
{
uint8_t v___x_3708_; 
v___x_3708_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3703_, v_ys_3704_, v_x_3706_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3709_, lean_object* v_ys_3710_, lean_object* v_hsz_3711_, lean_object* v_x_3712_, lean_object* v_x_3713_){
_start:
{
uint8_t v_res_3714_; lean_object* v_r_3715_; 
v_res_3714_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3709_, v_ys_3710_, v_hsz_3711_, v_x_3712_, v_x_3713_);
lean_dec_ref(v_ys_3710_);
lean_dec_ref(v_xs_3709_);
v_r_3715_ = lean_box(v_res_3714_);
return v_r_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3716_, lean_object* v_R_3717_, lean_object* v_a_3718_, lean_object* v_b_3719_){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3718_, v_b_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3721_, lean_object* v_val_3722_, lean_object* v_baseName_3723_, lean_object* v___x_3724_, lean_object* v_a_3725_, lean_object* v___x_3726_, lean_object* v___x_3727_, lean_object* v___x_3728_, lean_object* v_matchDeclName_3729_, lean_object* v___x_3730_, lean_object* v___x_3731_, lean_object* v___x_3732_, lean_object* v_inst_3733_, lean_object* v_R_3734_, lean_object* v_a_3735_, lean_object* v_b_3736_, lean_object* v_c_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3721_, v_val_3722_, v_baseName_3723_, v___x_3724_, v_a_3725_, v___x_3726_, v___x_3727_, v___x_3728_, v_matchDeclName_3729_, v___x_3730_, v___x_3731_, v___x_3732_, v_a_3735_, v_b_3736_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3744_ = _args[0];
lean_object* v_val_3745_ = _args[1];
lean_object* v_baseName_3746_ = _args[2];
lean_object* v___x_3747_ = _args[3];
lean_object* v_a_3748_ = _args[4];
lean_object* v___x_3749_ = _args[5];
lean_object* v___x_3750_ = _args[6];
lean_object* v___x_3751_ = _args[7];
lean_object* v_matchDeclName_3752_ = _args[8];
lean_object* v___x_3753_ = _args[9];
lean_object* v___x_3754_ = _args[10];
lean_object* v___x_3755_ = _args[11];
lean_object* v_inst_3756_ = _args[12];
lean_object* v_R_3757_ = _args[13];
lean_object* v_a_3758_ = _args[14];
lean_object* v_b_3759_ = _args[15];
lean_object* v_c_3760_ = _args[16];
lean_object* v___y_3761_ = _args[17];
lean_object* v___y_3762_ = _args[18];
lean_object* v___y_3763_ = _args[19];
lean_object* v___y_3764_ = _args[20];
lean_object* v___y_3765_ = _args[21];
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3744_, v_val_3745_, v_baseName_3746_, v___x_3747_, v_a_3748_, v___x_3749_, v___x_3750_, v___x_3751_, v_matchDeclName_3752_, v___x_3753_, v___x_3754_, v___x_3755_, v_inst_3756_, v_R_3757_, v_a_3758_, v_b_3759_, v_c_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v_upperBound_3744_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3767_, lean_object* v_constName_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3775_, lean_object* v_constName_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3775_, v_constName_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3783_, lean_object* v_ref_3784_, lean_object* v_constName_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3784_, v_constName_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3792_, lean_object* v_ref_3793_, lean_object* v_constName_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3792_, v_ref_3793_, v_constName_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v_ref_3793_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3801_, lean_object* v_ref_3802_, lean_object* v_msg_3803_, lean_object* v_declHint_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3802_, v_msg_3803_, v_declHint_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3811_, lean_object* v_ref_3812_, lean_object* v_msg_3813_, lean_object* v_declHint_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3811_, v_ref_3812_, v_msg_3813_, v_declHint_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v_ref_3812_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3821_, lean_object* v_declHint_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3821_, v_declHint_3822_, v___y_3826_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3829_, lean_object* v_declHint_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3829_, v_declHint_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3837_, lean_object* v_ref_3838_, lean_object* v_msg_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3838_, v_msg_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3846_, lean_object* v_ref_3847_, lean_object* v_msg_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3846_, v_ref_3847_, v_msg_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v_ref_3847_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3855_, lean_object* v_vals_3856_, lean_object* v_i_3857_, lean_object* v_k_3858_){
_start:
{
lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3859_ = lean_array_get_size(v_keys_3855_);
v___x_3860_ = lean_nat_dec_lt(v_i_3857_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_dec(v_i_3857_);
v___x_3861_ = lean_box(0);
return v___x_3861_;
}
else
{
lean_object* v_k_x27_3862_; uint8_t v___x_3863_; 
v_k_x27_3862_ = lean_array_fget_borrowed(v_keys_3855_, v_i_3857_);
v___x_3863_ = lean_name_eq(v_k_3858_, v_k_x27_3862_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_unsigned_to_nat(1u);
v___x_3865_ = lean_nat_add(v_i_3857_, v___x_3864_);
lean_dec(v_i_3857_);
v_i_3857_ = v___x_3865_;
goto _start;
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_array_fget_borrowed(v_vals_3856_, v_i_3857_);
lean_dec(v_i_3857_);
lean_inc(v___x_3867_);
v___x_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
return v___x_3868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3869_, lean_object* v_vals_3870_, lean_object* v_i_3871_, lean_object* v_k_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3869_, v_vals_3870_, v_i_3871_, v_k_3872_);
lean_dec(v_k_3872_);
lean_dec_ref(v_vals_3870_);
lean_dec_ref(v_keys_3869_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3874_, size_t v_x_3875_, lean_object* v_x_3876_){
_start:
{
if (lean_obj_tag(v_x_3874_) == 0)
{
lean_object* v_es_3877_; lean_object* v___x_3878_; size_t v___x_3879_; size_t v___x_3880_; lean_object* v_j_3881_; lean_object* v___x_3882_; 
v_es_3877_ = lean_ctor_get(v_x_3874_, 0);
v___x_3878_ = lean_box(2);
v___x_3879_ = ((size_t)31ULL);
v___x_3880_ = lean_usize_land(v_x_3875_, v___x_3879_);
v_j_3881_ = lean_usize_to_nat(v___x_3880_);
v___x_3882_ = lean_array_get_borrowed(v___x_3878_, v_es_3877_, v_j_3881_);
lean_dec(v_j_3881_);
switch(lean_obj_tag(v___x_3882_))
{
case 0:
{
lean_object* v_key_3883_; lean_object* v_val_3884_; uint8_t v___x_3885_; 
v_key_3883_ = lean_ctor_get(v___x_3882_, 0);
v_val_3884_ = lean_ctor_get(v___x_3882_, 1);
v___x_3885_ = lean_name_eq(v_x_3876_, v_key_3883_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_box(0);
return v___x_3886_;
}
else
{
lean_object* v___x_3887_; 
lean_inc(v_val_3884_);
v___x_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3887_, 0, v_val_3884_);
return v___x_3887_;
}
}
case 1:
{
lean_object* v_node_3888_; size_t v___x_3889_; size_t v___x_3890_; 
v_node_3888_ = lean_ctor_get(v___x_3882_, 0);
v___x_3889_ = ((size_t)5ULL);
v___x_3890_ = lean_usize_shift_right(v_x_3875_, v___x_3889_);
v_x_3874_ = v_node_3888_;
v_x_3875_ = v___x_3890_;
goto _start;
}
default: 
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_box(0);
return v___x_3892_;
}
}
}
else
{
lean_object* v_ks_3893_; lean_object* v_vs_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_ks_3893_ = lean_ctor_get(v_x_3874_, 0);
v_vs_3894_ = lean_ctor_get(v_x_3874_, 1);
v___x_3895_ = lean_unsigned_to_nat(0u);
v___x_3896_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3893_, v_vs_3894_, v___x_3895_, v_x_3876_);
return v___x_3896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3897_, lean_object* v_x_3898_, lean_object* v_x_3899_){
_start:
{
size_t v_x_712__boxed_3900_; lean_object* v_res_3901_; 
v_x_712__boxed_3900_ = lean_unbox_usize(v_x_3898_);
lean_dec(v_x_3898_);
v_res_3901_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3897_, v_x_712__boxed_3900_, v_x_3899_);
lean_dec(v_x_3899_);
lean_dec_ref(v_x_3897_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3902_, lean_object* v_x_3903_){
_start:
{
uint64_t v___y_3905_; 
if (lean_obj_tag(v_x_3903_) == 0)
{
uint64_t v___x_3908_; 
v___x_3908_ = 1723ULL;
v___y_3905_ = v___x_3908_;
goto v___jp_3904_;
}
else
{
uint64_t v_hash_3909_; 
v_hash_3909_ = lean_ctor_get_uint64(v_x_3903_, sizeof(void*)*2);
v___y_3905_ = v_hash_3909_;
goto v___jp_3904_;
}
v___jp_3904_:
{
size_t v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = lean_uint64_to_usize(v___y_3905_);
v___x_3907_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3902_, v___x_3906_, v_x_3903_);
return v___x_3907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3910_, lean_object* v_x_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3910_, v_x_3911_);
lean_dec(v_x_3911_);
lean_dec_ref(v_x_3910_);
return v_res_3912_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3920_ = l_Lean_stringToMessageData(v___x_3919_);
return v___x_3920_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3923_ = l_Lean_stringToMessageData(v___x_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v_env_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3930_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_3931_ = lean_st_ref_get(v_a_3928_);
v_env_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc_ref(v_env_3932_);
lean_dec(v___x_3931_);
lean_inc_n(v_matchDeclName_3924_, 3);
v___x_3933_ = l_Lean_mkPrivateName(v_env_3932_, v_matchDeclName_3924_);
lean_dec_ref(v_env_3932_);
v___x_3934_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_3933_);
v___x_3935_ = l_Lean_Name_append(v___x_3933_, v___x_3934_);
lean_inc_n(v___x_3935_, 2);
v___x_3936_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_3936_, 0, v_matchDeclName_3924_);
lean_closure_set(v___x_3936_, 1, v___x_3933_);
lean_closure_set(v___x_3936_, 2, v___x_3935_);
v___x_3937_ = l_Lean_Meta_realizeConst(v_matchDeclName_3924_, v___x_3935_, v___x_3936_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3966_; 
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3966_ == 0)
{
lean_object* v_unused_3967_; 
v_unused_3967_ = lean_ctor_get(v___x_3937_, 0);
lean_dec(v_unused_3967_);
v___x_3939_ = v___x_3937_;
v_isShared_3940_ = v_isSharedCheck_3966_;
goto v_resetjp_3938_;
}
else
{
lean_dec(v___x_3937_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3966_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3941_; lean_object* v_env_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; lean_object* v___x_3946_; lean_object* v_map_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3964_; 
v___x_3941_ = lean_st_ref_get(v_a_3928_);
v_env_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc_ref(v_env_3942_);
lean_dec(v___x_3941_);
v___x_3943_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_3944_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_3945_ = 0;
v___x_3946_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3930_, v___x_3943_, v_env_3942_, v___x_3944_, v___x_3935_, v___x_3945_);
v_map_3947_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3964_ == 0)
{
lean_object* v_unused_3965_; 
v_unused_3965_ = lean_ctor_get(v___x_3946_, 1);
lean_dec(v_unused_3965_);
v___x_3949_ = v___x_3946_;
v_isShared_3950_ = v_isSharedCheck_3964_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_map_3947_);
lean_dec(v___x_3946_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3964_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_3947_, v_matchDeclName_3924_);
lean_dec_ref(v_map_3947_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3955_; 
lean_del_object(v___x_3939_);
v___x_3952_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_3953_ = l_Lean_MessageData_ofName(v_matchDeclName_3924_);
if (v_isShared_3950_ == 0)
{
lean_ctor_set_tag(v___x_3949_, 7);
lean_ctor_set(v___x_3949_, 1, v___x_3953_);
lean_ctor_set(v___x_3949_, 0, v___x_3952_);
v___x_3955_ = v___x_3949_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3952_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3956_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_3957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3955_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3957_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
return v___x_3958_;
}
}
else
{
lean_object* v_val_3960_; lean_object* v___x_3962_; 
lean_del_object(v___x_3949_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_matchDeclName_3924_);
v_val_3960_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_val_3960_);
lean_dec_ref_known(v___x_3951_, 1);
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 0, v_val_3960_);
v___x_3962_ = v___x_3939_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_val_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec(v___x_3935_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_matchDeclName_3924_);
v_a_3968_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3937_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3937_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = lean_get_match_equations_for(v_matchDeclName_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_3983_, lean_object* v_x_3984_, lean_object* v_x_3985_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3984_, v_x_3985_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_3987_, lean_object* v_x_3988_, lean_object* v_x_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_3987_, v_x_3988_, v_x_3989_);
lean_dec(v_x_3989_);
lean_dec_ref(v_x_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_3991_, lean_object* v_x_3992_, size_t v_x_3993_, lean_object* v_x_3994_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3992_, v_x_3993_, v_x_3994_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3996_, lean_object* v_x_3997_, lean_object* v_x_3998_, lean_object* v_x_3999_){
_start:
{
size_t v_x_906__boxed_4000_; lean_object* v_res_4001_; 
v_x_906__boxed_4000_ = lean_unbox_usize(v_x_3998_);
lean_dec(v_x_3998_);
v_res_4001_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_3996_, v_x_3997_, v_x_906__boxed_4000_, v_x_3999_);
lean_dec(v_x_3999_);
lean_dec_ref(v_x_3997_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4002_, lean_object* v_keys_4003_, lean_object* v_vals_4004_, lean_object* v_heq_4005_, lean_object* v_i_4006_, lean_object* v_k_4007_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4003_, v_vals_4004_, v_i_4006_, v_k_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4009_, lean_object* v_keys_4010_, lean_object* v_vals_4011_, lean_object* v_heq_4012_, lean_object* v_i_4013_, lean_object* v_k_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4009_, v_keys_4010_, v_vals_4011_, v_heq_4012_, v_i_4013_, v_k_4014_);
lean_dec(v_k_4014_);
lean_dec_ref(v_vals_4011_);
lean_dec_ref(v_keys_4010_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4016_, lean_object* v_k_4017_, uint8_t v_cleanupAnnotations_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v___f_4024_; uint8_t v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___f_4024_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4024_, 0, v_k_4017_);
v___x_4025_ = 0;
v___x_4026_ = lean_box(0);
v___x_4027_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4025_, v___x_4026_, v_type_4016_, v___f_4024_, v_cleanupAnnotations_4018_, v___x_4025_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
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
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
v_a_4036_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4027_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4027_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4044_, lean_object* v_k_4045_, lean_object* v_cleanupAnnotations_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4052_; lean_object* v_res_4053_; 
v_cleanupAnnotations_boxed_4052_ = lean_unbox(v_cleanupAnnotations_4046_);
v_res_4053_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4044_, v_k_4045_, v_cleanupAnnotations_boxed_4052_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4054_, lean_object* v_type_4055_, lean_object* v_k_4056_, uint8_t v_cleanupAnnotations_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4055_, v_k_4056_, v_cleanupAnnotations_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4064_, lean_object* v_type_4065_, lean_object* v_k_4066_, lean_object* v_cleanupAnnotations_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4073_; lean_object* v_res_4074_; 
v_cleanupAnnotations_boxed_4073_ = lean_unbox(v_cleanupAnnotations_4067_);
v_res_4074_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4064_, v_type_4065_, v_k_4066_, v_cleanupAnnotations_boxed_4073_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_msg_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v___f_4081_; lean_object* v___x_18844__overap_4082_; lean_object* v___x_4083_; 
v___f_4081_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_18844__overap_4082_ = lean_panic_fn_borrowed(v___f_4081_, v_msg_4075_);
lean_inc(v___y_4079_);
lean_inc_ref(v___y_4078_);
lean_inc(v___y_4077_);
lean_inc_ref(v___y_4076_);
v___x_4083_ = lean_apply_5(v___x_18844__overap_4082_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, lean_box(0));
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_msg_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_msg_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4091_){
_start:
{
uint8_t v_foApprox_4092_; uint8_t v_ctxApprox_4093_; uint8_t v_quasiPatternApprox_4094_; uint8_t v_constApprox_4095_; uint8_t v_isDefEqStuckEx_4096_; uint8_t v_unificationHints_4097_; uint8_t v_proofIrrelevance_4098_; uint8_t v_assignSyntheticOpaque_4099_; uint8_t v_offsetCnstrs_4100_; uint8_t v_transparency_4101_; uint8_t v_univApprox_4102_; uint8_t v_iota_4103_; uint8_t v_beta_4104_; uint8_t v_proj_4105_; uint8_t v_zeta_4106_; uint8_t v_zetaDelta_4107_; uint8_t v_zetaUnused_4108_; uint8_t v_zetaHave_4109_; uint8_t v_canUnfoldPredicateConfig_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4118_; 
v_foApprox_4092_ = lean_ctor_get_uint8(v_c_4091_, 0);
v_ctxApprox_4093_ = lean_ctor_get_uint8(v_c_4091_, 1);
v_quasiPatternApprox_4094_ = lean_ctor_get_uint8(v_c_4091_, 2);
v_constApprox_4095_ = lean_ctor_get_uint8(v_c_4091_, 3);
v_isDefEqStuckEx_4096_ = lean_ctor_get_uint8(v_c_4091_, 4);
v_unificationHints_4097_ = lean_ctor_get_uint8(v_c_4091_, 5);
v_proofIrrelevance_4098_ = lean_ctor_get_uint8(v_c_4091_, 6);
v_assignSyntheticOpaque_4099_ = lean_ctor_get_uint8(v_c_4091_, 7);
v_offsetCnstrs_4100_ = lean_ctor_get_uint8(v_c_4091_, 8);
v_transparency_4101_ = lean_ctor_get_uint8(v_c_4091_, 9);
v_univApprox_4102_ = lean_ctor_get_uint8(v_c_4091_, 11);
v_iota_4103_ = lean_ctor_get_uint8(v_c_4091_, 12);
v_beta_4104_ = lean_ctor_get_uint8(v_c_4091_, 13);
v_proj_4105_ = lean_ctor_get_uint8(v_c_4091_, 14);
v_zeta_4106_ = lean_ctor_get_uint8(v_c_4091_, 15);
v_zetaDelta_4107_ = lean_ctor_get_uint8(v_c_4091_, 16);
v_zetaUnused_4108_ = lean_ctor_get_uint8(v_c_4091_, 17);
v_zetaHave_4109_ = lean_ctor_get_uint8(v_c_4091_, 18);
v_canUnfoldPredicateConfig_4110_ = lean_ctor_get_uint8(v_c_4091_, 19);
v_isSharedCheck_4118_ = !lean_is_exclusive(v_c_4091_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4112_ = v_c_4091_;
v_isShared_4113_ = v_isSharedCheck_4118_;
goto v_resetjp_4111_;
}
else
{
lean_dec(v_c_4091_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4118_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
uint8_t v___x_4114_; lean_object* v___x_4116_; 
v___x_4114_ = 2;
if (v_isShared_4113_ == 0)
{
v___x_4116_ = v___x_4112_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 0, v_foApprox_4092_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 1, v_ctxApprox_4093_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 2, v_quasiPatternApprox_4094_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 3, v_constApprox_4095_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 4, v_isDefEqStuckEx_4096_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 5, v_unificationHints_4097_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 6, v_proofIrrelevance_4098_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 7, v_assignSyntheticOpaque_4099_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 8, v_offsetCnstrs_4100_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 9, v_transparency_4101_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 11, v_univApprox_4102_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 12, v_iota_4103_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 13, v_beta_4104_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 14, v_proj_4105_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 15, v_zeta_4106_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 16, v_zetaDelta_4107_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 17, v_zetaUnused_4108_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 18, v_zetaHave_4109_);
lean_ctor_set_uint8(v_reuseFailAlloc_4117_, 19, v_canUnfoldPredicateConfig_4110_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
lean_ctor_set_uint8(v___x_4116_, 10, v___x_4114_);
return v___x_4116_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4119_, lean_object* v_t_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_dummy_4126_; lean_object* v_nargs_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v_dummy_4126_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4127_ = l_Lean_Expr_getAppNumArgs(v_t_4120_);
lean_inc(v_nargs_4127_);
v___x_4128_ = lean_mk_array(v_nargs_4127_, v_dummy_4126_);
v___x_4129_ = lean_unsigned_to_nat(1u);
v___x_4130_ = lean_nat_sub(v_nargs_4127_, v___x_4129_);
lean_dec(v_nargs_4127_);
v___x_4131_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4120_, v___x_4128_, v___x_4130_);
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4133_, lean_object* v_t_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4133_, v_t_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec_ref(v_x_4133_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4141_, lean_object* v_x_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v_snd_4141_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4149_, lean_object* v_x_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4149_, v_x_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec_ref(v_x_4150_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4157_, size_t v_i_4158_, lean_object* v_bs_4159_){
_start:
{
uint8_t v___x_4160_; 
v___x_4160_ = lean_usize_dec_lt(v_i_4158_, v_sz_4157_);
if (v___x_4160_ == 0)
{
return v_bs_4159_;
}
else
{
lean_object* v_v_4161_; lean_object* v_fst_4162_; lean_object* v_snd_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4177_; 
v_v_4161_ = lean_array_uget(v_bs_4159_, v_i_4158_);
v_fst_4162_ = lean_ctor_get(v_v_4161_, 0);
v_snd_4163_ = lean_ctor_get(v_v_4161_, 1);
v_isSharedCheck_4177_ = !lean_is_exclusive(v_v_4161_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4165_ = v_v_4161_;
v_isShared_4166_ = v_isSharedCheck_4177_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_snd_4163_);
lean_inc(v_fst_4162_);
lean_dec(v_v_4161_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4177_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4167_; lean_object* v_bs_x27_4168_; lean_object* v___f_4169_; lean_object* v___x_4171_; 
v___x_4167_ = lean_unsigned_to_nat(0u);
v_bs_x27_4168_ = lean_array_uset(v_bs_4159_, v_i_4158_, v___x_4167_);
v___f_4169_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4169_, 0, v_snd_4163_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 1, v___f_4169_);
v___x_4171_ = v___x_4165_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_fst_4162_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v___f_4169_);
v___x_4171_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
size_t v___x_4172_; size_t v___x_4173_; lean_object* v___x_4174_; 
v___x_4172_ = ((size_t)1ULL);
v___x_4173_ = lean_usize_add(v_i_4158_, v___x_4172_);
v___x_4174_ = lean_array_uset(v_bs_x27_4168_, v_i_4158_, v___x_4171_);
v_i_4158_ = v___x_4173_;
v_bs_4159_ = v___x_4174_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4178_, lean_object* v_i_4179_, lean_object* v_bs_4180_){
_start:
{
size_t v_sz_boxed_4181_; size_t v_i_boxed_4182_; lean_object* v_res_4183_; 
v_sz_boxed_4181_ = lean_unbox_usize(v_sz_4178_);
lean_dec(v_sz_4178_);
v_i_boxed_4182_ = lean_unbox_usize(v_i_4179_);
lean_dec(v_i_4179_);
v_res_4183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4181_, v_i_boxed_4182_, v_bs_4180_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4184_, size_t v_i_4185_, lean_object* v_bs_4186_){
_start:
{
uint8_t v___x_4187_; 
v___x_4187_ = lean_usize_dec_lt(v_i_4185_, v_sz_4184_);
if (v___x_4187_ == 0)
{
return v_bs_4186_;
}
else
{
lean_object* v_v_4188_; lean_object* v_fst_4189_; lean_object* v_snd_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4206_; 
v_v_4188_ = lean_array_uget(v_bs_4186_, v_i_4185_);
v_fst_4189_ = lean_ctor_get(v_v_4188_, 0);
v_snd_4190_ = lean_ctor_get(v_v_4188_, 1);
v_isSharedCheck_4206_ = !lean_is_exclusive(v_v_4188_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4192_ = v_v_4188_;
v_isShared_4193_ = v_isSharedCheck_4206_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_snd_4190_);
lean_inc(v_fst_4189_);
lean_dec(v_v_4188_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4206_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4194_; lean_object* v_bs_x27_4195_; uint8_t v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4199_; 
v___x_4194_ = lean_unsigned_to_nat(0u);
v_bs_x27_4195_ = lean_array_uset(v_bs_4186_, v_i_4185_, v___x_4194_);
v___x_4196_ = 0;
v___x_4197_ = lean_box(v___x_4196_);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 0, v___x_4197_);
v___x_4199_ = v___x_4192_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4197_);
lean_ctor_set(v_reuseFailAlloc_4205_, 1, v_snd_4190_);
v___x_4199_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4200_; size_t v___x_4201_; size_t v___x_4202_; lean_object* v___x_4203_; 
v___x_4200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4200_, 0, v_fst_4189_);
lean_ctor_set(v___x_4200_, 1, v___x_4199_);
v___x_4201_ = ((size_t)1ULL);
v___x_4202_ = lean_usize_add(v_i_4185_, v___x_4201_);
v___x_4203_ = lean_array_uset(v_bs_x27_4195_, v_i_4185_, v___x_4200_);
v_i_4185_ = v___x_4202_;
v_bs_4186_ = v___x_4203_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4207_, lean_object* v_i_4208_, lean_object* v_bs_4209_){
_start:
{
size_t v_sz_boxed_4210_; size_t v_i_boxed_4211_; lean_object* v_res_4212_; 
v_sz_boxed_4210_ = lean_unbox_usize(v_sz_4207_);
lean_dec(v_sz_4207_);
v_i_boxed_4211_ = lean_unbox_usize(v_i_4208_);
lean_dec(v_i_4208_);
v_res_4212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4210_, v_i_boxed_4211_, v_bs_4209_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4213_, lean_object* v___x_4214_, lean_object* v_a_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___x_20550__overap_4221_; lean_object* v___x_4222_; 
v___x_20550__overap_4221_ = l_instInhabitedOfMonad___redArg(v___x_4213_, v___x_4214_);
lean_inc(v___y_4219_);
lean_inc_ref(v___y_4218_);
lean_inc(v___y_4217_);
lean_inc_ref(v___y_4216_);
v___x_4222_ = lean_apply_5(v___x_20550__overap_4221_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, lean_box(0));
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4223_, lean_object* v___x_4224_, lean_object* v_a_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4223_, v___x_4224_, v_a_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec_ref(v_a_4225_);
return v_res_4231_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_instMonadEIO___redArg();
return v___x_4232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4234_ = l_StateRefT_x27_instMonad___redArg(v___x_4233_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4239_, lean_object* v_declInfos_4240_, lean_object* v_k_4241_, lean_object* v_kind_4242_, lean_object* v_x_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
uint8_t v_kind_boxed_4249_; lean_object* v_res_4250_; 
v_kind_boxed_4249_ = lean_unbox(v_kind_4242_);
v_res_4250_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4239_, v_declInfos_4240_, v_k_4241_, v_kind_boxed_4249_, v_x_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4251_, lean_object* v_k_4252_, uint8_t v_kind_4253_, lean_object* v_acc_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_4260_; lean_object* v_toApplicative_4261_; lean_object* v_toFunctor_4262_; lean_object* v_toSeq_4263_; lean_object* v_toSeqLeft_4264_; lean_object* v_toSeqRight_4265_; lean_object* v___f_4266_; lean_object* v___f_4267_; lean_object* v___f_4268_; lean_object* v___f_4269_; lean_object* v___x_4270_; lean_object* v___f_4271_; lean_object* v___f_4272_; lean_object* v___f_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v_toApplicative_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4327_; 
v___x_4260_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4261_ = lean_ctor_get(v___x_4260_, 0);
v_toFunctor_4262_ = lean_ctor_get(v_toApplicative_4261_, 0);
v_toSeq_4263_ = lean_ctor_get(v_toApplicative_4261_, 2);
v_toSeqLeft_4264_ = lean_ctor_get(v_toApplicative_4261_, 3);
v_toSeqRight_4265_ = lean_ctor_get(v_toApplicative_4261_, 4);
v___f_4266_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4267_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4262_, 2);
v___f_4268_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4268_, 0, v_toFunctor_4262_);
v___f_4269_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4269_, 0, v_toFunctor_4262_);
v___x_4270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___f_4268_);
lean_ctor_set(v___x_4270_, 1, v___f_4269_);
lean_inc(v_toSeqRight_4265_);
v___f_4271_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4271_, 0, v_toSeqRight_4265_);
lean_inc(v_toSeqLeft_4264_);
v___f_4272_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4272_, 0, v_toSeqLeft_4264_);
lean_inc(v_toSeq_4263_);
v___f_4273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4273_, 0, v_toSeq_4263_);
v___x_4274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4270_);
lean_ctor_set(v___x_4274_, 1, v___f_4266_);
lean_ctor_set(v___x_4274_, 2, v___f_4273_);
lean_ctor_set(v___x_4274_, 3, v___f_4272_);
lean_ctor_set(v___x_4274_, 4, v___f_4271_);
v___x_4275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
lean_ctor_set(v___x_4275_, 1, v___f_4267_);
v___x_4276_ = l_StateRefT_x27_instMonad___redArg(v___x_4275_);
v_toApplicative_4277_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4327_ == 0)
{
lean_object* v_unused_4328_; 
v_unused_4328_ = lean_ctor_get(v___x_4276_, 1);
lean_dec(v_unused_4328_);
v___x_4279_ = v___x_4276_;
v_isShared_4280_ = v_isSharedCheck_4327_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_toApplicative_4277_);
lean_dec(v___x_4276_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4327_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v_toFunctor_4281_; lean_object* v_toSeq_4282_; lean_object* v_toSeqLeft_4283_; lean_object* v_toSeqRight_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4325_; 
v_toFunctor_4281_ = lean_ctor_get(v_toApplicative_4277_, 0);
v_toSeq_4282_ = lean_ctor_get(v_toApplicative_4277_, 2);
v_toSeqLeft_4283_ = lean_ctor_get(v_toApplicative_4277_, 3);
v_toSeqRight_4284_ = lean_ctor_get(v_toApplicative_4277_, 4);
v_isSharedCheck_4325_ = !lean_is_exclusive(v_toApplicative_4277_);
if (v_isSharedCheck_4325_ == 0)
{
lean_object* v_unused_4326_; 
v_unused_4326_ = lean_ctor_get(v_toApplicative_4277_, 1);
lean_dec(v_unused_4326_);
v___x_4286_ = v_toApplicative_4277_;
v_isShared_4287_ = v_isSharedCheck_4325_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_toSeqRight_4284_);
lean_inc(v_toSeqLeft_4283_);
lean_inc(v_toSeq_4282_);
lean_inc(v_toFunctor_4281_);
lean_dec(v_toApplicative_4277_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4325_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___f_4288_; lean_object* v___f_4289_; lean_object* v___f_4290_; lean_object* v___f_4291_; lean_object* v___x_4292_; lean_object* v___f_4293_; lean_object* v___f_4294_; lean_object* v___f_4295_; lean_object* v___x_4297_; 
v___f_4288_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4289_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4281_);
v___f_4290_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4290_, 0, v_toFunctor_4281_);
v___f_4291_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4291_, 0, v_toFunctor_4281_);
v___x_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___f_4290_);
lean_ctor_set(v___x_4292_, 1, v___f_4291_);
v___f_4293_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4293_, 0, v_toSeqRight_4284_);
v___f_4294_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4294_, 0, v_toSeqLeft_4283_);
v___f_4295_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4295_, 0, v_toSeq_4282_);
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 4, v___f_4293_);
lean_ctor_set(v___x_4286_, 3, v___f_4294_);
lean_ctor_set(v___x_4286_, 2, v___f_4295_);
lean_ctor_set(v___x_4286_, 1, v___f_4288_);
lean_ctor_set(v___x_4286_, 0, v___x_4292_);
v___x_4297_ = v___x_4286_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4292_);
lean_ctor_set(v_reuseFailAlloc_4324_, 1, v___f_4288_);
lean_ctor_set(v_reuseFailAlloc_4324_, 2, v___f_4295_);
lean_ctor_set(v_reuseFailAlloc_4324_, 3, v___f_4294_);
lean_ctor_set(v_reuseFailAlloc_4324_, 4, v___f_4293_);
v___x_4297_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4299_; 
if (v_isShared_4280_ == 0)
{
lean_ctor_set(v___x_4279_, 1, v___f_4289_);
lean_ctor_set(v___x_4279_, 0, v___x_4297_);
v___x_4299_ = v___x_4279_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4297_);
lean_ctor_set(v_reuseFailAlloc_4323_, 1, v___f_4289_);
v___x_4299_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; 
v___x_4300_ = lean_array_get_size(v_acc_4254_);
v___x_4301_ = lean_array_get_size(v_declInfos_4251_);
v___x_4302_ = lean_nat_dec_lt(v___x_4300_, v___x_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; 
lean_dec_ref(v___x_4299_);
lean_dec_ref(v_declInfos_4251_);
lean_inc(v___y_4258_);
lean_inc_ref(v___y_4257_);
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
v___x_4303_ = lean_apply_6(v_k_4252_, v_acc_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, lean_box(0));
return v___x_4303_;
}
else
{
lean_object* v___x_4304_; uint8_t v___x_4305_; lean_object* v___x_4306_; lean_object* v___f_4307_; lean_object* v___f_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v_snd_4313_; lean_object* v_fst_4314_; lean_object* v_fst_4315_; lean_object* v_snd_4316_; lean_object* v___x_4317_; lean_object* v___f_4318_; lean_object* v___x_4319_; 
v___x_4304_ = lean_box(0);
v___x_4305_ = 0;
v___x_4306_ = l_Lean_instInhabitedExpr;
v___f_4307_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4307_, 0, v___x_4299_);
lean_closure_set(v___f_4307_, 1, v___x_4306_);
v___f_4308_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4308_, 0, v___f_4307_);
v___x_4309_ = lean_box(v___x_4305_);
v___x_4310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4309_);
lean_ctor_set(v___x_4310_, 1, v___f_4308_);
v___x_4311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4304_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = lean_array_get(v___x_4311_, v_declInfos_4251_, v___x_4300_);
lean_dec_ref_known(v___x_4311_, 2);
v_snd_4313_ = lean_ctor_get(v___x_4312_, 1);
lean_inc(v_snd_4313_);
v_fst_4314_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_fst_4314_);
lean_dec(v___x_4312_);
v_fst_4315_ = lean_ctor_get(v_snd_4313_, 0);
lean_inc(v_fst_4315_);
v_snd_4316_ = lean_ctor_get(v_snd_4313_, 1);
lean_inc(v_snd_4316_);
lean_dec(v_snd_4313_);
v___x_4317_ = lean_box(v_kind_4253_);
lean_inc_ref(v_acc_4254_);
v___f_4318_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4318_, 0, v_acc_4254_);
lean_closure_set(v___f_4318_, 1, v_declInfos_4251_);
lean_closure_set(v___f_4318_, 2, v_k_4252_);
lean_closure_set(v___f_4318_, 3, v___x_4317_);
lean_inc(v___y_4258_);
lean_inc_ref(v___y_4257_);
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
v___x_4319_ = lean_apply_6(v_snd_4316_, v_acc_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, lean_box(0));
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; uint8_t v___x_4321_; lean_object* v___x_4322_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4319_, 1);
v___x_4321_ = lean_unbox(v_fst_4315_);
lean_dec(v_fst_4315_);
v___x_4322_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4314_, v___x_4321_, v_a_4320_, v___f_4318_, v_kind_4253_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
return v___x_4322_;
}
else
{
lean_dec_ref(v___f_4318_);
lean_dec(v_fst_4315_);
lean_dec(v_fst_4314_);
return v___x_4319_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4329_, lean_object* v_declInfos_4330_, lean_object* v_k_4331_, uint8_t v_kind_4332_, lean_object* v_x_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4339_ = lean_array_push(v_acc_4329_, v_x_4333_);
v___x_4340_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4330_, v_k_4331_, v_kind_4332_, v___x_4339_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4341_, lean_object* v_k_4342_, lean_object* v_kind_4343_, lean_object* v_acc_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
uint8_t v_kind_boxed_4350_; lean_object* v_res_4351_; 
v_kind_boxed_4350_ = lean_unbox(v_kind_4343_);
v_res_4351_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4341_, v_k_4342_, v_kind_boxed_4350_, v_acc_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4352_, lean_object* v_k_4353_, uint8_t v_kind_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4361_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4352_, v_k_4353_, v_kind_4354_, v___x_4360_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4362_, lean_object* v_k_4363_, lean_object* v_kind_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
uint8_t v_kind_boxed_4370_; lean_object* v_res_4371_; 
v_kind_boxed_4370_ = lean_unbox(v_kind_4364_);
v_res_4371_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4362_, v_k_4363_, v_kind_boxed_4370_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4372_, lean_object* v_k_4373_, uint8_t v_kind_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
size_t v_sz_4380_; size_t v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v_sz_4380_ = lean_array_size(v_declInfos_4372_);
v___x_4381_ = ((size_t)0ULL);
v___x_4382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4380_, v___x_4381_, v_declInfos_4372_);
v___x_4383_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4382_, v_k_4373_, v_kind_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4384_, lean_object* v_k_4385_, lean_object* v_kind_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
uint8_t v_kind_boxed_4392_; lean_object* v_res_4393_; 
v_kind_boxed_4392_ = lean_unbox(v_kind_4386_);
v_res_4393_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4384_, v_k_4385_, v_kind_boxed_4392_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4394_, lean_object* v_k_4395_, uint8_t v_kind_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
size_t v_sz_4402_; size_t v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v_sz_4402_ = lean_array_size(v_declInfos_4394_);
v___x_4403_ = ((size_t)0ULL);
v___x_4404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4402_, v___x_4403_, v_declInfos_4394_);
v___x_4405_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4404_, v_k_4395_, v_kind_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4406_, lean_object* v_k_4407_, lean_object* v_kind_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
uint8_t v_kind_boxed_4414_; lean_object* v_res_4415_; 
v_kind_boxed_4414_ = lean_unbox(v_kind_4408_);
v_res_4415_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4406_, v_k_4407_, v_kind_boxed_4414_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(lean_object* v_a_4419_, lean_object* v_b_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v_array_4426_; lean_object* v_start_4427_; lean_object* v_stop_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4486_; 
v_array_4426_ = lean_ctor_get(v_a_4419_, 0);
v_start_4427_ = lean_ctor_get(v_a_4419_, 1);
v_stop_4428_ = lean_ctor_get(v_a_4419_, 2);
v_isSharedCheck_4486_ = !lean_is_exclusive(v_a_4419_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4430_ = v_a_4419_;
v_isShared_4431_ = v_isSharedCheck_4486_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_stop_4428_);
lean_inc(v_start_4427_);
lean_inc(v_array_4426_);
lean_dec(v_a_4419_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4486_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
uint8_t v___x_4432_; 
v___x_4432_ = lean_nat_dec_lt(v_start_4427_, v_stop_4428_);
if (v___x_4432_ == 0)
{
lean_object* v___x_4433_; 
lean_del_object(v___x_4430_);
lean_dec(v_stop_4428_);
lean_dec(v_start_4427_);
lean_dec_ref(v_array_4426_);
v___x_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4433_, 0, v_b_4420_);
return v___x_4433_;
}
else
{
lean_object* v_snd_4434_; lean_object* v_fst_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4485_; 
v_snd_4434_ = lean_ctor_get(v_b_4420_, 1);
v_fst_4435_ = lean_ctor_get(v_b_4420_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_b_4420_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4437_ = v_b_4420_;
v_isShared_4438_ = v_isSharedCheck_4485_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_snd_4434_);
lean_inc(v_fst_4435_);
lean_dec(v_b_4420_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4485_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v_array_4439_; lean_object* v_start_4440_; lean_object* v_stop_4441_; uint8_t v___x_4442_; 
v_array_4439_ = lean_ctor_get(v_snd_4434_, 0);
v_start_4440_ = lean_ctor_get(v_snd_4434_, 1);
v_stop_4441_ = lean_ctor_get(v_snd_4434_, 2);
v___x_4442_ = lean_nat_dec_lt(v_start_4440_, v_stop_4441_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4444_; 
lean_del_object(v___x_4430_);
lean_dec(v_stop_4428_);
lean_dec(v_start_4427_);
lean_dec_ref(v_array_4426_);
if (v_isShared_4438_ == 0)
{
v___x_4444_ = v___x_4437_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_fst_4435_);
lean_ctor_set(v_reuseFailAlloc_4446_, 1, v_snd_4434_);
v___x_4444_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
lean_object* v___x_4445_; 
v___x_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4445_, 0, v___x_4444_);
return v___x_4445_;
}
}
else
{
lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4481_; 
lean_inc(v_stop_4441_);
lean_inc(v_start_4440_);
lean_inc_ref(v_array_4439_);
v_isSharedCheck_4481_ = !lean_is_exclusive(v_snd_4434_);
if (v_isSharedCheck_4481_ == 0)
{
lean_object* v_unused_4482_; lean_object* v_unused_4483_; lean_object* v_unused_4484_; 
v_unused_4482_ = lean_ctor_get(v_snd_4434_, 2);
lean_dec(v_unused_4482_);
v_unused_4483_ = lean_ctor_get(v_snd_4434_, 1);
lean_dec(v_unused_4483_);
v_unused_4484_ = lean_ctor_get(v_snd_4434_, 0);
lean_dec(v_unused_4484_);
v___x_4448_ = v_snd_4434_;
v_isShared_4449_ = v_isSharedCheck_4481_;
goto v_resetjp_4447_;
}
else
{
lean_dec(v_snd_4434_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4481_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4453_; 
v___x_4450_ = lean_unsigned_to_nat(1u);
v___x_4451_ = lean_nat_add(v_start_4427_, v___x_4450_);
lean_inc_ref(v_array_4426_);
if (v_isShared_4449_ == 0)
{
lean_ctor_set(v___x_4448_, 2, v_stop_4428_);
lean_ctor_set(v___x_4448_, 1, v___x_4451_);
lean_ctor_set(v___x_4448_, 0, v_array_4426_);
v___x_4453_ = v___x_4448_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_array_4426_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v___x_4451_);
lean_ctor_set(v_reuseFailAlloc_4480_, 2, v_stop_4428_);
v___x_4453_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4458_; 
v___x_4454_ = lean_array_fget(v_array_4426_, v_start_4427_);
lean_dec(v_start_4427_);
lean_dec_ref(v_array_4426_);
v___x_4455_ = lean_array_fget(v_array_4439_, v_start_4440_);
v___x_4456_ = lean_nat_add(v_start_4440_, v___x_4450_);
lean_dec(v_start_4440_);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 2, v_stop_4441_);
lean_ctor_set(v___x_4430_, 1, v___x_4456_);
lean_ctor_set(v___x_4430_, 0, v_array_4439_);
v___x_4458_ = v___x_4430_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_array_4439_);
lean_ctor_set(v_reuseFailAlloc_4479_, 1, v___x_4456_);
lean_ctor_set(v_reuseFailAlloc_4479_, 2, v_stop_4441_);
v___x_4458_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
lean_object* v___x_4459_; 
v___x_4459_ = l_Lean_Meta_mkEqHEq(v___x_4454_, v___x_4455_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4466_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
v___x_4461_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__1));
v___x_4462_ = lean_array_get_size(v_fst_4435_);
v___x_4463_ = lean_nat_add(v___x_4462_, v___x_4450_);
v___x_4464_ = lean_name_append_index_after(v___x_4461_, v___x_4463_);
if (v_isShared_4438_ == 0)
{
lean_ctor_set(v___x_4437_, 1, v_a_4460_);
lean_ctor_set(v___x_4437_, 0, v___x_4464_);
v___x_4466_ = v___x_4437_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4464_);
lean_ctor_set(v_reuseFailAlloc_4470_, 1, v_a_4460_);
v___x_4466_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = lean_array_push(v_fst_4435_, v___x_4466_);
v___x_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
lean_ctor_set(v___x_4468_, 1, v___x_4458_);
v_a_4419_ = v___x_4453_;
v_b_4420_ = v___x_4468_;
goto _start;
}
}
else
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
lean_dec_ref(v___x_4458_);
lean_dec_ref(v___x_4453_);
lean_del_object(v___x_4437_);
lean_dec(v_fst_4435_);
v_a_4471_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4473_ = v___x_4459_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4459_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___boxed(lean_object* v_a_4487_, lean_object* v_b_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_4487_, v_b_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v___x_4495_, lean_object* v_a_4496_, lean_object* v___x_4497_, lean_object* v_as_4498_, size_t v_sz_4499_, size_t v_i_4500_, lean_object* v_b_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_a_4508_; uint8_t v___x_4512_; 
v___x_4512_ = lean_usize_dec_lt(v_i_4500_, v_sz_4499_);
if (v___x_4512_ == 0)
{
lean_object* v___x_4513_; 
lean_dec(v___x_4497_);
v___x_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4513_, 0, v_b_4501_);
return v___x_4513_;
}
else
{
lean_object* v___x_4514_; lean_object* v_a_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4514_ = l_Lean_instInhabitedExpr;
v_a_4515_ = lean_array_uget_borrowed(v_as_4498_, v_i_4500_);
v___x_4516_ = lean_array_get_borrowed(v___x_4514_, v___x_4495_, v_a_4515_);
lean_inc(v___x_4516_);
v___x_4517_ = l_Lean_Meta_instantiateForall(v___x_4516_, v_a_4496_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4519_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
lean_inc(v___x_4497_);
v___x_4519_ = l_Lean_Meta_Match_simpH_x3f(v_a_4518_, v___x_4497_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4520_);
lean_dec_ref_known(v___x_4519_, 1);
if (lean_obj_tag(v_a_4520_) == 1)
{
lean_object* v_val_4521_; lean_object* v___x_4522_; 
v_val_4521_ = lean_ctor_get(v_a_4520_, 0);
lean_inc(v_val_4521_);
lean_dec_ref_known(v_a_4520_, 1);
v___x_4522_ = lean_array_push(v_b_4501_, v_val_4521_);
v_a_4508_ = v___x_4522_;
goto v___jp_4507_;
}
else
{
lean_dec(v_a_4520_);
v_a_4508_ = v_b_4501_;
goto v___jp_4507_;
}
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
lean_dec_ref(v_b_4501_);
lean_dec(v___x_4497_);
v_a_4523_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4519_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4519_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_dec_ref(v_b_4501_);
lean_dec(v___x_4497_);
v_a_4531_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4517_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4517_);
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
v___jp_4507_:
{
size_t v___x_4509_; size_t v___x_4510_; 
v___x_4509_ = ((size_t)1ULL);
v___x_4510_ = lean_usize_add(v_i_4500_, v___x_4509_);
v_i_4500_ = v___x_4510_;
v_b_4501_ = v_a_4508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v___x_4539_, lean_object* v_a_4540_, lean_object* v___x_4541_, lean_object* v_as_4542_, lean_object* v_sz_4543_, lean_object* v_i_4544_, lean_object* v_b_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
size_t v_sz_boxed_4551_; size_t v_i_boxed_4552_; lean_object* v_res_4553_; 
v_sz_boxed_4551_ = lean_unbox_usize(v_sz_4543_);
lean_dec(v_sz_4543_);
v_i_boxed_4552_ = lean_unbox_usize(v_i_4544_);
lean_dec(v_i_4544_);
v_res_4553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4539_, v_a_4540_, v___x_4541_, v_as_4542_, v_sz_boxed_4551_, v_i_boxed_4552_, v_b_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec_ref(v_as_4542_);
lean_dec_ref(v_a_4540_);
lean_dec_ref(v___x_4539_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4554_, lean_object* v_args_4555_, lean_object* v___x_4556_, lean_object* v_overlaps_4557_, lean_object* v_a_4558_, lean_object* v_fst_4559_, lean_object* v_a_4560_, lean_object* v___x_4561_, lean_object* v___x_4562_, lean_object* v___x_4563_, lean_object* v___x_4564_, lean_object* v_altVars_4565_, uint8_t v___x_4566_, uint8_t v___x_4567_, lean_object* v_a_4568_, lean_object* v___x_4569_, lean_object* v___x_4570_, lean_object* v___x_4571_, lean_object* v___x_4572_, lean_object* v___x_4573_, lean_object* v___x_4574_, lean_object* v___x_4575_, lean_object* v_matchDeclName_4576_, lean_object* v___x_4577_, lean_object* v___x_4578_, lean_object* v___x_4579_, lean_object* v_heqs_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; 
v___x_4586_ = l_Lean_mkAppN(v___y_4554_, v_args_4555_);
lean_inc_ref(v_heqs_4580_);
v___x_4587_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4586_, v_heqs_4580_, v___x_4556_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v___x_4589_; size_t v_sz_4590_; size_t v___x_4591_; lean_object* v___x_4592_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4588_);
lean_dec_ref_known(v___x_4587_, 1);
v___x_4589_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4557_, v_a_4558_);
v_sz_4590_ = lean_array_size(v___x_4589_);
v___x_4591_ = ((size_t)0ULL);
lean_inc_ref(v___x_4562_);
v___x_4592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_fst_4559_, v_a_4560_, v___x_4561_, v___x_4589_, v_sz_4590_, v___x_4591_, v___x_4562_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
lean_dec_ref(v___x_4589_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; lean_object* v_toCold_4705_; lean_object* v_options_4706_; uint8_t v_hasTrace_4707_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref_known(v___x_4592_, 1);
v_toCold_4705_ = lean_ctor_get(v___y_4583_, 0);
v_options_4706_ = lean_ctor_get(v_toCold_4705_, 2);
v_hasTrace_4707_ = lean_ctor_get_uint8(v_options_4706_, sizeof(void*)*1);
if (v_hasTrace_4707_ == 0)
{
v___y_4595_ = v___y_4581_;
v___y_4596_ = v___y_4582_;
v___y_4597_ = v___y_4583_;
v___y_4598_ = v___y_4584_;
goto v___jp_4594_;
}
else
{
lean_object* v_inheritedTraceOptions_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; uint8_t v___x_4711_; 
v_inheritedTraceOptions_4708_ = lean_ctor_get(v_toCold_4705_, 11);
v___x_4709_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
v___x_4710_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17);
v___x_4711_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4708_, v_options_4706_, v___x_4710_);
if (v___x_4711_ == 0)
{
v___y_4595_ = v___y_4581_;
v___y_4596_ = v___y_4582_;
v___y_4597_ = v___y_4583_;
v___y_4598_ = v___y_4584_;
goto v___jp_4594_;
}
else
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4712_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4593_);
v___x_4713_ = lean_array_to_list(v_a_4593_);
v___x_4714_ = lean_box(0);
v___x_4715_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4713_, v___x_4714_);
v___x_4716_ = l_Lean_MessageData_ofList(v___x_4715_);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4712_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4709_, v___x_4717_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_dec_ref_known(v___x_4718_, 1);
v___y_4595_ = v___y_4581_;
v___y_4596_ = v___y_4582_;
v___y_4597_ = v___y_4583_;
v___y_4598_ = v___y_4584_;
goto v___jp_4594_;
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
lean_dec(v_a_4593_);
lean_dec(v_a_4588_);
lean_dec_ref(v_heqs_4580_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
lean_dec(v_matchDeclName_4576_);
lean_dec_ref(v___x_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v___x_4570_);
lean_dec(v___x_4569_);
lean_dec_ref(v___x_4564_);
lean_dec(v___x_4563_);
lean_dec_ref(v___x_4562_);
lean_dec_ref(v_a_4560_);
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4718_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4718_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
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
}
v___jp_4594_:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; size_t v_sz_4606_; lean_object* v___x_4607_; 
v___x_4599_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4600_ = l_Array_reverse___redArg(v_a_4560_);
v___x_4601_ = lean_array_get_size(v___x_4600_);
v___x_4602_ = l_Array_toSubarray___redArg(v___x_4600_, v___x_4563_, v___x_4601_);
lean_inc_ref(v___x_4564_);
v___x_4603_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4564_, v___x_4562_);
v___x_4604_ = l_Array_reverse___redArg(v___x_4603_);
v___x_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4599_);
lean_ctor_set(v___x_4605_, 1, v___x_4602_);
v_sz_4606_ = lean_array_size(v___x_4604_);
v___x_4607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4604_, v_sz_4606_, v___x_4591_, v___x_4605_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec_ref(v___x_4604_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v_a_4608_; lean_object* v_fst_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4695_; 
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc(v_a_4608_);
lean_dec_ref_known(v___x_4607_, 1);
v_fst_4609_ = lean_ctor_get(v_a_4608_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v_a_4608_);
if (v_isSharedCheck_4695_ == 0)
{
lean_object* v_unused_4696_; 
v_unused_4696_ = lean_ctor_get(v_a_4608_, 1);
lean_dec(v_unused_4696_);
v___x_4611_ = v_a_4608_;
v_isShared_4612_ = v_isSharedCheck_4695_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_fst_4609_);
lean_dec(v_a_4608_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4695_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; uint8_t v___x_4615_; lean_object* v___x_4616_; 
v___x_4613_ = l_Subarray_copy___redArg(v___x_4564_);
lean_inc_ref(v___x_4613_);
v___x_4614_ = l_Array_append___redArg(v___x_4613_, v_altVars_4565_);
v___x_4615_ = 1;
v___x_4616_ = l_Lean_Meta_mkForallFVars(v___x_4614_, v_fst_4609_, v___x_4566_, v___x_4567_, v___x_4567_, v___x_4615_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec_ref(v___x_4614_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
lean_inc(v_a_4617_);
lean_dec_ref_known(v___x_4616_, 1);
v___x_4618_ = l_Lean_ConstantInfo_name(v_a_4568_);
v___x_4619_ = l_Lean_mkConst(v___x_4618_, v___x_4569_);
lean_inc_ref(v___x_4570_);
v___x_4620_ = l_Subarray_copy___redArg(v___x_4570_);
v___x_4621_ = lean_mk_empty_array_with_capacity(v___x_4571_);
v___x_4622_ = lean_array_push(v___x_4621_, v___x_4572_);
v___x_4623_ = l_Array_append___redArg(v___x_4620_, v___x_4622_);
lean_dec_ref(v___x_4622_);
v___x_4624_ = l_Array_append___redArg(v___x_4623_, v___x_4613_);
lean_dec_ref(v___x_4613_);
v___x_4625_ = l_Subarray_copy___redArg(v___x_4573_);
v___x_4626_ = l_Array_append___redArg(v___x_4624_, v___x_4625_);
lean_dec_ref(v___x_4625_);
v___x_4627_ = l_Lean_mkAppN(v___x_4619_, v___x_4626_);
v___x_4628_ = l_Lean_Meta_mkHEq(v___x_4627_, v_a_4588_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___x_4630_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc(v_a_4629_);
lean_dec_ref_known(v___x_4628_, 1);
v___x_4630_ = l_Lean_mkArrowN(v_a_4593_, v_a_4629_, v___y_4597_, v___y_4598_);
lean_dec(v_a_4593_);
if (lean_obj_tag(v___x_4630_) == 0)
{
lean_object* v_a_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v_a_4631_ = lean_ctor_get(v___x_4630_, 0);
lean_inc(v_a_4631_);
lean_dec_ref_known(v___x_4630_, 1);
v___x_4632_ = l_Array_append___redArg(v___x_4626_, v_altVars_4565_);
v___x_4633_ = l_Array_append___redArg(v___x_4632_, v_heqs_4580_);
v___x_4634_ = l_Lean_Meta_mkForallFVars(v___x_4633_, v_a_4631_, v___x_4566_, v___x_4567_, v___x_4567_, v___x_4615_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec_ref(v___x_4633_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v_a_4635_; lean_object* v___x_4636_; 
v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
lean_inc(v_a_4635_);
lean_dec_ref_known(v___x_4634_, 1);
v___x_4636_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4635_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4694_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4639_ = v___x_4636_;
v_isShared_4640_ = v_isSharedCheck_4694_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4636_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4694_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v_start_4641_; lean_object* v_stop_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4692_; 
v_start_4641_ = lean_ctor_get(v___x_4570_, 1);
v_stop_4642_ = lean_ctor_get(v___x_4570_, 2);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4692_ == 0)
{
lean_object* v_unused_4693_; 
v_unused_4693_ = lean_ctor_get(v___x_4570_, 0);
lean_dec(v_unused_4693_);
v___x_4644_ = v___x_4570_;
v_isShared_4645_ = v_isSharedCheck_4692_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_stop_4642_);
lean_inc(v_start_4641_);
lean_dec(v___x_4570_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4692_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4646_ = lean_nat_sub(v_stop_4642_, v_start_4641_);
lean_dec(v_start_4641_);
lean_dec(v_stop_4642_);
v___x_4647_ = lean_nat_add(v___x_4646_, v___x_4571_);
lean_dec(v___x_4646_);
v___x_4648_ = lean_nat_add(v___x_4647_, v___x_4574_);
lean_dec(v___x_4647_);
v___x_4649_ = lean_nat_add(v___x_4648_, v___x_4575_);
lean_dec(v___x_4648_);
v___x_4650_ = lean_array_get_size(v_altVars_4565_);
v___x_4651_ = lean_nat_add(v___x_4649_, v___x_4650_);
lean_dec(v___x_4649_);
v___x_4652_ = lean_array_get_size(v_heqs_4580_);
lean_dec_ref(v_heqs_4580_);
lean_inc(v_a_4637_);
v___x_4653_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4576_, v_a_4637_, v___x_4651_, v___x_4652_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4691_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4656_ = v___x_4653_;
v_isShared_4657_ = v_isSharedCheck_4691_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4653_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4691_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4658_; lean_object* v_env_4659_; uint8_t v___x_4660_; 
v___x_4658_ = lean_st_ref_get(v___y_4598_);
v_env_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc_ref(v_env_4659_);
lean_dec(v___x_4658_);
lean_inc(v___x_4577_);
v___x_4660_ = l_Lean_Environment_contains(v_env_4659_, v___x_4577_, v___x_4567_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4662_; 
lean_del_object(v___x_4656_);
lean_inc(v___x_4577_);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 2, v_a_4637_);
lean_ctor_set(v___x_4644_, 1, v___x_4578_);
lean_ctor_set(v___x_4644_, 0, v___x_4577_);
v___x_4662_ = v___x_4644_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4577_);
lean_ctor_set(v_reuseFailAlloc_4687_, 1, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4687_, 2, v_a_4637_);
v___x_4662_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
lean_object* v___x_4664_; 
if (v_isShared_4612_ == 0)
{
lean_ctor_set_tag(v___x_4611_, 1);
lean_ctor_set(v___x_4611_, 1, v___x_4579_);
lean_ctor_set(v___x_4611_, 0, v___x_4577_);
v___x_4664_ = v___x_4611_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4577_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v___x_4579_);
v___x_4664_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
lean_object* v___x_4665_; lean_object* v___x_4667_; 
v___x_4665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4665_, 0, v___x_4662_);
lean_ctor_set(v___x_4665_, 1, v_a_4654_);
lean_ctor_set(v___x_4665_, 2, v___x_4664_);
if (v_isShared_4640_ == 0)
{
lean_ctor_set_tag(v___x_4639_, 2);
lean_ctor_set(v___x_4639_, 0, v___x_4665_);
v___x_4667_ = v___x_4639_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4665_);
v___x_4667_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
lean_object* v___x_4668_; 
v___x_4668_ = l_Lean_addDecl(v___x_4667_, v___x_4566_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4675_ == 0)
{
lean_object* v_unused_4676_; 
v_unused_4676_ = lean_ctor_get(v___x_4668_, 0);
lean_dec(v_unused_4676_);
v___x_4670_ = v___x_4668_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_dec(v___x_4668_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 0, v_a_4617_);
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4617_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec(v_a_4617_);
v_a_4677_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4668_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4668_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4689_; 
lean_dec(v_a_4654_);
lean_del_object(v___x_4644_);
lean_del_object(v___x_4639_);
lean_dec(v_a_4637_);
lean_del_object(v___x_4611_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
if (v_isShared_4657_ == 0)
{
lean_ctor_set(v___x_4656_, 0, v_a_4617_);
v___x_4689_ = v___x_4656_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4617_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
else
{
lean_del_object(v___x_4644_);
lean_del_object(v___x_4639_);
lean_dec(v_a_4637_);
lean_dec(v_a_4617_);
lean_del_object(v___x_4611_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
return v___x_4653_;
}
}
}
}
else
{
lean_dec(v_a_4617_);
lean_del_object(v___x_4611_);
lean_dec_ref(v_heqs_4580_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
lean_dec(v_matchDeclName_4576_);
lean_dec_ref(v___x_4570_);
return v___x_4636_;
}
}
else
{
lean_dec(v_a_4617_);
lean_del_object(v___x_4611_);
lean_dec_ref(v_heqs_4580_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
lean_dec(v_matchDeclName_4576_);
lean_dec_ref(v___x_4570_);
return v___x_4634_;
}
}
else
{
lean_dec_ref(v___x_4626_);
lean_dec(v_a_4617_);
lean_del_object(v___x_4611_);
lean_dec_ref(v_heqs_4580_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
lean_dec(v_matchDeclName_4576_);
lean_dec_ref(v___x_4570_);
return v___x_4630_;
}
}
else
{
lean_dec_ref(v___x_4626_);
lean_dec(v_a_4617_);
lean_del_object(v___x_4611_);
lean_dec(v_a_4593_);
lean_dec_ref(v_heqs_4580_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
lean_dec(v_matchDeclName_4576_);
lean_dec_ref(v___x_4570_);
return v___x_4628_;
}
}
else
{
lean_dec_ref(v___x_4613_);
lean_del_object(v___x_4611_);
lean_dec(v_a_4593_);
lean_dec(v_a_4588_);
lean_dec_ref(v_heqs_4580_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
lean_dec(v_matchDeclName_4576_);
lean_dec_ref(v___x_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v___x_4570_);
lean_dec(v___x_4569_);
return v___x_4616_;
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec(v_a_4593_);
lean_dec(v_a_4588_);
lean_dec_ref(v_heqs_4580_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
lean_dec(v_matchDeclName_4576_);
lean_dec_ref(v___x_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v___x_4570_);
lean_dec(v___x_4569_);
lean_dec_ref(v___x_4564_);
v_a_4697_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4607_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4607_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
lean_dec(v_a_4588_);
lean_dec_ref(v_heqs_4580_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
lean_dec(v_matchDeclName_4576_);
lean_dec_ref(v___x_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v___x_4570_);
lean_dec(v___x_4569_);
lean_dec_ref(v___x_4564_);
lean_dec(v___x_4563_);
lean_dec_ref(v___x_4562_);
lean_dec_ref(v_a_4560_);
v_a_4727_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4729_ = v___x_4592_;
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4592_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
if (v_isShared_4730_ == 0)
{
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4727_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4580_);
lean_dec(v___x_4579_);
lean_dec(v___x_4578_);
lean_dec(v___x_4577_);
lean_dec(v_matchDeclName_4576_);
lean_dec_ref(v___x_4573_);
lean_dec_ref(v___x_4572_);
lean_dec_ref(v___x_4570_);
lean_dec(v___x_4569_);
lean_dec_ref(v___x_4564_);
lean_dec(v___x_4563_);
lean_dec_ref(v___x_4562_);
lean_dec(v___x_4561_);
lean_dec_ref(v_a_4560_);
return v___x_4587_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4735_ = _args[0];
lean_object* v_args_4736_ = _args[1];
lean_object* v___x_4737_ = _args[2];
lean_object* v_overlaps_4738_ = _args[3];
lean_object* v_a_4739_ = _args[4];
lean_object* v_fst_4740_ = _args[5];
lean_object* v_a_4741_ = _args[6];
lean_object* v___x_4742_ = _args[7];
lean_object* v___x_4743_ = _args[8];
lean_object* v___x_4744_ = _args[9];
lean_object* v___x_4745_ = _args[10];
lean_object* v_altVars_4746_ = _args[11];
lean_object* v___x_4747_ = _args[12];
lean_object* v___x_4748_ = _args[13];
lean_object* v_a_4749_ = _args[14];
lean_object* v___x_4750_ = _args[15];
lean_object* v___x_4751_ = _args[16];
lean_object* v___x_4752_ = _args[17];
lean_object* v___x_4753_ = _args[18];
lean_object* v___x_4754_ = _args[19];
lean_object* v___x_4755_ = _args[20];
lean_object* v___x_4756_ = _args[21];
lean_object* v_matchDeclName_4757_ = _args[22];
lean_object* v___x_4758_ = _args[23];
lean_object* v___x_4759_ = _args[24];
lean_object* v___x_4760_ = _args[25];
lean_object* v_heqs_4761_ = _args[26];
lean_object* v___y_4762_ = _args[27];
lean_object* v___y_4763_ = _args[28];
lean_object* v___y_4764_ = _args[29];
lean_object* v___y_4765_ = _args[30];
lean_object* v___y_4766_ = _args[31];
_start:
{
uint8_t v___x_21293__boxed_4767_; uint8_t v___x_21294__boxed_4768_; lean_object* v_res_4769_; 
v___x_21293__boxed_4767_ = lean_unbox(v___x_4747_);
v___x_21294__boxed_4768_ = lean_unbox(v___x_4748_);
v_res_4769_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4735_, v_args_4736_, v___x_4737_, v_overlaps_4738_, v_a_4739_, v_fst_4740_, v_a_4741_, v___x_4742_, v___x_4743_, v___x_4744_, v___x_4745_, v_altVars_4746_, v___x_21293__boxed_4767_, v___x_21294__boxed_4768_, v_a_4749_, v___x_4750_, v___x_4751_, v___x_4752_, v___x_4753_, v___x_4754_, v___x_4755_, v___x_4756_, v_matchDeclName_4757_, v___x_4758_, v___x_4759_, v___x_4760_, v_heqs_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec(v___x_4756_);
lean_dec(v___x_4755_);
lean_dec(v___x_4752_);
lean_dec_ref(v_a_4749_);
lean_dec_ref(v_altVars_4746_);
lean_dec(v_fst_4740_);
lean_dec(v_a_4739_);
lean_dec_ref(v_overlaps_4738_);
lean_dec_ref(v_args_4736_);
return v_res_4769_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4772_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4773_ = lean_unsigned_to_nat(8u);
v___x_4774_ = lean_unsigned_to_nat(295u);
v___x_4775_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4776_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4777_ = l_mkPanicMessageWithDecl(v___x_4776_, v___x_4775_, v___x_4774_, v___x_4773_, v___x_4772_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4778_, lean_object* v___x_4779_, lean_object* v___y_4780_, lean_object* v___x_4781_, lean_object* v_overlaps_4782_, lean_object* v_a_4783_, lean_object* v_fst_4784_, lean_object* v___x_4785_, lean_object* v___x_4786_, uint8_t v___x_4787_, lean_object* v_a_4788_, lean_object* v___x_4789_, lean_object* v___x_4790_, lean_object* v___x_4791_, lean_object* v___x_4792_, lean_object* v___x_4793_, lean_object* v___x_4794_, lean_object* v_matchDeclName_4795_, lean_object* v___x_4796_, lean_object* v___x_4797_, lean_object* v___x_4798_, lean_object* v_altVars_4799_, lean_object* v_args_4800_, lean_object* v___mask_4801_, lean_object* v_altResultType_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
uint8_t v___x_4808_; lean_object* v___x_4809_; 
v___x_4808_ = 0;
v___x_4809_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4802_, v___f_4778_, v___x_4808_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_a_4810_; lean_object* v_start_4811_; lean_object* v_stop_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; uint8_t v___x_4815_; 
v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
lean_inc(v_a_4810_);
lean_dec_ref_known(v___x_4809_, 1);
v_start_4811_ = lean_ctor_get(v___x_4779_, 1);
v_stop_4812_ = lean_ctor_get(v___x_4779_, 2);
v___x_4813_ = lean_array_get_size(v_a_4810_);
v___x_4814_ = lean_nat_sub(v_stop_4812_, v_start_4811_);
v___x_4815_ = lean_nat_dec_eq(v___x_4813_, v___x_4814_);
if (v___x_4815_ == 0)
{
lean_object* v___x_4816_; lean_object* v___x_4817_; 
lean_dec(v___x_4814_);
lean_dec(v_a_4810_);
lean_dec_ref(v_args_4800_);
lean_dec_ref(v_altVars_4799_);
lean_dec(v___x_4798_);
lean_dec(v___x_4797_);
lean_dec(v___x_4796_);
lean_dec(v_matchDeclName_4795_);
lean_dec(v___x_4794_);
lean_dec_ref(v___x_4793_);
lean_dec_ref(v___x_4792_);
lean_dec(v___x_4791_);
lean_dec_ref(v___x_4790_);
lean_dec(v___x_4789_);
lean_dec_ref(v_a_4788_);
lean_dec(v___x_4786_);
lean_dec_ref(v___x_4785_);
lean_dec(v_fst_4784_);
lean_dec(v_a_4783_);
lean_dec_ref(v_overlaps_4782_);
lean_dec(v___x_4781_);
lean_dec_ref(v___y_4780_);
lean_dec_ref(v___x_4779_);
v___x_4816_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4817_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v___x_4816_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
return v___x_4817_;
}
else
{
lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___f_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4818_ = lean_box(v___x_4808_);
v___x_4819_ = lean_box(v___x_4787_);
lean_inc_ref(v___x_4779_);
lean_inc(v___x_4786_);
lean_inc(v_a_4810_);
v___f_4820_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4820_, 0, v___y_4780_);
lean_closure_set(v___f_4820_, 1, v_args_4800_);
lean_closure_set(v___f_4820_, 2, v___x_4781_);
lean_closure_set(v___f_4820_, 3, v_overlaps_4782_);
lean_closure_set(v___f_4820_, 4, v_a_4783_);
lean_closure_set(v___f_4820_, 5, v_fst_4784_);
lean_closure_set(v___f_4820_, 6, v_a_4810_);
lean_closure_set(v___f_4820_, 7, v___x_4813_);
lean_closure_set(v___f_4820_, 8, v___x_4785_);
lean_closure_set(v___f_4820_, 9, v___x_4786_);
lean_closure_set(v___f_4820_, 10, v___x_4779_);
lean_closure_set(v___f_4820_, 11, v_altVars_4799_);
lean_closure_set(v___f_4820_, 12, v___x_4818_);
lean_closure_set(v___f_4820_, 13, v___x_4819_);
lean_closure_set(v___f_4820_, 14, v_a_4788_);
lean_closure_set(v___f_4820_, 15, v___x_4789_);
lean_closure_set(v___f_4820_, 16, v___x_4790_);
lean_closure_set(v___f_4820_, 17, v___x_4791_);
lean_closure_set(v___f_4820_, 18, v___x_4792_);
lean_closure_set(v___f_4820_, 19, v___x_4793_);
lean_closure_set(v___f_4820_, 20, v___x_4814_);
lean_closure_set(v___f_4820_, 21, v___x_4794_);
lean_closure_set(v___f_4820_, 22, v_matchDeclName_4795_);
lean_closure_set(v___f_4820_, 23, v___x_4796_);
lean_closure_set(v___f_4820_, 24, v___x_4797_);
lean_closure_set(v___f_4820_, 25, v___x_4798_);
v___x_4821_ = lean_mk_empty_array_with_capacity(v___x_4786_);
v___x_4822_ = l_Array_toSubarray___redArg(v_a_4810_, v___x_4786_, v___x_4813_);
v___x_4823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4823_, 0, v___x_4821_);
lean_ctor_set(v___x_4823_, 1, v___x_4822_);
v___x_4824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v___x_4779_, v___x_4823_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v_fst_4826_; uint8_t v___x_4827_; lean_object* v___x_4828_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4824_, 1);
v_fst_4826_ = lean_ctor_get(v_a_4825_, 0);
lean_inc(v_fst_4826_);
lean_dec(v_a_4825_);
v___x_4827_ = 0;
v___x_4828_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4826_, v___f_4820_, v___x_4827_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
return v___x_4828_;
}
else
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4836_; 
lean_dec_ref(v___f_4820_);
v_a_4829_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4831_ = v___x_4824_;
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4824_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4834_; 
if (v_isShared_4832_ == 0)
{
v___x_4834_ = v___x_4831_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
}
else
{
lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4844_; 
lean_dec_ref(v_args_4800_);
lean_dec_ref(v_altVars_4799_);
lean_dec(v___x_4798_);
lean_dec(v___x_4797_);
lean_dec(v___x_4796_);
lean_dec(v_matchDeclName_4795_);
lean_dec(v___x_4794_);
lean_dec_ref(v___x_4793_);
lean_dec_ref(v___x_4792_);
lean_dec(v___x_4791_);
lean_dec_ref(v___x_4790_);
lean_dec(v___x_4789_);
lean_dec_ref(v_a_4788_);
lean_dec(v___x_4786_);
lean_dec_ref(v___x_4785_);
lean_dec(v_fst_4784_);
lean_dec(v_a_4783_);
lean_dec_ref(v_overlaps_4782_);
lean_dec(v___x_4781_);
lean_dec_ref(v___y_4780_);
lean_dec_ref(v___x_4779_);
v_a_4837_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4839_ = v___x_4809_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4809_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4840_ == 0)
{
v___x_4842_ = v___x_4839_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4837_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4845_ = _args[0];
lean_object* v___x_4846_ = _args[1];
lean_object* v___y_4847_ = _args[2];
lean_object* v___x_4848_ = _args[3];
lean_object* v_overlaps_4849_ = _args[4];
lean_object* v_a_4850_ = _args[5];
lean_object* v_fst_4851_ = _args[6];
lean_object* v___x_4852_ = _args[7];
lean_object* v___x_4853_ = _args[8];
lean_object* v___x_4854_ = _args[9];
lean_object* v_a_4855_ = _args[10];
lean_object* v___x_4856_ = _args[11];
lean_object* v___x_4857_ = _args[12];
lean_object* v___x_4858_ = _args[13];
lean_object* v___x_4859_ = _args[14];
lean_object* v___x_4860_ = _args[15];
lean_object* v___x_4861_ = _args[16];
lean_object* v_matchDeclName_4862_ = _args[17];
lean_object* v___x_4863_ = _args[18];
lean_object* v___x_4864_ = _args[19];
lean_object* v___x_4865_ = _args[20];
lean_object* v_altVars_4866_ = _args[21];
lean_object* v_args_4867_ = _args[22];
lean_object* v___mask_4868_ = _args[23];
lean_object* v_altResultType_4869_ = _args[24];
lean_object* v___y_4870_ = _args[25];
lean_object* v___y_4871_ = _args[26];
lean_object* v___y_4872_ = _args[27];
lean_object* v___y_4873_ = _args[28];
lean_object* v___y_4874_ = _args[29];
_start:
{
uint8_t v___x_21680__boxed_4875_; lean_object* v_res_4876_; 
v___x_21680__boxed_4875_ = lean_unbox(v___x_4854_);
v_res_4876_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4845_, v___x_4846_, v___y_4847_, v___x_4848_, v_overlaps_4849_, v_a_4850_, v_fst_4851_, v___x_4852_, v___x_4853_, v___x_21680__boxed_4875_, v_a_4855_, v___x_4856_, v___x_4857_, v___x_4858_, v___x_4859_, v___x_4860_, v___x_4861_, v_matchDeclName_4862_, v___x_4863_, v___x_4864_, v___x_4865_, v_altVars_4866_, v_args_4867_, v___mask_4868_, v_altResultType_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec_ref(v___mask_4868_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4878_, lean_object* v_val_4879_, lean_object* v_matchDeclName_4880_, lean_object* v___x_4881_, lean_object* v___x_4882_, lean_object* v_a_4883_, lean_object* v___x_4884_, lean_object* v___x_4885_, lean_object* v___x_4886_, lean_object* v___x_4887_, lean_object* v___x_4888_, lean_object* v___x_4889_, lean_object* v_a_4890_, lean_object* v_b_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_){
_start:
{
uint8_t v___x_4897_; 
v___x_4897_ = lean_nat_dec_lt(v_a_4890_, v_upperBound_4878_);
if (v___x_4897_ == 0)
{
lean_object* v___x_4898_; 
lean_dec(v_a_4890_);
lean_dec(v___x_4889_);
lean_dec(v___x_4888_);
lean_dec_ref(v___x_4887_);
lean_dec_ref(v___x_4886_);
lean_dec_ref(v___x_4885_);
lean_dec(v___x_4884_);
lean_dec_ref(v_a_4883_);
lean_dec(v___x_4882_);
lean_dec_ref(v___x_4881_);
lean_dec(v_matchDeclName_4880_);
lean_dec_ref(v_val_4879_);
v___x_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4898_, 0, v_b_4891_);
return v___x_4898_;
}
else
{
lean_object* v_snd_4899_; lean_object* v_fst_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4964_; 
v_snd_4899_ = lean_ctor_get(v_b_4891_, 1);
v_fst_4900_ = lean_ctor_get(v_b_4891_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v_b_4891_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4902_ = v_b_4891_;
v_isShared_4903_ = v_isSharedCheck_4964_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_snd_4899_);
lean_inc(v_fst_4900_);
lean_dec(v_b_4891_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4964_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v_fst_4904_; lean_object* v_snd_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4963_; 
v_fst_4904_ = lean_ctor_get(v_snd_4899_, 0);
v_snd_4905_ = lean_ctor_get(v_snd_4899_, 1);
v_isSharedCheck_4963_ = !lean_is_exclusive(v_snd_4899_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4907_ = v_snd_4899_;
v_isShared_4908_ = v_isSharedCheck_4963_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_snd_4905_);
lean_inc(v_fst_4904_);
lean_dec(v_snd_4899_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4963_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v_altInfos_4909_; lean_object* v_overlaps_4910_; lean_object* v_start_4911_; lean_object* v_stop_4912_; lean_object* v___f_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___y_4925_; lean_object* v___x_4958_; uint8_t v___x_4959_; 
v_altInfos_4909_ = lean_ctor_get(v_val_4879_, 2);
v_overlaps_4910_ = lean_ctor_get(v_val_4879_, 5);
v_start_4911_ = lean_ctor_get(v___x_4887_, 1);
v_stop_4912_ = lean_ctor_get(v___x_4887_, 2);
v___f_4913_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4914_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4915_ = lean_unsigned_to_nat(0u);
v___x_4916_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4917_ = lean_unsigned_to_nat(1u);
v___x_4918_ = lean_box(0);
v___x_4919_ = lean_array_get_borrowed(v___x_4914_, v_altInfos_4909_, v_a_4890_);
v___x_4920_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4880_);
v___x_4921_ = l_Lean_Name_str___override(v_matchDeclName_4880_, v___x_4920_);
lean_inc(v_snd_4905_);
v___x_4922_ = lean_name_append_index_after(v___x_4921_, v_snd_4905_);
lean_inc(v___x_4922_);
v___x_4923_ = lean_array_push(v_fst_4900_, v___x_4922_);
v___x_4958_ = lean_nat_sub(v_stop_4912_, v_start_4911_);
v___x_4959_ = lean_nat_dec_lt(v_a_4890_, v___x_4958_);
lean_dec(v___x_4958_);
if (v___x_4959_ == 0)
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4960_ = l_Lean_instInhabitedExpr;
v___x_4961_ = l_outOfBounds___redArg(v___x_4960_);
v___y_4925_ = v___x_4961_;
goto v___jp_4924_;
}
else
{
lean_object* v___x_4962_; 
v___x_4962_ = l_Subarray_get___redArg(v___x_4887_, v_a_4890_);
v___y_4925_ = v___x_4962_;
goto v___jp_4924_;
}
v___jp_4924_:
{
lean_object* v___x_4926_; lean_object* v___f_4927_; lean_object* v___x_4928_; 
v___x_4926_ = lean_box(v___x_4897_);
lean_inc(v___x_4889_);
lean_inc(v_matchDeclName_4880_);
lean_inc(v___x_4888_);
lean_inc_ref(v___x_4887_);
lean_inc_ref(v___x_4886_);
lean_inc_ref(v___x_4885_);
lean_inc(v___x_4884_);
lean_inc_ref(v_a_4883_);
lean_inc(v_fst_4904_);
lean_inc(v_a_4890_);
lean_inc_ref(v_overlaps_4910_);
lean_inc(v___x_4882_);
lean_inc_ref(v___y_4925_);
lean_inc_ref(v___x_4881_);
v___f_4927_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 30, 21);
lean_closure_set(v___f_4927_, 0, v___f_4913_);
lean_closure_set(v___f_4927_, 1, v___x_4881_);
lean_closure_set(v___f_4927_, 2, v___y_4925_);
lean_closure_set(v___f_4927_, 3, v___x_4882_);
lean_closure_set(v___f_4927_, 4, v_overlaps_4910_);
lean_closure_set(v___f_4927_, 5, v_a_4890_);
lean_closure_set(v___f_4927_, 6, v_fst_4904_);
lean_closure_set(v___f_4927_, 7, v___x_4916_);
lean_closure_set(v___f_4927_, 8, v___x_4915_);
lean_closure_set(v___f_4927_, 9, v___x_4926_);
lean_closure_set(v___f_4927_, 10, v_a_4883_);
lean_closure_set(v___f_4927_, 11, v___x_4884_);
lean_closure_set(v___f_4927_, 12, v___x_4885_);
lean_closure_set(v___f_4927_, 13, v___x_4917_);
lean_closure_set(v___f_4927_, 14, v___x_4886_);
lean_closure_set(v___f_4927_, 15, v___x_4887_);
lean_closure_set(v___f_4927_, 16, v___x_4888_);
lean_closure_set(v___f_4927_, 17, v_matchDeclName_4880_);
lean_closure_set(v___f_4927_, 18, v___x_4922_);
lean_closure_set(v___f_4927_, 19, v___x_4889_);
lean_closure_set(v___f_4927_, 20, v___x_4918_);
lean_inc(v___y_4895_);
lean_inc_ref(v___y_4894_);
lean_inc(v___y_4893_);
lean_inc_ref(v___y_4892_);
v___x_4928_ = lean_infer_type(v___y_4925_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref_known(v___x_4928_, 1);
lean_inc(v___x_4919_);
v___x_4930_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4929_, v___x_4919_, v___f_4927_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4935_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4930_, 1);
v___x_4932_ = lean_array_push(v_fst_4904_, v_a_4931_);
v___x_4933_ = lean_nat_add(v_snd_4905_, v___x_4917_);
lean_dec(v_snd_4905_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 1, v___x_4933_);
lean_ctor_set(v___x_4907_, 0, v___x_4932_);
v___x_4935_ = v___x_4907_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4932_);
lean_ctor_set(v_reuseFailAlloc_4941_, 1, v___x_4933_);
v___x_4935_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4937_; 
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 1, v___x_4935_);
lean_ctor_set(v___x_4902_, 0, v___x_4923_);
v___x_4937_ = v___x_4902_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4923_);
lean_ctor_set(v_reuseFailAlloc_4940_, 1, v___x_4935_);
v___x_4937_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
lean_object* v___x_4938_; 
v___x_4938_ = lean_nat_add(v_a_4890_, v___x_4917_);
lean_dec(v_a_4890_);
v_a_4890_ = v___x_4938_;
v_b_4891_ = v___x_4937_;
goto _start;
}
}
}
else
{
lean_object* v_a_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4949_; 
lean_dec_ref(v___x_4923_);
lean_del_object(v___x_4907_);
lean_dec(v_snd_4905_);
lean_dec(v_fst_4904_);
lean_del_object(v___x_4902_);
lean_dec(v_a_4890_);
lean_dec(v___x_4889_);
lean_dec(v___x_4888_);
lean_dec_ref(v___x_4887_);
lean_dec_ref(v___x_4886_);
lean_dec_ref(v___x_4885_);
lean_dec(v___x_4884_);
lean_dec_ref(v_a_4883_);
lean_dec(v___x_4882_);
lean_dec_ref(v___x_4881_);
lean_dec(v_matchDeclName_4880_);
lean_dec_ref(v_val_4879_);
v_a_4942_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4944_ = v___x_4930_;
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_a_4942_);
lean_dec(v___x_4930_);
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
else
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
lean_dec_ref(v___f_4927_);
lean_dec_ref(v___x_4923_);
lean_del_object(v___x_4907_);
lean_dec(v_snd_4905_);
lean_dec(v_fst_4904_);
lean_del_object(v___x_4902_);
lean_dec(v_a_4890_);
lean_dec(v___x_4889_);
lean_dec(v___x_4888_);
lean_dec_ref(v___x_4887_);
lean_dec_ref(v___x_4886_);
lean_dec_ref(v___x_4885_);
lean_dec(v___x_4884_);
lean_dec_ref(v_a_4883_);
lean_dec(v___x_4882_);
lean_dec_ref(v___x_4881_);
lean_dec(v_matchDeclName_4880_);
lean_dec_ref(v_val_4879_);
v_a_4950_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4928_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4928_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
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
lean_object* v_upperBound_4965_ = _args[0];
lean_object* v_val_4966_ = _args[1];
lean_object* v_matchDeclName_4967_ = _args[2];
lean_object* v___x_4968_ = _args[3];
lean_object* v___x_4969_ = _args[4];
lean_object* v_a_4970_ = _args[5];
lean_object* v___x_4971_ = _args[6];
lean_object* v___x_4972_ = _args[7];
lean_object* v___x_4973_ = _args[8];
lean_object* v___x_4974_ = _args[9];
lean_object* v___x_4975_ = _args[10];
lean_object* v___x_4976_ = _args[11];
lean_object* v_a_4977_ = _args[12];
lean_object* v_b_4978_ = _args[13];
lean_object* v___y_4979_ = _args[14];
lean_object* v___y_4980_ = _args[15];
lean_object* v___y_4981_ = _args[16];
lean_object* v___y_4982_ = _args[17];
lean_object* v___y_4983_ = _args[18];
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_4965_, v_val_4966_, v_matchDeclName_4967_, v___x_4968_, v___x_4969_, v_a_4970_, v___x_4971_, v___x_4972_, v___x_4973_, v___x_4974_, v___x_4975_, v___x_4976_, v_a_4977_, v_b_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
lean_dec(v___y_4982_);
lean_dec_ref(v___y_4981_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
lean_dec(v_upperBound_4965_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_4991_, lean_object* v___x_4992_, lean_object* v_matchDeclName_4993_, lean_object* v___x_4994_, lean_object* v_a_4995_, lean_object* v___x_4996_, lean_object* v___x_4997_, lean_object* v_xs_4998_, lean_object* v___matchResultType_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_){
_start:
{
lean_object* v_numParams_5005_; lean_object* v_numDiscrs_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v_lower_5012_; lean_object* v_upper_5013_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; uint8_t v___x_5044_; 
v_numParams_5005_ = lean_ctor_get(v_val_4991_, 0);
v_numDiscrs_5006_ = lean_ctor_get(v_val_4991_, 1);
v___x_5007_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5005_);
lean_inc_ref(v_xs_4998_);
v___x_5008_ = l_Array_toSubarray___redArg(v_xs_4998_, v___x_5007_, v_numParams_5005_);
v___x_5009_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_4991_);
v___x_5010_ = lean_array_get(v___x_4992_, v_xs_4998_, v___x_5009_);
lean_dec(v___x_5009_);
v___x_5041_ = lean_array_get_size(v_xs_4998_);
v___x_5042_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_4991_);
v___x_5043_ = lean_nat_sub(v___x_5041_, v___x_5042_);
lean_dec(v___x_5042_);
v___x_5044_ = lean_nat_dec_le(v___x_5043_, v___x_5007_);
if (v___x_5044_ == 0)
{
v_lower_5012_ = v___x_5043_;
v_upper_5013_ = v___x_5041_;
goto v___jp_5011_;
}
else
{
lean_dec(v___x_5043_);
v_lower_5012_ = v___x_5007_;
v_upper_5013_ = v___x_5041_;
goto v___jp_5011_;
}
v___jp_5011_:
{
lean_object* v___x_5014_; lean_object* v_start_5015_; lean_object* v_stop_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; 
lean_inc_ref(v_xs_4998_);
v___x_5014_ = l_Array_toSubarray___redArg(v_xs_4998_, v_lower_5012_, v_upper_5013_);
v_start_5015_ = lean_ctor_get(v___x_5014_, 1);
v_stop_5016_ = lean_ctor_get(v___x_5014_, 2);
v___x_5017_ = lean_unsigned_to_nat(1u);
v___x_5018_ = lean_nat_add(v_numParams_5005_, v___x_5017_);
v___x_5019_ = lean_nat_add(v___x_5018_, v_numDiscrs_5006_);
v___x_5020_ = lean_nat_sub(v_stop_5016_, v_start_5015_);
v___x_5021_ = l_Array_toSubarray___redArg(v_xs_4998_, v___x_5018_, v___x_5019_);
v___x_5022_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5020_);
v___x_5023_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5020_, v_val_4991_, v_matchDeclName_4993_, v___x_5021_, v___x_4994_, v_a_4995_, v___x_4996_, v___x_5008_, v___x_5010_, v___x_5014_, v___x_5020_, v___x_4997_, v___x_5007_, v___x_5022_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
lean_dec(v___x_5020_);
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5031_; 
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5031_ == 0)
{
lean_object* v_unused_5032_; 
v_unused_5032_ = lean_ctor_get(v___x_5023_, 0);
lean_dec(v_unused_5032_);
v___x_5025_ = v___x_5023_;
v_isShared_5026_ = v_isSharedCheck_5031_;
goto v_resetjp_5024_;
}
else
{
lean_dec(v___x_5023_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5031_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v___x_5027_; lean_object* v___x_5029_; 
v___x_5027_ = lean_box(0);
if (v_isShared_5026_ == 0)
{
lean_ctor_set(v___x_5025_, 0, v___x_5027_);
v___x_5029_ = v___x_5025_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v___x_5027_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
v_a_5033_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_5023_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_5023_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5045_, lean_object* v___x_5046_, lean_object* v_matchDeclName_5047_, lean_object* v___x_5048_, lean_object* v_a_5049_, lean_object* v___x_5050_, lean_object* v___x_5051_, lean_object* v_xs_5052_, lean_object* v___matchResultType_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5045_, v___x_5046_, v_matchDeclName_5047_, v___x_5048_, v_a_5049_, v___x_5050_, v___x_5051_, v_xs_5052_, v___matchResultType_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
lean_dec(v___y_5057_);
lean_dec_ref(v___y_5056_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec_ref(v___matchResultType_5053_);
lean_dec_ref(v___x_5046_);
return v_res_5059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_){
_start:
{
uint8_t v_trackZetaDelta_5066_; lean_object* v_zetaDeltaSet_5067_; lean_object* v_lctx_5068_; lean_object* v_localInstances_5069_; lean_object* v_defEqCtx_x3f_5070_; lean_object* v_synthPendingDepth_5071_; lean_object* v_customCanUnfoldPredicate_x3f_5072_; uint8_t v_univApprox_5073_; uint8_t v_inTypeClassResolution_5074_; uint8_t v_cacheInferType_5075_; lean_object* v___x_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5119_; 
v_trackZetaDelta_5066_ = lean_ctor_get_uint8(v_a_5061_, sizeof(void*)*7);
v_zetaDeltaSet_5067_ = lean_ctor_get(v_a_5061_, 1);
lean_inc(v_zetaDeltaSet_5067_);
v_lctx_5068_ = lean_ctor_get(v_a_5061_, 2);
lean_inc_ref(v_lctx_5068_);
v_localInstances_5069_ = lean_ctor_get(v_a_5061_, 3);
lean_inc_ref(v_localInstances_5069_);
v_defEqCtx_x3f_5070_ = lean_ctor_get(v_a_5061_, 4);
lean_inc(v_defEqCtx_x3f_5070_);
v_synthPendingDepth_5071_ = lean_ctor_get(v_a_5061_, 5);
lean_inc(v_synthPendingDepth_5071_);
v_customCanUnfoldPredicate_x3f_5072_ = lean_ctor_get(v_a_5061_, 6);
lean_inc(v_customCanUnfoldPredicate_x3f_5072_);
v_univApprox_5073_ = lean_ctor_get_uint8(v_a_5061_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5074_ = lean_ctor_get_uint8(v_a_5061_, sizeof(void*)*7 + 2);
v_cacheInferType_5075_ = lean_ctor_get_uint8(v_a_5061_, sizeof(void*)*7 + 3);
v___x_5076_ = l_Lean_Meta_Context_config(v_a_5061_);
v_isSharedCheck_5119_ = !lean_is_exclusive(v_a_5061_);
if (v_isSharedCheck_5119_ == 0)
{
lean_object* v_unused_5120_; lean_object* v_unused_5121_; lean_object* v_unused_5122_; lean_object* v_unused_5123_; lean_object* v_unused_5124_; lean_object* v_unused_5125_; lean_object* v_unused_5126_; 
v_unused_5120_ = lean_ctor_get(v_a_5061_, 6);
lean_dec(v_unused_5120_);
v_unused_5121_ = lean_ctor_get(v_a_5061_, 5);
lean_dec(v_unused_5121_);
v_unused_5122_ = lean_ctor_get(v_a_5061_, 4);
lean_dec(v_unused_5122_);
v_unused_5123_ = lean_ctor_get(v_a_5061_, 3);
lean_dec(v_unused_5123_);
v_unused_5124_ = lean_ctor_get(v_a_5061_, 2);
lean_dec(v_unused_5124_);
v_unused_5125_ = lean_ctor_get(v_a_5061_, 1);
lean_dec(v_unused_5125_);
v_unused_5126_ = lean_ctor_get(v_a_5061_, 0);
lean_dec(v_unused_5126_);
v___x_5078_ = v_a_5061_;
v_isShared_5079_ = v_isSharedCheck_5119_;
goto v_resetjp_5077_;
}
else
{
lean_dec(v_a_5061_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5119_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5080_; uint64_t v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5085_; 
v___x_5080_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5076_);
v___x_5081_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5080_);
v___x_5082_ = l_Lean_instInhabitedExpr;
v___x_5083_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5083_, 0, v___x_5080_);
lean_ctor_set_uint64(v___x_5083_, sizeof(void*)*1, v___x_5081_);
lean_inc(v_customCanUnfoldPredicate_x3f_5072_);
lean_inc(v_synthPendingDepth_5071_);
lean_inc(v_defEqCtx_x3f_5070_);
lean_inc_ref(v_localInstances_5069_);
lean_inc_ref(v_lctx_5068_);
lean_inc(v_zetaDeltaSet_5067_);
if (v_isShared_5079_ == 0)
{
lean_ctor_set(v___x_5078_, 0, v___x_5083_);
v___x_5085_ = v___x_5078_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5083_);
lean_ctor_set(v_reuseFailAlloc_5118_, 1, v_zetaDeltaSet_5067_);
lean_ctor_set(v_reuseFailAlloc_5118_, 2, v_lctx_5068_);
lean_ctor_set(v_reuseFailAlloc_5118_, 3, v_localInstances_5069_);
lean_ctor_set(v_reuseFailAlloc_5118_, 4, v_defEqCtx_x3f_5070_);
lean_ctor_set(v_reuseFailAlloc_5118_, 5, v_synthPendingDepth_5071_);
lean_ctor_set(v_reuseFailAlloc_5118_, 6, v_customCanUnfoldPredicate_x3f_5072_);
lean_ctor_set_uint8(v_reuseFailAlloc_5118_, sizeof(void*)*7, v_trackZetaDelta_5066_);
lean_ctor_set_uint8(v_reuseFailAlloc_5118_, sizeof(void*)*7 + 1, v_univApprox_5073_);
lean_ctor_set_uint8(v_reuseFailAlloc_5118_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5074_);
lean_ctor_set_uint8(v_reuseFailAlloc_5118_, sizeof(void*)*7 + 3, v_cacheInferType_5075_);
v___x_5085_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; uint64_t v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5086_ = l_Lean_Meta_Context_config(v___x_5085_);
lean_dec_ref(v___x_5085_);
v___x_5087_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5086_);
v___x_5088_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5087_);
v___x_5089_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5089_, 0, v___x_5087_);
lean_ctor_set_uint64(v___x_5089_, sizeof(void*)*1, v___x_5088_);
v___x_5090_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5090_, 0, v___x_5089_);
lean_ctor_set(v___x_5090_, 1, v_zetaDeltaSet_5067_);
lean_ctor_set(v___x_5090_, 2, v_lctx_5068_);
lean_ctor_set(v___x_5090_, 3, v_localInstances_5069_);
lean_ctor_set(v___x_5090_, 4, v_defEqCtx_x3f_5070_);
lean_ctor_set(v___x_5090_, 5, v_synthPendingDepth_5071_);
lean_ctor_set(v___x_5090_, 6, v_customCanUnfoldPredicate_x3f_5072_);
lean_ctor_set_uint8(v___x_5090_, sizeof(void*)*7, v_trackZetaDelta_5066_);
lean_ctor_set_uint8(v___x_5090_, sizeof(void*)*7 + 1, v_univApprox_5073_);
lean_ctor_set_uint8(v___x_5090_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5074_);
lean_ctor_set_uint8(v___x_5090_, sizeof(void*)*7 + 3, v_cacheInferType_5075_);
lean_inc(v_matchDeclName_5060_);
v___x_5091_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5060_, v___x_5090_, v_a_5062_, v_a_5063_, v_a_5064_);
if (lean_obj_tag(v___x_5091_) == 0)
{
lean_object* v_a_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v_a_5097_; 
v_a_5092_ = lean_ctor_get(v___x_5091_, 0);
lean_inc(v_a_5092_);
lean_dec_ref_known(v___x_5091_, 1);
v___x_5093_ = l_Lean_ConstantInfo_levelParams(v_a_5092_);
v___x_5094_ = lean_box(0);
lean_inc(v___x_5093_);
v___x_5095_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v___x_5093_, v___x_5094_);
lean_inc(v_matchDeclName_5060_);
v___x_5096_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_5060_, v_a_5064_);
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
lean_inc(v_a_5097_);
lean_dec_ref(v___x_5096_);
if (lean_obj_tag(v_a_5097_) == 1)
{
lean_object* v_val_5098_; lean_object* v___x_5099_; lean_object* v___f_5100_; lean_object* v___x_5101_; uint8_t v___x_5102_; lean_object* v___x_5103_; 
v_val_5098_ = lean_ctor_get(v_a_5097_, 0);
lean_inc(v_val_5098_);
lean_dec_ref_known(v_a_5097_, 1);
v___x_5099_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5098_);
lean_inc(v_a_5092_);
v___f_5100_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5100_, 0, v_val_5098_);
lean_closure_set(v___f_5100_, 1, v___x_5082_);
lean_closure_set(v___f_5100_, 2, v_matchDeclName_5060_);
lean_closure_set(v___f_5100_, 3, v___x_5099_);
lean_closure_set(v___f_5100_, 4, v_a_5092_);
lean_closure_set(v___f_5100_, 5, v___x_5095_);
lean_closure_set(v___f_5100_, 6, v___x_5093_);
v___x_5101_ = l_Lean_ConstantInfo_type(v_a_5092_);
lean_dec(v_a_5092_);
v___x_5102_ = 0;
v___x_5103_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5101_, v___f_5100_, v___x_5102_, v___x_5102_, v___x_5090_, v_a_5062_, v_a_5063_, v_a_5064_);
lean_dec_ref_known(v___x_5090_, 7);
return v___x_5103_;
}
else
{
lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
lean_dec(v_a_5097_);
lean_dec(v___x_5095_);
lean_dec(v___x_5093_);
lean_dec(v_a_5092_);
v___x_5104_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5105_ = l_Lean_MessageData_ofName(v_matchDeclName_5060_);
v___x_5106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5104_);
lean_ctor_set(v___x_5106_, 1, v___x_5105_);
v___x_5107_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5106_);
lean_ctor_set(v___x_5108_, 1, v___x_5107_);
v___x_5109_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5108_, v___x_5090_, v_a_5062_, v_a_5063_, v_a_5064_);
lean_dec_ref_known(v___x_5090_, 7);
return v___x_5109_;
}
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
lean_dec_ref_known(v___x_5090_, 7);
lean_dec(v_matchDeclName_5060_);
v_a_5110_ = lean_ctor_get(v___x_5091_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5091_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v___x_5091_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5091_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5113_ == 0)
{
v___x_5115_ = v___x_5112_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5110_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_);
lean_dec(v_a_5131_);
lean_dec_ref(v_a_5130_);
lean_dec(v_a_5129_);
return v_res_5133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v_inst_5134_, lean_object* v_R_5135_, lean_object* v_a_5136_, lean_object* v_b_5137_, lean_object* v_c_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_){
_start:
{
lean_object* v___x_5144_; 
v___x_5144_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_5136_, v_b_5137_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v_inst_5145_, lean_object* v_R_5146_, lean_object* v_a_5147_, lean_object* v_b_5148_, lean_object* v_c_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_){
_start:
{
lean_object* v_res_5155_; 
v_res_5155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_inst_5145_, v_R_5146_, v_a_5147_, v_b_5148_, v_c_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
lean_dec(v___y_5151_);
lean_dec_ref(v___y_5150_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5156_, lean_object* v_val_5157_, lean_object* v_matchDeclName_5158_, lean_object* v___x_5159_, lean_object* v___x_5160_, lean_object* v_a_5161_, lean_object* v___x_5162_, lean_object* v___x_5163_, lean_object* v___x_5164_, lean_object* v___x_5165_, lean_object* v___x_5166_, lean_object* v___x_5167_, lean_object* v_inst_5168_, lean_object* v_R_5169_, lean_object* v_a_5170_, lean_object* v_b_5171_, lean_object* v_c_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_){
_start:
{
lean_object* v___x_5178_; 
v___x_5178_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5156_, v_val_5157_, v_matchDeclName_5158_, v___x_5159_, v___x_5160_, v_a_5161_, v___x_5162_, v___x_5163_, v___x_5164_, v___x_5165_, v___x_5166_, v___x_5167_, v_a_5170_, v_b_5171_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
return v___x_5178_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5179_ = _args[0];
lean_object* v_val_5180_ = _args[1];
lean_object* v_matchDeclName_5181_ = _args[2];
lean_object* v___x_5182_ = _args[3];
lean_object* v___x_5183_ = _args[4];
lean_object* v_a_5184_ = _args[5];
lean_object* v___x_5185_ = _args[6];
lean_object* v___x_5186_ = _args[7];
lean_object* v___x_5187_ = _args[8];
lean_object* v___x_5188_ = _args[9];
lean_object* v___x_5189_ = _args[10];
lean_object* v___x_5190_ = _args[11];
lean_object* v_inst_5191_ = _args[12];
lean_object* v_R_5192_ = _args[13];
lean_object* v_a_5193_ = _args[14];
lean_object* v_b_5194_ = _args[15];
lean_object* v_c_5195_ = _args[16];
lean_object* v___y_5196_ = _args[17];
lean_object* v___y_5197_ = _args[18];
lean_object* v___y_5198_ = _args[19];
lean_object* v___y_5199_ = _args[20];
lean_object* v___y_5200_ = _args[21];
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5179_, v_val_5180_, v_matchDeclName_5181_, v___x_5182_, v___x_5183_, v_a_5184_, v___x_5185_, v___x_5186_, v___x_5187_, v___x_5188_, v___x_5189_, v___x_5190_, v_inst_5191_, v_R_5192_, v_a_5193_, v_b_5194_, v_c_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_);
lean_dec(v___y_5199_);
lean_dec_ref(v___y_5198_);
lean_dec(v___y_5197_);
lean_dec_ref(v___y_5196_);
lean_dec(v_upperBound_5179_);
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5202_, lean_object* v_matchDeclName_5203_, lean_object* v_a_5204_, lean_object* v_b_5205_){
_start:
{
uint8_t v___x_5207_; 
v___x_5207_ = lean_nat_dec_lt(v_a_5204_, v_upperBound_5202_);
if (v___x_5207_ == 0)
{
lean_object* v___x_5208_; 
lean_dec(v_a_5204_);
lean_dec(v_matchDeclName_5203_);
v___x_5208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5208_, 0, v_b_5205_);
return v___x_5208_;
}
else
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; 
v___x_5209_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5203_);
v___x_5210_ = l_Lean_Name_str___override(v_matchDeclName_5203_, v___x_5209_);
v___x_5211_ = lean_unsigned_to_nat(1u);
v___x_5212_ = lean_nat_add(v_a_5204_, v___x_5211_);
lean_dec(v_a_5204_);
lean_inc(v___x_5212_);
v___x_5213_ = lean_name_append_index_after(v___x_5210_, v___x_5212_);
v___x_5214_ = lean_array_push(v_b_5205_, v___x_5213_);
v_a_5204_ = v___x_5212_;
v_b_5205_ = v___x_5214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5216_, lean_object* v_matchDeclName_5217_, lean_object* v_a_5218_, lean_object* v_b_5219_, lean_object* v___y_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5216_, v_matchDeclName_5217_, v_a_5218_, v_b_5219_);
lean_dec(v_upperBound_5216_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_){
_start:
{
lean_object* v___x_5228_; lean_object* v_firstEqnName_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; 
v___x_5228_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5222_, 3);
v_firstEqnName_5229_ = l_Lean_Name_str___override(v_matchDeclName_5222_, v___x_5228_);
v___x_5230_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5230_, 0, v_matchDeclName_5222_);
v___x_5231_ = l_Lean_Meta_realizeConst(v_matchDeclName_5222_, v_firstEqnName_5229_, v___x_5230_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
if (lean_obj_tag(v___x_5231_) == 0)
{
lean_object* v___x_5232_; lean_object* v_a_5233_; 
lean_dec_ref_known(v___x_5231_, 1);
lean_inc(v_matchDeclName_5222_);
v___x_5232_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_5222_, v_a_5226_);
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc(v_a_5233_);
lean_dec_ref(v___x_5232_);
if (lean_obj_tag(v_a_5233_) == 1)
{
lean_object* v_val_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
lean_dec(v_a_5226_);
lean_dec_ref(v_a_5225_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
v_val_5234_ = lean_ctor_get(v_a_5233_, 0);
lean_inc(v_val_5234_);
lean_dec_ref_known(v_a_5233_, 1);
v___x_5235_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5234_);
lean_dec(v_val_5234_);
v___x_5236_ = lean_unsigned_to_nat(0u);
v___x_5237_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7));
v___x_5238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5235_, v_matchDeclName_5222_, v___x_5236_, v___x_5237_);
lean_dec(v___x_5235_);
return v___x_5238_;
}
else
{
lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; 
lean_dec(v_a_5233_);
v___x_5239_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5240_ = l_Lean_MessageData_ofName(v_matchDeclName_5222_);
v___x_5241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5241_, 0, v___x_5239_);
lean_ctor_set(v___x_5241_, 1, v___x_5240_);
v___x_5242_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5241_);
lean_ctor_set(v___x_5243_, 1, v___x_5242_);
v___x_5244_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5243_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_);
lean_dec(v_a_5226_);
lean_dec_ref(v_a_5225_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
return v___x_5244_;
}
}
else
{
lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5252_; 
lean_dec(v_a_5226_);
lean_dec_ref(v_a_5225_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
lean_dec(v_matchDeclName_5222_);
v_a_5245_ = lean_ctor_get(v___x_5231_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5231_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_5231_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5231_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5250_; 
if (v_isShared_5248_ == 0)
{
v___x_5250_ = v___x_5247_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_a_5245_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_, lean_object* v_a_5257_, lean_object* v_a_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = lean_get_congr_match_equations_for(v_matchDeclName_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_);
return v_res_5259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5260_, lean_object* v_matchDeclName_5261_, lean_object* v_inst_5262_, lean_object* v_R_5263_, lean_object* v_a_5264_, lean_object* v_b_5265_, lean_object* v_c_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
lean_object* v___x_5272_; 
v___x_5272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5260_, v_matchDeclName_5261_, v_a_5264_, v_b_5265_);
return v___x_5272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5273_, lean_object* v_matchDeclName_5274_, lean_object* v_inst_5275_, lean_object* v_R_5276_, lean_object* v_a_5277_, lean_object* v_b_5278_, lean_object* v_c_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5273_, v_matchDeclName_5274_, v_inst_5275_, v_R_5276_, v_a_5277_, v_b_5278_, v_c_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
lean_dec(v___y_5283_);
lean_dec_ref(v___y_5282_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v_upperBound_5273_);
return v_res_5285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5336_ = lean_unsigned_to_nat(3248161880u);
v___x_5337_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5338_ = l_Lean_Name_num___override(v___x_5337_, v___x_5336_);
return v___x_5338_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; 
v___x_5340_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5341_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5342_ = l_Lean_Name_str___override(v___x_5341_, v___x_5340_);
return v___x_5342_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; 
v___x_5344_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5345_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5346_ = l_Lean_Name_str___override(v___x_5345_, v___x_5344_);
return v___x_5346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; 
v___x_5347_ = lean_unsigned_to_nat(2u);
v___x_5348_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5349_ = l_Lean_Name_num___override(v___x_5348_, v___x_5347_);
return v___x_5349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5351_; uint8_t v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; 
v___x_5351_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
v___x_5352_ = 0;
v___x_5353_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5354_ = l_Lean_registerTraceClass(v___x_5351_, v___x_5352_, v___x_5353_);
return v___x_5354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5357_, lean_object* v_n_5358_){
_start:
{
if (lean_obj_tag(v_n_5358_) == 1)
{
lean_object* v_pre_5359_; lean_object* v_str_5360_; uint8_t v___x_5366_; 
v_pre_5359_ = lean_ctor_get(v_n_5358_, 0);
lean_inc(v_pre_5359_);
v_str_5360_ = lean_ctor_get(v_n_5358_, 1);
lean_inc_ref_n(v_str_5360_, 2);
lean_dec_ref_known(v_n_5358_, 2);
v___x_5366_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5360_);
if (v___x_5366_ == 0)
{
lean_object* v___x_5367_; uint8_t v___x_5368_; 
v___x_5367_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5368_ = lean_string_dec_eq(v_str_5360_, v___x_5367_);
lean_dec_ref(v_str_5360_);
if (v___x_5368_ == 0)
{
lean_object* v___x_5369_; 
lean_dec(v_pre_5359_);
lean_dec_ref(v_env_5357_);
v___x_5369_ = lean_box(0);
return v___x_5369_;
}
else
{
goto v___jp_5361_;
}
}
else
{
lean_dec_ref(v_str_5360_);
goto v___jp_5361_;
}
v___jp_5361_:
{
lean_object* v___x_5362_; 
v___x_5362_ = l_Lean_privateToUserName_x3f(v_pre_5359_);
if (lean_obj_tag(v___x_5362_) == 0)
{
lean_dec_ref(v_env_5357_);
return v___x_5362_;
}
else
{
lean_object* v_val_5363_; uint8_t v___x_5364_; 
v_val_5363_ = lean_ctor_get(v___x_5362_, 0);
lean_inc(v_val_5363_);
v___x_5364_ = l_Lean_Meta_isMatcherCore(v_env_5357_, v_val_5363_);
if (v___x_5364_ == 0)
{
lean_object* v___x_5365_; 
lean_dec_ref_known(v___x_5362_, 1);
v___x_5365_ = lean_box(0);
return v___x_5365_;
}
else
{
return v___x_5362_;
}
}
}
}
else
{
lean_object* v___x_5370_; 
lean_dec(v_n_5358_);
lean_dec_ref(v_env_5357_);
v___x_5370_ = lean_box(0);
return v___x_5370_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5371_, lean_object* v_x2_5372_){
_start:
{
lean_object* v___x_5373_; 
v___x_5373_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5371_, v_x2_5372_);
if (lean_obj_tag(v___x_5373_) == 0)
{
uint8_t v___x_5374_; 
v___x_5374_ = 0;
return v___x_5374_;
}
else
{
uint8_t v___x_5375_; 
lean_dec_ref_known(v___x_5373_, 1);
v___x_5375_ = 1;
return v___x_5375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5376_, lean_object* v_x2_5377_){
_start:
{
uint8_t v_res_5378_; lean_object* v_r_5379_; 
v_res_5378_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5376_, v_x2_5377_);
v_r_5379_ = lean_box(v_res_5378_);
return v_r_5379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5382_; lean_object* v___x_5383_; 
v___f_5382_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5383_ = l_Lean_registerReservedNamePredicate(v___f_5382_);
return v___x_5383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5385_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5392_; uint64_t v___x_5393_; 
v___x_5392_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5393_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5392_);
return v___x_5393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5394_; lean_object* v___x_5395_; lean_object* v___x_5396_; 
v___x_5394_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5395_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5396_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5396_, 0, v___x_5395_);
lean_ctor_set_uint64(v___x_5396_, sizeof(void*)*1, v___x_5394_);
return v___x_5396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5399_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5400_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5401_ = lean_unsigned_to_nat(0u);
v___x_5402_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5401_);
lean_ctor_set(v___x_5402_, 1, v___x_5401_);
lean_ctor_set(v___x_5402_, 2, v___x_5401_);
lean_ctor_set(v___x_5402_, 3, v___x_5401_);
lean_ctor_set(v___x_5402_, 4, v___x_5400_);
lean_ctor_set(v___x_5402_, 5, v___x_5400_);
lean_ctor_set(v___x_5402_, 6, v___x_5400_);
lean_ctor_set(v___x_5402_, 7, v___x_5400_);
lean_ctor_set(v___x_5402_, 8, v___x_5400_);
lean_ctor_set(v___x_5402_, 9, v___x_5400_);
lean_ctor_set(v___x_5402_, 10, v___x_5400_);
lean_ctor_set(v___x_5402_, 11, v___x_5399_);
return v___x_5402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5403_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5404_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_5404_, 0, v___x_5403_);
lean_ctor_set(v___x_5404_, 1, v___x_5403_);
lean_ctor_set(v___x_5404_, 2, v___x_5403_);
lean_ctor_set(v___x_5404_, 3, v___x_5403_);
lean_ctor_set(v___x_5404_, 4, v___x_5403_);
lean_ctor_set(v___x_5404_, 5, v___x_5403_);
lean_ctor_set(v___x_5404_, 6, v___x_5403_);
return v___x_5404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5405_; lean_object* v___x_5406_; 
v___x_5405_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5406_, 0, v___x_5405_);
lean_ctor_set(v___x_5406_, 1, v___x_5405_);
lean_ctor_set(v___x_5406_, 2, v___x_5405_);
lean_ctor_set(v___x_5406_, 3, v___x_5405_);
lean_ctor_set(v___x_5406_, 4, v___x_5405_);
return v___x_5406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5407_, lean_object* v_name_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v___x_5412_; lean_object* v_env_5413_; lean_object* v___x_5414_; 
v___x_5412_ = lean_st_ref_get(v___y_5410_);
v_env_5413_ = lean_ctor_get(v___x_5412_, 0);
lean_inc_ref(v_env_5413_);
lean_dec(v___x_5412_);
v___x_5414_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5413_, v_name_5408_);
if (lean_obj_tag(v___x_5414_) == 1)
{
lean_object* v_val_5415_; uint8_t v___x_5416_; uint8_t v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; 
v_val_5415_ = lean_ctor_get(v___x_5414_, 0);
lean_inc(v_val_5415_);
lean_dec_ref_known(v___x_5414_, 1);
v___x_5416_ = 0;
v___x_5417_ = 1;
v___x_5418_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5419_ = lean_unsigned_to_nat(0u);
v___x_5420_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5421_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5422_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5423_ = lean_box(0);
lean_inc(v___x_5407_);
v___x_5424_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5424_, 0, v___x_5418_);
lean_ctor_set(v___x_5424_, 1, v___x_5407_);
lean_ctor_set(v___x_5424_, 2, v___x_5421_);
lean_ctor_set(v___x_5424_, 3, v___x_5422_);
lean_ctor_set(v___x_5424_, 4, v___x_5423_);
lean_ctor_set(v___x_5424_, 5, v___x_5419_);
lean_ctor_set(v___x_5424_, 6, v___x_5423_);
lean_ctor_set_uint8(v___x_5424_, sizeof(void*)*7, v___x_5416_);
lean_ctor_set_uint8(v___x_5424_, sizeof(void*)*7 + 1, v___x_5416_);
lean_ctor_set_uint8(v___x_5424_, sizeof(void*)*7 + 2, v___x_5416_);
lean_ctor_set_uint8(v___x_5424_, sizeof(void*)*7 + 3, v___x_5417_);
v___x_5425_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5426_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5427_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5428_, 0, v___x_5425_);
lean_ctor_set(v___x_5428_, 1, v___x_5426_);
lean_ctor_set(v___x_5428_, 2, v___x_5407_);
lean_ctor_set(v___x_5428_, 3, v___x_5420_);
lean_ctor_set(v___x_5428_, 4, v___x_5427_);
v___x_5429_ = lean_st_mk_ref(v___x_5428_);
lean_inc(v___y_5410_);
lean_inc_ref(v___y_5409_);
lean_inc(v___x_5429_);
v___x_5430_ = lean_get_match_equations_for(v_val_5415_, v___x_5424_, v___x_5429_, v___y_5409_, v___y_5410_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5439_; 
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5439_ == 0)
{
lean_object* v_unused_5440_; 
v_unused_5440_ = lean_ctor_get(v___x_5430_, 0);
lean_dec(v_unused_5440_);
v___x_5432_ = v___x_5430_;
v_isShared_5433_ = v_isSharedCheck_5439_;
goto v_resetjp_5431_;
}
else
{
lean_dec(v___x_5430_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5439_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5437_; 
v___x_5434_ = lean_st_ref_get(v___x_5429_);
lean_dec(v___x_5429_);
lean_dec(v___x_5434_);
v___x_5435_ = lean_box(v___x_5417_);
if (v_isShared_5433_ == 0)
{
lean_ctor_set(v___x_5432_, 0, v___x_5435_);
v___x_5437_ = v___x_5432_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v___x_5435_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
return v___x_5437_;
}
}
}
else
{
lean_object* v_a_5441_; lean_object* v___x_5443_; uint8_t v_isShared_5444_; uint8_t v_isSharedCheck_5448_; 
lean_dec(v___x_5429_);
v_a_5441_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5448_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5448_ == 0)
{
v___x_5443_ = v___x_5430_;
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
else
{
lean_inc(v_a_5441_);
lean_dec(v___x_5430_);
v___x_5443_ = lean_box(0);
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
v_resetjp_5442_:
{
lean_object* v___x_5446_; 
if (v_isShared_5444_ == 0)
{
v___x_5446_ = v___x_5443_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_a_5441_);
v___x_5446_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
return v___x_5446_;
}
}
}
}
else
{
uint8_t v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; 
lean_dec(v___x_5414_);
lean_dec(v___x_5407_);
v___x_5449_ = 0;
v___x_5450_ = lean_box(v___x_5449_);
v___x_5451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5451_, 0, v___x_5450_);
return v___x_5451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5452_, lean_object* v_name_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_){
_start:
{
lean_object* v_res_5457_; 
v_res_5457_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5452_, v_name_5453_, v___y_5454_, v___y_5455_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
return v_res_5457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5461_; lean_object* v___x_5462_; 
v___f_5461_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5462_ = l_Lean_registerReservedNameAction(v___f_5461_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5463_){
_start:
{
lean_object* v_res_5464_; 
v_res_5464_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5465_, lean_object* v_n_5466_){
_start:
{
if (lean_obj_tag(v_n_5466_) == 1)
{
lean_object* v_pre_5467_; lean_object* v_str_5468_; uint8_t v___x_5469_; 
v_pre_5467_ = lean_ctor_get(v_n_5466_, 0);
lean_inc(v_pre_5467_);
v_str_5468_ = lean_ctor_get(v_n_5466_, 1);
lean_inc_ref(v_str_5468_);
lean_dec_ref_known(v_n_5466_, 2);
v___x_5469_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5468_);
if (v___x_5469_ == 0)
{
lean_object* v___x_5470_; 
lean_dec(v_pre_5467_);
lean_dec_ref(v_env_5465_);
v___x_5470_ = lean_box(0);
return v___x_5470_;
}
else
{
uint8_t v___x_5471_; 
lean_inc(v_pre_5467_);
v___x_5471_ = l_Lean_Meta_isMatcherCore(v_env_5465_, v_pre_5467_);
if (v___x_5471_ == 0)
{
lean_object* v___x_5472_; 
lean_dec(v_pre_5467_);
v___x_5472_ = lean_box(0);
return v___x_5472_;
}
else
{
lean_object* v___x_5473_; 
v___x_5473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5473_, 0, v_pre_5467_);
return v___x_5473_;
}
}
}
else
{
lean_object* v___x_5474_; 
lean_dec(v_n_5466_);
lean_dec_ref(v_env_5465_);
v___x_5474_ = lean_box(0);
return v___x_5474_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5475_, lean_object* v_x2_5476_){
_start:
{
lean_object* v___x_5477_; 
v___x_5477_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5475_, v_x2_5476_);
if (lean_obj_tag(v___x_5477_) == 0)
{
uint8_t v___x_5478_; 
v___x_5478_ = 0;
return v___x_5478_;
}
else
{
uint8_t v___x_5479_; 
lean_dec_ref_known(v___x_5477_, 1);
v___x_5479_ = 1;
return v___x_5479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5480_, lean_object* v_x2_5481_){
_start:
{
uint8_t v_res_5482_; lean_object* v_r_5483_; 
v_res_5482_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5480_, v_x2_5481_);
v_r_5483_ = lean_box(v_res_5482_);
return v_r_5483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5486_; lean_object* v___x_5487_; 
v___f_5486_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5487_ = l_Lean_registerReservedNamePredicate(v___f_5486_);
return v___x_5487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5488_){
_start:
{
lean_object* v_res_5489_; 
v_res_5489_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5490_, lean_object* v_name_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_){
_start:
{
lean_object* v___x_5495_; lean_object* v_env_5496_; lean_object* v___x_5497_; 
v___x_5495_ = lean_st_ref_get(v___y_5493_);
v_env_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc_ref(v_env_5496_);
lean_dec(v___x_5495_);
v___x_5497_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5496_, v_name_5491_);
if (lean_obj_tag(v___x_5497_) == 1)
{
lean_object* v_val_5498_; uint8_t v___x_5499_; uint8_t v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; 
v_val_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc(v_val_5498_);
lean_dec_ref_known(v___x_5497_, 1);
v___x_5499_ = 0;
v___x_5500_ = 1;
v___x_5501_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5502_ = lean_unsigned_to_nat(32u);
v___x_5503_ = lean_mk_empty_array_with_capacity(v___x_5502_);
lean_dec_ref(v___x_5503_);
v___x_5504_ = lean_unsigned_to_nat(0u);
v___x_5505_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5506_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5507_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5508_ = lean_box(0);
lean_inc(v___x_5490_);
v___x_5509_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5509_, 0, v___x_5501_);
lean_ctor_set(v___x_5509_, 1, v___x_5490_);
lean_ctor_set(v___x_5509_, 2, v___x_5506_);
lean_ctor_set(v___x_5509_, 3, v___x_5507_);
lean_ctor_set(v___x_5509_, 4, v___x_5508_);
lean_ctor_set(v___x_5509_, 5, v___x_5504_);
lean_ctor_set(v___x_5509_, 6, v___x_5508_);
lean_ctor_set_uint8(v___x_5509_, sizeof(void*)*7, v___x_5499_);
lean_ctor_set_uint8(v___x_5509_, sizeof(void*)*7 + 1, v___x_5499_);
lean_ctor_set_uint8(v___x_5509_, sizeof(void*)*7 + 2, v___x_5499_);
lean_ctor_set_uint8(v___x_5509_, sizeof(void*)*7 + 3, v___x_5500_);
v___x_5510_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5511_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5512_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5513_, 0, v___x_5510_);
lean_ctor_set(v___x_5513_, 1, v___x_5511_);
lean_ctor_set(v___x_5513_, 2, v___x_5490_);
lean_ctor_set(v___x_5513_, 3, v___x_5505_);
lean_ctor_set(v___x_5513_, 4, v___x_5512_);
v___x_5514_ = lean_st_mk_ref(v___x_5513_);
lean_inc(v___y_5493_);
lean_inc_ref(v___y_5492_);
lean_inc(v___x_5514_);
v___x_5515_ = lean_get_congr_match_equations_for(v_val_5498_, v___x_5509_, v___x_5514_, v___y_5492_, v___y_5493_);
if (lean_obj_tag(v___x_5515_) == 0)
{
lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5524_; 
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5515_);
if (v_isSharedCheck_5524_ == 0)
{
lean_object* v_unused_5525_; 
v_unused_5525_ = lean_ctor_get(v___x_5515_, 0);
lean_dec(v_unused_5525_);
v___x_5517_ = v___x_5515_;
v_isShared_5518_ = v_isSharedCheck_5524_;
goto v_resetjp_5516_;
}
else
{
lean_dec(v___x_5515_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5524_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5522_; 
v___x_5519_ = lean_st_ref_get(v___x_5514_);
lean_dec(v___x_5514_);
lean_dec(v___x_5519_);
v___x_5520_ = lean_box(v___x_5500_);
if (v_isShared_5518_ == 0)
{
lean_ctor_set(v___x_5517_, 0, v___x_5520_);
v___x_5522_ = v___x_5517_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v___x_5520_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
return v___x_5522_;
}
}
}
else
{
lean_object* v_a_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5533_; 
lean_dec(v___x_5514_);
v_a_5526_ = lean_ctor_get(v___x_5515_, 0);
v_isSharedCheck_5533_ = !lean_is_exclusive(v___x_5515_);
if (v_isSharedCheck_5533_ == 0)
{
v___x_5528_ = v___x_5515_;
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_a_5526_);
lean_dec(v___x_5515_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5533_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v___x_5531_; 
if (v_isShared_5529_ == 0)
{
v___x_5531_ = v___x_5528_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_a_5526_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
else
{
uint8_t v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; 
lean_dec(v___x_5497_);
lean_dec(v___x_5490_);
v___x_5534_ = 0;
v___x_5535_ = lean_box(v___x_5534_);
v___x_5536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5536_, 0, v___x_5535_);
return v___x_5536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5537_, lean_object* v_name_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_){
_start:
{
lean_object* v_res_5542_; 
v_res_5542_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5537_, v_name_5538_, v___y_5539_, v___y_5540_);
lean_dec(v___y_5540_);
lean_dec_ref(v___y_5539_);
return v_res_5542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5546_; lean_object* v___x_5547_; 
v___f_5546_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5547_ = l_Lean_registerReservedNameAction(v___f_5546_);
return v___x_5547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5548_){
_start:
{
lean_object* v_res_5549_; 
v_res_5549_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5549_;
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
