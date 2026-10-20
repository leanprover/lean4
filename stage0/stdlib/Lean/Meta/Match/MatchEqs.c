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
lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v_a_1419_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v_a_1435_; uint8_t v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v_a_1499_; uint8_t v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v_toCold_1725_; lean_object* v_currRecDepth_1726_; lean_object* v_ref_1727_; uint16_t v_optionFlags_1728_; uint8_t v_suppressElabErrors_1729_; uint8_t v_isRecordingDeps_1730_; lean_object* v_options_1731_; lean_object* v_maxRecDepth_1732_; lean_object* v_inheritedTraceOptions_1733_; lean_object* v_cls_1734_; lean_object* v___x_1746_; uint8_t v___x_1747_; 
v_toCold_1725_ = lean_ctor_get(v_a_1411_, 0);
v_currRecDepth_1726_ = lean_ctor_get(v_a_1411_, 1);
v_ref_1727_ = lean_ctor_get(v_a_1411_, 2);
v_optionFlags_1728_ = lean_ctor_get_uint16(v_a_1411_, sizeof(void*)*3);
v_suppressElabErrors_1729_ = lean_ctor_get_uint8(v_a_1411_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1730_ = lean_ctor_get_uint8(v_a_1411_, sizeof(void*)*3 + 3);
v_options_1731_ = lean_ctor_get(v_toCold_1725_, 2);
v_maxRecDepth_1732_ = lean_ctor_get(v_toCold_1725_, 3);
v_inheritedTraceOptions_1733_ = lean_ctor_get(v_toCold_1725_, 11);
v_cls_1734_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_nat_dec_eq(v_maxRecDepth_1732_, v___x_1746_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_nat_dec_eq(v_currRecDepth_1726_, v_maxRecDepth_1732_);
if (v___x_1748_ == 0)
{
goto v___jp_1735_;
}
else
{
lean_object* v___x_1749_; 
lean_dec(v_mvarId_1407_);
lean_dec(v_matchDeclName_1406_);
lean_inc(v_ref_1727_);
v___x_1749_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1727_);
return v___x_1749_;
}
}
else
{
goto v___jp_1735_;
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
lean_dec_ref(v___y_1418_);
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
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1408_, v_matchDeclName_1406_, v_a_1419_, v___x_1425_, v___x_1426_, v___x_1422_, v___y_1417_, v___y_1416_, v___y_1418_, v___y_1415_);
lean_dec_ref(v___y_1418_);
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
v___x_1438_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1432_, v___y_1430_, v___y_1429_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v___x_1439_; 
lean_dec_ref_known(v___x_1438_, 1);
v___x_1439_ = l_Lean_Meta_saveState___redArg(v___y_1430_, v___y_1429_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1441_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
lean_inc(v___y_1434_);
v___x_1441_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1434_, v___y_1431_, v___y_1430_, v___y_1433_, v___y_1429_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; 
lean_dec(v_a_1440_);
lean_dec(v___y_1434_);
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___y_1415_ = v___y_1429_;
v___y_1416_ = v___y_1430_;
v___y_1417_ = v___y_1431_;
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
v___x_1449_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1440_, v___y_1430_, v___y_1429_);
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
lean_ctor_set(v___x_1451_, 0, v___y_1434_);
v___x_1459_ = v___x_1451_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___y_1434_);
v___x_1459_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1457_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1460_, v___y_1431_, v___y_1430_, v___y_1433_, v___y_1429_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___y_1415_ = v___y_1429_;
v___y_1416_ = v___y_1430_;
v___y_1417_ = v___y_1431_;
v___y_1418_ = v___y_1433_;
v_a_1419_ = v_a_1462_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v___y_1433_);
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
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v_matchDeclName_1406_);
return v___x_1449_;
}
}
else
{
lean_object* v___x_1475_; 
lean_dec(v_a_1440_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
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
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
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
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
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
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v_matchDeclName_1406_);
return v___x_1438_;
}
}
else
{
lean_object* v___x_1489_; 
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v_matchDeclName_1406_);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_a_1435_);
return v___x_1489_;
}
}
else
{
lean_object* v___x_1490_; 
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec_ref(v___y_1432_);
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
v___x_1502_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1495_, v___y_1494_, v___y_1493_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref_known(v___x_1502_, 1);
v___x_1503_ = lean_box(0);
v___x_1504_ = l_Lean_Meta_saveState___redArg(v___y_1494_, v___y_1493_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1506_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
lean_inc(v___y_1497_);
v___x_1506_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1497_, v___x_1503_, v___y_1492_, v___y_1496_, v___y_1494_, v___y_1498_, v___y_1493_);
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
v___x_1513_ = l_Lean_Meta_trySubst(v_mvarId_1511_, v_fvarId_1512_, v___y_1496_, v___y_1494_, v___y_1498_, v___y_1493_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v_mvarId_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v_a_1505_);
lean_dec(v___y_1497_);
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
v___y_1416_ = v___y_1494_;
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
v___y_1429_ = v___y_1493_;
v___y_1430_ = v___y_1494_;
v___y_1431_ = v___y_1496_;
v___y_1432_ = v_a_1505_;
v___y_1433_ = v___y_1498_;
v___y_1434_ = v___y_1497_;
v_a_1435_ = v_a_1520_;
goto v___jp_1428_;
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec(v_a_1507_);
v___x_1521_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1522_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1521_, v___y_1496_, v___y_1494_, v___y_1498_, v___y_1493_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; 
lean_dec(v_a_1505_);
lean_dec(v___y_1497_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___y_1415_ = v___y_1493_;
v___y_1416_ = v___y_1494_;
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
v___y_1429_ = v___y_1493_;
v___y_1430_ = v___y_1494_;
v___y_1431_ = v___y_1496_;
v___y_1432_ = v_a_1505_;
v___y_1433_ = v___y_1498_;
v___y_1434_ = v___y_1497_;
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
v___y_1429_ = v___y_1493_;
v___y_1430_ = v___y_1494_;
v___y_1431_ = v___y_1496_;
v___y_1432_ = v_a_1505_;
v___y_1433_ = v___y_1498_;
v___y_1434_ = v___y_1497_;
v_a_1435_ = v_a_1525_;
goto v___jp_1428_;
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
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
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec(v_matchDeclName_1406_);
return v___x_1502_;
}
}
else
{
lean_object* v___x_1534_; 
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1495_);
lean_dec(v_matchDeclName_1406_);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_a_1499_);
return v___x_1534_;
}
}
else
{
lean_object* v___x_1535_; 
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1495_);
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
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1540_);
v_a_1545_ = lean_ctor_get(v___y_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___y_1544_, 1);
v___y_1415_ = v___y_1539_;
v___y_1416_ = v___y_1538_;
v___y_1417_ = v___y_1541_;
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
v___y_1493_ = v___y_1539_;
v___y_1494_ = v___y_1538_;
v___y_1495_ = v___y_1540_;
v___y_1496_ = v___y_1541_;
v___y_1497_ = v___y_1542_;
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
v___y_1415_ = v___y_1551_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1548_;
v___y_1418_ = v___y_1550_;
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
v___y_1415_ = v___y_1551_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1548_;
v___y_1418_ = v___y_1550_;
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
v___y_1415_ = v___y_1551_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1548_;
v___y_1418_ = v___y_1550_;
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
v___y_1415_ = v___y_1551_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1548_;
v___y_1418_ = v___y_1550_;
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
v___y_1415_ = v___y_1551_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1548_;
v___y_1418_ = v___y_1550_;
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
v___y_1415_ = v___y_1551_;
v___y_1416_ = v___y_1549_;
v___y_1417_ = v___y_1548_;
v___y_1418_ = v___y_1550_;
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
v___y_1537_ = v___x_1555_;
v___y_1538_ = v___y_1549_;
v___y_1539_ = v___y_1551_;
v___y_1540_ = v_a_1621_;
v___y_1541_ = v___y_1548_;
v___y_1542_ = v_a_1554_;
v___y_1543_ = v___y_1550_;
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
v___y_1537_ = v___x_1555_;
v___y_1538_ = v___y_1549_;
v___y_1539_ = v___y_1551_;
v___y_1540_ = v_a_1621_;
v___y_1541_ = v___y_1548_;
v___y_1542_ = v_a_1554_;
v___y_1543_ = v___y_1550_;
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
v___y_1492_ = v___x_1555_;
v___y_1493_ = v___y_1551_;
v___y_1494_ = v___y_1549_;
v___y_1495_ = v_a_1621_;
v___y_1496_ = v___y_1548_;
v___y_1497_ = v_a_1554_;
v___y_1498_ = v___y_1550_;
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
v___y_1492_ = v___x_1555_;
v___y_1493_ = v___y_1551_;
v___y_1494_ = v___y_1549_;
v___y_1495_ = v_a_1621_;
v___y_1496_ = v___y_1548_;
v___y_1497_ = v_a_1554_;
v___y_1498_ = v___y_1550_;
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
v___jp_1735_:
{
uint8_t v_hasTrace_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_hasTrace_1736_ = lean_ctor_get_uint8(v_options_1731_, sizeof(void*)*1);
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = lean_nat_add(v_currRecDepth_1726_, v___x_1737_);
lean_inc(v_ref_1727_);
lean_inc_ref(v_toCold_1725_);
v___x_1739_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1739_, 0, v_toCold_1725_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
lean_ctor_set(v___x_1739_, 2, v_ref_1727_);
lean_ctor_set_uint16(v___x_1739_, sizeof(void*)*3, v_optionFlags_1728_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*3 + 2, v_suppressElabErrors_1729_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*3 + 3, v_isRecordingDeps_1730_);
if (v_hasTrace_1736_ == 0)
{
v___y_1548_ = v_a_1409_;
v___y_1549_ = v_a_1410_;
v___y_1550_ = v___x_1739_;
v___y_1551_ = v_a_1412_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17);
v___x_1741_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1733_, v_options_1731_, v___x_1740_);
if (v___x_1741_ == 0)
{
v___y_1548_ = v_a_1409_;
v___y_1549_ = v_a_1410_;
v___y_1550_ = v___x_1739_;
v___y_1551_ = v_a_1412_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1742_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__19, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__19_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__19);
lean_inc(v_mvarId_1407_);
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_mvarId_1407_);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1734_, v___x_1744_, v_a_1409_, v_a_1410_, v___x_1739_, v_a_1412_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_dec_ref_known(v___x_1745_, 1);
v___y_1548_ = v_a_1409_;
v___y_1549_ = v_a_1410_;
v___y_1550_ = v___x_1739_;
v___y_1551_ = v_a_1412_;
goto v___jp_1547_;
}
else
{
lean_dec_ref_known(v___x_1739_, 3);
lean_dec(v_mvarId_1407_);
lean_dec(v_matchDeclName_1406_);
return v___x_1745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1750_, lean_object* v_matchDeclName_1751_, lean_object* v_as_1752_, size_t v_i_1753_, size_t v_stop_1754_, lean_object* v_b_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_usize_dec_eq(v_i_1753_, v_stop_1754_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1762_ = lean_array_uget_borrowed(v_as_1752_, v_i_1753_);
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_nat_add(v_depth_1750_, v___x_1763_);
lean_inc(v___x_1762_);
lean_inc(v_matchDeclName_1751_);
v___x_1765_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1751_, v___x_1762_, v___x_1764_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___x_1764_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; size_t v___x_1767_; size_t v___x_1768_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1767_ = ((size_t)1ULL);
v___x_1768_ = lean_usize_add(v_i_1753_, v___x_1767_);
v_i_1753_ = v___x_1768_;
v_b_1755_ = v_a_1766_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1751_);
return v___x_1765_;
}
}
else
{
lean_object* v___x_1770_; 
lean_dec(v_matchDeclName_1751_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_b_1755_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1771_, lean_object* v_matchDeclName_1772_, lean_object* v_as_1773_, lean_object* v_i_1774_, lean_object* v_stop_1775_, lean_object* v_b_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
size_t v_i_boxed_1782_; size_t v_stop_boxed_1783_; lean_object* v_res_1784_; 
v_i_boxed_1782_ = lean_unbox_usize(v_i_1774_);
lean_dec(v_i_1774_);
v_stop_boxed_1783_ = lean_unbox_usize(v_stop_1775_);
lean_dec(v_stop_1775_);
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1771_, v_matchDeclName_1772_, v_as_1773_, v_i_boxed_1782_, v_stop_boxed_1783_, v_b_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v_as_1773_);
lean_dec(v_depth_1771_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1785_, lean_object* v_mvarId_1786_, lean_object* v_depth_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1785_, v_mvarId_1786_, v_depth_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_depth_1787_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1794_, lean_object* v___y_1795_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = l_Lean_Expr_hasMVar(v_e_1794_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v_e_1794_);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; lean_object* v_mctx_1800_; lean_object* v___x_1801_; lean_object* v_fst_1802_; lean_object* v_snd_1803_; lean_object* v___x_1804_; lean_object* v_cache_1805_; lean_object* v_zetaDeltaFVarIds_1806_; lean_object* v_postponed_1807_; lean_object* v_diag_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1817_; 
v___x_1799_ = lean_st_ref_get(v___y_1795_);
v_mctx_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc_ref(v_mctx_1800_);
lean_dec(v___x_1799_);
v___x_1801_ = l_Lean_instantiateMVarsCore(v_mctx_1800_, v_e_1794_);
v_fst_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_fst_1802_);
v_snd_1803_ = lean_ctor_get(v___x_1801_, 1);
lean_inc(v_snd_1803_);
lean_dec_ref(v___x_1801_);
v___x_1804_ = lean_st_ref_take(v___y_1795_);
v_cache_1805_ = lean_ctor_get(v___x_1804_, 1);
v_zetaDeltaFVarIds_1806_ = lean_ctor_get(v___x_1804_, 2);
v_postponed_1807_ = lean_ctor_get(v___x_1804_, 3);
v_diag_1808_ = lean_ctor_get(v___x_1804_, 4);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v___x_1804_, 0);
lean_dec(v_unused_1818_);
v___x_1810_ = v___x_1804_;
v_isShared_1811_ = v_isSharedCheck_1817_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_diag_1808_);
lean_inc(v_postponed_1807_);
lean_inc(v_zetaDeltaFVarIds_1806_);
lean_inc(v_cache_1805_);
lean_dec(v___x_1804_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1817_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v_snd_1803_);
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_snd_1803_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_cache_1805_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_zetaDeltaFVarIds_1806_);
lean_ctor_set(v_reuseFailAlloc_1816_, 3, v_postponed_1807_);
lean_ctor_set(v_reuseFailAlloc_1816_, 4, v_diag_1808_);
v___x_1813_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_st_ref_put(v___y_1795_, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_fst_1802_);
return v___x_1815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1819_, v___y_1820_);
lean_dec(v___y_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1823_, v___y_1825_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1837_, lean_object* v_localInsts_1838_, lean_object* v_x_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1837_, v_localInsts_1838_, v_x_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_a_1854_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1845_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1845_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1862_, lean_object* v_localInsts_1863_, lean_object* v_x_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1862_, v_localInsts_1863_, v_x_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1871_, lean_object* v_lctx_1872_, lean_object* v_localInsts_1873_, lean_object* v_x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1872_, v_localInsts_1873_, v_x_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1881_, lean_object* v_lctx_1882_, lean_object* v_localInsts_1883_, lean_object* v_x_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1881_, v_lctx_1882_, v_localInsts_1883_, v_x_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1890_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1891_, lean_object* v_x_1892_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_name_eq(v_x_1892_, v_matchDeclName_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1894_, lean_object* v_x_1895_){
_start:
{
uint8_t v_res_1896_; lean_object* v_r_1897_; 
v_res_1896_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1894_, v_x_1895_);
lean_dec(v_x_1895_);
lean_dec(v_matchDeclName_1894_);
v_r_1897_ = lean_box(v_res_1896_);
return v_r_1897_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1898_, lean_object* v_a_1899_, lean_object* v_b_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_nat_dec_lt(v_a_1899_, v_upperBound_1898_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
lean_dec(v_a_1899_);
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_b_1900_);
return v___x_1907_;
}
else
{
uint8_t v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = 0;
v___x_1909_ = l_Lean_Meta_introSubstEq(v_b_1900_, v___x_1908_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v_snd_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v_snd_1911_ = lean_ctor_get(v_a_1910_, 1);
lean_inc(v_snd_1911_);
lean_dec(v_a_1910_);
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = lean_nat_add(v_a_1899_, v___x_1912_);
lean_dec(v_a_1899_);
v_a_1899_ = v___x_1913_;
v_b_1900_ = v_snd_1911_;
goto _start;
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_a_1899_);
v_a_1915_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1909_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1909_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1923_, lean_object* v_a_1924_, lean_object* v_b_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1923_, v_a_1924_, v_b_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v_upperBound_1923_);
return v_res_1931_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1937_ = l_Lean_stringToMessageData(v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1938_, lean_object* v___f_1939_, lean_object* v_matchDeclName_1940_, lean_object* v___x_1941_, lean_object* v_heqNum_1942_, lean_object* v_heqPos_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_2104_; 
v___x_1949_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1938_, v___y_1945_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_2104_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_2104_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = lean_box(0);
v___x_1955_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1950_, v___x_1954_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_2103_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_2103_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_2103_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_mvarId_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v_toCold_2023_; lean_object* v_options_2024_; lean_object* v_inheritedTraceOptions_2025_; uint8_t v_hasTrace_2026_; lean_object* v___x_2027_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; 
v_toCold_2023_ = lean_ctor_get(v___y_1946_, 0);
v_options_2024_ = lean_ctor_get(v_toCold_2023_, 2);
v_inheritedTraceOptions_2025_ = lean_ctor_get(v_toCold_2023_, 11);
v_hasTrace_2026_ = lean_ctor_get_uint8(v_options_2024_, sizeof(void*)*1);
v___x_2027_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
if (v_hasTrace_2026_ == 0)
{
lean_del_object(v___x_1952_);
v___y_2029_ = v___y_1944_;
v___y_2030_ = v___y_1945_;
v___y_2031_ = v___y_1946_;
v___y_2032_ = v___y_1947_;
goto v___jp_2028_;
}
else
{
lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17);
v___x_2087_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2025_, v_options_2024_, v___x_2086_);
if (v___x_2087_ == 0)
{
lean_del_object(v___x_1952_);
v___y_2029_ = v___y_1944_;
v___y_2030_ = v___y_1945_;
v___y_2031_ = v___y_1946_;
v___y_2032_ = v___y_1947_;
goto v___jp_2028_;
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2088_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2089_ = l_Lean_Expr_mvarId_x21(v_a_1956_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set_tag(v___x_1952_, 1);
lean_ctor_set(v___x_1952_, 0, v___x_2089_);
v___x_2091_ = v___x_1952_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2088_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2027_, v___x_2092_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_dec_ref_known(v___x_2093_, 1);
v___y_2029_ = v___y_1944_;
v___y_2030_ = v___y_1945_;
v___y_2031_ = v___y_1946_;
v___y_2032_ = v___y_1947_;
goto v___jp_2028_;
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_del_object(v___x_1958_);
lean_dec(v_a_1956_);
lean_dec(v_heqPos_1943_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
lean_dec_ref(v___f_1939_);
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
}
v___jp_1960_:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_MVarId_intros(v_mvarId_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v_snd_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
v_snd_1968_ = lean_ctor_get(v_a_1967_, 1);
lean_inc_n(v_snd_1968_, 2);
lean_dec(v_a_1967_);
v___x_1969_ = 1;
v___x_1970_ = l_Lean_MVarId_refl(v_snd_1968_, v___x_1969_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; 
lean_dec_ref_known(v___x_1970_, 1);
lean_dec(v_snd_1968_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
lean_dec_ref(v___f_1939_);
v___x_1971_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1956_, v___y_1963_);
return v___x_1971_;
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2014_; 
v_a_1972_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1974_ = v___x_1970_;
v_isShared_1975_ = v_isSharedCheck_2014_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1970_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2014_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
uint8_t v___x_1976_; 
v___x_1976_ = l_Lean_Exception_isInterrupt(v_a_1972_);
if (v___x_1976_ == 0)
{
uint8_t v___x_1977_; 
lean_inc(v_a_1972_);
v___x_1977_ = l_Lean_Exception_isRuntime(v_a_1972_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_del_object(v___x_1974_);
lean_dec(v_a_1972_);
v___x_1978_ = l_Lean_MVarId_deltaTarget(v_snd_1968_, v___f_1939_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = l_Lean_MVarId_heqOfEq(v_a_1979_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1982_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v___x_1982_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1940_, v_a_1981_, v___x_1941_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___x_1941_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v___x_1983_; 
lean_dec_ref_known(v___x_1982_, 1);
v___x_1983_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1956_, v___y_1963_);
return v___x_1983_;
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec(v_a_1956_);
v_a_1984_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1982_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1982_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_a_1956_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
v_a_1992_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1980_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1980_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_a_1956_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
v_a_2000_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1978_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1978_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v___x_2009_; 
lean_dec(v_snd_1968_);
lean_dec(v_a_1956_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
lean_dec_ref(v___f_1939_);
if (v_isShared_1975_ == 0)
{
v___x_2009_ = v___x_1974_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_1972_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
else
{
lean_object* v___x_2012_; 
lean_dec(v_snd_1968_);
lean_dec(v_a_1956_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
lean_dec_ref(v___f_1939_);
if (v_isShared_1975_ == 0)
{
v___x_2012_ = v___x_1974_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_1972_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_a_1956_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
lean_dec_ref(v___f_1939_);
v_a_2015_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1966_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1966_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
v___jp_2028_:
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = l_Lean_Expr_mvarId_x21(v_a_1956_);
v___x_2034_ = lean_nat_dec_lt(v___x_1941_, v_heqNum_1942_);
if (v___x_2034_ == 0)
{
lean_del_object(v___x_1958_);
lean_dec(v_heqPos_1943_);
v_mvarId_1961_ = v___x_2033_;
v___y_1962_ = v___y_2029_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_2035_; uint8_t v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = lean_box(0);
v___x_2036_ = 0;
v___x_2037_ = l_Lean_Meta_introNCore(v___x_2033_, v_heqPos_1943_, v___x_2035_, v___x_2036_, v___x_2036_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v_snd_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2076_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v_snd_2039_ = lean_ctor_get(v_a_2038_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v_a_2038_, 0);
lean_dec(v_unused_2077_);
v___x_2041_ = v_a_2038_;
v_isShared_2042_ = v_isSharedCheck_2076_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_snd_2039_);
lean_dec(v_a_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2076_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; 
lean_inc(v___x_1941_);
v___x_2043_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1942_, v___x_1941_, v_snd_2039_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_toCold_2044_; lean_object* v_options_2045_; uint8_t v_hasTrace_2046_; 
v_toCold_2044_ = lean_ctor_get(v___y_2031_, 0);
v_options_2045_ = lean_ctor_get(v_toCold_2044_, 2);
v_hasTrace_2046_ = lean_ctor_get_uint8(v_options_2045_, sizeof(void*)*1);
if (v_hasTrace_2046_ == 0)
{
lean_object* v_a_2047_; 
lean_del_object(v___x_2041_);
lean_del_object(v___x_1958_);
v_a_2047_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2043_, 1);
v_mvarId_1961_ = v_a_2047_;
v___y_1962_ = v___y_2029_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
goto v___jp_1960_;
}
else
{
lean_object* v_a_2048_; lean_object* v_inheritedTraceOptions_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v_a_2048_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2043_, 1);
v_inheritedTraceOptions_2049_ = lean_ctor_get(v_toCold_2044_, 11);
v___x_2050_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17);
v___x_2051_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2049_, v_options_2045_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_del_object(v___x_2041_);
lean_del_object(v___x_1958_);
v_mvarId_1961_ = v_a_2048_;
v___y_1962_ = v___y_2029_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2048_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set_tag(v___x_1958_, 1);
lean_ctor_set(v___x_1958_, 0, v_a_2048_);
v___x_2054_ = v___x_1958_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2048_);
v___x_2054_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2056_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 7);
lean_ctor_set(v___x_2041_, 1, v___x_2054_);
lean_ctor_set(v___x_2041_, 0, v___x_2052_);
v___x_2056_ = v___x_2041_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2057_; 
v___x_2057_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2027_, v___x_2056_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref_known(v___x_2057_, 1);
v_mvarId_1961_ = v_a_2048_;
v___y_1962_ = v___y_2029_;
v___y_1963_ = v___y_2030_;
v___y_1964_ = v___y_2031_;
v___y_1965_ = v___y_2032_;
goto v___jp_1960_;
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_2048_);
lean_dec(v_a_1956_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
lean_dec_ref(v___f_1939_);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
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
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_del_object(v___x_2041_);
lean_del_object(v___x_1958_);
lean_dec(v_a_1956_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
lean_dec_ref(v___f_1939_);
v_a_2068_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2043_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2043_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_del_object(v___x_1958_);
lean_dec(v_a_1956_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
lean_dec_ref(v___f_1939_);
v_a_2078_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2037_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2037_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1952_);
lean_dec(v_heqPos_1943_);
lean_dec(v___x_1941_);
lean_dec(v_matchDeclName_1940_);
lean_dec_ref(v___f_1939_);
return v___x_1955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2105_, lean_object* v___f_2106_, lean_object* v_matchDeclName_2107_, lean_object* v___x_2108_, lean_object* v_heqNum_2109_, lean_object* v_heqPos_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2105_, v___f_2106_, v_matchDeclName_2107_, v___x_2108_, v_heqNum_2109_, v_heqPos_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v_heqNum_2109_);
return v_res_2116_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = lean_unsigned_to_nat(32u);
v___x_2121_ = lean_mk_empty_array_with_capacity(v___x_2120_);
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2123_ = ((size_t)5ULL);
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = lean_unsigned_to_nat(32u);
v___x_2126_ = lean_mk_empty_array_with_capacity(v___x_2125_);
v___x_2127_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2128_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v___x_2126_);
lean_ctor_set(v___x_2128_, 2, v___x_2124_);
lean_ctor_set(v___x_2128_, 3, v___x_2124_);
lean_ctor_set_usize(v___x_2128_, 4, v___x_2123_);
return v___x_2128_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2129_ = lean_box(1);
v___x_2130_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2131_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2132_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___x_2130_);
lean_ctor_set(v___x_2132_, 2, v___x_2129_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2135_, lean_object* v_type_2136_, lean_object* v_heqPos_2137_, lean_object* v_heqNum_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v___f_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_inc(v_matchDeclName_2135_);
v___f_2144_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2144_, 0, v_matchDeclName_2135_);
v___x_2145_ = lean_unsigned_to_nat(0u);
v___f_2146_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 11, 6);
lean_closure_set(v___f_2146_, 0, v_type_2136_);
lean_closure_set(v___f_2146_, 1, v___f_2144_);
lean_closure_set(v___f_2146_, 2, v_matchDeclName_2135_);
lean_closure_set(v___f_2146_, 3, v___x_2145_);
lean_closure_set(v___f_2146_, 4, v_heqNum_2138_);
lean_closure_set(v___f_2146_, 5, v_heqPos_2137_);
v___x_2147_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2148_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2149_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2147_, v___x_2148_, v___f_2146_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2150_, lean_object* v_type_2151_, lean_object* v_heqPos_2152_, lean_object* v_heqNum_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2150_, v_type_2151_, v_heqPos_2152_, v_heqNum_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2160_, lean_object* v_inst_2161_, lean_object* v_R_2162_, lean_object* v_a_2163_, lean_object* v_b_2164_, lean_object* v_c_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2160_, v_a_2163_, v_b_2164_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2172_, lean_object* v_inst_2173_, lean_object* v_R_2174_, lean_object* v_a_2175_, lean_object* v_b_2176_, lean_object* v_c_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2172_, v_inst_2173_, v_R_2174_, v_a_2175_, v_b_2176_, v_c_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v_upperBound_2172_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2184_, lean_object* v_b_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
lean_inc(v___y_2187_);
lean_inc_ref(v___y_2186_);
v___x_2191_ = lean_apply_6(v_k_2184_, v_b_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, lean_box(0));
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2192_, lean_object* v_b_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2192_, v_b_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2200_, uint8_t v_bi_2201_, lean_object* v_type_2202_, lean_object* v_k_2203_, uint8_t v_kind_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___f_2210_; lean_object* v___x_2211_; 
v___f_2210_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2210_, 0, v_k_2203_);
v___x_2211_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2200_, v_bi_2201_, v_type_2202_, v___f_2210_, v_kind_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_a_2220_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2211_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2211_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2228_, lean_object* v_bi_2229_, lean_object* v_type_2230_, lean_object* v_k_2231_, lean_object* v_kind_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
uint8_t v_bi_boxed_2238_; uint8_t v_kind_boxed_2239_; lean_object* v_res_2240_; 
v_bi_boxed_2238_ = lean_unbox(v_bi_2229_);
v_kind_boxed_2239_ = lean_unbox(v_kind_2232_);
v_res_2240_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2228_, v_bi_boxed_2238_, v_type_2230_, v_k_2231_, v_kind_boxed_2239_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2241_, lean_object* v_name_2242_, uint8_t v_bi_2243_, lean_object* v_type_2244_, lean_object* v_k_2245_, uint8_t v_kind_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2242_, v_bi_2243_, v_type_2244_, v_k_2245_, v_kind_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2253_, lean_object* v_name_2254_, lean_object* v_bi_2255_, lean_object* v_type_2256_, lean_object* v_k_2257_, lean_object* v_kind_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
uint8_t v_bi_boxed_2264_; uint8_t v_kind_boxed_2265_; lean_object* v_res_2266_; 
v_bi_boxed_2264_ = lean_unbox(v_bi_2255_);
v_kind_boxed_2265_ = lean_unbox(v_kind_2258_);
v_res_2266_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2253_, v_name_2254_, v_bi_boxed_2264_, v_type_2256_, v_k_2257_, v_kind_boxed_2265_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2267_, lean_object* v_altsNew_2268_, lean_object* v_discrs_2269_, lean_object* v_patterns_2270_, lean_object* v_alts_2271_, lean_object* v_k_2272_, lean_object* v_altNew_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2267_, v_altsNew_2268_, v_discrs_2269_, v_patterns_2270_, v_alts_2271_, v_k_2272_, v_altNew_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v_i_2267_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2280_, lean_object* v_patterns_2281_, lean_object* v_alts_2282_, lean_object* v_k_2283_, lean_object* v_i_2284_, lean_object* v_altsNew_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = lean_array_get_size(v_alts_2282_);
v___x_2292_ = lean_nat_dec_lt(v_i_2284_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; 
lean_dec(v_i_2284_);
lean_dec_ref(v_alts_2282_);
lean_dec_ref(v_patterns_2281_);
lean_dec_ref(v_discrs_2280_);
lean_inc(v_a_2289_);
lean_inc_ref(v_a_2288_);
lean_inc(v_a_2287_);
lean_inc_ref(v_a_2286_);
v___x_2293_ = lean_apply_6(v_k_2283_, v_altsNew_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, lean_box(0));
return v___x_2293_;
}
else
{
lean_object* v___f_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_inc_ref(v_alts_2282_);
lean_inc_ref(v_patterns_2281_);
lean_inc_ref(v_discrs_2280_);
lean_inc(v_i_2284_);
v___f_2294_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2294_, 0, v_i_2284_);
lean_closure_set(v___f_2294_, 1, v_altsNew_2285_);
lean_closure_set(v___f_2294_, 2, v_discrs_2280_);
lean_closure_set(v___f_2294_, 3, v_patterns_2281_);
lean_closure_set(v___f_2294_, 4, v_alts_2282_);
lean_closure_set(v___f_2294_, 5, v_k_2283_);
v___x_2295_ = lean_array_fget(v_alts_2282_, v_i_2284_);
lean_dec(v_i_2284_);
lean_dec_ref(v_alts_2282_);
v___x_2296_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2295_, v_a_2286_, v_a_2288_, v_a_2289_);
lean_dec(v___x_2295_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = l_Lean_LocalDecl_type(v_a_2297_);
v___x_2299_ = l_Lean_Expr_replaceFVars(v___x_2298_, v_discrs_2280_, v_patterns_2281_);
lean_dec_ref(v_patterns_2281_);
lean_dec_ref(v_discrs_2280_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = l_Lean_LocalDecl_userName(v_a_2297_);
v___x_2301_ = l_Lean_LocalDecl_binderInfo(v_a_2297_);
lean_dec(v_a_2297_);
v___x_2302_ = 0;
v___x_2303_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2300_, v___x_2301_, v___x_2299_, v___f_2294_, v___x_2302_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
return v___x_2303_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v___f_2294_);
lean_dec_ref(v_patterns_2281_);
lean_dec_ref(v_discrs_2280_);
v_a_2304_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2296_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2296_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2312_, lean_object* v_altsNew_2313_, lean_object* v_discrs_2314_, lean_object* v_patterns_2315_, lean_object* v_alts_2316_, lean_object* v_k_2317_, lean_object* v_altNew_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2324_ = lean_unsigned_to_nat(1u);
v___x_2325_ = lean_nat_add(v_i_2312_, v___x_2324_);
v___x_2326_ = lean_array_push(v_altsNew_2313_, v_altNew_2318_);
v___x_2327_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2314_, v_patterns_2315_, v_alts_2316_, v_k_2317_, v___x_2325_, v___x_2326_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2328_, lean_object* v_patterns_2329_, lean_object* v_alts_2330_, lean_object* v_k_2331_, lean_object* v_i_2332_, lean_object* v_altsNew_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2328_, v_patterns_2329_, v_alts_2330_, v_k_2331_, v_i_2332_, v_altsNew_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2340_, lean_object* v_discrs_2341_, lean_object* v_patterns_2342_, lean_object* v_alts_2343_, lean_object* v_k_2344_, lean_object* v_i_2345_, lean_object* v_altsNew_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2341_, v_patterns_2342_, v_alts_2343_, v_k_2344_, v_i_2345_, v_altsNew_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2353_, lean_object* v_discrs_2354_, lean_object* v_patterns_2355_, lean_object* v_alts_2356_, lean_object* v_k_2357_, lean_object* v_i_2358_, lean_object* v_altsNew_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2353_, v_discrs_2354_, v_patterns_2355_, v_alts_2356_, v_k_2357_, v_i_2358_, v_altsNew_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2368_, lean_object* v_discrs_2369_, lean_object* v_patterns_2370_, lean_object* v_alts_2371_, lean_object* v_k_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___x_2378_; uint8_t v___x_2379_; 
v___x_2378_ = lean_unsigned_to_nat(0u);
v___x_2379_ = lean_nat_dec_eq(v_numDiscrEqs_2368_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2381_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2369_, v_patterns_2370_, v_alts_2371_, v_k_2372_, v___x_2378_, v___x_2380_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2381_;
}
else
{
lean_object* v___x_2382_; 
lean_dec_ref(v_patterns_2370_);
lean_dec_ref(v_discrs_2369_);
lean_inc(v_a_2376_);
lean_inc_ref(v_a_2375_);
lean_inc(v_a_2374_);
lean_inc_ref(v_a_2373_);
v___x_2382_ = lean_apply_6(v_k_2372_, v_alts_2371_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, lean_box(0));
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2383_, lean_object* v_discrs_2384_, lean_object* v_patterns_2385_, lean_object* v_alts_2386_, lean_object* v_k_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2383_, v_discrs_2384_, v_patterns_2385_, v_alts_2386_, v_k_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_numDiscrEqs_2383_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2394_, lean_object* v_numDiscrEqs_2395_, lean_object* v_discrs_2396_, lean_object* v_patterns_2397_, lean_object* v_alts_2398_, lean_object* v_k_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2395_, v_discrs_2396_, v_patterns_2397_, v_alts_2398_, v_k_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2406_, lean_object* v_numDiscrEqs_2407_, lean_object* v_discrs_2408_, lean_object* v_patterns_2409_, lean_object* v_alts_2410_, lean_object* v_k_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2406_, v_numDiscrEqs_2407_, v_discrs_2408_, v_patterns_2409_, v_alts_2410_, v_k_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_numDiscrEqs_2407_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(lean_object* v_declName_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; lean_object* v_env_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2421_ = lean_st_ref_get(v___y_2419_);
v_env_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc_ref(v_env_2422_);
lean_dec(v___x_2421_);
v___x_2423_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2422_, v_declName_2418_);
v___x_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg___boxed(lean_object* v_declName_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2425_, v___y_2426_);
lean_dec(v___y_2426_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_declName_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2429_, v___y_2433_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___boxed(lean_object* v_declName_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v_declName_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___f_2450_; lean_object* v___x_14366__overap_2451_; lean_object* v___x_2452_; 
v___f_2450_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14366__overap_2451_ = lean_panic_fn_borrowed(v___f_2450_, v_msg_2444_);
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
v___x_2452_ = lean_apply_5(v___x_14366__overap_2451_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, lean_box(0));
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2460_, lean_object* v_b_2461_, lean_object* v_c_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; 
lean_inc(v___y_2466_);
lean_inc_ref(v___y_2465_);
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
v___x_2468_ = lean_apply_7(v_k_2460_, v_b_2461_, v_c_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, lean_box(0));
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2469_, lean_object* v_b_2470_, lean_object* v_c_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2469_, v_b_2470_, v_c_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2478_, lean_object* v_k_2479_, uint8_t v_cleanupAnnotations_2480_, uint8_t v_whnfType_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v___f_2487_; lean_object* v___x_2488_; 
v___f_2487_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2487_, 0, v_k_2479_);
v___x_2488_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2478_, v___f_2487_, v_cleanupAnnotations_2480_, v_whnfType_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
v_a_2497_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2488_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2488_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2505_, lean_object* v_k_2506_, lean_object* v_cleanupAnnotations_2507_, lean_object* v_whnfType_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2514_; uint8_t v_whnfType_boxed_2515_; lean_object* v_res_2516_; 
v_cleanupAnnotations_boxed_2514_ = lean_unbox(v_cleanupAnnotations_2507_);
v_whnfType_boxed_2515_ = lean_unbox(v_whnfType_2508_);
v_res_2516_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2505_, v_k_2506_, v_cleanupAnnotations_boxed_2514_, v_whnfType_boxed_2515_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2517_, lean_object* v_type_2518_, lean_object* v_k_2519_, uint8_t v_cleanupAnnotations_2520_, uint8_t v_whnfType_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___x_2527_; 
v___x_2527_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2518_, v_k_2519_, v_cleanupAnnotations_2520_, v_whnfType_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2528_, lean_object* v_type_2529_, lean_object* v_k_2530_, lean_object* v_cleanupAnnotations_2531_, lean_object* v_whnfType_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2538_; uint8_t v_whnfType_boxed_2539_; lean_object* v_res_2540_; 
v_cleanupAnnotations_boxed_2538_ = lean_unbox(v_cleanupAnnotations_2531_);
v_whnfType_boxed_2539_ = lean_unbox(v_whnfType_2532_);
v_res_2540_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2528_, v_type_2529_, v_k_2530_, v_cleanupAnnotations_boxed_2538_, v_whnfType_boxed_2539_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2541_, lean_object* v_splitterName_2542_, lean_object* v_matcherInput_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_matchType_2549_; lean_object* v_discrInfos_2550_; lean_object* v_lhss_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2571_; 
v_matchType_2549_ = lean_ctor_get(v_matcherInput_2543_, 1);
v_discrInfos_2550_ = lean_ctor_get(v_matcherInput_2543_, 2);
v_lhss_2551_ = lean_ctor_get(v_matcherInput_2543_, 3);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_matcherInput_2543_);
if (v_isSharedCheck_2571_ == 0)
{
lean_object* v_unused_2572_; lean_object* v_unused_2573_; 
v_unused_2572_ = lean_ctor_get(v_matcherInput_2543_, 4);
lean_dec(v_unused_2572_);
v_unused_2573_ = lean_ctor_get(v_matcherInput_2543_, 0);
lean_dec(v_unused_2573_);
v___x_2553_ = v_matcherInput_2543_;
v_isShared_2554_ = v_isSharedCheck_2571_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_lhss_2551_);
lean_inc(v_discrInfos_2550_);
lean_inc(v_matchType_2549_);
lean_dec(v_matcherInput_2543_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2571_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_overlaps_2541_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v___x_2555_);
lean_ctor_set(v___x_2553_, 0, v_splitterName_2542_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_splitterName_2542_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_matchType_2549_);
lean_ctor_set(v_reuseFailAlloc_2570_, 2, v_discrInfos_2550_);
lean_ctor_set(v_reuseFailAlloc_2570_, 3, v_lhss_2551_);
lean_ctor_set(v_reuseFailAlloc_2570_, 4, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Meta_Match_mkMatcher(v___x_2557_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v_addMatcher_2560_; lean_object* v___x_2561_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v_addMatcher_2560_ = lean_ctor_get(v_a_2559_, 3);
lean_inc_ref(v_addMatcher_2560_);
lean_dec(v_a_2559_);
lean_inc(v___y_2547_);
lean_inc_ref(v___y_2546_);
lean_inc(v___y_2545_);
lean_inc_ref(v___y_2544_);
v___x_2561_ = lean_apply_5(v_addMatcher_2560_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, lean_box(0));
return v___x_2561_;
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
v_a_2562_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2558_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2558_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2574_, lean_object* v_splitterName_2575_, lean_object* v_matcherInput_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2574_, v_splitterName_2575_, v_matcherInput_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
return v_res_2582_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2583_, lean_object* v_ys_2584_, lean_object* v_x_2585_){
_start:
{
lean_object* v_zero_2586_; uint8_t v_isZero_2587_; 
v_zero_2586_ = lean_unsigned_to_nat(0u);
v_isZero_2587_ = lean_nat_dec_eq(v_x_2585_, v_zero_2586_);
if (v_isZero_2587_ == 1)
{
lean_dec(v_x_2585_);
return v_isZero_2587_;
}
else
{
lean_object* v_one_2588_; lean_object* v_n_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v_one_2588_ = lean_unsigned_to_nat(1u);
v_n_2589_ = lean_nat_sub(v_x_2585_, v_one_2588_);
lean_dec(v_x_2585_);
v___x_2590_ = lean_array_fget_borrowed(v_xs_2583_, v_n_2589_);
v___x_2591_ = lean_array_fget_borrowed(v_ys_2584_, v_n_2589_);
v___x_2592_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2590_, v___x_2591_);
if (v___x_2592_ == 0)
{
lean_dec(v_n_2589_);
return v___x_2592_;
}
else
{
v_x_2585_ = v_n_2589_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2594_, lean_object* v_ys_2595_, lean_object* v_x_2596_){
_start:
{
uint8_t v_res_2597_; lean_object* v_r_2598_; 
v_res_2597_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2594_, v_ys_2595_, v_x_2596_);
lean_dec_ref(v_ys_2595_);
lean_dec_ref(v_xs_2594_);
v_r_2598_ = lean_box(v_res_2597_);
return v_r_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2599_, lean_object* v_b_2600_){
_start:
{
lean_object* v_array_2601_; lean_object* v_start_2602_; lean_object* v_stop_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2616_; 
v_array_2601_ = lean_ctor_get(v_a_2599_, 0);
v_start_2602_ = lean_ctor_get(v_a_2599_, 1);
v_stop_2603_ = lean_ctor_get(v_a_2599_, 2);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_a_2599_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2605_ = v_a_2599_;
v_isShared_2606_ = v_isSharedCheck_2616_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_stop_2603_);
lean_inc(v_start_2602_);
lean_inc(v_array_2601_);
lean_dec(v_a_2599_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2616_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
uint8_t v___x_2607_; 
v___x_2607_ = lean_nat_dec_lt(v_start_2602_, v_stop_2603_);
if (v___x_2607_ == 0)
{
lean_del_object(v___x_2605_);
lean_dec(v_stop_2603_);
lean_dec(v_start_2602_);
lean_dec_ref(v_array_2601_);
return v_b_2600_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2608_ = lean_unsigned_to_nat(1u);
v___x_2609_ = lean_nat_add(v_start_2602_, v___x_2608_);
lean_inc_ref(v_array_2601_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 1, v___x_2609_);
v___x_2611_ = v___x_2605_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_array_2601_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_stop_2603_);
v___x_2611_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = lean_array_fget(v_array_2601_, v_start_2602_);
lean_dec(v_start_2602_);
lean_dec_ref(v_array_2601_);
v___x_2613_ = lean_array_push(v_b_2600_, v___x_2612_);
v_a_2599_ = v___x_2611_;
v_b_2600_ = v___x_2613_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2617_, size_t v_sz_2618_, size_t v_i_2619_, lean_object* v_b_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
uint8_t v___x_2626_; 
v___x_2626_ = lean_usize_dec_lt(v_i_2619_, v_sz_2618_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v_b_2620_);
return v___x_2627_;
}
else
{
lean_object* v_snd_2628_; lean_object* v_fst_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2681_; 
v_snd_2628_ = lean_ctor_get(v_b_2620_, 1);
v_fst_2629_ = lean_ctor_get(v_b_2620_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_b_2620_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2631_ = v_b_2620_;
v_isShared_2632_ = v_isSharedCheck_2681_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_snd_2628_);
lean_inc(v_fst_2629_);
lean_dec(v_b_2620_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2681_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_array_2633_; lean_object* v_start_2634_; lean_object* v_stop_2635_; uint8_t v___x_2636_; 
v_array_2633_ = lean_ctor_get(v_snd_2628_, 0);
v_start_2634_ = lean_ctor_get(v_snd_2628_, 1);
v_stop_2635_ = lean_ctor_get(v_snd_2628_, 2);
v___x_2636_ = lean_nat_dec_lt(v_start_2634_, v_stop_2635_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2638_; 
if (v_isShared_2632_ == 0)
{
v___x_2638_ = v___x_2631_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_fst_2629_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_snd_2628_);
v___x_2638_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
return v___x_2639_;
}
}
else
{
lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2677_; 
lean_inc(v_stop_2635_);
lean_inc(v_start_2634_);
lean_inc_ref(v_array_2633_);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_snd_2628_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; lean_object* v_unused_2679_; lean_object* v_unused_2680_; 
v_unused_2678_ = lean_ctor_get(v_snd_2628_, 2);
lean_dec(v_unused_2678_);
v_unused_2679_ = lean_ctor_get(v_snd_2628_, 1);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_snd_2628_, 0);
lean_dec(v_unused_2680_);
v___x_2642_ = v_snd_2628_;
v_isShared_2643_ = v_isSharedCheck_2677_;
goto v_resetjp_2641_;
}
else
{
lean_dec(v_snd_2628_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2677_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v_a_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
v_a_2644_ = lean_array_uget_borrowed(v_as_2617_, v_i_2619_);
v___x_2645_ = lean_array_fget(v_array_2633_, v_start_2634_);
v___x_2646_ = lean_unsigned_to_nat(1u);
v___x_2647_ = lean_nat_add(v_start_2634_, v___x_2646_);
lean_dec(v_start_2634_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 1, v___x_2647_);
v___x_2649_ = v___x_2642_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_array_2633_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v_stop_2635_);
v___x_2649_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; 
lean_inc(v_a_2644_);
v___x_2650_ = l_Lean_Meta_mkEqHEq(v_a_2644_, v___x_2645_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2652_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2652_ = l_Lean_mkArrow(v_a_2651_, v_fst_2629_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 1, v___x_2649_);
lean_ctor_set(v___x_2631_, 0, v_a_2653_);
v___x_2655_ = v___x_2631_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2649_);
v___x_2655_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
size_t v___x_2656_; size_t v___x_2657_; 
v___x_2656_ = ((size_t)1ULL);
v___x_2657_ = lean_usize_add(v_i_2619_, v___x_2656_);
v_i_2619_ = v___x_2657_;
v_b_2620_ = v___x_2655_;
goto _start;
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec_ref(v___x_2649_);
lean_del_object(v___x_2631_);
v_a_2660_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2652_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2652_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec_ref(v___x_2649_);
lean_del_object(v___x_2631_);
lean_dec(v_fst_2629_);
v_a_2668_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2650_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2650_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2682_, lean_object* v_sz_2683_, lean_object* v_i_2684_, lean_object* v_b_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
size_t v_sz_boxed_2691_; size_t v_i_boxed_2692_; lean_object* v_res_2693_; 
v_sz_boxed_2691_ = lean_unbox_usize(v_sz_2683_);
lean_dec(v_sz_2683_);
v_i_boxed_2692_ = lean_unbox_usize(v_i_2684_);
lean_dec(v_i_2684_);
v_res_2693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2682_, v_sz_boxed_2691_, v_i_boxed_2692_, v_b_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_as_2682_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2694_, lean_object* v___x_2695_, lean_object* v_as_2696_, size_t v_sz_2697_, size_t v_i_2698_, lean_object* v_b_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_a_2706_; uint8_t v___x_2710_; 
v___x_2710_ = lean_usize_dec_lt(v_i_2698_, v_sz_2697_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; 
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v_b_2699_);
return v___x_2711_;
}
else
{
lean_object* v___x_2712_; lean_object* v_a_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2712_ = l_Lean_instInhabitedExpr;
v_a_2713_ = lean_array_uget_borrowed(v_as_2696_, v_i_2698_);
v___x_2714_ = lean_array_get_borrowed(v___x_2712_, v___x_2694_, v_a_2713_);
lean_inc(v___x_2714_);
v___x_2715_ = l_Lean_Meta_instantiateForall(v___x_2714_, v___x_2695_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2717_ = lean_array_get_size(v___x_2695_);
v___x_2718_ = l_Lean_Meta_Match_simpH_x3f(v_a_2716_, v___x_2717_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2718_, 1);
if (lean_obj_tag(v_a_2719_) == 1)
{
lean_object* v_val_2720_; lean_object* v___x_2721_; 
v_val_2720_ = lean_ctor_get(v_a_2719_, 0);
lean_inc(v_val_2720_);
lean_dec_ref_known(v_a_2719_, 1);
v___x_2721_ = lean_array_push(v_b_2699_, v_val_2720_);
v_a_2706_ = v___x_2721_;
goto v___jp_2705_;
}
else
{
lean_dec(v_a_2719_);
v_a_2706_ = v_b_2699_;
goto v___jp_2705_;
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec_ref(v_b_2699_);
v_a_2722_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2718_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2718_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec_ref(v_b_2699_);
v_a_2730_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2715_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2715_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
v___jp_2705_:
{
size_t v___x_2707_; size_t v___x_2708_; 
v___x_2707_ = ((size_t)1ULL);
v___x_2708_ = lean_usize_add(v_i_2698_, v___x_2707_);
v_i_2698_ = v___x_2708_;
v_b_2699_ = v_a_2706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2738_, lean_object* v___x_2739_, lean_object* v_as_2740_, lean_object* v_sz_2741_, lean_object* v_i_2742_, lean_object* v_b_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
size_t v_sz_boxed_2749_; size_t v_i_boxed_2750_; lean_object* v_res_2751_; 
v_sz_boxed_2749_ = lean_unbox_usize(v_sz_2741_);
lean_dec(v_sz_2741_);
v_i_boxed_2750_ = lean_unbox_usize(v_i_2742_);
lean_dec(v_i_2742_);
v_res_2751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2738_, v___x_2739_, v_as_2740_, v_sz_boxed_2749_, v_i_boxed_2750_, v_b_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v_as_2740_);
lean_dec_ref(v___x_2739_);
lean_dec_ref(v___x_2738_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v___x_2755_, lean_object* v___x_2756_, lean_object* v___x_2757_, lean_object* v___x_2758_, lean_object* v___x_2759_, lean_object* v_rhsArgs_2760_, lean_object* v_a_2761_, lean_object* v_ys_2762_, uint8_t v___x_2763_, uint8_t v___x_2764_, uint8_t v___x_2765_, lean_object* v_matchDeclName_2766_, lean_object* v___x_2767_, lean_object* v___x_2768_, lean_object* v___x_2769_, lean_object* v___x_2770_, lean_object* v___x_2771_, lean_object* v_argMask_2772_, lean_object* v_a_2773_, lean_object* v_alts_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2780_ = lean_array_get_borrowed(v___x_2752_, v_alts_2774_, v_a_2753_);
v___x_2781_ = l_Lean_ConstantInfo_name(v_a_2754_);
v___x_2782_ = l_Lean_mkConst(v___x_2781_, v___x_2755_);
v___x_2783_ = l_Subarray_copy___redArg(v___x_2756_);
v___x_2784_ = lean_mk_empty_array_with_capacity(v___x_2757_);
v___x_2785_ = lean_array_push(v___x_2784_, v___x_2758_);
v___x_2786_ = l_Array_append___redArg(v___x_2783_, v___x_2785_);
lean_dec_ref(v___x_2785_);
lean_inc_ref(v___x_2786_);
v___x_2787_ = l_Array_append___redArg(v___x_2786_, v___x_2759_);
v___x_2788_ = l_Array_append___redArg(v___x_2787_, v_alts_2774_);
v___x_2789_ = l_Lean_mkAppN(v___x_2782_, v___x_2788_);
lean_dec_ref(v___x_2788_);
lean_inc(v___x_2780_);
v___x_2790_ = l_Lean_mkAppN(v___x_2780_, v_rhsArgs_2760_);
v___x_2791_ = l_Lean_Meta_mkEq(v___x_2789_, v___x_2790_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2793_ = l_Lean_mkArrowN(v_a_2761_, v_a_2792_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v___x_2795_ = l_Array_append___redArg(v___x_2786_, v_ys_2762_);
v___x_2796_ = l_Array_append___redArg(v___x_2795_, v_alts_2774_);
v___x_2797_ = l_Lean_Meta_mkForallFVars(v___x_2796_, v_a_2794_, v___x_2763_, v___x_2764_, v___x_2764_, v___x_2765_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec_ref(v___x_2796_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2798_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc_n(v_a_2800_, 2);
lean_dec_ref_known(v___x_2799_, 1);
lean_inc(v___x_2767_);
v___x_2801_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2766_, v_a_2800_, v___x_2767_, v___x_2767_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
lean_inc(v___x_2768_);
v___x_2803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2768_);
lean_ctor_set(v___x_2803_, 1, v___x_2769_);
lean_ctor_set(v___x_2803_, 2, v_a_2800_);
v___x_2804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2768_);
lean_ctor_set(v___x_2804_, 1, v___x_2770_);
v___x_2805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v_a_2802_);
lean_ctor_set(v___x_2805_, 2, v___x_2804_);
v___x_2806_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
v___x_2807_ = l_Lean_addDecl(v___x_2806_, v___x_2763_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2816_; 
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2816_ == 0)
{
lean_object* v_unused_2817_; 
v_unused_2817_ = lean_ctor_get(v___x_2807_, 0);
lean_dec(v_unused_2817_);
v___x_2809_ = v___x_2807_;
v_isShared_2810_ = v_isSharedCheck_2816_;
goto v_resetjp_2808_;
}
else
{
lean_dec(v___x_2807_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2816_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2771_);
lean_ctor_set(v___x_2811_, 1, v_argMask_2772_);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v_a_2773_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2812_);
v___x_2814_ = v___x_2809_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec_ref(v_a_2773_);
lean_dec_ref(v_argMask_2772_);
lean_dec_ref(v___x_2771_);
v_a_2818_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2807_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2807_);
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
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2773_);
lean_dec_ref(v_argMask_2772_);
lean_dec_ref(v___x_2771_);
lean_dec(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
v_a_2826_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2801_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2801_);
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
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec_ref(v_a_2773_);
lean_dec_ref(v_argMask_2772_);
lean_dec_ref(v___x_2771_);
lean_dec(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec(v___x_2767_);
lean_dec(v_matchDeclName_2766_);
v_a_2834_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2799_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2799_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref(v_a_2773_);
lean_dec_ref(v_argMask_2772_);
lean_dec_ref(v___x_2771_);
lean_dec(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec(v___x_2767_);
lean_dec(v_matchDeclName_2766_);
v_a_2842_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2797_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2797_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v___x_2786_);
lean_dec_ref(v_a_2773_);
lean_dec_ref(v_argMask_2772_);
lean_dec_ref(v___x_2771_);
lean_dec(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec(v___x_2767_);
lean_dec(v_matchDeclName_2766_);
v_a_2850_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2793_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2793_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec_ref(v___x_2786_);
lean_dec_ref(v_a_2773_);
lean_dec_ref(v_argMask_2772_);
lean_dec_ref(v___x_2771_);
lean_dec(v___x_2770_);
lean_dec(v___x_2769_);
lean_dec(v___x_2768_);
lean_dec(v___x_2767_);
lean_dec(v_matchDeclName_2766_);
v_a_2858_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2791_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2791_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2866_ = _args[0];
lean_object* v_a_2867_ = _args[1];
lean_object* v_a_2868_ = _args[2];
lean_object* v___x_2869_ = _args[3];
lean_object* v___x_2870_ = _args[4];
lean_object* v___x_2871_ = _args[5];
lean_object* v___x_2872_ = _args[6];
lean_object* v___x_2873_ = _args[7];
lean_object* v_rhsArgs_2874_ = _args[8];
lean_object* v_a_2875_ = _args[9];
lean_object* v_ys_2876_ = _args[10];
lean_object* v___x_2877_ = _args[11];
lean_object* v___x_2878_ = _args[12];
lean_object* v___x_2879_ = _args[13];
lean_object* v_matchDeclName_2880_ = _args[14];
lean_object* v___x_2881_ = _args[15];
lean_object* v___x_2882_ = _args[16];
lean_object* v___x_2883_ = _args[17];
lean_object* v___x_2884_ = _args[18];
lean_object* v___x_2885_ = _args[19];
lean_object* v_argMask_2886_ = _args[20];
lean_object* v_a_2887_ = _args[21];
lean_object* v_alts_2888_ = _args[22];
lean_object* v___y_2889_ = _args[23];
lean_object* v___y_2890_ = _args[24];
lean_object* v___y_2891_ = _args[25];
lean_object* v___y_2892_ = _args[26];
lean_object* v___y_2893_ = _args[27];
_start:
{
uint8_t v___x_18504__boxed_2894_; uint8_t v___x_18505__boxed_2895_; uint8_t v___x_18506__boxed_2896_; lean_object* v_res_2897_; 
v___x_18504__boxed_2894_ = lean_unbox(v___x_2877_);
v___x_18505__boxed_2895_ = lean_unbox(v___x_2878_);
v___x_18506__boxed_2896_ = lean_unbox(v___x_2879_);
v_res_2897_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2866_, v_a_2867_, v_a_2868_, v___x_2869_, v___x_2870_, v___x_2871_, v___x_2872_, v___x_2873_, v_rhsArgs_2874_, v_a_2875_, v_ys_2876_, v___x_18504__boxed_2894_, v___x_18505__boxed_2895_, v___x_18506__boxed_2896_, v_matchDeclName_2880_, v___x_2881_, v___x_2882_, v___x_2883_, v___x_2884_, v___x_2885_, v_argMask_2886_, v_a_2887_, v_alts_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec_ref(v_alts_2888_);
lean_dec_ref(v_ys_2876_);
lean_dec_ref(v_a_2875_);
lean_dec_ref(v_rhsArgs_2874_);
lean_dec_ref(v___x_2873_);
lean_dec(v___x_2871_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
lean_dec_ref(v___x_2866_);
return v_res_2897_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2898_; lean_object* v_dummy_2899_; 
v___x_2898_ = lean_box(0);
v_dummy_2899_ = l_Lean_Expr_sort___override(v___x_2898_);
return v_dummy_2899_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_box(0);
v___x_2904_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_2905_ = l_Lean_mkConst(v___x_2904_, v___x_2903_);
return v___x_2905_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_2908_ = l_Lean_stringToMessageData(v___x_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_2909_, lean_object* v_overlaps_2910_, lean_object* v_a_2911_, lean_object* v_fst_2912_, lean_object* v___x_2913_, lean_object* v___x_2914_, lean_object* v___x_2915_, uint8_t v___x_2916_, lean_object* v___x_2917_, lean_object* v_a_2918_, lean_object* v___x_2919_, lean_object* v___x_2920_, lean_object* v___x_2921_, lean_object* v_matchDeclName_2922_, lean_object* v___x_2923_, lean_object* v___x_2924_, lean_object* v___x_2925_, lean_object* v___x_2926_, lean_object* v___x_2927_, lean_object* v_ys_2928_, lean_object* v___eqs_2929_, lean_object* v_rhsArgs_2930_, lean_object* v_argMask_2931_, lean_object* v_altResultType_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_dummy_2938_; lean_object* v_nargs_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; size_t v_sz_2944_; size_t v___x_2945_; lean_object* v___x_2946_; 
v_dummy_2938_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_2939_ = l_Lean_Expr_getAppNumArgs(v_altResultType_2932_);
lean_inc(v_nargs_2939_);
v___x_2940_ = lean_mk_array(v_nargs_2939_, v_dummy_2938_);
v___x_2941_ = lean_nat_sub(v_nargs_2939_, v___x_2909_);
lean_dec(v_nargs_2939_);
v___x_2942_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_2932_, v___x_2940_, v___x_2941_);
v___x_2943_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_2910_, v_a_2911_);
v_sz_2944_ = lean_array_size(v___x_2943_);
v___x_2945_ = ((size_t)0ULL);
lean_inc_ref(v___x_2913_);
v___x_2946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_2912_, v___x_2942_, v___x_2943_, v_sz_2944_, v___x_2945_, v___x_2913_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec_ref(v___x_2943_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; uint8_t v___y_2953_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v_toCold_3006_; lean_object* v_options_3007_; uint8_t v_hasTrace_3008_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v_toCold_3006_ = lean_ctor_get(v___y_2935_, 0);
v_options_3007_ = lean_ctor_get(v_toCold_3006_, 2);
v_hasTrace_3008_ = lean_ctor_get_uint8(v_options_3007_, sizeof(void*)*1);
if (v_hasTrace_3008_ == 0)
{
v___y_2997_ = v___y_2933_;
v___y_2998_ = v___y_2934_;
v___y_2999_ = v___y_2935_;
v___y_3000_ = v___y_2936_;
goto v___jp_2996_;
}
else
{
lean_object* v_inheritedTraceOptions_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v_inheritedTraceOptions_3009_ = lean_ctor_get(v_toCold_3006_, 11);
v___x_3010_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
v___x_3011_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17);
v___x_3012_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3009_, v_options_3007_, v___x_3011_);
if (v___x_3012_ == 0)
{
v___y_2997_ = v___y_2933_;
v___y_2998_ = v___y_2934_;
v___y_2999_ = v___y_2935_;
v___y_3000_ = v___y_2936_;
goto v___jp_2996_;
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3013_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_2947_);
v___x_3014_ = lean_array_to_list(v_a_2947_);
v___x_3015_ = lean_box(0);
v___x_3016_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3014_, v___x_3015_);
v___x_3017_ = l_Lean_MessageData_ofList(v___x_3016_);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3013_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3010_, v___x_3018_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_dec_ref_known(v___x_3019_, 1);
v___y_2997_ = v___y_2933_;
v___y_2998_ = v___y_2934_;
v___y_2999_ = v___y_2935_;
v___y_3000_ = v___y_2936_;
goto v___jp_2996_;
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v_a_2947_);
lean_dec_ref(v___x_2942_);
lean_dec_ref(v_argMask_2931_);
lean_dec_ref(v_rhsArgs_2930_);
lean_dec_ref(v_ys_2928_);
lean_dec_ref(v___x_2926_);
lean_dec(v___x_2925_);
lean_dec(v___x_2924_);
lean_dec(v___x_2923_);
lean_dec(v_matchDeclName_2922_);
lean_dec_ref(v___x_2921_);
lean_dec_ref(v___x_2920_);
lean_dec(v___x_2919_);
lean_dec_ref(v_a_2918_);
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2915_);
lean_dec(v___x_2914_);
lean_dec_ref(v___x_2913_);
lean_dec(v_a_2911_);
lean_dec(v___x_2909_);
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
v___jp_2948_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; size_t v_sz_2964_; lean_object* v___x_2965_; 
v___x_2954_ = lean_array_get_size(v_ys_2928_);
v___x_2955_ = lean_array_get_size(v_a_2947_);
v___x_2956_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2956_, 0, v___x_2954_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
lean_ctor_set_uint8(v___x_2956_, sizeof(void*)*2, v___y_2953_);
v___x_2957_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2942_);
v___x_2958_ = l_Array_reverse___redArg(v___x_2942_);
v___x_2959_ = lean_array_get_size(v___x_2958_);
lean_inc(v___x_2914_);
v___x_2960_ = l_Array_toSubarray___redArg(v___x_2958_, v___x_2914_, v___x_2959_);
lean_inc_ref(v___x_2915_);
v___x_2961_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2915_, v___x_2913_);
v___x_2962_ = l_Array_reverse___redArg(v___x_2961_);
v___x_2963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2957_);
lean_ctor_set(v___x_2963_, 1, v___x_2960_);
v_sz_2964_ = lean_array_size(v___x_2962_);
v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_2962_, v_sz_2964_, v___x_2945_, v___x_2963_, v___y_2949_, v___y_2952_, v___y_2950_, v___y_2951_);
lean_dec_ref(v___x_2962_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v_fst_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; uint8_t v___x_2971_; lean_object* v___x_2972_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v_fst_2967_ = lean_ctor_get(v_a_2966_, 0);
lean_inc(v_fst_2967_);
lean_dec(v_a_2966_);
v___x_2968_ = l_Subarray_copy___redArg(v___x_2915_);
lean_inc_ref(v___x_2968_);
v___x_2969_ = l_Array_append___redArg(v___x_2968_, v_ys_2928_);
v___x_2970_ = 0;
v___x_2971_ = 1;
v___x_2972_ = l_Lean_Meta_mkForallFVars(v___x_2969_, v_fst_2967_, v___x_2970_, v___x_2916_, v___x_2916_, v___x_2971_, v___y_2949_, v___y_2952_, v___y_2950_, v___y_2951_);
lean_dec_ref(v___x_2969_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___f_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v___x_2974_ = lean_box(v___x_2970_);
v___x_2975_ = lean_box(v___x_2916_);
v___x_2976_ = lean_box(v___x_2971_);
lean_inc_ref(v___x_2942_);
v___f_2977_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_2977_, 0, v___x_2917_);
lean_closure_set(v___f_2977_, 1, v_a_2911_);
lean_closure_set(v___f_2977_, 2, v_a_2918_);
lean_closure_set(v___f_2977_, 3, v___x_2919_);
lean_closure_set(v___f_2977_, 4, v___x_2920_);
lean_closure_set(v___f_2977_, 5, v___x_2909_);
lean_closure_set(v___f_2977_, 6, v___x_2921_);
lean_closure_set(v___f_2977_, 7, v___x_2942_);
lean_closure_set(v___f_2977_, 8, v_rhsArgs_2930_);
lean_closure_set(v___f_2977_, 9, v_a_2947_);
lean_closure_set(v___f_2977_, 10, v_ys_2928_);
lean_closure_set(v___f_2977_, 11, v___x_2974_);
lean_closure_set(v___f_2977_, 12, v___x_2975_);
lean_closure_set(v___f_2977_, 13, v___x_2976_);
lean_closure_set(v___f_2977_, 14, v_matchDeclName_2922_);
lean_closure_set(v___f_2977_, 15, v___x_2914_);
lean_closure_set(v___f_2977_, 16, v___x_2923_);
lean_closure_set(v___f_2977_, 17, v___x_2924_);
lean_closure_set(v___f_2977_, 18, v___x_2925_);
lean_closure_set(v___f_2977_, 19, v___x_2956_);
lean_closure_set(v___f_2977_, 20, v_argMask_2931_);
lean_closure_set(v___f_2977_, 21, v_a_2973_);
v___x_2978_ = l_Subarray_copy___redArg(v___x_2926_);
v___x_2979_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2927_, v___x_2968_, v___x_2942_, v___x_2978_, v___f_2977_, v___y_2949_, v___y_2952_, v___y_2950_, v___y_2951_);
return v___x_2979_;
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec_ref(v___x_2968_);
lean_dec_ref_known(v___x_2956_, 2);
lean_dec(v_a_2947_);
lean_dec_ref(v___x_2942_);
lean_dec_ref(v_argMask_2931_);
lean_dec_ref(v_rhsArgs_2930_);
lean_dec_ref(v_ys_2928_);
lean_dec_ref(v___x_2926_);
lean_dec(v___x_2925_);
lean_dec(v___x_2924_);
lean_dec(v___x_2923_);
lean_dec(v_matchDeclName_2922_);
lean_dec_ref(v___x_2921_);
lean_dec_ref(v___x_2920_);
lean_dec(v___x_2919_);
lean_dec_ref(v_a_2918_);
lean_dec_ref(v___x_2917_);
lean_dec(v___x_2914_);
lean_dec(v_a_2911_);
lean_dec(v___x_2909_);
v_a_2980_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2972_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2972_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref_known(v___x_2956_, 2);
lean_dec(v_a_2947_);
lean_dec_ref(v___x_2942_);
lean_dec_ref(v_argMask_2931_);
lean_dec_ref(v_rhsArgs_2930_);
lean_dec_ref(v_ys_2928_);
lean_dec_ref(v___x_2926_);
lean_dec(v___x_2925_);
lean_dec(v___x_2924_);
lean_dec(v___x_2923_);
lean_dec(v_matchDeclName_2922_);
lean_dec_ref(v___x_2921_);
lean_dec_ref(v___x_2920_);
lean_dec(v___x_2919_);
lean_dec_ref(v_a_2918_);
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2915_);
lean_dec(v___x_2914_);
lean_dec(v_a_2911_);
lean_dec(v___x_2909_);
v_a_2988_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2965_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2965_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
v___jp_2996_:
{
lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3001_ = lean_array_get_size(v_ys_2928_);
v___x_3002_ = lean_nat_dec_eq(v___x_3001_, v___x_2914_);
if (v___x_3002_ == 0)
{
v___y_2949_ = v___y_2997_;
v___y_2950_ = v___y_2999_;
v___y_2951_ = v___y_3000_;
v___y_2952_ = v___y_2998_;
v___y_2953_ = v___x_3002_;
goto v___jp_2948_;
}
else
{
lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3003_ = lean_array_get_size(v_a_2947_);
v___x_3004_ = lean_nat_dec_eq(v___x_3003_, v___x_2914_);
if (v___x_3004_ == 0)
{
v___y_2949_ = v___y_2997_;
v___y_2950_ = v___y_2999_;
v___y_2951_ = v___y_3000_;
v___y_2952_ = v___y_2998_;
v___y_2953_ = v___x_3004_;
goto v___jp_2948_;
}
else
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_nat_dec_eq(v___x_2927_, v___x_2914_);
v___y_2949_ = v___y_2997_;
v___y_2950_ = v___y_2999_;
v___y_2951_ = v___y_3000_;
v___y_2952_ = v___y_2998_;
v___y_2953_ = v___x_3005_;
goto v___jp_2948_;
}
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec_ref(v___x_2942_);
lean_dec_ref(v_argMask_2931_);
lean_dec_ref(v_rhsArgs_2930_);
lean_dec_ref(v_ys_2928_);
lean_dec_ref(v___x_2926_);
lean_dec(v___x_2925_);
lean_dec(v___x_2924_);
lean_dec(v___x_2923_);
lean_dec(v_matchDeclName_2922_);
lean_dec_ref(v___x_2921_);
lean_dec_ref(v___x_2920_);
lean_dec(v___x_2919_);
lean_dec_ref(v_a_2918_);
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2915_);
lean_dec(v___x_2914_);
lean_dec_ref(v___x_2913_);
lean_dec(v_a_2911_);
lean_dec(v___x_2909_);
v_a_3028_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_2946_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_2946_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3036_ = _args[0];
lean_object* v_overlaps_3037_ = _args[1];
lean_object* v_a_3038_ = _args[2];
lean_object* v_fst_3039_ = _args[3];
lean_object* v___x_3040_ = _args[4];
lean_object* v___x_3041_ = _args[5];
lean_object* v___x_3042_ = _args[6];
lean_object* v___x_3043_ = _args[7];
lean_object* v___x_3044_ = _args[8];
lean_object* v_a_3045_ = _args[9];
lean_object* v___x_3046_ = _args[10];
lean_object* v___x_3047_ = _args[11];
lean_object* v___x_3048_ = _args[12];
lean_object* v_matchDeclName_3049_ = _args[13];
lean_object* v___x_3050_ = _args[14];
lean_object* v___x_3051_ = _args[15];
lean_object* v___x_3052_ = _args[16];
lean_object* v___x_3053_ = _args[17];
lean_object* v___x_3054_ = _args[18];
lean_object* v_ys_3055_ = _args[19];
lean_object* v___eqs_3056_ = _args[20];
lean_object* v_rhsArgs_3057_ = _args[21];
lean_object* v_argMask_3058_ = _args[22];
lean_object* v_altResultType_3059_ = _args[23];
lean_object* v___y_3060_ = _args[24];
lean_object* v___y_3061_ = _args[25];
lean_object* v___y_3062_ = _args[26];
lean_object* v___y_3063_ = _args[27];
lean_object* v___y_3064_ = _args[28];
_start:
{
uint8_t v___x_18772__boxed_3065_; lean_object* v_res_3066_; 
v___x_18772__boxed_3065_ = lean_unbox(v___x_3043_);
v_res_3066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3036_, v_overlaps_3037_, v_a_3038_, v_fst_3039_, v___x_3040_, v___x_3041_, v___x_3042_, v___x_18772__boxed_3065_, v___x_3044_, v_a_3045_, v___x_3046_, v___x_3047_, v___x_3048_, v_matchDeclName_3049_, v___x_3050_, v___x_3051_, v___x_3052_, v___x_3053_, v___x_3054_, v_ys_3055_, v___eqs_3056_, v_rhsArgs_3057_, v_argMask_3058_, v_altResultType_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec_ref(v___eqs_3056_);
lean_dec(v___x_3054_);
lean_dec(v_fst_3039_);
lean_dec_ref(v_overlaps_3037_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3067_, lean_object* v_val_3068_, lean_object* v_baseName_3069_, lean_object* v___x_3070_, lean_object* v_a_3071_, lean_object* v___x_3072_, lean_object* v___x_3073_, lean_object* v___x_3074_, lean_object* v_matchDeclName_3075_, lean_object* v___x_3076_, lean_object* v___x_3077_, lean_object* v___x_3078_, lean_object* v_a_3079_, lean_object* v_b_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
uint8_t v___x_3086_; 
v___x_3086_ = lean_nat_dec_lt(v_a_3079_, v_upperBound_3067_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; 
lean_dec(v_a_3079_);
lean_dec(v___x_3078_);
lean_dec_ref(v___x_3077_);
lean_dec(v___x_3076_);
lean_dec(v_matchDeclName_3075_);
lean_dec_ref(v___x_3074_);
lean_dec_ref(v___x_3073_);
lean_dec(v___x_3072_);
lean_dec_ref(v_a_3071_);
lean_dec_ref(v___x_3070_);
lean_dec(v_baseName_3069_);
lean_dec_ref(v_val_3068_);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v_b_3080_);
return v___x_3087_;
}
else
{
lean_object* v_snd_3088_; lean_object* v_snd_3089_; lean_object* v_snd_3090_; lean_object* v_fst_3091_; lean_object* v_fst_3092_; lean_object* v_fst_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3176_; 
v_snd_3088_ = lean_ctor_get(v_b_3080_, 1);
lean_inc(v_snd_3088_);
v_snd_3089_ = lean_ctor_get(v_snd_3088_, 1);
lean_inc(v_snd_3089_);
v_snd_3090_ = lean_ctor_get(v_snd_3089_, 1);
lean_inc(v_snd_3090_);
v_fst_3091_ = lean_ctor_get(v_b_3080_, 0);
lean_inc(v_fst_3091_);
lean_dec_ref(v_b_3080_);
v_fst_3092_ = lean_ctor_get(v_snd_3088_, 0);
lean_inc(v_fst_3092_);
lean_dec(v_snd_3088_);
v_fst_3093_ = lean_ctor_get(v_snd_3089_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_snd_3089_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; 
v_unused_3177_ = lean_ctor_get(v_snd_3089_, 1);
lean_dec(v_unused_3177_);
v___x_3095_ = v_snd_3089_;
v_isShared_3096_ = v_isSharedCheck_3176_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_fst_3093_);
lean_dec(v_snd_3089_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3176_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v_fst_3097_; lean_object* v_snd_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3175_; 
v_fst_3097_ = lean_ctor_get(v_snd_3090_, 0);
v_snd_3098_ = lean_ctor_get(v_snd_3090_, 1);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_snd_3090_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3100_ = v_snd_3090_;
v_isShared_3101_ = v_isSharedCheck_3175_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_snd_3098_);
lean_inc(v_fst_3097_);
lean_dec(v_snd_3090_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3175_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v_altInfos_3102_; lean_object* v_overlaps_3103_; lean_object* v_start_3104_; lean_object* v_stop_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___f_3117_; lean_object* v___x_3118_; lean_object* v___y_3120_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v_altInfos_3102_ = lean_ctor_get(v_val_3068_, 2);
v_overlaps_3103_ = lean_ctor_get(v_val_3068_, 5);
v_start_3104_ = lean_ctor_get(v___x_3077_, 1);
v_stop_3105_ = lean_ctor_get(v___x_3077_, 2);
v___x_3106_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3107_ = l_Lean_instInhabitedExpr;
v___x_3108_ = lean_unsigned_to_nat(0u);
v___x_3109_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3110_ = lean_box(0);
v___x_3111_ = lean_unsigned_to_nat(1u);
v___x_3112_ = lean_array_get_borrowed(v___x_3106_, v_altInfos_3102_, v_a_3079_);
v___x_3113_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3069_);
v___x_3114_ = l_Lean_Name_str___override(v_baseName_3069_, v___x_3113_);
lean_inc(v_fst_3093_);
v___x_3115_ = lean_name_append_index_after(v___x_3114_, v_fst_3093_);
v___x_3116_ = lean_box(v___x_3086_);
lean_inc(v___x_3078_);
lean_inc_ref(v___x_3077_);
lean_inc(v___x_3076_);
lean_inc(v___x_3115_);
lean_inc(v_matchDeclName_3075_);
lean_inc_ref(v___x_3074_);
lean_inc_ref(v___x_3073_);
lean_inc(v___x_3072_);
lean_inc_ref(v_a_3071_);
lean_inc_ref(v___x_3070_);
lean_inc(v_fst_3092_);
lean_inc(v_a_3079_);
lean_inc_ref(v_overlaps_3103_);
v___f_3117_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3117_, 0, v___x_3111_);
lean_closure_set(v___f_3117_, 1, v_overlaps_3103_);
lean_closure_set(v___f_3117_, 2, v_a_3079_);
lean_closure_set(v___f_3117_, 3, v_fst_3092_);
lean_closure_set(v___f_3117_, 4, v___x_3109_);
lean_closure_set(v___f_3117_, 5, v___x_3108_);
lean_closure_set(v___f_3117_, 6, v___x_3070_);
lean_closure_set(v___f_3117_, 7, v___x_3116_);
lean_closure_set(v___f_3117_, 8, v___x_3107_);
lean_closure_set(v___f_3117_, 9, v_a_3071_);
lean_closure_set(v___f_3117_, 10, v___x_3072_);
lean_closure_set(v___f_3117_, 11, v___x_3073_);
lean_closure_set(v___f_3117_, 12, v___x_3074_);
lean_closure_set(v___f_3117_, 13, v_matchDeclName_3075_);
lean_closure_set(v___f_3117_, 14, v___x_3115_);
lean_closure_set(v___f_3117_, 15, v___x_3076_);
lean_closure_set(v___f_3117_, 16, v___x_3110_);
lean_closure_set(v___f_3117_, 17, v___x_3077_);
lean_closure_set(v___f_3117_, 18, v___x_3078_);
v___x_3118_ = lean_array_push(v_fst_3091_, v___x_3115_);
v___x_3171_ = lean_nat_sub(v_stop_3105_, v_start_3104_);
v___x_3172_ = lean_nat_dec_lt(v_a_3079_, v___x_3171_);
lean_dec(v___x_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; 
v___x_3173_ = l_outOfBounds___redArg(v___x_3107_);
v___y_3120_ = v___x_3173_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3174_; 
v___x_3174_ = l_Subarray_get___redArg(v___x_3077_, v_a_3079_);
v___y_3120_ = v___x_3174_;
goto v___jp_3119_;
}
v___jp_3119_:
{
lean_object* v___x_3121_; 
lean_inc(v___y_3084_);
lean_inc_ref(v___y_3083_);
lean_inc(v___y_3082_);
lean_inc_ref(v___y_3081_);
v___x_3121_ = lean_infer_type(v___y_3120_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3123_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref_known(v___x_3121_, 1);
lean_inc(v___x_3078_);
lean_inc(v___x_3112_);
v___x_3123_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3122_, v___x_3112_, v___x_3078_, v___f_3117_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v_snd_3125_; lean_object* v_fst_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3154_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
v_snd_3125_ = lean_ctor_get(v_a_3124_, 1);
v_fst_3126_ = lean_ctor_get(v_a_3124_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_a_3124_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3128_ = v_a_3124_;
v_isShared_3129_ = v_isSharedCheck_3154_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_snd_3125_);
lean_inc(v_fst_3126_);
lean_dec(v_a_3124_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3154_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v_fst_3130_; lean_object* v_snd_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3153_; 
v_fst_3130_ = lean_ctor_get(v_snd_3125_, 0);
v_snd_3131_ = lean_ctor_get(v_snd_3125_, 1);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_snd_3125_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3133_ = v_snd_3125_;
v_isShared_3134_ = v_isSharedCheck_3153_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_snd_3131_);
lean_inc(v_fst_3130_);
lean_dec(v_snd_3125_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3153_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3135_ = lean_array_push(v_fst_3092_, v_fst_3126_);
v___x_3136_ = lean_array_push(v_fst_3097_, v_fst_3130_);
v___x_3137_ = lean_array_push(v_snd_3098_, v_snd_3131_);
v___x_3138_ = lean_nat_add(v_fst_3093_, v___x_3111_);
lean_dec(v_fst_3093_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 1, v___x_3137_);
lean_ctor_set(v___x_3133_, 0, v___x_3136_);
v___x_3140_ = v___x_3133_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v___x_3137_);
v___x_3140_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3142_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 1, v___x_3140_);
lean_ctor_set(v___x_3128_, 0, v___x_3138_);
v___x_3142_ = v___x_3128_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3144_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 1, v___x_3142_);
lean_ctor_set(v___x_3100_, 0, v___x_3135_);
v___x_3144_ = v___x_3100_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3146_; 
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 1, v___x_3144_);
lean_ctor_set(v___x_3095_, 0, v___x_3118_);
v___x_3146_ = v___x_3095_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_nat_add(v_a_3079_, v___x_3111_);
lean_dec(v_a_3079_);
v_a_3079_ = v___x_3147_;
v_b_3080_ = v___x_3146_;
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
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref(v___x_3118_);
lean_del_object(v___x_3100_);
lean_dec(v_snd_3098_);
lean_dec(v_fst_3097_);
lean_del_object(v___x_3095_);
lean_dec(v_fst_3093_);
lean_dec(v_fst_3092_);
lean_dec(v_a_3079_);
lean_dec(v___x_3078_);
lean_dec_ref(v___x_3077_);
lean_dec(v___x_3076_);
lean_dec(v_matchDeclName_3075_);
lean_dec_ref(v___x_3074_);
lean_dec_ref(v___x_3073_);
lean_dec(v___x_3072_);
lean_dec_ref(v_a_3071_);
lean_dec_ref(v___x_3070_);
lean_dec(v_baseName_3069_);
lean_dec_ref(v_val_3068_);
v_a_3155_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3123_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3123_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref(v___x_3118_);
lean_dec_ref(v___f_3117_);
lean_del_object(v___x_3100_);
lean_dec(v_snd_3098_);
lean_dec(v_fst_3097_);
lean_del_object(v___x_3095_);
lean_dec(v_fst_3093_);
lean_dec(v_fst_3092_);
lean_dec(v_a_3079_);
lean_dec(v___x_3078_);
lean_dec_ref(v___x_3077_);
lean_dec(v___x_3076_);
lean_dec(v_matchDeclName_3075_);
lean_dec_ref(v___x_3074_);
lean_dec_ref(v___x_3073_);
lean_dec(v___x_3072_);
lean_dec_ref(v_a_3071_);
lean_dec_ref(v___x_3070_);
lean_dec(v_baseName_3069_);
lean_dec_ref(v_val_3068_);
v_a_3163_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3121_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3121_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
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
lean_object* v_upperBound_3178_ = _args[0];
lean_object* v_val_3179_ = _args[1];
lean_object* v_baseName_3180_ = _args[2];
lean_object* v___x_3181_ = _args[3];
lean_object* v_a_3182_ = _args[4];
lean_object* v___x_3183_ = _args[5];
lean_object* v___x_3184_ = _args[6];
lean_object* v___x_3185_ = _args[7];
lean_object* v_matchDeclName_3186_ = _args[8];
lean_object* v___x_3187_ = _args[9];
lean_object* v___x_3188_ = _args[10];
lean_object* v___x_3189_ = _args[11];
lean_object* v_a_3190_ = _args[12];
lean_object* v_b_3191_ = _args[13];
lean_object* v___y_3192_ = _args[14];
lean_object* v___y_3193_ = _args[15];
lean_object* v___y_3194_ = _args[16];
lean_object* v___y_3195_ = _args[17];
lean_object* v___y_3196_ = _args[18];
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3178_, v_val_3179_, v_baseName_3180_, v___x_3181_, v_a_3182_, v___x_3183_, v___x_3184_, v___x_3185_, v_matchDeclName_3186_, v___x_3187_, v___x_3188_, v___x_3189_, v_a_3190_, v_b_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v_upperBound_3178_);
return v_res_3197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3201_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3202_ = lean_unsigned_to_nat(6u);
v___x_3203_ = lean_unsigned_to_nat(233u);
v___x_3204_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3205_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3206_ = l_mkPanicMessageWithDecl(v___x_3205_, v___x_3204_, v___x_3203_, v___x_3202_, v___x_3201_);
return v___x_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3219_, lean_object* v_matchDeclName_3220_, lean_object* v_numParams_3221_, lean_object* v_val_3222_, lean_object* v___x_3223_, lean_object* v_numDiscrs_3224_, lean_object* v_baseName_3225_, lean_object* v_a_3226_, lean_object* v___x_3227_, lean_object* v___x_3228_, lean_object* v___x_3229_, lean_object* v_uElimPos_x3f_3230_, lean_object* v_discrInfos_3231_, lean_object* v_overlaps_3232_, lean_object* v___f_3233_, lean_object* v___x_3234_, lean_object* v_altInfos_3235_, lean_object* v_xs_3236_, lean_object* v___matchResultType_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; uint8_t v___y_3255_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v_lower_3263_; lean_object* v_upper_3264_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3257_ = lean_box(0);
v___x_3258_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3221_);
lean_inc_ref(v_xs_3236_);
v___x_3259_ = l_Array_toSubarray___redArg(v_xs_3236_, v___x_3258_, v_numParams_3221_);
v___x_3260_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3222_);
v___x_3261_ = lean_array_get(v___x_3223_, v_xs_3236_, v___x_3260_);
lean_dec(v___x_3260_);
v___x_3317_ = lean_array_get_size(v_xs_3236_);
v___x_3318_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3222_);
v___x_3319_ = lean_nat_sub(v___x_3317_, v___x_3318_);
lean_dec(v___x_3318_);
v___x_3320_ = lean_nat_dec_le(v___x_3319_, v___x_3258_);
if (v___x_3320_ == 0)
{
v_lower_3263_ = v___x_3319_;
v_upper_3264_ = v___x_3317_;
goto v___jp_3262_;
}
else
{
lean_dec(v___x_3319_);
v_lower_3263_ = v___x_3258_;
v_upper_3264_ = v___x_3317_;
goto v___jp_3262_;
}
v___jp_3243_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3245_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3244_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
return v___x_3245_;
}
v___jp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3249_, 0, v___y_3248_);
lean_ctor_set(v___x_3249_, 1, v_splitterName_3219_);
lean_ctor_set(v___x_3249_, 2, v___y_3247_);
v___x_3250_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3220_, v___x_3249_, v___y_3241_);
return v___x_3250_;
}
v___jp_3251_:
{
lean_object* v___x_3256_; 
lean_inc(v_matchDeclName_3220_);
v___x_3256_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3220_, v___y_3255_, v___y_3253_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_dec_ref_known(v___x_3256_, 1);
v___y_3247_ = v___y_3252_;
v___y_3248_ = v___y_3254_;
goto v___jp_3246_;
}
else
{
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3252_);
lean_dec(v_matchDeclName_3220_);
lean_dec(v_splitterName_3219_);
return v___x_3256_;
}
}
v___jp_3262_:
{
lean_object* v___x_3265_; lean_object* v_start_3266_; lean_object* v_stop_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
lean_inc_ref(v_xs_3236_);
v___x_3265_ = l_Array_toSubarray___redArg(v_xs_3236_, v_lower_3263_, v_upper_3264_);
v_start_3266_ = lean_ctor_get(v___x_3265_, 1);
v_stop_3267_ = lean_ctor_get(v___x_3265_, 2);
v___x_3268_ = lean_unsigned_to_nat(1u);
v___x_3269_ = lean_nat_add(v_numParams_3221_, v___x_3268_);
v___x_3270_ = lean_nat_add(v___x_3269_, v_numDiscrs_3224_);
v___x_3271_ = lean_nat_sub(v_stop_3267_, v_start_3266_);
v___x_3272_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3273_ = l_Array_toSubarray___redArg(v_xs_3236_, v___x_3269_, v___x_3270_);
lean_inc(v___x_3228_);
lean_inc(v_matchDeclName_3220_);
lean_inc(v___x_3227_);
v___x_3274_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3271_, v_val_3222_, v_baseName_3225_, v___x_3273_, v_a_3226_, v___x_3227_, v___x_3259_, v___x_3261_, v_matchDeclName_3220_, v___x_3228_, v___x_3265_, v___x_3229_, v___x_3258_, v___x_3272_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___x_3271_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v_snd_3276_; lean_object* v_snd_3277_; lean_object* v_snd_3278_; lean_object* v_fst_3279_; lean_object* v_fst_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3307_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v_snd_3276_ = lean_ctor_get(v_a_3275_, 1);
v_snd_3277_ = lean_ctor_get(v_snd_3276_, 1);
v_snd_3278_ = lean_ctor_get(v_snd_3277_, 1);
lean_inc(v_snd_3278_);
v_fst_3279_ = lean_ctor_get(v_a_3275_, 0);
lean_inc(v_fst_3279_);
lean_dec(v_a_3275_);
v_fst_3280_ = lean_ctor_get(v_snd_3278_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_snd_3278_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; 
v_unused_3308_ = lean_ctor_get(v_snd_3278_, 1);
lean_dec(v_unused_3308_);
v___x_3282_ = v_snd_3278_;
v_isShared_3283_ = v_isSharedCheck_3307_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_fst_3280_);
lean_dec(v_snd_3278_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3307_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; uint8_t v___x_3285_; 
lean_inc_ref(v_overlaps_3232_);
lean_inc(v_fst_3280_);
v___x_3284_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3284_, 0, v_numParams_3221_);
lean_ctor_set(v___x_3284_, 1, v_numDiscrs_3224_);
lean_ctor_set(v___x_3284_, 2, v_fst_3280_);
lean_ctor_set(v___x_3284_, 3, v_uElimPos_x3f_3230_);
lean_ctor_set(v___x_3284_, 4, v_discrInfos_3231_);
lean_ctor_set(v___x_3284_, 5, v_overlaps_3232_);
v___x_3285_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3232_);
lean_dec_ref(v_overlaps_3232_);
if (v___x_3285_ == 0)
{
uint8_t v___x_3286_; 
lean_del_object(v___x_3282_);
lean_dec(v_fst_3280_);
lean_dec_ref(v___x_3234_);
lean_dec(v___x_3228_);
lean_dec(v___x_3227_);
v___x_3286_ = 1;
v___y_3252_ = v___x_3284_;
v___y_3253_ = v___f_3233_;
v___y_3254_ = v_fst_3279_;
v___y_3255_ = v___x_3286_;
goto v___jp_3251_;
}
else
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3288_ = lean_find_expr(v___x_3287_, v___x_3234_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
lean_dec_ref(v___f_3233_);
v___x_3289_ = lean_array_get_size(v_altInfos_3235_);
v___x_3290_ = lean_array_get_size(v_fst_3280_);
v___x_3291_ = lean_nat_dec_eq(v___x_3289_, v___x_3290_);
if (v___x_3291_ == 0)
{
lean_dec_ref_known(v___x_3284_, 6);
lean_del_object(v___x_3282_);
lean_dec(v_fst_3280_);
lean_dec(v_fst_3279_);
lean_dec_ref(v___x_3234_);
lean_dec(v___x_3228_);
lean_dec(v___x_3227_);
lean_dec(v_matchDeclName_3220_);
lean_dec(v_splitterName_3219_);
goto v___jp_3243_;
}
else
{
uint8_t v___x_3292_; 
v___x_3292_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3235_, v_fst_3280_, v___x_3289_);
lean_dec(v_fst_3280_);
if (v___x_3292_ == 0)
{
lean_dec_ref_known(v___x_3284_, 6);
lean_del_object(v___x_3282_);
lean_dec(v_fst_3279_);
lean_dec_ref(v___x_3234_);
lean_dec(v___x_3228_);
lean_dec(v___x_3227_);
lean_dec(v_matchDeclName_3220_);
lean_dec(v_splitterName_3219_);
goto v___jp_3243_;
}
else
{
uint8_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; lean_object* v___x_3299_; 
v___x_3293_ = 0;
lean_inc_n(v_splitterName_3219_, 2);
v___x_3294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3294_, 0, v_splitterName_3219_);
lean_ctor_set(v___x_3294_, 1, v___x_3228_);
lean_ctor_set(v___x_3294_, 2, v___x_3234_);
lean_inc(v_matchDeclName_3220_);
v___x_3295_ = l_Lean_mkConst(v_matchDeclName_3220_, v___x_3227_);
v___x_3296_ = lean_box(1);
v___x_3297_ = 1;
if (v_isShared_3283_ == 0)
{
lean_ctor_set_tag(v___x_3282_, 1);
lean_ctor_set(v___x_3282_, 1, v___x_3257_);
lean_ctor_set(v___x_3282_, 0, v_splitterName_3219_);
v___x_3299_ = v___x_3282_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_splitterName_3219_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v___x_3257_);
v___x_3299_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3300_, 0, v___x_3294_);
lean_ctor_set(v___x_3300_, 1, v___x_3295_);
lean_ctor_set(v___x_3300_, 2, v___x_3296_);
lean_ctor_set(v___x_3300_, 3, v___x_3299_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*4, v___x_3297_);
v___x_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_inc_ref(v___x_3301_);
v___x_3302_ = l_Lean_addDecl(v___x_3301_, v___x_3293_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3302_) == 0)
{
uint8_t v___x_3303_; lean_object* v___x_3304_; 
lean_dec_ref_known(v___x_3302_, 1);
v___x_3303_ = 0;
lean_inc(v_splitterName_3219_);
v___x_3304_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3219_, v___x_3303_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v___x_3305_; 
lean_dec_ref_known(v___x_3304_, 1);
v___x_3305_ = l_Lean_compileDecl(v___x_3301_, v___x_3293_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_dec_ref_known(v___x_3305_, 1);
v___y_3247_ = v___x_3284_;
v___y_3248_ = v_fst_3279_;
goto v___jp_3246_;
}
else
{
lean_dec_ref_known(v___x_3284_, 6);
lean_dec(v_fst_3279_);
lean_dec(v_matchDeclName_3220_);
lean_dec(v_splitterName_3219_);
return v___x_3305_;
}
}
else
{
lean_dec_ref_known(v___x_3301_, 1);
lean_dec_ref_known(v___x_3284_, 6);
lean_dec(v_fst_3279_);
lean_dec(v_matchDeclName_3220_);
lean_dec(v_splitterName_3219_);
return v___x_3304_;
}
}
else
{
lean_dec_ref_known(v___x_3301_, 1);
lean_dec_ref_known(v___x_3284_, 6);
lean_dec(v_fst_3279_);
lean_dec(v_matchDeclName_3220_);
lean_dec(v_splitterName_3219_);
return v___x_3302_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3288_, 1);
lean_del_object(v___x_3282_);
lean_dec(v_fst_3280_);
lean_dec_ref(v___x_3234_);
lean_dec(v___x_3228_);
lean_dec(v___x_3227_);
v___y_3252_ = v___x_3284_;
v___y_3253_ = v___f_3233_;
v___y_3254_ = v_fst_3279_;
v___y_3255_ = v___x_3285_;
goto v___jp_3251_;
}
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref(v___x_3234_);
lean_dec_ref(v___f_3233_);
lean_dec_ref(v_overlaps_3232_);
lean_dec_ref(v_discrInfos_3231_);
lean_dec(v_uElimPos_x3f_3230_);
lean_dec(v___x_3228_);
lean_dec(v___x_3227_);
lean_dec(v_numDiscrs_3224_);
lean_dec(v_numParams_3221_);
lean_dec(v_matchDeclName_3220_);
lean_dec(v_splitterName_3219_);
v_a_3309_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3274_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3274_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3321_ = _args[0];
lean_object* v_matchDeclName_3322_ = _args[1];
lean_object* v_numParams_3323_ = _args[2];
lean_object* v_val_3324_ = _args[3];
lean_object* v___x_3325_ = _args[4];
lean_object* v_numDiscrs_3326_ = _args[5];
lean_object* v_baseName_3327_ = _args[6];
lean_object* v_a_3328_ = _args[7];
lean_object* v___x_3329_ = _args[8];
lean_object* v___x_3330_ = _args[9];
lean_object* v___x_3331_ = _args[10];
lean_object* v_uElimPos_x3f_3332_ = _args[11];
lean_object* v_discrInfos_3333_ = _args[12];
lean_object* v_overlaps_3334_ = _args[13];
lean_object* v___f_3335_ = _args[14];
lean_object* v___x_3336_ = _args[15];
lean_object* v_altInfos_3337_ = _args[16];
lean_object* v_xs_3338_ = _args[17];
lean_object* v___matchResultType_3339_ = _args[18];
lean_object* v___y_3340_ = _args[19];
lean_object* v___y_3341_ = _args[20];
lean_object* v___y_3342_ = _args[21];
lean_object* v___y_3343_ = _args[22];
lean_object* v___y_3344_ = _args[23];
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3321_, v_matchDeclName_3322_, v_numParams_3323_, v_val_3324_, v___x_3325_, v_numDiscrs_3326_, v_baseName_3327_, v_a_3328_, v___x_3329_, v___x_3330_, v___x_3331_, v_uElimPos_x3f_3332_, v_discrInfos_3333_, v_overlaps_3334_, v___f_3335_, v___x_3336_, v_altInfos_3337_, v_xs_3338_, v___matchResultType_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec_ref(v___matchResultType_3339_);
lean_dec_ref(v_altInfos_3337_);
lean_dec_ref(v___x_3325_);
return v_res_3345_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
return v___x_3347_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3348_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3349_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
lean_ctor_set(v___x_3351_, 2, v___x_3350_);
lean_ctor_set(v___x_3351_, 3, v___x_3350_);
lean_ctor_set(v___x_3351_, 4, v___x_3349_);
lean_ctor_set(v___x_3351_, 5, v___x_3349_);
lean_ctor_set(v___x_3351_, 6, v___x_3349_);
lean_ctor_set(v___x_3351_, 7, v___x_3349_);
lean_ctor_set(v___x_3351_, 8, v___x_3349_);
lean_ctor_set(v___x_3351_, 9, v___x_3349_);
lean_ctor_set(v___x_3351_, 10, v___x_3349_);
lean_ctor_set(v___x_3351_, 11, v___x_3348_);
return v___x_3351_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3352_ = lean_box(1);
v___x_3353_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3354_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
lean_ctor_set(v___x_3355_, 1, v___x_3353_);
lean_ctor_set(v___x_3355_, 2, v___x_3352_);
return v___x_3355_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3));
v___x_3358_ = l_Lean_stringToMessageData(v___x_3357_);
return v___x_3358_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_3361_ = l_Lean_stringToMessageData(v___x_3360_);
return v___x_3361_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_3364_ = l_Lean_stringToMessageData(v___x_3363_);
return v___x_3364_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_3367_ = l_Lean_stringToMessageData(v___x_3366_);
return v___x_3367_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_3370_ = l_Lean_stringToMessageData(v___x_3369_);
return v___x_3370_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_3373_ = l_Lean_stringToMessageData(v___x_3372_);
return v___x_3373_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_3376_ = l_Lean_stringToMessageData(v___x_3375_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3377_, lean_object* v_declHint_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v_env_3383_; uint8_t v___x_3384_; 
v___x_3381_ = lean_box(0);
v___x_3382_ = lean_st_ref_get(v___y_3379_);
v_env_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc_ref(v_env_3383_);
lean_dec(v___x_3382_);
v___x_3384_ = l_Lean_Name_isAnonymous(v_declHint_3378_);
if (v___x_3384_ == 0)
{
uint8_t v_isExporting_3385_; 
v_isExporting_3385_ = lean_ctor_get_uint8(v_env_3383_, sizeof(void*)*13);
if (v_isExporting_3385_ == 0)
{
lean_object* v___x_3386_; 
lean_dec_ref(v_env_3383_);
lean_dec(v_declHint_3378_);
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v_msg_3377_);
return v___x_3386_;
}
else
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
lean_inc_ref(v_env_3383_);
v___x_3387_ = l_Lean_Environment_setExporting(v_env_3383_, v___x_3384_);
lean_inc(v_declHint_3378_);
lean_inc_ref(v___x_3387_);
v___x_3388_ = l_Lean_Environment_contains(v___x_3387_, v_declHint_3378_, v_isExporting_3385_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; 
lean_dec_ref(v___x_3387_);
lean_dec_ref(v_env_3383_);
lean_dec(v_declHint_3378_);
v___x_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3389_, 0, v_msg_3377_);
return v___x_3389_;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v_c_3395_; lean_object* v___x_3396_; 
v___x_3390_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3391_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3392_ = l_Lean_Options_empty;
v___x_3393_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3387_);
lean_ctor_set(v___x_3393_, 1, v___x_3390_);
lean_ctor_set(v___x_3393_, 2, v___x_3391_);
lean_ctor_set(v___x_3393_, 3, v___x_3392_);
lean_inc(v_declHint_3378_);
v___x_3394_ = l_Lean_MessageData_ofConstName(v_declHint_3378_, v___x_3384_);
v_c_3395_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3395_, 0, v___x_3393_);
lean_ctor_set(v_c_3395_, 1, v___x_3394_);
v___x_3396_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3383_, v_declHint_3378_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v_env_3383_);
lean_dec(v_declHint_3378_);
v___x_3397_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_3398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v_c_3395_);
v___x_3399_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_3400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3398_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = l_Lean_MessageData_note(v___x_3400_);
v___x_3402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3402_, 0, v_msg_3377_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
return v___x_3403_;
}
else
{
lean_object* v_val_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3438_; 
v_val_3404_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3406_ = v___x_3396_;
v_isShared_3407_ = v_isSharedCheck_3438_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_val_3404_);
lean_dec(v___x_3396_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3438_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; lean_object* v_moduleNames_3409_; lean_object* v_mod_3410_; uint8_t v___x_3411_; 
v___x_3408_ = l_Lean_Environment_header(v_env_3383_);
lean_dec_ref(v_env_3383_);
v_moduleNames_3409_ = lean_ctor_get(v___x_3408_, 4);
lean_inc_ref(v_moduleNames_3409_);
lean_dec_ref(v___x_3408_);
v_mod_3410_ = lean_array_get(v___x_3381_, v_moduleNames_3409_, v_val_3404_);
lean_dec(v_val_3404_);
lean_dec_ref(v_moduleNames_3409_);
v___x_3411_ = l_Lean_isPrivateName(v_declHint_3378_);
lean_dec(v_declHint_3378_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3423_; 
v___x_3412_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_3413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v_c_3395_);
v___x_3414_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_3415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = l_Lean_MessageData_ofName(v_mod_3410_);
v___x_3417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___x_3418_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_3419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = l_Lean_MessageData_note(v___x_3419_);
v___x_3421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3421_, 0, v_msg_3377_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set_tag(v___x_3406_, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3421_);
v___x_3423_ = v___x_3406_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3425_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
lean_ctor_set(v___x_3426_, 1, v_c_3395_);
v___x_3427_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_3428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = l_Lean_MessageData_ofName(v_mod_3410_);
v___x_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3430_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = l_Lean_MessageData_note(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v_msg_3377_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set_tag(v___x_3406_, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3434_);
v___x_3436_ = v___x_3406_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3439_; 
lean_dec_ref(v_env_3383_);
lean_dec(v_declHint_3378_);
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v_msg_3377_);
return v___x_3439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3440_, lean_object* v_declHint_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3440_, v_declHint_3441_, v___y_3442_);
lean_dec(v___y_3442_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3445_, lean_object* v_declHint_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3462_; 
v___x_3452_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3445_, v_declHint_3446_, v___y_3450_);
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3462_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3462_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3457_ = l_Lean_unknownIdentifierMessageTag;
v___x_3458_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
lean_ctor_set(v___x_3458_, 1, v_a_3453_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3458_);
v___x_3460_ = v___x_3455_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3463_, lean_object* v_declHint_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3463_, v_declHint_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3471_, lean_object* v_msg_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v_toCold_3478_; lean_object* v_currRecDepth_3479_; lean_object* v_ref_3480_; uint16_t v_optionFlags_3481_; uint8_t v_suppressElabErrors_3482_; uint8_t v_isRecordingDeps_3483_; lean_object* v_ref_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_toCold_3478_ = lean_ctor_get(v___y_3475_, 0);
v_currRecDepth_3479_ = lean_ctor_get(v___y_3475_, 1);
v_ref_3480_ = lean_ctor_get(v___y_3475_, 2);
v_optionFlags_3481_ = lean_ctor_get_uint16(v___y_3475_, sizeof(void*)*3);
v_suppressElabErrors_3482_ = lean_ctor_get_uint8(v___y_3475_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3483_ = lean_ctor_get_uint8(v___y_3475_, sizeof(void*)*3 + 3);
v_ref_3484_ = l_Lean_replaceRef(v_ref_3471_, v_ref_3480_);
lean_inc(v_currRecDepth_3479_);
lean_inc_ref(v_toCold_3478_);
v___x_3485_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3485_, 0, v_toCold_3478_);
lean_ctor_set(v___x_3485_, 1, v_currRecDepth_3479_);
lean_ctor_set(v___x_3485_, 2, v_ref_3484_);
lean_ctor_set_uint16(v___x_3485_, sizeof(void*)*3, v_optionFlags_3481_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*3 + 2, v_suppressElabErrors_3482_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*3 + 3, v_isRecordingDeps_3483_);
v___x_3486_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3472_, v___y_3473_, v___y_3474_, v___x_3485_, v___y_3476_);
lean_dec_ref_known(v___x_3485_, 3);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3487_, lean_object* v_msg_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3487_, v_msg_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v_ref_3487_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3495_, lean_object* v_msg_3496_, lean_object* v_declHint_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v___x_3503_; lean_object* v_a_3504_; lean_object* v___x_3505_; 
v___x_3503_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3496_, v_declHint_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3503_);
v___x_3505_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3495_, v_a_3504_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3506_, lean_object* v_msg_3507_, lean_object* v_declHint_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3506_, v_msg_3507_, v_declHint_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v_ref_3506_);
return v_res_3514_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3517_ = l_Lean_stringToMessageData(v___x_3516_);
return v___x_3517_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3520_ = l_Lean_stringToMessageData(v___x_3519_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3521_, lean_object* v_constName_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3528_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3529_ = 0;
lean_inc(v_constName_3522_);
v___x_3530_ = l_Lean_MessageData_ofConstName(v_constName_3522_, v___x_3529_);
v___x_3531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3528_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3531_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3521_, v___x_3533_, v_constName_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3535_, lean_object* v_constName_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3535_, v_constName_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v_ref_3535_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_ref_3549_; lean_object* v___x_3550_; 
v_ref_3549_ = lean_ctor_get(v___y_3546_, 2);
v___x_3550_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3549_, v_constName_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v___x_3564_; lean_object* v_env_3565_; uint8_t v___x_3566_; lean_object* v___x_3567_; 
v___x_3564_ = lean_st_ref_get(v___y_3562_);
v_env_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc_ref(v_env_3565_);
lean_dec(v___x_3564_);
v___x_3566_ = 0;
lean_inc(v_constName_3558_);
v___x_3567_ = l_Lean_Environment_find_x3f(v_env_3565_, v_constName_3558_, v___x_3566_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
return v___x_3568_;
}
else
{
lean_object* v_val_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_constName_3558_);
v_val_3569_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3567_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_val_3569_);
lean_dec(v___x_3567_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
lean_ctor_set_tag(v___x_3571_, 0);
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_val_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
if (lean_obj_tag(v_a_3584_) == 0)
{
lean_object* v___x_3586_; 
v___x_3586_ = l_List_reverse___redArg(v_a_3585_);
return v___x_3586_;
}
else
{
lean_object* v_head_3587_; lean_object* v_tail_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3597_; 
v_head_3587_ = lean_ctor_get(v_a_3584_, 0);
v_tail_3588_ = lean_ctor_get(v_a_3584_, 1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_a_3584_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3590_ = v_a_3584_;
v_isShared_3591_ = v_isSharedCheck_3597_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_tail_3588_);
lean_inc(v_head_3587_);
lean_dec(v_a_3584_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3597_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3592_ = l_Lean_mkLevelParam(v_head_3587_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 1, v_a_3585_);
lean_ctor_set(v___x_3590_, 0, v___x_3592_);
v___x_3594_ = v___x_3590_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_a_3585_);
v___x_3594_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
v_a_3584_ = v_tail_3588_;
v_a_3585_ = v___x_3594_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3600_ = l_Lean_stringToMessageData(v___x_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3601_, lean_object* v_baseName_3602_, lean_object* v_splitterName_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_){
_start:
{
lean_object* v___x_3609_; uint8_t v_foApprox_3610_; uint8_t v_ctxApprox_3611_; uint8_t v_quasiPatternApprox_3612_; uint8_t v_constApprox_3613_; uint8_t v_isDefEqStuckEx_3614_; uint8_t v_unificationHints_3615_; uint8_t v_proofIrrelevance_3616_; uint8_t v_assignSyntheticOpaque_3617_; uint8_t v_offsetCnstrs_3618_; uint8_t v_transparency_3619_; uint8_t v_univApprox_3620_; uint8_t v_iota_3621_; uint8_t v_beta_3622_; uint8_t v_proj_3623_; uint8_t v_zeta_3624_; uint8_t v_zetaDelta_3625_; uint8_t v_zetaUnused_3626_; uint8_t v_zetaHave_3627_; uint8_t v_canUnfoldPredicateConfig_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3691_; 
v___x_3609_ = l_Lean_Meta_Context_config(v_a_3604_);
v_foApprox_3610_ = lean_ctor_get_uint8(v___x_3609_, 0);
v_ctxApprox_3611_ = lean_ctor_get_uint8(v___x_3609_, 1);
v_quasiPatternApprox_3612_ = lean_ctor_get_uint8(v___x_3609_, 2);
v_constApprox_3613_ = lean_ctor_get_uint8(v___x_3609_, 3);
v_isDefEqStuckEx_3614_ = lean_ctor_get_uint8(v___x_3609_, 4);
v_unificationHints_3615_ = lean_ctor_get_uint8(v___x_3609_, 5);
v_proofIrrelevance_3616_ = lean_ctor_get_uint8(v___x_3609_, 6);
v_assignSyntheticOpaque_3617_ = lean_ctor_get_uint8(v___x_3609_, 7);
v_offsetCnstrs_3618_ = lean_ctor_get_uint8(v___x_3609_, 8);
v_transparency_3619_ = lean_ctor_get_uint8(v___x_3609_, 9);
v_univApprox_3620_ = lean_ctor_get_uint8(v___x_3609_, 11);
v_iota_3621_ = lean_ctor_get_uint8(v___x_3609_, 12);
v_beta_3622_ = lean_ctor_get_uint8(v___x_3609_, 13);
v_proj_3623_ = lean_ctor_get_uint8(v___x_3609_, 14);
v_zeta_3624_ = lean_ctor_get_uint8(v___x_3609_, 15);
v_zetaDelta_3625_ = lean_ctor_get_uint8(v___x_3609_, 16);
v_zetaUnused_3626_ = lean_ctor_get_uint8(v___x_3609_, 17);
v_zetaHave_3627_ = lean_ctor_get_uint8(v___x_3609_, 18);
v_canUnfoldPredicateConfig_3628_ = lean_ctor_get_uint8(v___x_3609_, 19);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3630_ = v___x_3609_;
v_isShared_3631_ = v_isSharedCheck_3691_;
goto v_resetjp_3629_;
}
else
{
lean_dec(v___x_3609_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3691_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
uint8_t v_trackZetaDelta_3632_; lean_object* v_zetaDeltaSet_3633_; lean_object* v_lctx_3634_; lean_object* v_localInstances_3635_; lean_object* v_defEqCtx_x3f_3636_; lean_object* v_synthPendingDepth_3637_; lean_object* v_customCanUnfoldPredicate_x3f_3638_; uint8_t v_univApprox_3639_; uint8_t v_inTypeClassResolution_3640_; uint8_t v_cacheInferType_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3689_; 
v_trackZetaDelta_3632_ = lean_ctor_get_uint8(v_a_3604_, sizeof(void*)*7);
v_zetaDeltaSet_3633_ = lean_ctor_get(v_a_3604_, 1);
v_lctx_3634_ = lean_ctor_get(v_a_3604_, 2);
v_localInstances_3635_ = lean_ctor_get(v_a_3604_, 3);
v_defEqCtx_x3f_3636_ = lean_ctor_get(v_a_3604_, 4);
v_synthPendingDepth_3637_ = lean_ctor_get(v_a_3604_, 5);
v_customCanUnfoldPredicate_x3f_3638_ = lean_ctor_get(v_a_3604_, 6);
v_univApprox_3639_ = lean_ctor_get_uint8(v_a_3604_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3640_ = lean_ctor_get_uint8(v_a_3604_, sizeof(void*)*7 + 2);
v_cacheInferType_3641_ = lean_ctor_get_uint8(v_a_3604_, sizeof(void*)*7 + 3);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_a_3604_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v_a_3604_, 0);
lean_dec(v_unused_3690_);
v___x_3643_ = v_a_3604_;
v_isShared_3644_ = v_isSharedCheck_3689_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3638_);
lean_inc(v_synthPendingDepth_3637_);
lean_inc(v_defEqCtx_x3f_3636_);
lean_inc(v_localInstances_3635_);
lean_inc(v_lctx_3634_);
lean_inc(v_zetaDeltaSet_3633_);
lean_dec(v_a_3604_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3689_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
uint8_t v___x_3645_; lean_object* v___x_3647_; 
v___x_3645_ = 2;
if (v_isShared_3631_ == 0)
{
v___x_3647_ = v___x_3630_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 0, v_foApprox_3610_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 1, v_ctxApprox_3611_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 2, v_quasiPatternApprox_3612_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 3, v_constApprox_3613_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 4, v_isDefEqStuckEx_3614_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 5, v_unificationHints_3615_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 6, v_proofIrrelevance_3616_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 7, v_assignSyntheticOpaque_3617_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 8, v_offsetCnstrs_3618_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 9, v_transparency_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 11, v_univApprox_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 12, v_iota_3621_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 13, v_beta_3622_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 14, v_proj_3623_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 15, v_zeta_3624_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 16, v_zetaDelta_3625_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 17, v_zetaUnused_3626_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 18, v_zetaHave_3627_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, 19, v_canUnfoldPredicateConfig_3628_);
v___x_3647_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
uint64_t v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3652_; 
lean_ctor_set_uint8(v___x_3647_, 10, v___x_3645_);
v___x_3648_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3647_);
v___x_3649_ = l_Lean_instInhabitedExpr;
v___x_3650_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3650_, 0, v___x_3647_);
lean_ctor_set_uint64(v___x_3650_, sizeof(void*)*1, v___x_3648_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 0, v___x_3650_);
v___x_3652_ = v___x_3643_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3650_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_zetaDeltaSet_3633_);
lean_ctor_set(v_reuseFailAlloc_3687_, 2, v_lctx_3634_);
lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_localInstances_3635_);
lean_ctor_set(v_reuseFailAlloc_3687_, 4, v_defEqCtx_x3f_3636_);
lean_ctor_set(v_reuseFailAlloc_3687_, 5, v_synthPendingDepth_3637_);
lean_ctor_set(v_reuseFailAlloc_3687_, 6, v_customCanUnfoldPredicate_x3f_3638_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*7, v_trackZetaDelta_3632_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*7 + 1, v_univApprox_3639_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3640_);
lean_ctor_set_uint8(v_reuseFailAlloc_3687_, sizeof(void*)*7 + 3, v_cacheInferType_3641_);
v___x_3652_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3653_; 
lean_inc(v_matchDeclName_3601_);
v___x_3653_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3601_, v___x_3652_, v_a_3605_, v_a_3606_, v_a_3607_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v_a_3659_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3653_, 1);
v___x_3655_ = l_Lean_ConstantInfo_levelParams(v_a_3654_);
v___x_3656_ = lean_box(0);
lean_inc(v___x_3655_);
v___x_3657_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v___x_3655_, v___x_3656_);
lean_inc(v_matchDeclName_3601_);
v___x_3658_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_3601_, v_a_3607_);
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref(v___x_3658_);
if (lean_obj_tag(v_a_3659_) == 1)
{
lean_object* v_val_3660_; lean_object* v_numParams_3661_; lean_object* v_numDiscrs_3662_; lean_object* v_altInfos_3663_; lean_object* v_uElimPos_x3f_3664_; lean_object* v_discrInfos_3665_; lean_object* v_overlaps_3666_; lean_object* v___f_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___f_3670_; uint8_t v___x_3671_; lean_object* v___x_3672_; 
v_val_3660_ = lean_ctor_get(v_a_3659_, 0);
lean_inc(v_val_3660_);
lean_dec_ref_known(v_a_3659_, 1);
v_numParams_3661_ = lean_ctor_get(v_val_3660_, 0);
lean_inc(v_numParams_3661_);
v_numDiscrs_3662_ = lean_ctor_get(v_val_3660_, 1);
lean_inc(v_numDiscrs_3662_);
v_altInfos_3663_ = lean_ctor_get(v_val_3660_, 2);
lean_inc_ref(v_altInfos_3663_);
v_uElimPos_x3f_3664_ = lean_ctor_get(v_val_3660_, 3);
lean_inc(v_uElimPos_x3f_3664_);
v_discrInfos_3665_ = lean_ctor_get(v_val_3660_, 4);
lean_inc_ref(v_discrInfos_3665_);
v_overlaps_3666_ = lean_ctor_get(v_val_3660_, 5);
lean_inc_ref_n(v_overlaps_3666_, 2);
lean_inc(v_splitterName_3603_);
v___f_3667_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3667_, 0, v_overlaps_3666_);
lean_closure_set(v___f_3667_, 1, v_splitterName_3603_);
v___x_3668_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3665_);
v___x_3669_ = l_Lean_ConstantInfo_type(v_a_3654_);
lean_inc_ref(v___x_3669_);
v___f_3670_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3670_, 0, v_splitterName_3603_);
lean_closure_set(v___f_3670_, 1, v_matchDeclName_3601_);
lean_closure_set(v___f_3670_, 2, v_numParams_3661_);
lean_closure_set(v___f_3670_, 3, v_val_3660_);
lean_closure_set(v___f_3670_, 4, v___x_3649_);
lean_closure_set(v___f_3670_, 5, v_numDiscrs_3662_);
lean_closure_set(v___f_3670_, 6, v_baseName_3602_);
lean_closure_set(v___f_3670_, 7, v_a_3654_);
lean_closure_set(v___f_3670_, 8, v___x_3657_);
lean_closure_set(v___f_3670_, 9, v___x_3655_);
lean_closure_set(v___f_3670_, 10, v___x_3668_);
lean_closure_set(v___f_3670_, 11, v_uElimPos_x3f_3664_);
lean_closure_set(v___f_3670_, 12, v_discrInfos_3665_);
lean_closure_set(v___f_3670_, 13, v_overlaps_3666_);
lean_closure_set(v___f_3670_, 14, v___f_3667_);
lean_closure_set(v___f_3670_, 15, v___x_3669_);
lean_closure_set(v___f_3670_, 16, v_altInfos_3663_);
v___x_3671_ = 0;
v___x_3672_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3669_, v___f_3670_, v___x_3671_, v___x_3671_, v___x_3652_, v_a_3605_, v_a_3606_, v_a_3607_);
lean_dec_ref(v___x_3652_);
return v___x_3672_;
}
else
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
lean_dec(v_a_3659_);
lean_dec(v___x_3657_);
lean_dec(v___x_3655_);
lean_dec(v_a_3654_);
lean_dec(v_splitterName_3603_);
lean_dec(v_baseName_3602_);
v___x_3673_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3674_ = l_Lean_MessageData_ofName(v_matchDeclName_3601_);
v___x_3675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3673_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
v___x_3676_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3675_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___x_3678_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3677_, v___x_3652_, v_a_3605_, v_a_3606_, v_a_3607_);
lean_dec_ref(v___x_3652_);
return v___x_3678_;
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec_ref(v___x_3652_);
lean_dec(v_splitterName_3603_);
lean_dec(v_baseName_3602_);
lean_dec(v_matchDeclName_3601_);
v_a_3679_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3653_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3653_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3692_, lean_object* v_baseName_3693_, lean_object* v_splitterName_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3692_, v_baseName_3693_, v_splitterName_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
lean_dec(v_a_3696_);
return v_res_3700_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3701_, lean_object* v_ys_3702_, lean_object* v_hsz_3703_, lean_object* v_x_3704_, lean_object* v_x_3705_){
_start:
{
uint8_t v___x_3706_; 
v___x_3706_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3701_, v_ys_3702_, v_x_3704_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3707_, lean_object* v_ys_3708_, lean_object* v_hsz_3709_, lean_object* v_x_3710_, lean_object* v_x_3711_){
_start:
{
uint8_t v_res_3712_; lean_object* v_r_3713_; 
v_res_3712_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3707_, v_ys_3708_, v_hsz_3709_, v_x_3710_, v_x_3711_);
lean_dec_ref(v_ys_3708_);
lean_dec_ref(v_xs_3707_);
v_r_3713_ = lean_box(v_res_3712_);
return v_r_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3714_, lean_object* v_R_3715_, lean_object* v_a_3716_, lean_object* v_b_3717_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3716_, v_b_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3719_, lean_object* v_val_3720_, lean_object* v_baseName_3721_, lean_object* v___x_3722_, lean_object* v_a_3723_, lean_object* v___x_3724_, lean_object* v___x_3725_, lean_object* v___x_3726_, lean_object* v_matchDeclName_3727_, lean_object* v___x_3728_, lean_object* v___x_3729_, lean_object* v___x_3730_, lean_object* v_inst_3731_, lean_object* v_R_3732_, lean_object* v_a_3733_, lean_object* v_b_3734_, lean_object* v_c_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3719_, v_val_3720_, v_baseName_3721_, v___x_3722_, v_a_3723_, v___x_3724_, v___x_3725_, v___x_3726_, v_matchDeclName_3727_, v___x_3728_, v___x_3729_, v___x_3730_, v_a_3733_, v_b_3734_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3742_ = _args[0];
lean_object* v_val_3743_ = _args[1];
lean_object* v_baseName_3744_ = _args[2];
lean_object* v___x_3745_ = _args[3];
lean_object* v_a_3746_ = _args[4];
lean_object* v___x_3747_ = _args[5];
lean_object* v___x_3748_ = _args[6];
lean_object* v___x_3749_ = _args[7];
lean_object* v_matchDeclName_3750_ = _args[8];
lean_object* v___x_3751_ = _args[9];
lean_object* v___x_3752_ = _args[10];
lean_object* v___x_3753_ = _args[11];
lean_object* v_inst_3754_ = _args[12];
lean_object* v_R_3755_ = _args[13];
lean_object* v_a_3756_ = _args[14];
lean_object* v_b_3757_ = _args[15];
lean_object* v_c_3758_ = _args[16];
lean_object* v___y_3759_ = _args[17];
lean_object* v___y_3760_ = _args[18];
lean_object* v___y_3761_ = _args[19];
lean_object* v___y_3762_ = _args[20];
lean_object* v___y_3763_ = _args[21];
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3742_, v_val_3743_, v_baseName_3744_, v___x_3745_, v_a_3746_, v___x_3747_, v___x_3748_, v___x_3749_, v_matchDeclName_3750_, v___x_3751_, v___x_3752_, v___x_3753_, v_inst_3754_, v_R_3755_, v_a_3756_, v_b_3757_, v_c_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v_upperBound_3742_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3765_, lean_object* v_constName_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3773_, lean_object* v_constName_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3773_, v_constName_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3781_, lean_object* v_ref_3782_, lean_object* v_constName_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3782_, v_constName_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3790_, lean_object* v_ref_3791_, lean_object* v_constName_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3790_, v_ref_3791_, v_constName_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v_ref_3791_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3799_, lean_object* v_ref_3800_, lean_object* v_msg_3801_, lean_object* v_declHint_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3800_, v_msg_3801_, v_declHint_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3809_, lean_object* v_ref_3810_, lean_object* v_msg_3811_, lean_object* v_declHint_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3809_, v_ref_3810_, v_msg_3811_, v_declHint_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v_ref_3810_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3819_, lean_object* v_declHint_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v___x_3826_; 
v___x_3826_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3819_, v_declHint_3820_, v___y_3824_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3827_, lean_object* v_declHint_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3827_, v_declHint_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3835_, lean_object* v_ref_3836_, lean_object* v_msg_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3836_, v_msg_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3844_, lean_object* v_ref_3845_, lean_object* v_msg_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3844_, v_ref_3845_, v_msg_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v_ref_3845_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3853_, lean_object* v_vals_3854_, lean_object* v_i_3855_, lean_object* v_k_3856_){
_start:
{
lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___x_3857_ = lean_array_get_size(v_keys_3853_);
v___x_3858_ = lean_nat_dec_lt(v_i_3855_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; 
lean_dec(v_i_3855_);
v___x_3859_ = lean_box(0);
return v___x_3859_;
}
else
{
lean_object* v_k_x27_3860_; uint8_t v___x_3861_; 
v_k_x27_3860_ = lean_array_fget_borrowed(v_keys_3853_, v_i_3855_);
v___x_3861_ = lean_name_eq(v_k_3856_, v_k_x27_3860_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = lean_unsigned_to_nat(1u);
v___x_3863_ = lean_nat_add(v_i_3855_, v___x_3862_);
lean_dec(v_i_3855_);
v_i_3855_ = v___x_3863_;
goto _start;
}
else
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = lean_array_fget_borrowed(v_vals_3854_, v_i_3855_);
lean_dec(v_i_3855_);
lean_inc(v___x_3865_);
v___x_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
return v___x_3866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3867_, lean_object* v_vals_3868_, lean_object* v_i_3869_, lean_object* v_k_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3867_, v_vals_3868_, v_i_3869_, v_k_3870_);
lean_dec(v_k_3870_);
lean_dec_ref(v_vals_3868_);
lean_dec_ref(v_keys_3867_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3872_, size_t v_x_3873_, lean_object* v_x_3874_){
_start:
{
if (lean_obj_tag(v_x_3872_) == 0)
{
lean_object* v_es_3875_; lean_object* v___x_3876_; size_t v___x_3877_; size_t v___x_3878_; lean_object* v_j_3879_; lean_object* v___x_3880_; 
v_es_3875_ = lean_ctor_get(v_x_3872_, 0);
v___x_3876_ = lean_box(2);
v___x_3877_ = ((size_t)31ULL);
v___x_3878_ = lean_usize_land(v_x_3873_, v___x_3877_);
v_j_3879_ = lean_usize_to_nat(v___x_3878_);
v___x_3880_ = lean_array_get_borrowed(v___x_3876_, v_es_3875_, v_j_3879_);
lean_dec(v_j_3879_);
switch(lean_obj_tag(v___x_3880_))
{
case 0:
{
lean_object* v_key_3881_; lean_object* v_val_3882_; uint8_t v___x_3883_; 
v_key_3881_ = lean_ctor_get(v___x_3880_, 0);
v_val_3882_ = lean_ctor_get(v___x_3880_, 1);
v___x_3883_ = lean_name_eq(v_x_3874_, v_key_3881_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_box(0);
return v___x_3884_;
}
else
{
lean_object* v___x_3885_; 
lean_inc(v_val_3882_);
v___x_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3885_, 0, v_val_3882_);
return v___x_3885_;
}
}
case 1:
{
lean_object* v_node_3886_; size_t v___x_3887_; size_t v___x_3888_; 
v_node_3886_ = lean_ctor_get(v___x_3880_, 0);
v___x_3887_ = ((size_t)5ULL);
v___x_3888_ = lean_usize_shift_right(v_x_3873_, v___x_3887_);
v_x_3872_ = v_node_3886_;
v_x_3873_ = v___x_3888_;
goto _start;
}
default: 
{
lean_object* v___x_3890_; 
v___x_3890_ = lean_box(0);
return v___x_3890_;
}
}
}
else
{
lean_object* v_ks_3891_; lean_object* v_vs_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_ks_3891_ = lean_ctor_get(v_x_3872_, 0);
v_vs_3892_ = lean_ctor_get(v_x_3872_, 1);
v___x_3893_ = lean_unsigned_to_nat(0u);
v___x_3894_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3891_, v_vs_3892_, v___x_3893_, v_x_3874_);
return v___x_3894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3895_, lean_object* v_x_3896_, lean_object* v_x_3897_){
_start:
{
size_t v_x_709__boxed_3898_; lean_object* v_res_3899_; 
v_x_709__boxed_3898_ = lean_unbox_usize(v_x_3896_);
lean_dec(v_x_3896_);
v_res_3899_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3895_, v_x_709__boxed_3898_, v_x_3897_);
lean_dec(v_x_3897_);
lean_dec_ref(v_x_3895_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3900_, lean_object* v_x_3901_){
_start:
{
uint64_t v___y_3903_; 
if (lean_obj_tag(v_x_3901_) == 0)
{
uint64_t v___x_3906_; 
v___x_3906_ = 1723ULL;
v___y_3903_ = v___x_3906_;
goto v___jp_3902_;
}
else
{
uint64_t v_hash_3907_; 
v_hash_3907_ = lean_ctor_get_uint64(v_x_3901_, sizeof(void*)*2);
v___y_3903_ = v_hash_3907_;
goto v___jp_3902_;
}
v___jp_3902_:
{
size_t v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_uint64_to_usize(v___y_3903_);
v___x_3905_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3900_, v___x_3904_, v_x_3901_);
return v___x_3905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3908_, lean_object* v_x_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3908_, v_x_3909_);
lean_dec(v_x_3909_);
lean_dec_ref(v_x_3908_);
return v_res_3910_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3918_ = l_Lean_stringToMessageData(v___x_3917_);
return v___x_3918_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3921_ = l_Lean_stringToMessageData(v___x_3920_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v_env_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3928_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_3929_ = lean_st_ref_get(v_a_3926_);
v_env_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc_ref(v_env_3930_);
lean_dec(v___x_3929_);
lean_inc_n(v_matchDeclName_3922_, 3);
v___x_3931_ = l_Lean_mkPrivateName(v_env_3930_, v_matchDeclName_3922_);
lean_dec_ref(v_env_3930_);
v___x_3932_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_3931_);
v___x_3933_ = l_Lean_Name_append(v___x_3931_, v___x_3932_);
lean_inc_n(v___x_3933_, 2);
v___x_3934_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_3934_, 0, v_matchDeclName_3922_);
lean_closure_set(v___x_3934_, 1, v___x_3931_);
lean_closure_set(v___x_3934_, 2, v___x_3933_);
v___x_3935_ = l_Lean_Meta_realizeConst(v_matchDeclName_3922_, v___x_3933_, v___x_3934_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3964_; 
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3964_ == 0)
{
lean_object* v_unused_3965_; 
v_unused_3965_ = lean_ctor_get(v___x_3935_, 0);
lean_dec(v_unused_3965_);
v___x_3937_ = v___x_3935_;
v_isShared_3938_ = v_isSharedCheck_3964_;
goto v_resetjp_3936_;
}
else
{
lean_dec(v___x_3935_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3964_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v_env_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; uint8_t v___x_3943_; lean_object* v___x_3944_; lean_object* v_map_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3962_; 
v___x_3939_ = lean_st_ref_get(v_a_3926_);
v_env_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc_ref(v_env_3940_);
lean_dec(v___x_3939_);
v___x_3941_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_3942_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_3943_ = 0;
v___x_3944_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3928_, v___x_3941_, v_env_3940_, v___x_3942_, v___x_3933_, v___x_3943_);
v_map_3945_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3962_ == 0)
{
lean_object* v_unused_3963_; 
v_unused_3963_ = lean_ctor_get(v___x_3944_, 1);
lean_dec(v_unused_3963_);
v___x_3947_ = v___x_3944_;
v_isShared_3948_ = v_isSharedCheck_3962_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_map_3945_);
lean_dec(v___x_3944_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3962_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_3945_, v_matchDeclName_3922_);
lean_dec_ref(v_map_3945_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3953_; 
lean_del_object(v___x_3937_);
v___x_3950_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_3951_ = l_Lean_MessageData_ofName(v_matchDeclName_3922_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set_tag(v___x_3947_, 7);
lean_ctor_set(v___x_3947_, 1, v___x_3951_);
lean_ctor_set(v___x_3947_, 0, v___x_3950_);
v___x_3953_ = v___x_3947_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3957_, 1, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3954_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_3955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
v___x_3956_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3955_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
return v___x_3956_;
}
}
else
{
lean_object* v_val_3958_; lean_object* v___x_3960_; 
lean_del_object(v___x_3947_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_matchDeclName_3922_);
v_val_3958_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_val_3958_);
lean_dec_ref_known(v___x_3949_, 1);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v_val_3958_);
v___x_3960_ = v___x_3937_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_val_3958_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v___x_3933_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_matchDeclName_3922_);
v_a_3966_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3935_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3935_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = lean_get_match_equations_for(v_matchDeclName_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_3981_, lean_object* v_x_3982_, lean_object* v_x_3983_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3982_, v_x_3983_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_3985_, lean_object* v_x_3986_, lean_object* v_x_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_3985_, v_x_3986_, v_x_3987_);
lean_dec(v_x_3987_);
lean_dec_ref(v_x_3986_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_3989_, lean_object* v_x_3990_, size_t v_x_3991_, lean_object* v_x_3992_){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3990_, v_x_3991_, v_x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_, lean_object* v_x_3997_){
_start:
{
size_t v_x_903__boxed_3998_; lean_object* v_res_3999_; 
v_x_903__boxed_3998_ = lean_unbox_usize(v_x_3996_);
lean_dec(v_x_3996_);
v_res_3999_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_3994_, v_x_3995_, v_x_903__boxed_3998_, v_x_3997_);
lean_dec(v_x_3997_);
lean_dec_ref(v_x_3995_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4000_, lean_object* v_keys_4001_, lean_object* v_vals_4002_, lean_object* v_heq_4003_, lean_object* v_i_4004_, lean_object* v_k_4005_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4001_, v_vals_4002_, v_i_4004_, v_k_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4007_, lean_object* v_keys_4008_, lean_object* v_vals_4009_, lean_object* v_heq_4010_, lean_object* v_i_4011_, lean_object* v_k_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4007_, v_keys_4008_, v_vals_4009_, v_heq_4010_, v_i_4011_, v_k_4012_);
lean_dec(v_k_4012_);
lean_dec_ref(v_vals_4009_);
lean_dec_ref(v_keys_4008_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4014_, lean_object* v_k_4015_, uint8_t v_cleanupAnnotations_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v___f_4022_; uint8_t v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___f_4022_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4022_, 0, v_k_4015_);
v___x_4023_ = 0;
v___x_4024_ = lean_box(0);
v___x_4025_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4023_, v___x_4024_, v_type_4014_, v___f_4022_, v_cleanupAnnotations_4016_, v___x_4023_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_4025_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_4025_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
v_a_4034_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_4025_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4025_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4042_, lean_object* v_k_4043_, lean_object* v_cleanupAnnotations_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4050_; lean_object* v_res_4051_; 
v_cleanupAnnotations_boxed_4050_ = lean_unbox(v_cleanupAnnotations_4044_);
v_res_4051_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4042_, v_k_4043_, v_cleanupAnnotations_boxed_4050_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4052_, lean_object* v_type_4053_, lean_object* v_k_4054_, uint8_t v_cleanupAnnotations_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4053_, v_k_4054_, v_cleanupAnnotations_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4062_, lean_object* v_type_4063_, lean_object* v_k_4064_, lean_object* v_cleanupAnnotations_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4071_; lean_object* v_res_4072_; 
v_cleanupAnnotations_boxed_4071_ = lean_unbox(v_cleanupAnnotations_4065_);
v_res_4072_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4062_, v_type_4063_, v_k_4064_, v_cleanupAnnotations_boxed_4071_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_msg_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v___f_4079_; lean_object* v___x_18841__overap_4080_; lean_object* v___x_4081_; 
v___f_4079_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_18841__overap_4080_ = lean_panic_fn_borrowed(v___f_4079_, v_msg_4073_);
lean_inc(v___y_4077_);
lean_inc_ref(v___y_4076_);
lean_inc(v___y_4075_);
lean_inc_ref(v___y_4074_);
v___x_4081_ = lean_apply_5(v___x_18841__overap_4080_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, lean_box(0));
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_msg_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_msg_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4089_){
_start:
{
uint8_t v_foApprox_4090_; uint8_t v_ctxApprox_4091_; uint8_t v_quasiPatternApprox_4092_; uint8_t v_constApprox_4093_; uint8_t v_isDefEqStuckEx_4094_; uint8_t v_unificationHints_4095_; uint8_t v_proofIrrelevance_4096_; uint8_t v_assignSyntheticOpaque_4097_; uint8_t v_offsetCnstrs_4098_; uint8_t v_transparency_4099_; uint8_t v_univApprox_4100_; uint8_t v_iota_4101_; uint8_t v_beta_4102_; uint8_t v_proj_4103_; uint8_t v_zeta_4104_; uint8_t v_zetaDelta_4105_; uint8_t v_zetaUnused_4106_; uint8_t v_zetaHave_4107_; uint8_t v_canUnfoldPredicateConfig_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4116_; 
v_foApprox_4090_ = lean_ctor_get_uint8(v_c_4089_, 0);
v_ctxApprox_4091_ = lean_ctor_get_uint8(v_c_4089_, 1);
v_quasiPatternApprox_4092_ = lean_ctor_get_uint8(v_c_4089_, 2);
v_constApprox_4093_ = lean_ctor_get_uint8(v_c_4089_, 3);
v_isDefEqStuckEx_4094_ = lean_ctor_get_uint8(v_c_4089_, 4);
v_unificationHints_4095_ = lean_ctor_get_uint8(v_c_4089_, 5);
v_proofIrrelevance_4096_ = lean_ctor_get_uint8(v_c_4089_, 6);
v_assignSyntheticOpaque_4097_ = lean_ctor_get_uint8(v_c_4089_, 7);
v_offsetCnstrs_4098_ = lean_ctor_get_uint8(v_c_4089_, 8);
v_transparency_4099_ = lean_ctor_get_uint8(v_c_4089_, 9);
v_univApprox_4100_ = lean_ctor_get_uint8(v_c_4089_, 11);
v_iota_4101_ = lean_ctor_get_uint8(v_c_4089_, 12);
v_beta_4102_ = lean_ctor_get_uint8(v_c_4089_, 13);
v_proj_4103_ = lean_ctor_get_uint8(v_c_4089_, 14);
v_zeta_4104_ = lean_ctor_get_uint8(v_c_4089_, 15);
v_zetaDelta_4105_ = lean_ctor_get_uint8(v_c_4089_, 16);
v_zetaUnused_4106_ = lean_ctor_get_uint8(v_c_4089_, 17);
v_zetaHave_4107_ = lean_ctor_get_uint8(v_c_4089_, 18);
v_canUnfoldPredicateConfig_4108_ = lean_ctor_get_uint8(v_c_4089_, 19);
v_isSharedCheck_4116_ = !lean_is_exclusive(v_c_4089_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4110_ = v_c_4089_;
v_isShared_4111_ = v_isSharedCheck_4116_;
goto v_resetjp_4109_;
}
else
{
lean_dec(v_c_4089_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4116_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
uint8_t v___x_4112_; lean_object* v___x_4114_; 
v___x_4112_ = 2;
if (v_isShared_4111_ == 0)
{
v___x_4114_ = v___x_4110_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 0, v_foApprox_4090_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 1, v_ctxApprox_4091_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 2, v_quasiPatternApprox_4092_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 3, v_constApprox_4093_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 4, v_isDefEqStuckEx_4094_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 5, v_unificationHints_4095_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 6, v_proofIrrelevance_4096_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 7, v_assignSyntheticOpaque_4097_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 8, v_offsetCnstrs_4098_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 9, v_transparency_4099_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 11, v_univApprox_4100_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 12, v_iota_4101_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 13, v_beta_4102_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 14, v_proj_4103_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 15, v_zeta_4104_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 16, v_zetaDelta_4105_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 17, v_zetaUnused_4106_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 18, v_zetaHave_4107_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, 19, v_canUnfoldPredicateConfig_4108_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_ctor_set_uint8(v___x_4114_, 10, v___x_4112_);
return v___x_4114_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4117_, lean_object* v_t_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_dummy_4124_; lean_object* v_nargs_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_dummy_4124_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4125_ = l_Lean_Expr_getAppNumArgs(v_t_4118_);
lean_inc(v_nargs_4125_);
v___x_4126_ = lean_mk_array(v_nargs_4125_, v_dummy_4124_);
v___x_4127_ = lean_unsigned_to_nat(1u);
v___x_4128_ = lean_nat_sub(v_nargs_4125_, v___x_4127_);
lean_dec(v_nargs_4125_);
v___x_4129_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4118_, v___x_4126_, v___x_4128_);
v___x_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4131_, lean_object* v_t_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4131_, v_t_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec_ref(v_x_4131_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4139_, lean_object* v_x_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v_snd_4139_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4147_, lean_object* v_x_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4147_, v_x_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec_ref(v_x_4148_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4155_, size_t v_i_4156_, lean_object* v_bs_4157_){
_start:
{
uint8_t v___x_4158_; 
v___x_4158_ = lean_usize_dec_lt(v_i_4156_, v_sz_4155_);
if (v___x_4158_ == 0)
{
return v_bs_4157_;
}
else
{
lean_object* v_v_4159_; lean_object* v_fst_4160_; lean_object* v_snd_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4175_; 
v_v_4159_ = lean_array_uget(v_bs_4157_, v_i_4156_);
v_fst_4160_ = lean_ctor_get(v_v_4159_, 0);
v_snd_4161_ = lean_ctor_get(v_v_4159_, 1);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_v_4159_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4163_ = v_v_4159_;
v_isShared_4164_ = v_isSharedCheck_4175_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_snd_4161_);
lean_inc(v_fst_4160_);
lean_dec(v_v_4159_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4175_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v_bs_x27_4166_; lean_object* v___f_4167_; lean_object* v___x_4169_; 
v___x_4165_ = lean_unsigned_to_nat(0u);
v_bs_x27_4166_ = lean_array_uset(v_bs_4157_, v_i_4156_, v___x_4165_);
v___f_4167_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4167_, 0, v_snd_4161_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 1, v___f_4167_);
v___x_4169_ = v___x_4163_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_fst_4160_);
lean_ctor_set(v_reuseFailAlloc_4174_, 1, v___f_4167_);
v___x_4169_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
size_t v___x_4170_; size_t v___x_4171_; lean_object* v___x_4172_; 
v___x_4170_ = ((size_t)1ULL);
v___x_4171_ = lean_usize_add(v_i_4156_, v___x_4170_);
v___x_4172_ = lean_array_uset(v_bs_x27_4166_, v_i_4156_, v___x_4169_);
v_i_4156_ = v___x_4171_;
v_bs_4157_ = v___x_4172_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4176_, lean_object* v_i_4177_, lean_object* v_bs_4178_){
_start:
{
size_t v_sz_boxed_4179_; size_t v_i_boxed_4180_; lean_object* v_res_4181_; 
v_sz_boxed_4179_ = lean_unbox_usize(v_sz_4176_);
lean_dec(v_sz_4176_);
v_i_boxed_4180_ = lean_unbox_usize(v_i_4177_);
lean_dec(v_i_4177_);
v_res_4181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4179_, v_i_boxed_4180_, v_bs_4178_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4182_, size_t v_i_4183_, lean_object* v_bs_4184_){
_start:
{
uint8_t v___x_4185_; 
v___x_4185_ = lean_usize_dec_lt(v_i_4183_, v_sz_4182_);
if (v___x_4185_ == 0)
{
return v_bs_4184_;
}
else
{
lean_object* v_v_4186_; lean_object* v_fst_4187_; lean_object* v_snd_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4204_; 
v_v_4186_ = lean_array_uget(v_bs_4184_, v_i_4183_);
v_fst_4187_ = lean_ctor_get(v_v_4186_, 0);
v_snd_4188_ = lean_ctor_get(v_v_4186_, 1);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_v_4186_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4190_ = v_v_4186_;
v_isShared_4191_ = v_isSharedCheck_4204_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_snd_4188_);
lean_inc(v_fst_4187_);
lean_dec(v_v_4186_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4204_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4192_; lean_object* v_bs_x27_4193_; uint8_t v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4192_ = lean_unsigned_to_nat(0u);
v_bs_x27_4193_ = lean_array_uset(v_bs_4184_, v_i_4183_, v___x_4192_);
v___x_4194_ = 0;
v___x_4195_ = lean_box(v___x_4194_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4195_);
v___x_4197_ = v___x_4190_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4195_);
lean_ctor_set(v_reuseFailAlloc_4203_, 1, v_snd_4188_);
v___x_4197_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4198_; size_t v___x_4199_; size_t v___x_4200_; lean_object* v___x_4201_; 
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v_fst_4187_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = ((size_t)1ULL);
v___x_4200_ = lean_usize_add(v_i_4183_, v___x_4199_);
v___x_4201_ = lean_array_uset(v_bs_x27_4193_, v_i_4183_, v___x_4198_);
v_i_4183_ = v___x_4200_;
v_bs_4184_ = v___x_4201_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4205_, lean_object* v_i_4206_, lean_object* v_bs_4207_){
_start:
{
size_t v_sz_boxed_4208_; size_t v_i_boxed_4209_; lean_object* v_res_4210_; 
v_sz_boxed_4208_ = lean_unbox_usize(v_sz_4205_);
lean_dec(v_sz_4205_);
v_i_boxed_4209_ = lean_unbox_usize(v_i_4206_);
lean_dec(v_i_4206_);
v_res_4210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4208_, v_i_boxed_4209_, v_bs_4207_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4211_, lean_object* v___x_4212_, lean_object* v_a_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v___x_20547__overap_4219_; lean_object* v___x_4220_; 
v___x_20547__overap_4219_ = l_instInhabitedOfMonad___redArg(v___x_4211_, v___x_4212_);
lean_inc(v___y_4217_);
lean_inc_ref(v___y_4216_);
lean_inc(v___y_4215_);
lean_inc_ref(v___y_4214_);
v___x_4220_ = lean_apply_5(v___x_20547__overap_4219_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, lean_box(0));
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4221_, lean_object* v___x_4222_, lean_object* v_a_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4221_, v___x_4222_, v_a_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec_ref(v_a_4223_);
return v_res_4229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_instMonadEIO___redArg();
return v___x_4230_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4231_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4232_ = l_StateRefT_x27_instMonad___redArg(v___x_4231_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4237_, lean_object* v_declInfos_4238_, lean_object* v_k_4239_, lean_object* v_kind_4240_, lean_object* v_x_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
uint8_t v_kind_boxed_4247_; lean_object* v_res_4248_; 
v_kind_boxed_4247_ = lean_unbox(v_kind_4240_);
v_res_4248_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4237_, v_declInfos_4238_, v_k_4239_, v_kind_boxed_4247_, v_x_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4249_, lean_object* v_k_4250_, uint8_t v_kind_4251_, lean_object* v_acc_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v___x_4258_; lean_object* v_toApplicative_4259_; lean_object* v_toFunctor_4260_; lean_object* v_toSeq_4261_; lean_object* v_toSeqLeft_4262_; lean_object* v_toSeqRight_4263_; lean_object* v___f_4264_; lean_object* v___f_4265_; lean_object* v___f_4266_; lean_object* v___f_4267_; lean_object* v___x_4268_; lean_object* v___f_4269_; lean_object* v___f_4270_; lean_object* v___f_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v_toApplicative_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4325_; 
v___x_4258_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4259_ = lean_ctor_get(v___x_4258_, 0);
v_toFunctor_4260_ = lean_ctor_get(v_toApplicative_4259_, 0);
v_toSeq_4261_ = lean_ctor_get(v_toApplicative_4259_, 2);
v_toSeqLeft_4262_ = lean_ctor_get(v_toApplicative_4259_, 3);
v_toSeqRight_4263_ = lean_ctor_get(v_toApplicative_4259_, 4);
v___f_4264_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4265_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4260_, 2);
v___f_4266_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4266_, 0, v_toFunctor_4260_);
v___f_4267_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4267_, 0, v_toFunctor_4260_);
v___x_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___f_4266_);
lean_ctor_set(v___x_4268_, 1, v___f_4267_);
lean_inc(v_toSeqRight_4263_);
v___f_4269_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4269_, 0, v_toSeqRight_4263_);
lean_inc(v_toSeqLeft_4262_);
v___f_4270_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4270_, 0, v_toSeqLeft_4262_);
lean_inc(v_toSeq_4261_);
v___f_4271_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4271_, 0, v_toSeq_4261_);
v___x_4272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4268_);
lean_ctor_set(v___x_4272_, 1, v___f_4264_);
lean_ctor_set(v___x_4272_, 2, v___f_4271_);
lean_ctor_set(v___x_4272_, 3, v___f_4270_);
lean_ctor_set(v___x_4272_, 4, v___f_4269_);
v___x_4273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
lean_ctor_set(v___x_4273_, 1, v___f_4265_);
v___x_4274_ = l_StateRefT_x27_instMonad___redArg(v___x_4273_);
v_toApplicative_4275_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4325_ == 0)
{
lean_object* v_unused_4326_; 
v_unused_4326_ = lean_ctor_get(v___x_4274_, 1);
lean_dec(v_unused_4326_);
v___x_4277_ = v___x_4274_;
v_isShared_4278_ = v_isSharedCheck_4325_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_toApplicative_4275_);
lean_dec(v___x_4274_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4325_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v_toFunctor_4279_; lean_object* v_toSeq_4280_; lean_object* v_toSeqLeft_4281_; lean_object* v_toSeqRight_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4323_; 
v_toFunctor_4279_ = lean_ctor_get(v_toApplicative_4275_, 0);
v_toSeq_4280_ = lean_ctor_get(v_toApplicative_4275_, 2);
v_toSeqLeft_4281_ = lean_ctor_get(v_toApplicative_4275_, 3);
v_toSeqRight_4282_ = lean_ctor_get(v_toApplicative_4275_, 4);
v_isSharedCheck_4323_ = !lean_is_exclusive(v_toApplicative_4275_);
if (v_isSharedCheck_4323_ == 0)
{
lean_object* v_unused_4324_; 
v_unused_4324_ = lean_ctor_get(v_toApplicative_4275_, 1);
lean_dec(v_unused_4324_);
v___x_4284_ = v_toApplicative_4275_;
v_isShared_4285_ = v_isSharedCheck_4323_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_toSeqRight_4282_);
lean_inc(v_toSeqLeft_4281_);
lean_inc(v_toSeq_4280_);
lean_inc(v_toFunctor_4279_);
lean_dec(v_toApplicative_4275_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4323_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___f_4286_; lean_object* v___f_4287_; lean_object* v___f_4288_; lean_object* v___f_4289_; lean_object* v___x_4290_; lean_object* v___f_4291_; lean_object* v___f_4292_; lean_object* v___f_4293_; lean_object* v___x_4295_; 
v___f_4286_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4287_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4279_);
v___f_4288_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4288_, 0, v_toFunctor_4279_);
v___f_4289_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4289_, 0, v_toFunctor_4279_);
v___x_4290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4290_, 0, v___f_4288_);
lean_ctor_set(v___x_4290_, 1, v___f_4289_);
v___f_4291_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4291_, 0, v_toSeqRight_4282_);
v___f_4292_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4292_, 0, v_toSeqLeft_4281_);
v___f_4293_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4293_, 0, v_toSeq_4280_);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 4, v___f_4291_);
lean_ctor_set(v___x_4284_, 3, v___f_4292_);
lean_ctor_set(v___x_4284_, 2, v___f_4293_);
lean_ctor_set(v___x_4284_, 1, v___f_4286_);
lean_ctor_set(v___x_4284_, 0, v___x_4290_);
v___x_4295_ = v___x_4284_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4290_);
lean_ctor_set(v_reuseFailAlloc_4322_, 1, v___f_4286_);
lean_ctor_set(v_reuseFailAlloc_4322_, 2, v___f_4293_);
lean_ctor_set(v_reuseFailAlloc_4322_, 3, v___f_4292_);
lean_ctor_set(v_reuseFailAlloc_4322_, 4, v___f_4291_);
v___x_4295_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
lean_object* v___x_4297_; 
if (v_isShared_4278_ == 0)
{
lean_ctor_set(v___x_4277_, 1, v___f_4287_);
lean_ctor_set(v___x_4277_, 0, v___x_4295_);
v___x_4297_ = v___x_4277_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4295_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v___f_4287_);
v___x_4297_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4298_ = lean_array_get_size(v_acc_4252_);
v___x_4299_ = lean_array_get_size(v_declInfos_4249_);
v___x_4300_ = lean_nat_dec_lt(v___x_4298_, v___x_4299_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; 
lean_dec_ref(v___x_4297_);
lean_dec_ref(v_declInfos_4249_);
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
lean_inc(v___y_4254_);
lean_inc_ref(v___y_4253_);
v___x_4301_ = lean_apply_6(v_k_4250_, v_acc_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, lean_box(0));
return v___x_4301_;
}
else
{
lean_object* v___x_4302_; uint8_t v___x_4303_; lean_object* v___x_4304_; lean_object* v___f_4305_; lean_object* v___f_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v_snd_4311_; lean_object* v_fst_4312_; lean_object* v_fst_4313_; lean_object* v_snd_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; lean_object* v___x_4317_; 
v___x_4302_ = lean_box(0);
v___x_4303_ = 0;
v___x_4304_ = l_Lean_instInhabitedExpr;
v___f_4305_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4305_, 0, v___x_4297_);
lean_closure_set(v___f_4305_, 1, v___x_4304_);
v___f_4306_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4306_, 0, v___f_4305_);
v___x_4307_ = lean_box(v___x_4303_);
v___x_4308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
lean_ctor_set(v___x_4308_, 1, v___f_4306_);
v___x_4309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4302_);
lean_ctor_set(v___x_4309_, 1, v___x_4308_);
v___x_4310_ = lean_array_get(v___x_4309_, v_declInfos_4249_, v___x_4298_);
lean_dec_ref_known(v___x_4309_, 2);
v_snd_4311_ = lean_ctor_get(v___x_4310_, 1);
lean_inc(v_snd_4311_);
v_fst_4312_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_fst_4312_);
lean_dec(v___x_4310_);
v_fst_4313_ = lean_ctor_get(v_snd_4311_, 0);
lean_inc(v_fst_4313_);
v_snd_4314_ = lean_ctor_get(v_snd_4311_, 1);
lean_inc(v_snd_4314_);
lean_dec(v_snd_4311_);
v___x_4315_ = lean_box(v_kind_4251_);
lean_inc_ref(v_acc_4252_);
v___f_4316_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4316_, 0, v_acc_4252_);
lean_closure_set(v___f_4316_, 1, v_declInfos_4249_);
lean_closure_set(v___f_4316_, 2, v_k_4250_);
lean_closure_set(v___f_4316_, 3, v___x_4315_);
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
lean_inc(v___y_4254_);
lean_inc_ref(v___y_4253_);
v___x_4317_ = lean_apply_6(v_snd_4314_, v_acc_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, lean_box(0));
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; uint8_t v___x_4319_; lean_object* v___x_4320_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v___x_4317_, 1);
v___x_4319_ = lean_unbox(v_fst_4313_);
lean_dec(v_fst_4313_);
v___x_4320_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4312_, v___x_4319_, v_a_4318_, v___f_4316_, v_kind_4251_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
return v___x_4320_;
}
else
{
lean_dec_ref(v___f_4316_);
lean_dec(v_fst_4313_);
lean_dec(v_fst_4312_);
return v___x_4317_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4327_, lean_object* v_declInfos_4328_, lean_object* v_k_4329_, uint8_t v_kind_4330_, lean_object* v_x_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4337_ = lean_array_push(v_acc_4327_, v_x_4331_);
v___x_4338_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4328_, v_k_4329_, v_kind_4330_, v___x_4337_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4339_, lean_object* v_k_4340_, lean_object* v_kind_4341_, lean_object* v_acc_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
uint8_t v_kind_boxed_4348_; lean_object* v_res_4349_; 
v_kind_boxed_4348_ = lean_unbox(v_kind_4341_);
v_res_4349_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4339_, v_k_4340_, v_kind_boxed_4348_, v_acc_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4350_, lean_object* v_k_4351_, uint8_t v_kind_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4358_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4359_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4350_, v_k_4351_, v_kind_4352_, v___x_4358_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4360_, lean_object* v_k_4361_, lean_object* v_kind_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
uint8_t v_kind_boxed_4368_; lean_object* v_res_4369_; 
v_kind_boxed_4368_ = lean_unbox(v_kind_4362_);
v_res_4369_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4360_, v_k_4361_, v_kind_boxed_4368_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
return v_res_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4370_, lean_object* v_k_4371_, uint8_t v_kind_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
size_t v_sz_4378_; size_t v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v_sz_4378_ = lean_array_size(v_declInfos_4370_);
v___x_4379_ = ((size_t)0ULL);
v___x_4380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4378_, v___x_4379_, v_declInfos_4370_);
v___x_4381_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4380_, v_k_4371_, v_kind_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4382_, lean_object* v_k_4383_, lean_object* v_kind_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
uint8_t v_kind_boxed_4390_; lean_object* v_res_4391_; 
v_kind_boxed_4390_ = lean_unbox(v_kind_4384_);
v_res_4391_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4382_, v_k_4383_, v_kind_boxed_4390_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4392_, lean_object* v_k_4393_, uint8_t v_kind_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
size_t v_sz_4400_; size_t v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v_sz_4400_ = lean_array_size(v_declInfos_4392_);
v___x_4401_ = ((size_t)0ULL);
v___x_4402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4400_, v___x_4401_, v_declInfos_4392_);
v___x_4403_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4402_, v_k_4393_, v_kind_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4404_, lean_object* v_k_4405_, lean_object* v_kind_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
uint8_t v_kind_boxed_4412_; lean_object* v_res_4413_; 
v_kind_boxed_4412_ = lean_unbox(v_kind_4406_);
v_res_4413_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4404_, v_k_4405_, v_kind_boxed_4412_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(lean_object* v_a_4417_, lean_object* v_b_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v_array_4424_; lean_object* v_start_4425_; lean_object* v_stop_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4484_; 
v_array_4424_ = lean_ctor_get(v_a_4417_, 0);
v_start_4425_ = lean_ctor_get(v_a_4417_, 1);
v_stop_4426_ = lean_ctor_get(v_a_4417_, 2);
v_isSharedCheck_4484_ = !lean_is_exclusive(v_a_4417_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4428_ = v_a_4417_;
v_isShared_4429_ = v_isSharedCheck_4484_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_stop_4426_);
lean_inc(v_start_4425_);
lean_inc(v_array_4424_);
lean_dec(v_a_4417_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4484_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
uint8_t v___x_4430_; 
v___x_4430_ = lean_nat_dec_lt(v_start_4425_, v_stop_4426_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4431_; 
lean_del_object(v___x_4428_);
lean_dec(v_stop_4426_);
lean_dec(v_start_4425_);
lean_dec_ref(v_array_4424_);
v___x_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4431_, 0, v_b_4418_);
return v___x_4431_;
}
else
{
lean_object* v_snd_4432_; lean_object* v_fst_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4483_; 
v_snd_4432_ = lean_ctor_get(v_b_4418_, 1);
v_fst_4433_ = lean_ctor_get(v_b_4418_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v_b_4418_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4435_ = v_b_4418_;
v_isShared_4436_ = v_isSharedCheck_4483_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_snd_4432_);
lean_inc(v_fst_4433_);
lean_dec(v_b_4418_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4483_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v_array_4437_; lean_object* v_start_4438_; lean_object* v_stop_4439_; uint8_t v___x_4440_; 
v_array_4437_ = lean_ctor_get(v_snd_4432_, 0);
v_start_4438_ = lean_ctor_get(v_snd_4432_, 1);
v_stop_4439_ = lean_ctor_get(v_snd_4432_, 2);
v___x_4440_ = lean_nat_dec_lt(v_start_4438_, v_stop_4439_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4442_; 
lean_del_object(v___x_4428_);
lean_dec(v_stop_4426_);
lean_dec(v_start_4425_);
lean_dec_ref(v_array_4424_);
if (v_isShared_4436_ == 0)
{
v___x_4442_ = v___x_4435_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_fst_4433_);
lean_ctor_set(v_reuseFailAlloc_4444_, 1, v_snd_4432_);
v___x_4442_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4443_; 
v___x_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4442_);
return v___x_4443_;
}
}
else
{
lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4479_; 
lean_inc(v_stop_4439_);
lean_inc(v_start_4438_);
lean_inc_ref(v_array_4437_);
v_isSharedCheck_4479_ = !lean_is_exclusive(v_snd_4432_);
if (v_isSharedCheck_4479_ == 0)
{
lean_object* v_unused_4480_; lean_object* v_unused_4481_; lean_object* v_unused_4482_; 
v_unused_4480_ = lean_ctor_get(v_snd_4432_, 2);
lean_dec(v_unused_4480_);
v_unused_4481_ = lean_ctor_get(v_snd_4432_, 1);
lean_dec(v_unused_4481_);
v_unused_4482_ = lean_ctor_get(v_snd_4432_, 0);
lean_dec(v_unused_4482_);
v___x_4446_ = v_snd_4432_;
v_isShared_4447_ = v_isSharedCheck_4479_;
goto v_resetjp_4445_;
}
else
{
lean_dec(v_snd_4432_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4479_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4451_; 
v___x_4448_ = lean_unsigned_to_nat(1u);
v___x_4449_ = lean_nat_add(v_start_4425_, v___x_4448_);
lean_inc_ref(v_array_4424_);
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 2, v_stop_4426_);
lean_ctor_set(v___x_4446_, 1, v___x_4449_);
lean_ctor_set(v___x_4446_, 0, v_array_4424_);
v___x_4451_ = v___x_4446_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_array_4424_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v___x_4449_);
lean_ctor_set(v_reuseFailAlloc_4478_, 2, v_stop_4426_);
v___x_4451_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4456_; 
v___x_4452_ = lean_array_fget(v_array_4424_, v_start_4425_);
lean_dec(v_start_4425_);
lean_dec_ref(v_array_4424_);
v___x_4453_ = lean_array_fget(v_array_4437_, v_start_4438_);
v___x_4454_ = lean_nat_add(v_start_4438_, v___x_4448_);
lean_dec(v_start_4438_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 2, v_stop_4439_);
lean_ctor_set(v___x_4428_, 1, v___x_4454_);
lean_ctor_set(v___x_4428_, 0, v_array_4437_);
v___x_4456_ = v___x_4428_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_array_4437_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v___x_4454_);
lean_ctor_set(v_reuseFailAlloc_4477_, 2, v_stop_4439_);
v___x_4456_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
lean_object* v___x_4457_; 
v___x_4457_ = l_Lean_Meta_mkEqHEq(v___x_4452_, v___x_4453_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4464_; 
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_a_4458_);
lean_dec_ref_known(v___x_4457_, 1);
v___x_4459_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__1));
v___x_4460_ = lean_array_get_size(v_fst_4433_);
v___x_4461_ = lean_nat_add(v___x_4460_, v___x_4448_);
v___x_4462_ = lean_name_append_index_after(v___x_4459_, v___x_4461_);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 1, v_a_4458_);
lean_ctor_set(v___x_4435_, 0, v___x_4462_);
v___x_4464_ = v___x_4435_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4462_);
lean_ctor_set(v_reuseFailAlloc_4468_, 1, v_a_4458_);
v___x_4464_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = lean_array_push(v_fst_4433_, v___x_4464_);
v___x_4466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4465_);
lean_ctor_set(v___x_4466_, 1, v___x_4456_);
v_a_4417_ = v___x_4451_;
v_b_4418_ = v___x_4466_;
goto _start;
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec_ref(v___x_4456_);
lean_dec_ref(v___x_4451_);
lean_del_object(v___x_4435_);
lean_dec(v_fst_4433_);
v_a_4469_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4457_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4457_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___boxed(lean_object* v_a_4485_, lean_object* v_b_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_4485_, v_b_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v___x_4493_, lean_object* v_a_4494_, lean_object* v___x_4495_, lean_object* v_as_4496_, size_t v_sz_4497_, size_t v_i_4498_, lean_object* v_b_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
lean_object* v_a_4506_; uint8_t v___x_4510_; 
v___x_4510_ = lean_usize_dec_lt(v_i_4498_, v_sz_4497_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; 
lean_dec(v___x_4495_);
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v_b_4499_);
return v___x_4511_;
}
else
{
lean_object* v___x_4512_; lean_object* v_a_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v___x_4512_ = l_Lean_instInhabitedExpr;
v_a_4513_ = lean_array_uget_borrowed(v_as_4496_, v_i_4498_);
v___x_4514_ = lean_array_get_borrowed(v___x_4512_, v___x_4493_, v_a_4513_);
lean_inc(v___x_4514_);
v___x_4515_ = l_Lean_Meta_instantiateForall(v___x_4514_, v_a_4494_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_object* v_a_4516_; lean_object* v___x_4517_; 
v_a_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_a_4516_);
lean_dec_ref_known(v___x_4515_, 1);
lean_inc(v___x_4495_);
v___x_4517_ = l_Lean_Meta_Match_simpH_x3f(v_a_4516_, v___x_4495_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
if (lean_obj_tag(v_a_4518_) == 1)
{
lean_object* v_val_4519_; lean_object* v___x_4520_; 
v_val_4519_ = lean_ctor_get(v_a_4518_, 0);
lean_inc(v_val_4519_);
lean_dec_ref_known(v_a_4518_, 1);
v___x_4520_ = lean_array_push(v_b_4499_, v_val_4519_);
v_a_4506_ = v___x_4520_;
goto v___jp_4505_;
}
else
{
lean_dec(v_a_4518_);
v_a_4506_ = v_b_4499_;
goto v___jp_4505_;
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_dec_ref(v_b_4499_);
lean_dec(v___x_4495_);
v_a_4521_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4517_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4517_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_dec_ref(v_b_4499_);
lean_dec(v___x_4495_);
v_a_4529_ = lean_ctor_get(v___x_4515_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4515_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4515_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
v___jp_4505_:
{
size_t v___x_4507_; size_t v___x_4508_; 
v___x_4507_ = ((size_t)1ULL);
v___x_4508_ = lean_usize_add(v_i_4498_, v___x_4507_);
v_i_4498_ = v___x_4508_;
v_b_4499_ = v_a_4506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v___x_4537_, lean_object* v_a_4538_, lean_object* v___x_4539_, lean_object* v_as_4540_, lean_object* v_sz_4541_, lean_object* v_i_4542_, lean_object* v_b_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
size_t v_sz_boxed_4549_; size_t v_i_boxed_4550_; lean_object* v_res_4551_; 
v_sz_boxed_4549_ = lean_unbox_usize(v_sz_4541_);
lean_dec(v_sz_4541_);
v_i_boxed_4550_ = lean_unbox_usize(v_i_4542_);
lean_dec(v_i_4542_);
v_res_4551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4537_, v_a_4538_, v___x_4539_, v_as_4540_, v_sz_boxed_4549_, v_i_boxed_4550_, v_b_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec_ref(v_as_4540_);
lean_dec_ref(v_a_4538_);
lean_dec_ref(v___x_4537_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4552_, lean_object* v_args_4553_, lean_object* v___x_4554_, lean_object* v_overlaps_4555_, lean_object* v_a_4556_, lean_object* v_fst_4557_, lean_object* v_a_4558_, lean_object* v___x_4559_, lean_object* v___x_4560_, lean_object* v___x_4561_, lean_object* v___x_4562_, lean_object* v_altVars_4563_, uint8_t v___x_4564_, uint8_t v___x_4565_, lean_object* v_a_4566_, lean_object* v___x_4567_, lean_object* v___x_4568_, lean_object* v___x_4569_, lean_object* v___x_4570_, lean_object* v___x_4571_, lean_object* v___x_4572_, lean_object* v___x_4573_, lean_object* v_matchDeclName_4574_, lean_object* v___x_4575_, lean_object* v___x_4576_, lean_object* v___x_4577_, lean_object* v_heqs_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4584_ = l_Lean_mkAppN(v___y_4552_, v_args_4553_);
lean_inc_ref(v_heqs_4578_);
v___x_4585_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4584_, v_heqs_4578_, v___x_4554_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v_a_4586_; lean_object* v___x_4587_; size_t v_sz_4588_; size_t v___x_4589_; lean_object* v___x_4590_; 
v_a_4586_ = lean_ctor_get(v___x_4585_, 0);
lean_inc(v_a_4586_);
lean_dec_ref_known(v___x_4585_, 1);
v___x_4587_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4555_, v_a_4556_);
v_sz_4588_ = lean_array_size(v___x_4587_);
v___x_4589_ = ((size_t)0ULL);
lean_inc_ref(v___x_4560_);
v___x_4590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_fst_4557_, v_a_4558_, v___x_4559_, v___x_4587_, v_sz_4588_, v___x_4589_, v___x_4560_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec_ref(v___x_4587_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v_toCold_4703_; lean_object* v_options_4704_; uint8_t v_hasTrace_4705_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc(v_a_4591_);
lean_dec_ref_known(v___x_4590_, 1);
v_toCold_4703_ = lean_ctor_get(v___y_4581_, 0);
v_options_4704_ = lean_ctor_get(v_toCold_4703_, 2);
v_hasTrace_4705_ = lean_ctor_get_uint8(v_options_4704_, sizeof(void*)*1);
if (v_hasTrace_4705_ == 0)
{
v___y_4593_ = v___y_4579_;
v___y_4594_ = v___y_4580_;
v___y_4595_ = v___y_4581_;
v___y_4596_ = v___y_4582_;
goto v___jp_4592_;
}
else
{
lean_object* v_inheritedTraceOptions_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; 
v_inheritedTraceOptions_4706_ = lean_ctor_get(v_toCold_4703_, 11);
v___x_4707_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
v___x_4708_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17);
v___x_4709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4706_, v_options_4704_, v___x_4708_);
if (v___x_4709_ == 0)
{
v___y_4593_ = v___y_4579_;
v___y_4594_ = v___y_4580_;
v___y_4595_ = v___y_4581_;
v___y_4596_ = v___y_4582_;
goto v___jp_4592_;
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4710_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4591_);
v___x_4711_ = lean_array_to_list(v_a_4591_);
v___x_4712_ = lean_box(0);
v___x_4713_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4711_, v___x_4712_);
v___x_4714_ = l_Lean_MessageData_ofList(v___x_4713_);
v___x_4715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4710_);
lean_ctor_set(v___x_4715_, 1, v___x_4714_);
v___x_4716_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4707_, v___x_4715_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_dec_ref_known(v___x_4716_, 1);
v___y_4593_ = v___y_4579_;
v___y_4594_ = v___y_4580_;
v___y_4595_ = v___y_4581_;
v___y_4596_ = v___y_4582_;
goto v___jp_4592_;
}
else
{
lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
lean_dec(v_a_4591_);
lean_dec(v_a_4586_);
lean_dec_ref(v_heqs_4578_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
lean_dec(v_matchDeclName_4574_);
lean_dec_ref(v___x_4571_);
lean_dec_ref(v___x_4570_);
lean_dec_ref(v___x_4568_);
lean_dec(v___x_4567_);
lean_dec_ref(v___x_4562_);
lean_dec(v___x_4561_);
lean_dec_ref(v___x_4560_);
lean_dec_ref(v_a_4558_);
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4719_ = v___x_4716_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_dec(v___x_4716_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4717_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
v___jp_4592_:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; size_t v_sz_4604_; lean_object* v___x_4605_; 
v___x_4597_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4598_ = l_Array_reverse___redArg(v_a_4558_);
v___x_4599_ = lean_array_get_size(v___x_4598_);
v___x_4600_ = l_Array_toSubarray___redArg(v___x_4598_, v___x_4561_, v___x_4599_);
lean_inc_ref(v___x_4562_);
v___x_4601_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4562_, v___x_4560_);
v___x_4602_ = l_Array_reverse___redArg(v___x_4601_);
v___x_4603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4597_);
lean_ctor_set(v___x_4603_, 1, v___x_4600_);
v_sz_4604_ = lean_array_size(v___x_4602_);
v___x_4605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4602_, v_sz_4604_, v___x_4589_, v___x_4603_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
lean_dec_ref(v___x_4602_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v_fst_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4693_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4606_);
lean_dec_ref_known(v___x_4605_, 1);
v_fst_4607_ = lean_ctor_get(v_a_4606_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v_a_4606_);
if (v_isSharedCheck_4693_ == 0)
{
lean_object* v_unused_4694_; 
v_unused_4694_ = lean_ctor_get(v_a_4606_, 1);
lean_dec(v_unused_4694_);
v___x_4609_ = v_a_4606_;
v_isShared_4610_ = v_isSharedCheck_4693_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_fst_4607_);
lean_dec(v_a_4606_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4693_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; uint8_t v___x_4613_; lean_object* v___x_4614_; 
v___x_4611_ = l_Subarray_copy___redArg(v___x_4562_);
lean_inc_ref(v___x_4611_);
v___x_4612_ = l_Array_append___redArg(v___x_4611_, v_altVars_4563_);
v___x_4613_ = 1;
v___x_4614_ = l_Lean_Meta_mkForallFVars(v___x_4612_, v_fst_4607_, v___x_4564_, v___x_4565_, v___x_4565_, v___x_4613_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
lean_dec_ref(v___x_4612_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_a_4615_);
lean_dec_ref_known(v___x_4614_, 1);
v___x_4616_ = l_Lean_ConstantInfo_name(v_a_4566_);
v___x_4617_ = l_Lean_mkConst(v___x_4616_, v___x_4567_);
lean_inc_ref(v___x_4568_);
v___x_4618_ = l_Subarray_copy___redArg(v___x_4568_);
v___x_4619_ = lean_mk_empty_array_with_capacity(v___x_4569_);
v___x_4620_ = lean_array_push(v___x_4619_, v___x_4570_);
v___x_4621_ = l_Array_append___redArg(v___x_4618_, v___x_4620_);
lean_dec_ref(v___x_4620_);
v___x_4622_ = l_Array_append___redArg(v___x_4621_, v___x_4611_);
lean_dec_ref(v___x_4611_);
v___x_4623_ = l_Subarray_copy___redArg(v___x_4571_);
v___x_4624_ = l_Array_append___redArg(v___x_4622_, v___x_4623_);
lean_dec_ref(v___x_4623_);
v___x_4625_ = l_Lean_mkAppN(v___x_4617_, v___x_4624_);
v___x_4626_ = l_Lean_Meta_mkHEq(v___x_4625_, v_a_4586_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4628_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
lean_inc(v_a_4627_);
lean_dec_ref_known(v___x_4626_, 1);
v___x_4628_ = l_Lean_mkArrowN(v_a_4591_, v_a_4627_, v___y_4595_, v___y_4596_);
lean_dec(v_a_4591_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc(v_a_4629_);
lean_dec_ref_known(v___x_4628_, 1);
v___x_4630_ = l_Array_append___redArg(v___x_4624_, v_altVars_4563_);
v___x_4631_ = l_Array_append___redArg(v___x_4630_, v_heqs_4578_);
v___x_4632_ = l_Lean_Meta_mkForallFVars(v___x_4631_, v_a_4629_, v___x_4564_, v___x_4565_, v___x_4565_, v___x_4613_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
lean_dec_ref(v___x_4631_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; lean_object* v___x_4634_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
lean_inc(v_a_4633_);
lean_dec_ref_known(v___x_4632_, 1);
v___x_4634_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4633_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4692_; 
v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4637_ = v___x_4634_;
v_isShared_4638_ = v_isSharedCheck_4692_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4634_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4692_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v_start_4639_; lean_object* v_stop_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4690_; 
v_start_4639_ = lean_ctor_get(v___x_4568_, 1);
v_stop_4640_ = lean_ctor_get(v___x_4568_, 2);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4690_ == 0)
{
lean_object* v_unused_4691_; 
v_unused_4691_ = lean_ctor_get(v___x_4568_, 0);
lean_dec(v_unused_4691_);
v___x_4642_ = v___x_4568_;
v_isShared_4643_ = v_isSharedCheck_4690_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_stop_4640_);
lean_inc(v_start_4639_);
lean_dec(v___x_4568_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4690_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4644_ = lean_nat_sub(v_stop_4640_, v_start_4639_);
lean_dec(v_start_4639_);
lean_dec(v_stop_4640_);
v___x_4645_ = lean_nat_add(v___x_4644_, v___x_4569_);
lean_dec(v___x_4644_);
v___x_4646_ = lean_nat_add(v___x_4645_, v___x_4572_);
lean_dec(v___x_4645_);
v___x_4647_ = lean_nat_add(v___x_4646_, v___x_4573_);
lean_dec(v___x_4646_);
v___x_4648_ = lean_array_get_size(v_altVars_4563_);
v___x_4649_ = lean_nat_add(v___x_4647_, v___x_4648_);
lean_dec(v___x_4647_);
v___x_4650_ = lean_array_get_size(v_heqs_4578_);
lean_dec_ref(v_heqs_4578_);
lean_inc(v_a_4635_);
v___x_4651_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4574_, v_a_4635_, v___x_4649_, v___x_4650_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4689_; 
v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4654_ = v___x_4651_;
v_isShared_4655_ = v_isSharedCheck_4689_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4651_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4689_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4656_; lean_object* v_env_4657_; uint8_t v___x_4658_; 
v___x_4656_ = lean_st_ref_get(v___y_4596_);
v_env_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc_ref(v_env_4657_);
lean_dec(v___x_4656_);
lean_inc(v___x_4575_);
v___x_4658_ = l_Lean_Environment_contains(v_env_4657_, v___x_4575_, v___x_4565_);
if (v___x_4658_ == 0)
{
lean_object* v___x_4660_; 
lean_del_object(v___x_4654_);
lean_inc(v___x_4575_);
if (v_isShared_4643_ == 0)
{
lean_ctor_set(v___x_4642_, 2, v_a_4635_);
lean_ctor_set(v___x_4642_, 1, v___x_4576_);
lean_ctor_set(v___x_4642_, 0, v___x_4575_);
v___x_4660_ = v___x_4642_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4575_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v___x_4576_);
lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_a_4635_);
v___x_4660_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4662_; 
if (v_isShared_4610_ == 0)
{
lean_ctor_set_tag(v___x_4609_, 1);
lean_ctor_set(v___x_4609_, 1, v___x_4577_);
lean_ctor_set(v___x_4609_, 0, v___x_4575_);
v___x_4662_ = v___x_4609_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v___x_4575_);
lean_ctor_set(v_reuseFailAlloc_4684_, 1, v___x_4577_);
v___x_4662_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
lean_object* v___x_4663_; lean_object* v___x_4665_; 
v___x_4663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4660_);
lean_ctor_set(v___x_4663_, 1, v_a_4652_);
lean_ctor_set(v___x_4663_, 2, v___x_4662_);
if (v_isShared_4638_ == 0)
{
lean_ctor_set_tag(v___x_4637_, 2);
lean_ctor_set(v___x_4637_, 0, v___x_4663_);
v___x_4665_ = v___x_4637_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v___x_4663_);
v___x_4665_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
lean_object* v___x_4666_; 
v___x_4666_ = l_Lean_addDecl(v___x_4665_, v___x_4564_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4673_ == 0)
{
lean_object* v_unused_4674_; 
v_unused_4674_ = lean_ctor_get(v___x_4666_, 0);
lean_dec(v_unused_4674_);
v___x_4668_ = v___x_4666_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_dec(v___x_4666_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 0, v_a_4615_);
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4615_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4682_; 
lean_dec(v_a_4615_);
v_a_4675_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4677_ = v___x_4666_;
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4666_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4680_; 
if (v_isShared_4678_ == 0)
{
v___x_4680_ = v___x_4677_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4675_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4687_; 
lean_dec(v_a_4652_);
lean_del_object(v___x_4642_);
lean_del_object(v___x_4637_);
lean_dec(v_a_4635_);
lean_del_object(v___x_4609_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
if (v_isShared_4655_ == 0)
{
lean_ctor_set(v___x_4654_, 0, v_a_4615_);
v___x_4687_ = v___x_4654_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4615_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
else
{
lean_del_object(v___x_4642_);
lean_del_object(v___x_4637_);
lean_dec(v_a_4635_);
lean_dec(v_a_4615_);
lean_del_object(v___x_4609_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
return v___x_4651_;
}
}
}
}
else
{
lean_dec(v_a_4615_);
lean_del_object(v___x_4609_);
lean_dec_ref(v_heqs_4578_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
lean_dec(v_matchDeclName_4574_);
lean_dec_ref(v___x_4568_);
return v___x_4634_;
}
}
else
{
lean_dec(v_a_4615_);
lean_del_object(v___x_4609_);
lean_dec_ref(v_heqs_4578_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
lean_dec(v_matchDeclName_4574_);
lean_dec_ref(v___x_4568_);
return v___x_4632_;
}
}
else
{
lean_dec_ref(v___x_4624_);
lean_dec(v_a_4615_);
lean_del_object(v___x_4609_);
lean_dec_ref(v_heqs_4578_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
lean_dec(v_matchDeclName_4574_);
lean_dec_ref(v___x_4568_);
return v___x_4628_;
}
}
else
{
lean_dec_ref(v___x_4624_);
lean_dec(v_a_4615_);
lean_del_object(v___x_4609_);
lean_dec(v_a_4591_);
lean_dec_ref(v_heqs_4578_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
lean_dec(v_matchDeclName_4574_);
lean_dec_ref(v___x_4568_);
return v___x_4626_;
}
}
else
{
lean_dec_ref(v___x_4611_);
lean_del_object(v___x_4609_);
lean_dec(v_a_4591_);
lean_dec(v_a_4586_);
lean_dec_ref(v_heqs_4578_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
lean_dec(v_matchDeclName_4574_);
lean_dec_ref(v___x_4571_);
lean_dec_ref(v___x_4570_);
lean_dec_ref(v___x_4568_);
lean_dec(v___x_4567_);
return v___x_4614_;
}
}
}
else
{
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4702_; 
lean_dec(v_a_4591_);
lean_dec(v_a_4586_);
lean_dec_ref(v_heqs_4578_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
lean_dec(v_matchDeclName_4574_);
lean_dec_ref(v___x_4571_);
lean_dec_ref(v___x_4570_);
lean_dec_ref(v___x_4568_);
lean_dec(v___x_4567_);
lean_dec_ref(v___x_4562_);
v_a_4695_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4697_ = v___x_4605_;
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v___x_4605_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4700_; 
if (v_isShared_4698_ == 0)
{
v___x_4700_ = v___x_4697_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4695_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
}
else
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4732_; 
lean_dec(v_a_4586_);
lean_dec_ref(v_heqs_4578_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
lean_dec(v_matchDeclName_4574_);
lean_dec_ref(v___x_4571_);
lean_dec_ref(v___x_4570_);
lean_dec_ref(v___x_4568_);
lean_dec(v___x_4567_);
lean_dec_ref(v___x_4562_);
lean_dec(v___x_4561_);
lean_dec_ref(v___x_4560_);
lean_dec_ref(v_a_4558_);
v_a_4725_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4727_ = v___x_4590_;
v_isShared_4728_ = v_isSharedCheck_4732_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4590_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4732_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v___x_4730_; 
if (v_isShared_4728_ == 0)
{
v___x_4730_ = v___x_4727_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_a_4725_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4578_);
lean_dec(v___x_4577_);
lean_dec(v___x_4576_);
lean_dec(v___x_4575_);
lean_dec(v_matchDeclName_4574_);
lean_dec_ref(v___x_4571_);
lean_dec_ref(v___x_4570_);
lean_dec_ref(v___x_4568_);
lean_dec(v___x_4567_);
lean_dec_ref(v___x_4562_);
lean_dec(v___x_4561_);
lean_dec_ref(v___x_4560_);
lean_dec(v___x_4559_);
lean_dec_ref(v_a_4558_);
return v___x_4585_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4733_ = _args[0];
lean_object* v_args_4734_ = _args[1];
lean_object* v___x_4735_ = _args[2];
lean_object* v_overlaps_4736_ = _args[3];
lean_object* v_a_4737_ = _args[4];
lean_object* v_fst_4738_ = _args[5];
lean_object* v_a_4739_ = _args[6];
lean_object* v___x_4740_ = _args[7];
lean_object* v___x_4741_ = _args[8];
lean_object* v___x_4742_ = _args[9];
lean_object* v___x_4743_ = _args[10];
lean_object* v_altVars_4744_ = _args[11];
lean_object* v___x_4745_ = _args[12];
lean_object* v___x_4746_ = _args[13];
lean_object* v_a_4747_ = _args[14];
lean_object* v___x_4748_ = _args[15];
lean_object* v___x_4749_ = _args[16];
lean_object* v___x_4750_ = _args[17];
lean_object* v___x_4751_ = _args[18];
lean_object* v___x_4752_ = _args[19];
lean_object* v___x_4753_ = _args[20];
lean_object* v___x_4754_ = _args[21];
lean_object* v_matchDeclName_4755_ = _args[22];
lean_object* v___x_4756_ = _args[23];
lean_object* v___x_4757_ = _args[24];
lean_object* v___x_4758_ = _args[25];
lean_object* v_heqs_4759_ = _args[26];
lean_object* v___y_4760_ = _args[27];
lean_object* v___y_4761_ = _args[28];
lean_object* v___y_4762_ = _args[29];
lean_object* v___y_4763_ = _args[30];
lean_object* v___y_4764_ = _args[31];
_start:
{
uint8_t v___x_21290__boxed_4765_; uint8_t v___x_21291__boxed_4766_; lean_object* v_res_4767_; 
v___x_21290__boxed_4765_ = lean_unbox(v___x_4745_);
v___x_21291__boxed_4766_ = lean_unbox(v___x_4746_);
v_res_4767_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4733_, v_args_4734_, v___x_4735_, v_overlaps_4736_, v_a_4737_, v_fst_4738_, v_a_4739_, v___x_4740_, v___x_4741_, v___x_4742_, v___x_4743_, v_altVars_4744_, v___x_21290__boxed_4765_, v___x_21291__boxed_4766_, v_a_4747_, v___x_4748_, v___x_4749_, v___x_4750_, v___x_4751_, v___x_4752_, v___x_4753_, v___x_4754_, v_matchDeclName_4755_, v___x_4756_, v___x_4757_, v___x_4758_, v_heqs_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___x_4754_);
lean_dec(v___x_4753_);
lean_dec(v___x_4750_);
lean_dec_ref(v_a_4747_);
lean_dec_ref(v_altVars_4744_);
lean_dec(v_fst_4738_);
lean_dec(v_a_4737_);
lean_dec_ref(v_overlaps_4736_);
lean_dec_ref(v_args_4734_);
return v_res_4767_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4770_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4771_ = lean_unsigned_to_nat(8u);
v___x_4772_ = lean_unsigned_to_nat(295u);
v___x_4773_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4774_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4775_ = l_mkPanicMessageWithDecl(v___x_4774_, v___x_4773_, v___x_4772_, v___x_4771_, v___x_4770_);
return v___x_4775_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4776_, lean_object* v___x_4777_, lean_object* v___y_4778_, lean_object* v___x_4779_, lean_object* v_overlaps_4780_, lean_object* v_a_4781_, lean_object* v_fst_4782_, lean_object* v___x_4783_, lean_object* v___x_4784_, uint8_t v___x_4785_, lean_object* v_a_4786_, lean_object* v___x_4787_, lean_object* v___x_4788_, lean_object* v___x_4789_, lean_object* v___x_4790_, lean_object* v___x_4791_, lean_object* v___x_4792_, lean_object* v_matchDeclName_4793_, lean_object* v___x_4794_, lean_object* v___x_4795_, lean_object* v___x_4796_, lean_object* v_altVars_4797_, lean_object* v_args_4798_, lean_object* v___mask_4799_, lean_object* v_altResultType_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
uint8_t v___x_4806_; lean_object* v___x_4807_; 
v___x_4806_ = 0;
v___x_4807_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4800_, v___f_4776_, v___x_4806_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_a_4808_; lean_object* v_start_4809_; lean_object* v_stop_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; uint8_t v___x_4813_; 
v_a_4808_ = lean_ctor_get(v___x_4807_, 0);
lean_inc(v_a_4808_);
lean_dec_ref_known(v___x_4807_, 1);
v_start_4809_ = lean_ctor_get(v___x_4777_, 1);
v_stop_4810_ = lean_ctor_get(v___x_4777_, 2);
v___x_4811_ = lean_array_get_size(v_a_4808_);
v___x_4812_ = lean_nat_sub(v_stop_4810_, v_start_4809_);
v___x_4813_ = lean_nat_dec_eq(v___x_4811_, v___x_4812_);
if (v___x_4813_ == 0)
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
lean_dec(v___x_4812_);
lean_dec(v_a_4808_);
lean_dec_ref(v_args_4798_);
lean_dec_ref(v_altVars_4797_);
lean_dec(v___x_4796_);
lean_dec(v___x_4795_);
lean_dec(v___x_4794_);
lean_dec(v_matchDeclName_4793_);
lean_dec(v___x_4792_);
lean_dec_ref(v___x_4791_);
lean_dec_ref(v___x_4790_);
lean_dec(v___x_4789_);
lean_dec_ref(v___x_4788_);
lean_dec(v___x_4787_);
lean_dec_ref(v_a_4786_);
lean_dec(v___x_4784_);
lean_dec_ref(v___x_4783_);
lean_dec(v_fst_4782_);
lean_dec(v_a_4781_);
lean_dec_ref(v_overlaps_4780_);
lean_dec(v___x_4779_);
lean_dec_ref(v___y_4778_);
lean_dec_ref(v___x_4777_);
v___x_4814_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4815_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v___x_4814_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
return v___x_4815_;
}
else
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___f_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4816_ = lean_box(v___x_4806_);
v___x_4817_ = lean_box(v___x_4785_);
lean_inc_ref(v___x_4777_);
lean_inc(v___x_4784_);
lean_inc(v_a_4808_);
v___f_4818_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4818_, 0, v___y_4778_);
lean_closure_set(v___f_4818_, 1, v_args_4798_);
lean_closure_set(v___f_4818_, 2, v___x_4779_);
lean_closure_set(v___f_4818_, 3, v_overlaps_4780_);
lean_closure_set(v___f_4818_, 4, v_a_4781_);
lean_closure_set(v___f_4818_, 5, v_fst_4782_);
lean_closure_set(v___f_4818_, 6, v_a_4808_);
lean_closure_set(v___f_4818_, 7, v___x_4811_);
lean_closure_set(v___f_4818_, 8, v___x_4783_);
lean_closure_set(v___f_4818_, 9, v___x_4784_);
lean_closure_set(v___f_4818_, 10, v___x_4777_);
lean_closure_set(v___f_4818_, 11, v_altVars_4797_);
lean_closure_set(v___f_4818_, 12, v___x_4816_);
lean_closure_set(v___f_4818_, 13, v___x_4817_);
lean_closure_set(v___f_4818_, 14, v_a_4786_);
lean_closure_set(v___f_4818_, 15, v___x_4787_);
lean_closure_set(v___f_4818_, 16, v___x_4788_);
lean_closure_set(v___f_4818_, 17, v___x_4789_);
lean_closure_set(v___f_4818_, 18, v___x_4790_);
lean_closure_set(v___f_4818_, 19, v___x_4791_);
lean_closure_set(v___f_4818_, 20, v___x_4812_);
lean_closure_set(v___f_4818_, 21, v___x_4792_);
lean_closure_set(v___f_4818_, 22, v_matchDeclName_4793_);
lean_closure_set(v___f_4818_, 23, v___x_4794_);
lean_closure_set(v___f_4818_, 24, v___x_4795_);
lean_closure_set(v___f_4818_, 25, v___x_4796_);
v___x_4819_ = lean_mk_empty_array_with_capacity(v___x_4784_);
v___x_4820_ = l_Array_toSubarray___redArg(v_a_4808_, v___x_4784_, v___x_4811_);
v___x_4821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4819_);
lean_ctor_set(v___x_4821_, 1, v___x_4820_);
v___x_4822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v___x_4777_, v___x_4821_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v_fst_4824_; uint8_t v___x_4825_; lean_object* v___x_4826_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4822_, 1);
v_fst_4824_ = lean_ctor_get(v_a_4823_, 0);
lean_inc(v_fst_4824_);
lean_dec(v_a_4823_);
v___x_4825_ = 0;
v___x_4826_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4824_, v___f_4818_, v___x_4825_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
return v___x_4826_;
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
lean_dec_ref(v___f_4818_);
v_a_4827_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4822_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4822_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
}
else
{
lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
lean_dec_ref(v_args_4798_);
lean_dec_ref(v_altVars_4797_);
lean_dec(v___x_4796_);
lean_dec(v___x_4795_);
lean_dec(v___x_4794_);
lean_dec(v_matchDeclName_4793_);
lean_dec(v___x_4792_);
lean_dec_ref(v___x_4791_);
lean_dec_ref(v___x_4790_);
lean_dec(v___x_4789_);
lean_dec_ref(v___x_4788_);
lean_dec(v___x_4787_);
lean_dec_ref(v_a_4786_);
lean_dec(v___x_4784_);
lean_dec_ref(v___x_4783_);
lean_dec(v_fst_4782_);
lean_dec(v_a_4781_);
lean_dec_ref(v_overlaps_4780_);
lean_dec(v___x_4779_);
lean_dec_ref(v___y_4778_);
lean_dec_ref(v___x_4777_);
v_a_4835_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4807_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v___x_4807_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4843_ = _args[0];
lean_object* v___x_4844_ = _args[1];
lean_object* v___y_4845_ = _args[2];
lean_object* v___x_4846_ = _args[3];
lean_object* v_overlaps_4847_ = _args[4];
lean_object* v_a_4848_ = _args[5];
lean_object* v_fst_4849_ = _args[6];
lean_object* v___x_4850_ = _args[7];
lean_object* v___x_4851_ = _args[8];
lean_object* v___x_4852_ = _args[9];
lean_object* v_a_4853_ = _args[10];
lean_object* v___x_4854_ = _args[11];
lean_object* v___x_4855_ = _args[12];
lean_object* v___x_4856_ = _args[13];
lean_object* v___x_4857_ = _args[14];
lean_object* v___x_4858_ = _args[15];
lean_object* v___x_4859_ = _args[16];
lean_object* v_matchDeclName_4860_ = _args[17];
lean_object* v___x_4861_ = _args[18];
lean_object* v___x_4862_ = _args[19];
lean_object* v___x_4863_ = _args[20];
lean_object* v_altVars_4864_ = _args[21];
lean_object* v_args_4865_ = _args[22];
lean_object* v___mask_4866_ = _args[23];
lean_object* v_altResultType_4867_ = _args[24];
lean_object* v___y_4868_ = _args[25];
lean_object* v___y_4869_ = _args[26];
lean_object* v___y_4870_ = _args[27];
lean_object* v___y_4871_ = _args[28];
lean_object* v___y_4872_ = _args[29];
_start:
{
uint8_t v___x_21677__boxed_4873_; lean_object* v_res_4874_; 
v___x_21677__boxed_4873_ = lean_unbox(v___x_4852_);
v_res_4874_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4843_, v___x_4844_, v___y_4845_, v___x_4846_, v_overlaps_4847_, v_a_4848_, v_fst_4849_, v___x_4850_, v___x_4851_, v___x_21677__boxed_4873_, v_a_4853_, v___x_4854_, v___x_4855_, v___x_4856_, v___x_4857_, v___x_4858_, v___x_4859_, v_matchDeclName_4860_, v___x_4861_, v___x_4862_, v___x_4863_, v_altVars_4864_, v_args_4865_, v___mask_4866_, v_altResultType_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec_ref(v___mask_4866_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4876_, lean_object* v_val_4877_, lean_object* v_matchDeclName_4878_, lean_object* v___x_4879_, lean_object* v___x_4880_, lean_object* v_a_4881_, lean_object* v___x_4882_, lean_object* v___x_4883_, lean_object* v___x_4884_, lean_object* v___x_4885_, lean_object* v___x_4886_, lean_object* v___x_4887_, lean_object* v_a_4888_, lean_object* v_b_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
uint8_t v___x_4895_; 
v___x_4895_ = lean_nat_dec_lt(v_a_4888_, v_upperBound_4876_);
if (v___x_4895_ == 0)
{
lean_object* v___x_4896_; 
lean_dec(v_a_4888_);
lean_dec(v___x_4887_);
lean_dec(v___x_4886_);
lean_dec_ref(v___x_4885_);
lean_dec_ref(v___x_4884_);
lean_dec_ref(v___x_4883_);
lean_dec(v___x_4882_);
lean_dec_ref(v_a_4881_);
lean_dec(v___x_4880_);
lean_dec_ref(v___x_4879_);
lean_dec(v_matchDeclName_4878_);
lean_dec_ref(v_val_4877_);
v___x_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4896_, 0, v_b_4889_);
return v___x_4896_;
}
else
{
lean_object* v_snd_4897_; lean_object* v_fst_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4962_; 
v_snd_4897_ = lean_ctor_get(v_b_4889_, 1);
v_fst_4898_ = lean_ctor_get(v_b_4889_, 0);
v_isSharedCheck_4962_ = !lean_is_exclusive(v_b_4889_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4900_ = v_b_4889_;
v_isShared_4901_ = v_isSharedCheck_4962_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_snd_4897_);
lean_inc(v_fst_4898_);
lean_dec(v_b_4889_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4962_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v_fst_4902_; lean_object* v_snd_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4961_; 
v_fst_4902_ = lean_ctor_get(v_snd_4897_, 0);
v_snd_4903_ = lean_ctor_get(v_snd_4897_, 1);
v_isSharedCheck_4961_ = !lean_is_exclusive(v_snd_4897_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4905_ = v_snd_4897_;
v_isShared_4906_ = v_isSharedCheck_4961_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_snd_4903_);
lean_inc(v_fst_4902_);
lean_dec(v_snd_4897_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4961_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v_altInfos_4907_; lean_object* v_overlaps_4908_; lean_object* v_start_4909_; lean_object* v_stop_4910_; lean_object* v___f_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___y_4923_; lean_object* v___x_4956_; uint8_t v___x_4957_; 
v_altInfos_4907_ = lean_ctor_get(v_val_4877_, 2);
v_overlaps_4908_ = lean_ctor_get(v_val_4877_, 5);
v_start_4909_ = lean_ctor_get(v___x_4885_, 1);
v_stop_4910_ = lean_ctor_get(v___x_4885_, 2);
v___f_4911_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4912_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4913_ = lean_unsigned_to_nat(0u);
v___x_4914_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4915_ = lean_unsigned_to_nat(1u);
v___x_4916_ = lean_box(0);
v___x_4917_ = lean_array_get_borrowed(v___x_4912_, v_altInfos_4907_, v_a_4888_);
v___x_4918_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4878_);
v___x_4919_ = l_Lean_Name_str___override(v_matchDeclName_4878_, v___x_4918_);
lean_inc(v_snd_4903_);
v___x_4920_ = lean_name_append_index_after(v___x_4919_, v_snd_4903_);
lean_inc(v___x_4920_);
v___x_4921_ = lean_array_push(v_fst_4898_, v___x_4920_);
v___x_4956_ = lean_nat_sub(v_stop_4910_, v_start_4909_);
v___x_4957_ = lean_nat_dec_lt(v_a_4888_, v___x_4956_);
lean_dec(v___x_4956_);
if (v___x_4957_ == 0)
{
lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4958_ = l_Lean_instInhabitedExpr;
v___x_4959_ = l_outOfBounds___redArg(v___x_4958_);
v___y_4923_ = v___x_4959_;
goto v___jp_4922_;
}
else
{
lean_object* v___x_4960_; 
v___x_4960_ = l_Subarray_get___redArg(v___x_4885_, v_a_4888_);
v___y_4923_ = v___x_4960_;
goto v___jp_4922_;
}
v___jp_4922_:
{
lean_object* v___x_4924_; lean_object* v___f_4925_; lean_object* v___x_4926_; 
v___x_4924_ = lean_box(v___x_4895_);
lean_inc(v___x_4887_);
lean_inc(v_matchDeclName_4878_);
lean_inc(v___x_4886_);
lean_inc_ref(v___x_4885_);
lean_inc_ref(v___x_4884_);
lean_inc_ref(v___x_4883_);
lean_inc(v___x_4882_);
lean_inc_ref(v_a_4881_);
lean_inc(v_fst_4902_);
lean_inc(v_a_4888_);
lean_inc_ref(v_overlaps_4908_);
lean_inc(v___x_4880_);
lean_inc_ref(v___y_4923_);
lean_inc_ref(v___x_4879_);
v___f_4925_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 30, 21);
lean_closure_set(v___f_4925_, 0, v___f_4911_);
lean_closure_set(v___f_4925_, 1, v___x_4879_);
lean_closure_set(v___f_4925_, 2, v___y_4923_);
lean_closure_set(v___f_4925_, 3, v___x_4880_);
lean_closure_set(v___f_4925_, 4, v_overlaps_4908_);
lean_closure_set(v___f_4925_, 5, v_a_4888_);
lean_closure_set(v___f_4925_, 6, v_fst_4902_);
lean_closure_set(v___f_4925_, 7, v___x_4914_);
lean_closure_set(v___f_4925_, 8, v___x_4913_);
lean_closure_set(v___f_4925_, 9, v___x_4924_);
lean_closure_set(v___f_4925_, 10, v_a_4881_);
lean_closure_set(v___f_4925_, 11, v___x_4882_);
lean_closure_set(v___f_4925_, 12, v___x_4883_);
lean_closure_set(v___f_4925_, 13, v___x_4915_);
lean_closure_set(v___f_4925_, 14, v___x_4884_);
lean_closure_set(v___f_4925_, 15, v___x_4885_);
lean_closure_set(v___f_4925_, 16, v___x_4886_);
lean_closure_set(v___f_4925_, 17, v_matchDeclName_4878_);
lean_closure_set(v___f_4925_, 18, v___x_4920_);
lean_closure_set(v___f_4925_, 19, v___x_4887_);
lean_closure_set(v___f_4925_, 20, v___x_4916_);
lean_inc(v___y_4893_);
lean_inc_ref(v___y_4892_);
lean_inc(v___y_4891_);
lean_inc_ref(v___y_4890_);
v___x_4926_ = lean_infer_type(v___y_4923_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v_a_4927_; lean_object* v___x_4928_; 
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
lean_inc(v_a_4927_);
lean_dec_ref_known(v___x_4926_, 1);
lean_inc(v___x_4917_);
v___x_4928_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4927_, v___x_4917_, v___f_4925_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4933_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref_known(v___x_4928_, 1);
v___x_4930_ = lean_array_push(v_fst_4902_, v_a_4929_);
v___x_4931_ = lean_nat_add(v_snd_4903_, v___x_4915_);
lean_dec(v_snd_4903_);
if (v_isShared_4906_ == 0)
{
lean_ctor_set(v___x_4905_, 1, v___x_4931_);
lean_ctor_set(v___x_4905_, 0, v___x_4930_);
v___x_4933_ = v___x_4905_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4930_);
lean_ctor_set(v_reuseFailAlloc_4939_, 1, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
lean_object* v___x_4935_; 
if (v_isShared_4901_ == 0)
{
lean_ctor_set(v___x_4900_, 1, v___x_4933_);
lean_ctor_set(v___x_4900_, 0, v___x_4921_);
v___x_4935_ = v___x_4900_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4921_);
lean_ctor_set(v_reuseFailAlloc_4938_, 1, v___x_4933_);
v___x_4935_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4936_; 
v___x_4936_ = lean_nat_add(v_a_4888_, v___x_4915_);
lean_dec(v_a_4888_);
v_a_4888_ = v___x_4936_;
v_b_4889_ = v___x_4935_;
goto _start;
}
}
}
else
{
lean_object* v_a_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
lean_dec_ref(v___x_4921_);
lean_del_object(v___x_4905_);
lean_dec(v_snd_4903_);
lean_dec(v_fst_4902_);
lean_del_object(v___x_4900_);
lean_dec(v_a_4888_);
lean_dec(v___x_4887_);
lean_dec(v___x_4886_);
lean_dec_ref(v___x_4885_);
lean_dec_ref(v___x_4884_);
lean_dec_ref(v___x_4883_);
lean_dec(v___x_4882_);
lean_dec_ref(v_a_4881_);
lean_dec(v___x_4880_);
lean_dec_ref(v___x_4879_);
lean_dec(v_matchDeclName_4878_);
lean_dec_ref(v_val_4877_);
v_a_4940_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4942_ = v___x_4928_;
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_a_4940_);
lean_dec(v___x_4928_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4940_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
lean_dec_ref(v___f_4925_);
lean_dec_ref(v___x_4921_);
lean_del_object(v___x_4905_);
lean_dec(v_snd_4903_);
lean_dec(v_fst_4902_);
lean_del_object(v___x_4900_);
lean_dec(v_a_4888_);
lean_dec(v___x_4887_);
lean_dec(v___x_4886_);
lean_dec_ref(v___x_4885_);
lean_dec_ref(v___x_4884_);
lean_dec_ref(v___x_4883_);
lean_dec(v___x_4882_);
lean_dec_ref(v_a_4881_);
lean_dec(v___x_4880_);
lean_dec_ref(v___x_4879_);
lean_dec(v_matchDeclName_4878_);
lean_dec_ref(v_val_4877_);
v_a_4948_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4926_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4926_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
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
lean_object* v_upperBound_4963_ = _args[0];
lean_object* v_val_4964_ = _args[1];
lean_object* v_matchDeclName_4965_ = _args[2];
lean_object* v___x_4966_ = _args[3];
lean_object* v___x_4967_ = _args[4];
lean_object* v_a_4968_ = _args[5];
lean_object* v___x_4969_ = _args[6];
lean_object* v___x_4970_ = _args[7];
lean_object* v___x_4971_ = _args[8];
lean_object* v___x_4972_ = _args[9];
lean_object* v___x_4973_ = _args[10];
lean_object* v___x_4974_ = _args[11];
lean_object* v_a_4975_ = _args[12];
lean_object* v_b_4976_ = _args[13];
lean_object* v___y_4977_ = _args[14];
lean_object* v___y_4978_ = _args[15];
lean_object* v___y_4979_ = _args[16];
lean_object* v___y_4980_ = _args[17];
lean_object* v___y_4981_ = _args[18];
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_4963_, v_val_4964_, v_matchDeclName_4965_, v___x_4966_, v___x_4967_, v_a_4968_, v___x_4969_, v___x_4970_, v___x_4971_, v___x_4972_, v___x_4973_, v___x_4974_, v_a_4975_, v_b_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
lean_dec(v___y_4978_);
lean_dec_ref(v___y_4977_);
lean_dec(v_upperBound_4963_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_4989_, lean_object* v___x_4990_, lean_object* v_matchDeclName_4991_, lean_object* v___x_4992_, lean_object* v_a_4993_, lean_object* v___x_4994_, lean_object* v___x_4995_, lean_object* v_xs_4996_, lean_object* v___matchResultType_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v_numParams_5003_; lean_object* v_numDiscrs_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v_lower_5010_; lean_object* v_upper_5011_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; uint8_t v___x_5042_; 
v_numParams_5003_ = lean_ctor_get(v_val_4989_, 0);
v_numDiscrs_5004_ = lean_ctor_get(v_val_4989_, 1);
v___x_5005_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5003_);
lean_inc_ref(v_xs_4996_);
v___x_5006_ = l_Array_toSubarray___redArg(v_xs_4996_, v___x_5005_, v_numParams_5003_);
v___x_5007_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_4989_);
v___x_5008_ = lean_array_get(v___x_4990_, v_xs_4996_, v___x_5007_);
lean_dec(v___x_5007_);
v___x_5039_ = lean_array_get_size(v_xs_4996_);
v___x_5040_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_4989_);
v___x_5041_ = lean_nat_sub(v___x_5039_, v___x_5040_);
lean_dec(v___x_5040_);
v___x_5042_ = lean_nat_dec_le(v___x_5041_, v___x_5005_);
if (v___x_5042_ == 0)
{
v_lower_5010_ = v___x_5041_;
v_upper_5011_ = v___x_5039_;
goto v___jp_5009_;
}
else
{
lean_dec(v___x_5041_);
v_lower_5010_ = v___x_5005_;
v_upper_5011_ = v___x_5039_;
goto v___jp_5009_;
}
v___jp_5009_:
{
lean_object* v___x_5012_; lean_object* v_start_5013_; lean_object* v_stop_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
lean_inc_ref(v_xs_4996_);
v___x_5012_ = l_Array_toSubarray___redArg(v_xs_4996_, v_lower_5010_, v_upper_5011_);
v_start_5013_ = lean_ctor_get(v___x_5012_, 1);
v_stop_5014_ = lean_ctor_get(v___x_5012_, 2);
v___x_5015_ = lean_unsigned_to_nat(1u);
v___x_5016_ = lean_nat_add(v_numParams_5003_, v___x_5015_);
v___x_5017_ = lean_nat_add(v___x_5016_, v_numDiscrs_5004_);
v___x_5018_ = lean_nat_sub(v_stop_5014_, v_start_5013_);
v___x_5019_ = l_Array_toSubarray___redArg(v_xs_4996_, v___x_5016_, v___x_5017_);
v___x_5020_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5018_);
v___x_5021_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5018_, v_val_4989_, v_matchDeclName_4991_, v___x_5019_, v___x_4992_, v_a_4993_, v___x_4994_, v___x_5006_, v___x_5008_, v___x_5012_, v___x_5018_, v___x_4995_, v___x_5005_, v___x_5020_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
lean_dec(v___x_5018_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5029_; 
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5029_ == 0)
{
lean_object* v_unused_5030_; 
v_unused_5030_ = lean_ctor_get(v___x_5021_, 0);
lean_dec(v_unused_5030_);
v___x_5023_ = v___x_5021_;
v_isShared_5024_ = v_isSharedCheck_5029_;
goto v_resetjp_5022_;
}
else
{
lean_dec(v___x_5021_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5029_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5025_; lean_object* v___x_5027_; 
v___x_5025_ = lean_box(0);
if (v_isShared_5024_ == 0)
{
lean_ctor_set(v___x_5023_, 0, v___x_5025_);
v___x_5027_ = v___x_5023_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v___x_5025_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
else
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5038_; 
v_a_5031_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5033_ = v___x_5021_;
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v___x_5021_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5043_, lean_object* v___x_5044_, lean_object* v_matchDeclName_5045_, lean_object* v___x_5046_, lean_object* v_a_5047_, lean_object* v___x_5048_, lean_object* v___x_5049_, lean_object* v_xs_5050_, lean_object* v___matchResultType_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5043_, v___x_5044_, v_matchDeclName_5045_, v___x_5046_, v_a_5047_, v___x_5048_, v___x_5049_, v_xs_5050_, v___matchResultType_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec_ref(v___matchResultType_5051_);
lean_dec_ref(v___x_5044_);
return v_res_5057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_){
_start:
{
uint8_t v_trackZetaDelta_5064_; lean_object* v_zetaDeltaSet_5065_; lean_object* v_lctx_5066_; lean_object* v_localInstances_5067_; lean_object* v_defEqCtx_x3f_5068_; lean_object* v_synthPendingDepth_5069_; lean_object* v_customCanUnfoldPredicate_x3f_5070_; uint8_t v_univApprox_5071_; uint8_t v_inTypeClassResolution_5072_; uint8_t v_cacheInferType_5073_; lean_object* v___x_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5117_; 
v_trackZetaDelta_5064_ = lean_ctor_get_uint8(v_a_5059_, sizeof(void*)*7);
v_zetaDeltaSet_5065_ = lean_ctor_get(v_a_5059_, 1);
lean_inc(v_zetaDeltaSet_5065_);
v_lctx_5066_ = lean_ctor_get(v_a_5059_, 2);
lean_inc_ref(v_lctx_5066_);
v_localInstances_5067_ = lean_ctor_get(v_a_5059_, 3);
lean_inc_ref(v_localInstances_5067_);
v_defEqCtx_x3f_5068_ = lean_ctor_get(v_a_5059_, 4);
lean_inc(v_defEqCtx_x3f_5068_);
v_synthPendingDepth_5069_ = lean_ctor_get(v_a_5059_, 5);
lean_inc(v_synthPendingDepth_5069_);
v_customCanUnfoldPredicate_x3f_5070_ = lean_ctor_get(v_a_5059_, 6);
lean_inc(v_customCanUnfoldPredicate_x3f_5070_);
v_univApprox_5071_ = lean_ctor_get_uint8(v_a_5059_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5072_ = lean_ctor_get_uint8(v_a_5059_, sizeof(void*)*7 + 2);
v_cacheInferType_5073_ = lean_ctor_get_uint8(v_a_5059_, sizeof(void*)*7 + 3);
v___x_5074_ = l_Lean_Meta_Context_config(v_a_5059_);
v_isSharedCheck_5117_ = !lean_is_exclusive(v_a_5059_);
if (v_isSharedCheck_5117_ == 0)
{
lean_object* v_unused_5118_; lean_object* v_unused_5119_; lean_object* v_unused_5120_; lean_object* v_unused_5121_; lean_object* v_unused_5122_; lean_object* v_unused_5123_; lean_object* v_unused_5124_; 
v_unused_5118_ = lean_ctor_get(v_a_5059_, 6);
lean_dec(v_unused_5118_);
v_unused_5119_ = lean_ctor_get(v_a_5059_, 5);
lean_dec(v_unused_5119_);
v_unused_5120_ = lean_ctor_get(v_a_5059_, 4);
lean_dec(v_unused_5120_);
v_unused_5121_ = lean_ctor_get(v_a_5059_, 3);
lean_dec(v_unused_5121_);
v_unused_5122_ = lean_ctor_get(v_a_5059_, 2);
lean_dec(v_unused_5122_);
v_unused_5123_ = lean_ctor_get(v_a_5059_, 1);
lean_dec(v_unused_5123_);
v_unused_5124_ = lean_ctor_get(v_a_5059_, 0);
lean_dec(v_unused_5124_);
v___x_5076_ = v_a_5059_;
v_isShared_5077_ = v_isSharedCheck_5117_;
goto v_resetjp_5075_;
}
else
{
lean_dec(v_a_5059_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5117_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5078_; uint64_t v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5083_; 
v___x_5078_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5074_);
v___x_5079_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5078_);
v___x_5080_ = l_Lean_instInhabitedExpr;
v___x_5081_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5081_, 0, v___x_5078_);
lean_ctor_set_uint64(v___x_5081_, sizeof(void*)*1, v___x_5079_);
lean_inc(v_customCanUnfoldPredicate_x3f_5070_);
lean_inc(v_synthPendingDepth_5069_);
lean_inc(v_defEqCtx_x3f_5068_);
lean_inc_ref(v_localInstances_5067_);
lean_inc_ref(v_lctx_5066_);
lean_inc(v_zetaDeltaSet_5065_);
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 0, v___x_5081_);
v___x_5083_ = v___x_5076_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5081_);
lean_ctor_set(v_reuseFailAlloc_5116_, 1, v_zetaDeltaSet_5065_);
lean_ctor_set(v_reuseFailAlloc_5116_, 2, v_lctx_5066_);
lean_ctor_set(v_reuseFailAlloc_5116_, 3, v_localInstances_5067_);
lean_ctor_set(v_reuseFailAlloc_5116_, 4, v_defEqCtx_x3f_5068_);
lean_ctor_set(v_reuseFailAlloc_5116_, 5, v_synthPendingDepth_5069_);
lean_ctor_set(v_reuseFailAlloc_5116_, 6, v_customCanUnfoldPredicate_x3f_5070_);
lean_ctor_set_uint8(v_reuseFailAlloc_5116_, sizeof(void*)*7, v_trackZetaDelta_5064_);
lean_ctor_set_uint8(v_reuseFailAlloc_5116_, sizeof(void*)*7 + 1, v_univApprox_5071_);
lean_ctor_set_uint8(v_reuseFailAlloc_5116_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5072_);
lean_ctor_set_uint8(v_reuseFailAlloc_5116_, sizeof(void*)*7 + 3, v_cacheInferType_5073_);
v___x_5083_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; uint64_t v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5084_ = l_Lean_Meta_Context_config(v___x_5083_);
lean_dec_ref(v___x_5083_);
v___x_5085_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5084_);
v___x_5086_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5085_);
v___x_5087_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5087_, 0, v___x_5085_);
lean_ctor_set_uint64(v___x_5087_, sizeof(void*)*1, v___x_5086_);
v___x_5088_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5088_, 0, v___x_5087_);
lean_ctor_set(v___x_5088_, 1, v_zetaDeltaSet_5065_);
lean_ctor_set(v___x_5088_, 2, v_lctx_5066_);
lean_ctor_set(v___x_5088_, 3, v_localInstances_5067_);
lean_ctor_set(v___x_5088_, 4, v_defEqCtx_x3f_5068_);
lean_ctor_set(v___x_5088_, 5, v_synthPendingDepth_5069_);
lean_ctor_set(v___x_5088_, 6, v_customCanUnfoldPredicate_x3f_5070_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*7, v_trackZetaDelta_5064_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*7 + 1, v_univApprox_5071_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5072_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*7 + 3, v_cacheInferType_5073_);
lean_inc(v_matchDeclName_5058_);
v___x_5089_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5058_, v___x_5088_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5089_) == 0)
{
lean_object* v_a_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v_a_5095_; 
v_a_5090_ = lean_ctor_get(v___x_5089_, 0);
lean_inc(v_a_5090_);
lean_dec_ref_known(v___x_5089_, 1);
v___x_5091_ = l_Lean_ConstantInfo_levelParams(v_a_5090_);
v___x_5092_ = lean_box(0);
lean_inc(v___x_5091_);
v___x_5093_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v___x_5091_, v___x_5092_);
lean_inc(v_matchDeclName_5058_);
v___x_5094_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_5058_, v_a_5062_);
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
lean_inc(v_a_5095_);
lean_dec_ref(v___x_5094_);
if (lean_obj_tag(v_a_5095_) == 1)
{
lean_object* v_val_5096_; lean_object* v___x_5097_; lean_object* v___f_5098_; lean_object* v___x_5099_; uint8_t v___x_5100_; lean_object* v___x_5101_; 
v_val_5096_ = lean_ctor_get(v_a_5095_, 0);
lean_inc(v_val_5096_);
lean_dec_ref_known(v_a_5095_, 1);
v___x_5097_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5096_);
lean_inc(v_a_5090_);
v___f_5098_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5098_, 0, v_val_5096_);
lean_closure_set(v___f_5098_, 1, v___x_5080_);
lean_closure_set(v___f_5098_, 2, v_matchDeclName_5058_);
lean_closure_set(v___f_5098_, 3, v___x_5097_);
lean_closure_set(v___f_5098_, 4, v_a_5090_);
lean_closure_set(v___f_5098_, 5, v___x_5093_);
lean_closure_set(v___f_5098_, 6, v___x_5091_);
v___x_5099_ = l_Lean_ConstantInfo_type(v_a_5090_);
lean_dec(v_a_5090_);
v___x_5100_ = 0;
v___x_5101_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5099_, v___f_5098_, v___x_5100_, v___x_5100_, v___x_5088_, v_a_5060_, v_a_5061_, v_a_5062_);
lean_dec_ref_known(v___x_5088_, 7);
return v___x_5101_;
}
else
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
lean_dec(v_a_5095_);
lean_dec(v___x_5093_);
lean_dec(v___x_5091_);
lean_dec(v_a_5090_);
v___x_5102_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5103_ = l_Lean_MessageData_ofName(v_matchDeclName_5058_);
v___x_5104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5102_);
lean_ctor_set(v___x_5104_, 1, v___x_5103_);
v___x_5105_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5104_);
lean_ctor_set(v___x_5106_, 1, v___x_5105_);
v___x_5107_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5106_, v___x_5088_, v_a_5060_, v_a_5061_, v_a_5062_);
lean_dec_ref_known(v___x_5088_, 7);
return v___x_5107_;
}
}
else
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5115_; 
lean_dec_ref_known(v___x_5088_, 7);
lean_dec(v_matchDeclName_5058_);
v_a_5108_ = lean_ctor_get(v___x_5089_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5089_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5110_ = v___x_5089_;
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v___x_5089_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5115_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5113_; 
if (v_isShared_5111_ == 0)
{
v___x_5113_ = v___x_5110_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5108_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
return v___x_5113_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_);
lean_dec(v_a_5129_);
lean_dec_ref(v_a_5128_);
lean_dec(v_a_5127_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v_inst_5132_, lean_object* v_R_5133_, lean_object* v_a_5134_, lean_object* v_b_5135_, lean_object* v_c_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_){
_start:
{
lean_object* v___x_5142_; 
v___x_5142_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_5134_, v_b_5135_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
return v___x_5142_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v_inst_5143_, lean_object* v_R_5144_, lean_object* v_a_5145_, lean_object* v_b_5146_, lean_object* v_c_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_inst_5143_, v_R_5144_, v_a_5145_, v_b_5146_, v_c_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_);
lean_dec(v___y_5151_);
lean_dec_ref(v___y_5150_);
lean_dec(v___y_5149_);
lean_dec_ref(v___y_5148_);
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5154_, lean_object* v_val_5155_, lean_object* v_matchDeclName_5156_, lean_object* v___x_5157_, lean_object* v___x_5158_, lean_object* v_a_5159_, lean_object* v___x_5160_, lean_object* v___x_5161_, lean_object* v___x_5162_, lean_object* v___x_5163_, lean_object* v___x_5164_, lean_object* v___x_5165_, lean_object* v_inst_5166_, lean_object* v_R_5167_, lean_object* v_a_5168_, lean_object* v_b_5169_, lean_object* v_c_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_){
_start:
{
lean_object* v___x_5176_; 
v___x_5176_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5154_, v_val_5155_, v_matchDeclName_5156_, v___x_5157_, v___x_5158_, v_a_5159_, v___x_5160_, v___x_5161_, v___x_5162_, v___x_5163_, v___x_5164_, v___x_5165_, v_a_5168_, v_b_5169_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_);
return v___x_5176_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5177_ = _args[0];
lean_object* v_val_5178_ = _args[1];
lean_object* v_matchDeclName_5179_ = _args[2];
lean_object* v___x_5180_ = _args[3];
lean_object* v___x_5181_ = _args[4];
lean_object* v_a_5182_ = _args[5];
lean_object* v___x_5183_ = _args[6];
lean_object* v___x_5184_ = _args[7];
lean_object* v___x_5185_ = _args[8];
lean_object* v___x_5186_ = _args[9];
lean_object* v___x_5187_ = _args[10];
lean_object* v___x_5188_ = _args[11];
lean_object* v_inst_5189_ = _args[12];
lean_object* v_R_5190_ = _args[13];
lean_object* v_a_5191_ = _args[14];
lean_object* v_b_5192_ = _args[15];
lean_object* v_c_5193_ = _args[16];
lean_object* v___y_5194_ = _args[17];
lean_object* v___y_5195_ = _args[18];
lean_object* v___y_5196_ = _args[19];
lean_object* v___y_5197_ = _args[20];
lean_object* v___y_5198_ = _args[21];
_start:
{
lean_object* v_res_5199_; 
v_res_5199_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5177_, v_val_5178_, v_matchDeclName_5179_, v___x_5180_, v___x_5181_, v_a_5182_, v___x_5183_, v___x_5184_, v___x_5185_, v___x_5186_, v___x_5187_, v___x_5188_, v_inst_5189_, v_R_5190_, v_a_5191_, v_b_5192_, v_c_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_);
lean_dec(v___y_5197_);
lean_dec_ref(v___y_5196_);
lean_dec(v___y_5195_);
lean_dec_ref(v___y_5194_);
lean_dec(v_upperBound_5177_);
return v_res_5199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5200_, lean_object* v_matchDeclName_5201_, lean_object* v_a_5202_, lean_object* v_b_5203_){
_start:
{
uint8_t v___x_5205_; 
v___x_5205_ = lean_nat_dec_lt(v_a_5202_, v_upperBound_5200_);
if (v___x_5205_ == 0)
{
lean_object* v___x_5206_; 
lean_dec(v_a_5202_);
lean_dec(v_matchDeclName_5201_);
v___x_5206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5206_, 0, v_b_5203_);
return v___x_5206_;
}
else
{
lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
v___x_5207_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5201_);
v___x_5208_ = l_Lean_Name_str___override(v_matchDeclName_5201_, v___x_5207_);
v___x_5209_ = lean_unsigned_to_nat(1u);
v___x_5210_ = lean_nat_add(v_a_5202_, v___x_5209_);
lean_dec(v_a_5202_);
lean_inc(v___x_5210_);
v___x_5211_ = lean_name_append_index_after(v___x_5208_, v___x_5210_);
v___x_5212_ = lean_array_push(v_b_5203_, v___x_5211_);
v_a_5202_ = v___x_5210_;
v_b_5203_ = v___x_5212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5214_, lean_object* v_matchDeclName_5215_, lean_object* v_a_5216_, lean_object* v_b_5217_, lean_object* v___y_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5214_, v_matchDeclName_5215_, v_a_5216_, v_b_5217_);
lean_dec(v_upperBound_5214_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_){
_start:
{
lean_object* v___x_5226_; lean_object* v_firstEqnName_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v___x_5226_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5220_, 3);
v_firstEqnName_5227_ = l_Lean_Name_str___override(v_matchDeclName_5220_, v___x_5226_);
v___x_5228_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5228_, 0, v_matchDeclName_5220_);
v___x_5229_ = l_Lean_Meta_realizeConst(v_matchDeclName_5220_, v_firstEqnName_5227_, v___x_5228_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v___x_5230_; lean_object* v_a_5231_; 
lean_dec_ref_known(v___x_5229_, 1);
lean_inc(v_matchDeclName_5220_);
v___x_5230_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_5220_, v_a_5224_);
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_a_5231_);
lean_dec_ref(v___x_5230_);
if (lean_obj_tag(v_a_5231_) == 1)
{
lean_object* v_val_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
lean_dec(v_a_5222_);
lean_dec_ref(v_a_5221_);
v_val_5232_ = lean_ctor_get(v_a_5231_, 0);
lean_inc(v_val_5232_);
lean_dec_ref_known(v_a_5231_, 1);
v___x_5233_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5232_);
lean_dec(v_val_5232_);
v___x_5234_ = lean_unsigned_to_nat(0u);
v___x_5235_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7));
v___x_5236_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5233_, v_matchDeclName_5220_, v___x_5234_, v___x_5235_);
lean_dec(v___x_5233_);
return v___x_5236_;
}
else
{
lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; 
lean_dec(v_a_5231_);
v___x_5237_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5238_ = l_Lean_MessageData_ofName(v_matchDeclName_5220_);
v___x_5239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5237_);
lean_ctor_set(v___x_5239_, 1, v___x_5238_);
v___x_5240_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5241_, 0, v___x_5239_);
lean_ctor_set(v___x_5241_, 1, v___x_5240_);
v___x_5242_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5241_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
lean_dec(v_a_5222_);
lean_dec_ref(v_a_5221_);
return v___x_5242_;
}
}
else
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5250_; 
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
lean_dec(v_a_5222_);
lean_dec_ref(v_a_5221_);
lean_dec(v_matchDeclName_5220_);
v_a_5243_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5229_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5229_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5248_; 
if (v_isShared_5246_ == 0)
{
v___x_5248_ = v___x_5245_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_a_5243_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
return v___x_5248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_){
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = lean_get_congr_match_equations_for(v_matchDeclName_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5258_, lean_object* v_matchDeclName_5259_, lean_object* v_inst_5260_, lean_object* v_R_5261_, lean_object* v_a_5262_, lean_object* v_b_5263_, lean_object* v_c_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
lean_object* v___x_5270_; 
v___x_5270_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5258_, v_matchDeclName_5259_, v_a_5262_, v_b_5263_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5271_, lean_object* v_matchDeclName_5272_, lean_object* v_inst_5273_, lean_object* v_R_5274_, lean_object* v_a_5275_, lean_object* v_b_5276_, lean_object* v_c_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v_res_5283_; 
v_res_5283_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5271_, v_matchDeclName_5272_, v_inst_5273_, v_R_5274_, v_a_5275_, v_b_5276_, v_c_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_);
lean_dec(v___y_5281_);
lean_dec_ref(v___y_5280_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v_upperBound_5271_);
return v_res_5283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5334_ = lean_unsigned_to_nat(3248161880u);
v___x_5335_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5336_ = l_Lean_Name_num___override(v___x_5335_, v___x_5334_);
return v___x_5336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; 
v___x_5338_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5339_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5340_ = l_Lean_Name_str___override(v___x_5339_, v___x_5338_);
return v___x_5340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; 
v___x_5342_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5343_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5344_ = l_Lean_Name_str___override(v___x_5343_, v___x_5342_);
return v___x_5344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; 
v___x_5345_ = lean_unsigned_to_nat(2u);
v___x_5346_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5347_ = l_Lean_Name_num___override(v___x_5346_, v___x_5345_);
return v___x_5347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5349_; uint8_t v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; 
v___x_5349_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
v___x_5350_ = 0;
v___x_5351_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5352_ = l_Lean_registerTraceClass(v___x_5349_, v___x_5350_, v___x_5351_);
return v___x_5352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5353_){
_start:
{
lean_object* v_res_5354_; 
v_res_5354_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5355_, lean_object* v_n_5356_){
_start:
{
if (lean_obj_tag(v_n_5356_) == 1)
{
lean_object* v_pre_5357_; lean_object* v_str_5358_; uint8_t v___x_5364_; 
v_pre_5357_ = lean_ctor_get(v_n_5356_, 0);
lean_inc(v_pre_5357_);
v_str_5358_ = lean_ctor_get(v_n_5356_, 1);
lean_inc_ref_n(v_str_5358_, 2);
lean_dec_ref_known(v_n_5356_, 2);
v___x_5364_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5358_);
if (v___x_5364_ == 0)
{
lean_object* v___x_5365_; uint8_t v___x_5366_; 
v___x_5365_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5366_ = lean_string_dec_eq(v_str_5358_, v___x_5365_);
lean_dec_ref(v_str_5358_);
if (v___x_5366_ == 0)
{
lean_object* v___x_5367_; 
lean_dec(v_pre_5357_);
lean_dec_ref(v_env_5355_);
v___x_5367_ = lean_box(0);
return v___x_5367_;
}
else
{
goto v___jp_5359_;
}
}
else
{
lean_dec_ref(v_str_5358_);
goto v___jp_5359_;
}
v___jp_5359_:
{
lean_object* v___x_5360_; 
v___x_5360_ = l_Lean_privateToUserName_x3f(v_pre_5357_);
if (lean_obj_tag(v___x_5360_) == 0)
{
lean_dec_ref(v_env_5355_);
return v___x_5360_;
}
else
{
lean_object* v_val_5361_; uint8_t v___x_5362_; 
v_val_5361_ = lean_ctor_get(v___x_5360_, 0);
lean_inc(v_val_5361_);
v___x_5362_ = l_Lean_Meta_isMatcherCore(v_env_5355_, v_val_5361_);
if (v___x_5362_ == 0)
{
lean_object* v___x_5363_; 
lean_dec_ref_known(v___x_5360_, 1);
v___x_5363_ = lean_box(0);
return v___x_5363_;
}
else
{
return v___x_5360_;
}
}
}
}
else
{
lean_object* v___x_5368_; 
lean_dec(v_n_5356_);
lean_dec_ref(v_env_5355_);
v___x_5368_ = lean_box(0);
return v___x_5368_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5369_, lean_object* v_x2_5370_){
_start:
{
lean_object* v___x_5371_; 
v___x_5371_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5369_, v_x2_5370_);
if (lean_obj_tag(v___x_5371_) == 0)
{
uint8_t v___x_5372_; 
v___x_5372_ = 0;
return v___x_5372_;
}
else
{
uint8_t v___x_5373_; 
lean_dec_ref_known(v___x_5371_, 1);
v___x_5373_ = 1;
return v___x_5373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5374_, lean_object* v_x2_5375_){
_start:
{
uint8_t v_res_5376_; lean_object* v_r_5377_; 
v_res_5376_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5374_, v_x2_5375_);
v_r_5377_ = lean_box(v_res_5376_);
return v_r_5377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5380_; lean_object* v___x_5381_; 
v___f_5380_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5381_ = l_Lean_registerReservedNamePredicate(v___f_5380_);
return v___x_5381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5382_){
_start:
{
lean_object* v_res_5383_; 
v_res_5383_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5383_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5390_; uint64_t v___x_5391_; 
v___x_5390_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5391_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5390_);
return v___x_5391_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; 
v___x_5392_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5393_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5394_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5394_, 0, v___x_5393_);
lean_ctor_set_uint64(v___x_5394_, sizeof(void*)*1, v___x_5392_);
return v___x_5394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5397_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5398_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5399_ = lean_unsigned_to_nat(0u);
v___x_5400_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5399_);
lean_ctor_set(v___x_5400_, 1, v___x_5399_);
lean_ctor_set(v___x_5400_, 2, v___x_5399_);
lean_ctor_set(v___x_5400_, 3, v___x_5399_);
lean_ctor_set(v___x_5400_, 4, v___x_5398_);
lean_ctor_set(v___x_5400_, 5, v___x_5398_);
lean_ctor_set(v___x_5400_, 6, v___x_5398_);
lean_ctor_set(v___x_5400_, 7, v___x_5398_);
lean_ctor_set(v___x_5400_, 8, v___x_5398_);
lean_ctor_set(v___x_5400_, 9, v___x_5398_);
lean_ctor_set(v___x_5400_, 10, v___x_5398_);
lean_ctor_set(v___x_5400_, 11, v___x_5397_);
return v___x_5400_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5401_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5402_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5401_);
lean_ctor_set(v___x_5402_, 1, v___x_5401_);
lean_ctor_set(v___x_5402_, 2, v___x_5401_);
lean_ctor_set(v___x_5402_, 3, v___x_5401_);
lean_ctor_set(v___x_5402_, 4, v___x_5401_);
lean_ctor_set(v___x_5402_, 5, v___x_5401_);
return v___x_5402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5403_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5404_, 0, v___x_5403_);
lean_ctor_set(v___x_5404_, 1, v___x_5403_);
lean_ctor_set(v___x_5404_, 2, v___x_5403_);
lean_ctor_set(v___x_5404_, 3, v___x_5403_);
lean_ctor_set(v___x_5404_, 4, v___x_5403_);
return v___x_5404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5405_, lean_object* v_name_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_){
_start:
{
lean_object* v___x_5410_; lean_object* v_env_5411_; lean_object* v___x_5412_; 
v___x_5410_ = lean_st_ref_get(v___y_5408_);
v_env_5411_ = lean_ctor_get(v___x_5410_, 0);
lean_inc_ref(v_env_5411_);
lean_dec(v___x_5410_);
v___x_5412_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5411_, v_name_5406_);
if (lean_obj_tag(v___x_5412_) == 1)
{
lean_object* v_val_5413_; uint8_t v___x_5414_; uint8_t v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
v_val_5413_ = lean_ctor_get(v___x_5412_, 0);
lean_inc(v_val_5413_);
lean_dec_ref_known(v___x_5412_, 1);
v___x_5414_ = 0;
v___x_5415_ = 1;
v___x_5416_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5417_ = lean_unsigned_to_nat(0u);
v___x_5418_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5419_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5420_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5421_ = lean_box(0);
lean_inc(v___x_5405_);
v___x_5422_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5422_, 0, v___x_5416_);
lean_ctor_set(v___x_5422_, 1, v___x_5405_);
lean_ctor_set(v___x_5422_, 2, v___x_5419_);
lean_ctor_set(v___x_5422_, 3, v___x_5420_);
lean_ctor_set(v___x_5422_, 4, v___x_5421_);
lean_ctor_set(v___x_5422_, 5, v___x_5417_);
lean_ctor_set(v___x_5422_, 6, v___x_5421_);
lean_ctor_set_uint8(v___x_5422_, sizeof(void*)*7, v___x_5414_);
lean_ctor_set_uint8(v___x_5422_, sizeof(void*)*7 + 1, v___x_5414_);
lean_ctor_set_uint8(v___x_5422_, sizeof(void*)*7 + 2, v___x_5414_);
lean_ctor_set_uint8(v___x_5422_, sizeof(void*)*7 + 3, v___x_5415_);
v___x_5423_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5424_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5425_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5426_, 0, v___x_5423_);
lean_ctor_set(v___x_5426_, 1, v___x_5424_);
lean_ctor_set(v___x_5426_, 2, v___x_5405_);
lean_ctor_set(v___x_5426_, 3, v___x_5418_);
lean_ctor_set(v___x_5426_, 4, v___x_5425_);
v___x_5427_ = lean_st_mk_ref(v___x_5426_);
lean_inc(v___y_5408_);
lean_inc_ref(v___y_5407_);
lean_inc(v___x_5427_);
v___x_5428_ = lean_get_match_equations_for(v_val_5413_, v___x_5422_, v___x_5427_, v___y_5407_, v___y_5408_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5437_; 
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5437_ == 0)
{
lean_object* v_unused_5438_; 
v_unused_5438_ = lean_ctor_get(v___x_5428_, 0);
lean_dec(v_unused_5438_);
v___x_5430_ = v___x_5428_;
v_isShared_5431_ = v_isSharedCheck_5437_;
goto v_resetjp_5429_;
}
else
{
lean_dec(v___x_5428_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5437_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5435_; 
v___x_5432_ = lean_st_ref_get(v___x_5427_);
lean_dec(v___x_5427_);
lean_dec(v___x_5432_);
v___x_5433_ = lean_box(v___x_5415_);
if (v_isShared_5431_ == 0)
{
lean_ctor_set(v___x_5430_, 0, v___x_5433_);
v___x_5435_ = v___x_5430_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v___x_5433_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
return v___x_5435_;
}
}
}
else
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5446_; 
lean_dec(v___x_5427_);
v_a_5439_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5441_ = v___x_5428_;
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5428_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5444_; 
if (v_isShared_5442_ == 0)
{
v___x_5444_ = v___x_5441_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
}
else
{
uint8_t v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; 
lean_dec(v___x_5412_);
lean_dec(v___x_5405_);
v___x_5447_ = 0;
v___x_5448_ = lean_box(v___x_5447_);
v___x_5449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5449_, 0, v___x_5448_);
return v___x_5449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5450_, lean_object* v_name_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_){
_start:
{
lean_object* v_res_5455_; 
v_res_5455_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5450_, v_name_5451_, v___y_5452_, v___y_5453_);
lean_dec(v___y_5453_);
lean_dec_ref(v___y_5452_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5459_; lean_object* v___x_5460_; 
v___f_5459_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5460_ = l_Lean_registerReservedNameAction(v___f_5459_);
return v___x_5460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5463_, lean_object* v_n_5464_){
_start:
{
if (lean_obj_tag(v_n_5464_) == 1)
{
lean_object* v_pre_5465_; lean_object* v_str_5466_; uint8_t v___x_5467_; 
v_pre_5465_ = lean_ctor_get(v_n_5464_, 0);
lean_inc(v_pre_5465_);
v_str_5466_ = lean_ctor_get(v_n_5464_, 1);
lean_inc_ref(v_str_5466_);
lean_dec_ref_known(v_n_5464_, 2);
v___x_5467_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5466_);
if (v___x_5467_ == 0)
{
lean_object* v___x_5468_; 
lean_dec(v_pre_5465_);
lean_dec_ref(v_env_5463_);
v___x_5468_ = lean_box(0);
return v___x_5468_;
}
else
{
uint8_t v___x_5469_; 
lean_inc(v_pre_5465_);
v___x_5469_ = l_Lean_Meta_isMatcherCore(v_env_5463_, v_pre_5465_);
if (v___x_5469_ == 0)
{
lean_object* v___x_5470_; 
lean_dec(v_pre_5465_);
v___x_5470_ = lean_box(0);
return v___x_5470_;
}
else
{
lean_object* v___x_5471_; 
v___x_5471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5471_, 0, v_pre_5465_);
return v___x_5471_;
}
}
}
else
{
lean_object* v___x_5472_; 
lean_dec(v_n_5464_);
lean_dec_ref(v_env_5463_);
v___x_5472_ = lean_box(0);
return v___x_5472_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5473_, lean_object* v_x2_5474_){
_start:
{
lean_object* v___x_5475_; 
v___x_5475_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5473_, v_x2_5474_);
if (lean_obj_tag(v___x_5475_) == 0)
{
uint8_t v___x_5476_; 
v___x_5476_ = 0;
return v___x_5476_;
}
else
{
uint8_t v___x_5477_; 
lean_dec_ref_known(v___x_5475_, 1);
v___x_5477_ = 1;
return v___x_5477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5478_, lean_object* v_x2_5479_){
_start:
{
uint8_t v_res_5480_; lean_object* v_r_5481_; 
v_res_5480_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5478_, v_x2_5479_);
v_r_5481_ = lean_box(v_res_5480_);
return v_r_5481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5484_; lean_object* v___x_5485_; 
v___f_5484_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5485_ = l_Lean_registerReservedNamePredicate(v___f_5484_);
return v___x_5485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5486_){
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5488_, lean_object* v_name_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_){
_start:
{
lean_object* v___x_5493_; lean_object* v_env_5494_; lean_object* v___x_5495_; 
v___x_5493_ = lean_st_ref_get(v___y_5491_);
v_env_5494_ = lean_ctor_get(v___x_5493_, 0);
lean_inc_ref(v_env_5494_);
lean_dec(v___x_5493_);
v___x_5495_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5494_, v_name_5489_);
if (lean_obj_tag(v___x_5495_) == 1)
{
lean_object* v_val_5496_; uint8_t v___x_5497_; uint8_t v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; 
v_val_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_val_5496_);
lean_dec_ref_known(v___x_5495_, 1);
v___x_5497_ = 0;
v___x_5498_ = 1;
v___x_5499_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5500_ = lean_unsigned_to_nat(32u);
v___x_5501_ = lean_mk_empty_array_with_capacity(v___x_5500_);
lean_dec_ref(v___x_5501_);
v___x_5502_ = lean_unsigned_to_nat(0u);
v___x_5503_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5504_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5505_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5506_ = lean_box(0);
lean_inc(v___x_5488_);
v___x_5507_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5507_, 0, v___x_5499_);
lean_ctor_set(v___x_5507_, 1, v___x_5488_);
lean_ctor_set(v___x_5507_, 2, v___x_5504_);
lean_ctor_set(v___x_5507_, 3, v___x_5505_);
lean_ctor_set(v___x_5507_, 4, v___x_5506_);
lean_ctor_set(v___x_5507_, 5, v___x_5502_);
lean_ctor_set(v___x_5507_, 6, v___x_5506_);
lean_ctor_set_uint8(v___x_5507_, sizeof(void*)*7, v___x_5497_);
lean_ctor_set_uint8(v___x_5507_, sizeof(void*)*7 + 1, v___x_5497_);
lean_ctor_set_uint8(v___x_5507_, sizeof(void*)*7 + 2, v___x_5497_);
lean_ctor_set_uint8(v___x_5507_, sizeof(void*)*7 + 3, v___x_5498_);
v___x_5508_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5509_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5510_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5511_, 0, v___x_5508_);
lean_ctor_set(v___x_5511_, 1, v___x_5509_);
lean_ctor_set(v___x_5511_, 2, v___x_5488_);
lean_ctor_set(v___x_5511_, 3, v___x_5503_);
lean_ctor_set(v___x_5511_, 4, v___x_5510_);
v___x_5512_ = lean_st_mk_ref(v___x_5511_);
lean_inc(v___y_5491_);
lean_inc_ref(v___y_5490_);
lean_inc(v___x_5512_);
v___x_5513_ = lean_get_congr_match_equations_for(v_val_5496_, v___x_5507_, v___x_5512_, v___y_5490_, v___y_5491_);
if (lean_obj_tag(v___x_5513_) == 0)
{
lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5522_; 
v_isSharedCheck_5522_ = !lean_is_exclusive(v___x_5513_);
if (v_isSharedCheck_5522_ == 0)
{
lean_object* v_unused_5523_; 
v_unused_5523_ = lean_ctor_get(v___x_5513_, 0);
lean_dec(v_unused_5523_);
v___x_5515_ = v___x_5513_;
v_isShared_5516_ = v_isSharedCheck_5522_;
goto v_resetjp_5514_;
}
else
{
lean_dec(v___x_5513_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5522_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5520_; 
v___x_5517_ = lean_st_ref_get(v___x_5512_);
lean_dec(v___x_5512_);
lean_dec(v___x_5517_);
v___x_5518_ = lean_box(v___x_5498_);
if (v_isShared_5516_ == 0)
{
lean_ctor_set(v___x_5515_, 0, v___x_5518_);
v___x_5520_ = v___x_5515_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5518_);
v___x_5520_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
return v___x_5520_;
}
}
}
else
{
lean_object* v_a_5524_; lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5531_; 
lean_dec(v___x_5512_);
v_a_5524_ = lean_ctor_get(v___x_5513_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v___x_5513_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5526_ = v___x_5513_;
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
else
{
lean_inc(v_a_5524_);
lean_dec(v___x_5513_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5531_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v___x_5529_; 
if (v_isShared_5527_ == 0)
{
v___x_5529_ = v___x_5526_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5524_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
else
{
uint8_t v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; 
lean_dec(v___x_5495_);
lean_dec(v___x_5488_);
v___x_5532_ = 0;
v___x_5533_ = lean_box(v___x_5532_);
v___x_5534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5534_, 0, v___x_5533_);
return v___x_5534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5535_, lean_object* v_name_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_){
_start:
{
lean_object* v_res_5540_; 
v_res_5540_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5535_, v_name_5536_, v___y_5537_, v___y_5538_);
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5537_);
return v_res_5540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5544_; lean_object* v___x_5545_; 
v___f_5544_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5545_ = l_Lean_registerReservedNameAction(v___f_5544_);
return v___x_5545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5546_){
_start:
{
lean_object* v_res_5547_; 
v_res_5547_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5547_;
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
