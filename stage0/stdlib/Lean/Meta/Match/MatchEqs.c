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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__24;
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(lean_object* v_msg_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_ref_33_; lean_object* v___x_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_ref_33_ = lean_ctor_get(v___y_30_, 2);
v___x_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_ref_33_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_ref_33_);
lean_ctor_set(v___x_39_, 1, v_a_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_27_ = stack[0].m_obj;
lean_object* v___y_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
if (lean_obj_tag(v_a_52_) == 0)
{
lean_object* v___x_54_; 
v___x_54_ = l_List_reverse___redArg(v_a_53_);
return v___x_54_;
}
else
{
lean_object* v_head_55_; lean_object* v_tail_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_65_; 
v_head_55_ = lean_ctor_get(v_a_52_, 0);
v_tail_56_ = lean_ctor_get(v_a_52_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_a_52_);
if (v_isSharedCheck_65_ == 0)
{
v___x_58_ = v_a_52_;
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_tail_56_);
lean_inc(v_head_55_);
lean_dec(v_a_52_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = l_Lean_MessageData_ofExpr(v_head_55_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v_a_53_);
lean_ctor_set(v___x_58_, 0, v___x_60_);
v___x_62_ = v___x_58_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_a_53_);
v___x_62_ = v_reuseFailAlloc_64_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
v_a_52_ = v_tail_56_;
v_a_53_ = v___x_62_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__0));
v___x_71_ = l_Lean_stringToMessageData(v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__2));
v___x_74_ = l_Lean_stringToMessageData(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__4));
v___x_77_ = l_Lean_stringToMessageData(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__6));
v___x_80_ = l_Lean_stringToMessageData(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__8));
v___x_83_ = l_Lean_stringToMessageData(v___x_82_);
return v___x_83_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(lean_object* v_alt_84_, lean_object* v_heqs_85_, lean_object* v_numDiscrEqs_86_, lean_object* v_e_87_, lean_object* v_ty_88_, lean_object* v_i_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = lean_nat_dec_lt(v_i_89_, v_numDiscrEqs_86_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec_ref(v_ty_88_);
lean_dec(v_numDiscrEqs_86_);
lean_dec_ref(v_heqs_85_);
lean_dec_ref(v_alt_84_);
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v_e_87_);
return v___x_96_;
}
else
{
if (lean_obj_tag(v_ty_88_) == 7)
{
lean_object* v_binderName_97_; lean_object* v_binderType_98_; lean_object* v_body_99_; lean_object* v___x_100_; size_t v_sz_101_; size_t v___x_102_; lean_object* v___x_103_; 
v_binderName_97_ = lean_ctor_get(v_ty_88_, 0);
lean_inc(v_binderName_97_);
v_binderType_98_ = lean_ctor_get(v_ty_88_, 1);
lean_inc_ref_n(v_binderType_98_, 2);
v_body_99_ = lean_ctor_get(v_ty_88_, 2);
lean_inc_ref(v_body_99_);
lean_dec_ref_known(v_ty_88_, 3);
v___x_100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0));
v_sz_101_ = lean_array_size(v_heqs_85_);
v___x_102_ = ((size_t)0ULL);
lean_inc_ref(v_heqs_85_);
v___x_103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(v_binderType_98_, v_e_87_, v_body_99_, v_i_89_, v_alt_84_, v_heqs_85_, v_numDiscrEqs_86_, v_heqs_85_, v_sz_101_, v___x_102_, v___x_100_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec_ref(v_body_99_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_135_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_135_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_135_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_135_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_fst_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_133_; 
v_fst_108_ = lean_ctor_get(v_a_104_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_a_104_);
if (v_isSharedCheck_133_ == 0)
{
lean_object* v_unused_134_; 
v_unused_134_ = lean_ctor_get(v_a_104_, 1);
lean_dec(v_unused_134_);
v___x_110_ = v_a_104_;
v_isShared_111_ = v_isSharedCheck_133_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_fst_108_);
lean_dec(v_a_104_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_133_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
if (lean_obj_tag(v_fst_108_) == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
lean_del_object(v___x_106_);
v___x_112_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1);
v___x_113_ = l_Lean_MessageData_ofName(v_binderName_97_);
if (v_isShared_111_ == 0)
{
lean_ctor_set_tag(v___x_110_, 7);
lean_ctor_set(v___x_110_, 1, v___x_113_);
lean_ctor_set(v___x_110_, 0, v___x_112_);
v___x_115_ = v___x_110_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_113_);
v___x_115_ = v_reuseFailAlloc_128_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_116_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3);
v___x_117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = l_Lean_MessageData_ofExpr(v_binderType_98_);
v___x_119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5);
v___x_121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_array_to_list(v_heqs_85_);
v___x_123_ = lean_box(0);
v___x_124_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_122_, v___x_123_);
v___x_125_ = l_Lean_MessageData_ofList(v___x_124_);
v___x_126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_121_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_126_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
return v___x_127_;
}
}
else
{
lean_object* v_val_129_; lean_object* v___x_131_; 
lean_del_object(v___x_110_);
lean_dec_ref(v_binderType_98_);
lean_dec(v_binderName_97_);
lean_dec_ref(v_heqs_85_);
v_val_129_ = lean_ctor_get(v_fst_108_, 0);
lean_inc(v_val_129_);
lean_dec_ref_known(v_fst_108_, 1);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v_val_129_);
v___x_131_ = v___x_106_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_val_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec_ref(v_binderType_98_);
lean_dec(v_binderName_97_);
lean_dec_ref(v_heqs_85_);
v_a_136_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_103_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_103_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec_ref(v_ty_88_);
lean_dec_ref(v_e_87_);
lean_dec_ref(v_heqs_85_);
v___x_144_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7);
v___x_145_ = l_Nat_reprFast(v_numDiscrEqs_86_);
v___x_146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
v___x_147_ = l_Lean_MessageData_ofFormat(v___x_146_);
v___x_148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_144_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9);
v___x_150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = l_Lean_indentExpr(v_alt_84_);
v___x_152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_152_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_84_ = stack[0].m_obj;
lean_object* v_heqs_85_ = stack[1].m_obj;
lean_object* v_numDiscrEqs_86_ = stack[2].m_obj;
lean_object* v_e_87_ = stack[3].m_obj;
lean_object* v_ty_88_ = stack[4].m_obj;
lean_object* v_i_89_ = stack[5].m_obj;
lean_object* v_a_90_ = stack[6].m_obj;
lean_object* v_a_91_ = stack[7].m_obj;
lean_object* v_a_92_ = stack[8].m_obj;
lean_object* v_a_93_ = stack[9].m_obj;
lean_object* v_res_154_;
v_res_154_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_84_, v_heqs_85_, v_numDiscrEqs_86_, v_e_87_, v_ty_88_, v_i_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
stack->m_obj
 = v_res_154_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(lean_object* v_binderType_155_, lean_object* v_e_156_, lean_object* v_body_157_, lean_object* v_i_158_, lean_object* v_alt_159_, lean_object* v_heqs_160_, lean_object* v_numDiscrEqs_161_, lean_object* v_as_162_, size_t v_sz_163_, size_t v_i_164_, lean_object* v_b_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = lean_usize_dec_lt(v_i_164_, v_sz_163_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
lean_dec(v_numDiscrEqs_161_);
lean_dec_ref(v_heqs_160_);
lean_dec_ref(v_alt_159_);
lean_dec_ref(v_e_156_);
lean_dec_ref(v_binderType_155_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v_b_165_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_a_175_; lean_object* v___x_176_; 
lean_dec_ref(v_b_165_);
v___x_173_ = lean_box(0);
v___x_174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0));
v_a_175_ = lean_array_uget_borrowed(v_as_162_, v_i_164_);
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
lean_inc(v_a_175_);
v___x_176_ = lean_infer_type(v_a_175_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_178_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
lean_inc_ref(v_binderType_155_);
v___x_178_ = l_Lean_Meta_isExprDefEq(v_a_177_, v_binderType_155_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; uint8_t v___x_180_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = lean_unbox(v_a_179_);
lean_dec(v_a_179_);
if (v___x_180_ == 0)
{
size_t v___x_181_; size_t v___x_182_; 
v___x_181_ = ((size_t)1ULL);
v___x_182_ = lean_usize_add(v_i_164_, v___x_181_);
v_i_164_ = v___x_182_;
v_b_165_ = v___x_174_;
goto _start;
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec_ref(v_binderType_155_);
lean_inc(v_a_175_);
v___x_184_ = l_Lean_Expr_app___override(v_e_156_, v_a_175_);
v___x_185_ = lean_expr_instantiate1(v_body_157_, v_a_175_);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_i_158_, v___x_186_);
v___x_188_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_159_, v_heqs_160_, v_numDiscrEqs_161_, v___x_184_, v___x_185_, v___x_187_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___x_187_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_198_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_198_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_198_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_198_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v_a_189_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_173_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_a_199_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_188_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_188_);
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
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_numDiscrEqs_161_);
lean_dec_ref(v_heqs_160_);
lean_dec_ref(v_alt_159_);
lean_dec_ref(v_e_156_);
lean_dec_ref(v_binderType_155_);
v_a_207_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_178_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_178_);
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
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec(v_numDiscrEqs_161_);
lean_dec_ref(v_heqs_160_);
lean_dec_ref(v_alt_159_);
lean_dec_ref(v_e_156_);
lean_dec_ref(v_binderType_155_);
v_a_215_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_176_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_176_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_155_ = stack[0].m_obj;
lean_object* v_e_156_ = stack[1].m_obj;
lean_object* v_body_157_ = stack[2].m_obj;
lean_object* v_i_158_ = stack[3].m_obj;
lean_object* v_alt_159_ = stack[4].m_obj;
lean_object* v_heqs_160_ = stack[5].m_obj;
lean_object* v_numDiscrEqs_161_ = stack[6].m_obj;
lean_object* v_as_162_ = stack[7].m_obj;
size_t v_sz_163_ = stack[8].m_num;
size_t v_i_164_ = stack[9].m_num;
lean_object* v_b_165_ = stack[10].m_obj;
lean_object* v___y_166_ = stack[11].m_obj;
lean_object* v___y_167_ = stack[12].m_obj;
lean_object* v___y_168_ = stack[13].m_obj;
lean_object* v___y_169_ = stack[14].m_obj;
lean_object* v_res_223_;
v_res_223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(v_binderType_155_, v_e_156_, v_body_157_, v_i_158_, v_alt_159_, v_heqs_160_, v_numDiscrEqs_161_, v_as_162_, v_sz_163_, v_i_164_, v_b_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___boxed(lean_object* v_binderType_224_, lean_object* v_e_225_, lean_object* v_body_226_, lean_object* v_i_227_, lean_object* v_alt_228_, lean_object* v_heqs_229_, lean_object* v_numDiscrEqs_230_, lean_object* v_as_231_, lean_object* v_sz_232_, lean_object* v_i_233_, lean_object* v_b_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
size_t v_sz_boxed_240_; size_t v_i_boxed_241_; lean_object* v_res_242_; 
v_sz_boxed_240_ = lean_unbox_usize(v_sz_232_);
lean_dec(v_sz_232_);
v_i_boxed_241_ = lean_unbox_usize(v_i_233_);
lean_dec(v_i_233_);
v_res_242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(v_binderType_224_, v_e_225_, v_body_226_, v_i_227_, v_alt_228_, v_heqs_229_, v_numDiscrEqs_230_, v_as_231_, v_sz_boxed_240_, v_i_boxed_241_, v_b_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec_ref(v_as_231_);
lean_dec(v_i_227_);
lean_dec_ref(v_body_226_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___boxed(lean_object* v_alt_243_, lean_object* v_heqs_244_, lean_object* v_numDiscrEqs_245_, lean_object* v_e_246_, lean_object* v_ty_247_, lean_object* v_i_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_243_, v_heqs_244_, v_numDiscrEqs_245_, v_e_246_, v_ty_247_, v_i_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_i_248_);
return v_res_254_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2(lean_object* v_00_u03b1_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
return v___x_262_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_256_ = stack[1].m_obj;
lean_object* v___y_257_ = stack[2].m_obj;
lean_object* v___y_258_ = stack[3].m_obj;
lean_object* v___y_259_ = stack[4].m_obj;
lean_object* v___y_260_ = stack[5].m_obj;
lean_object* v_res_263_;
v_res_263_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2(lean_box(0), v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
stack->m_obj
 = v_res_263_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___boxed(lean_object* v_00_u03b1_264_, lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2(v_00_u03b1_264_, v_msg_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_271_;
}
}
lean_object* l_Lean_Meta_Match_mkAppDiscrEqs(lean_object* v_alt_272_, lean_object* v_heqs_273_, lean_object* v_numDiscrEqs_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_280_; 
lean_inc(v_a_278_);
lean_inc_ref(v_a_277_);
lean_inc(v_a_276_);
lean_inc_ref(v_a_275_);
lean_inc_ref(v_alt_272_);
v___x_280_ = lean_infer_type(v_alt_272_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alt_272_);
v___x_283_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_272_, v_heqs_273_, v_numDiscrEqs_274_, v_alt_272_, v_a_281_, v___x_282_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
return v___x_283_;
}
else
{
lean_dec(v_numDiscrEqs_274_);
lean_dec_ref(v_heqs_273_);
lean_dec_ref(v_alt_272_);
return v___x_280_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_mkAppDiscrEqs_0interp(lean_interpreter_value* stack)
{
lean_object* v_alt_272_ = stack[0].m_obj;
lean_object* v_heqs_273_ = stack[1].m_obj;
lean_object* v_numDiscrEqs_274_ = stack[2].m_obj;
lean_object* v_a_275_ = stack[3].m_obj;
lean_object* v_a_276_ = stack[4].m_obj;
lean_object* v_a_277_ = stack[5].m_obj;
lean_object* v_a_278_ = stack[6].m_obj;
lean_object* v_res_284_;
v_res_284_ = l_Lean_Meta_Match_mkAppDiscrEqs(v_alt_272_, v_heqs_273_, v_numDiscrEqs_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
stack->m_obj
 = v_res_284_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkAppDiscrEqs___boxed(lean_object* v_alt_285_, lean_object* v_heqs_286_, lean_object* v_numDiscrEqs_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Meta_Match_mkAppDiscrEqs(v_alt_285_, v_heqs_286_, v_numDiscrEqs_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
return v_res_293_;
}
}
uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0(lean_object* v_x_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = 0;
return v___x_295_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_294_ = stack[0].m_obj;
uint8_t v_res_296_;
v_res_296_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0(v_x_294_);
stack->m_num = v_res_296_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0___boxed(lean_object* v_x_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0(v_x_297_);
lean_dec(v_x_297_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1(lean_object* v_fvarId_300_, lean_object* v_x_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = l_Lean_instBEqFVarId_beq(v_fvarId_300_, v_x_301_);
return v___x_302_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_300_ = stack[0].m_obj;
lean_object* v_x_301_ = stack[1].m_obj;
uint8_t v_res_303_;
v_res_303_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1(v_fvarId_300_, v_x_301_);
stack->m_num = v_res_303_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_304_, lean_object* v_x_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1(v_fvarId_304_, v_x_305_);
lean_dec(v_x_305_);
lean_dec(v_fvarId_304_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_box(0);
v___x_310_ = lean_unsigned_to_nat(16u);
v___x_311_ = lean_mk_array(v___x_310_, v___x_309_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_312_);
return v___x_314_;
}
}
lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(lean_object* v_e_315_, lean_object* v_fvarId_316_, lean_object* v___y_317_){
_start:
{
lean_object* v___f_319_; lean_object* v___f_320_; lean_object* v___x_321_; uint8_t v_fst_323_; lean_object* v_mctx_324_; lean_object* v___y_342_; lean_object* v_mctx_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___f_319_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0));
v___f_320_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_320_, 0, v_fvarId_316_);
v___x_321_ = lean_st_ref_get(v___y_317_);
v_mctx_347_ = lean_ctor_get(v___x_321_, 0);
lean_inc_ref_n(v_mctx_347_, 2);
lean_dec(v___x_321_);
v___x_348_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_mctx_347_);
v___x_350_ = l_Lean_Expr_hasFVar(v_e_315_);
if (v___x_350_ == 0)
{
uint8_t v___x_351_; 
v___x_351_ = l_Lean_Expr_hasMVar(v_e_315_);
if (v___x_351_ == 0)
{
lean_dec_ref_known(v___x_349_, 2);
lean_dec_ref(v___f_320_);
lean_dec_ref(v_e_315_);
v_fst_323_ = v___x_351_;
v_mctx_324_ = v_mctx_347_;
goto v___jp_322_;
}
else
{
lean_object* v___x_352_; 
lean_dec_ref(v_mctx_347_);
v___x_352_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_320_, v___f_319_, v_e_315_, v___x_349_);
v___y_342_ = v___x_352_;
goto v___jp_341_;
}
}
else
{
lean_object* v___x_353_; 
lean_dec_ref(v_mctx_347_);
v___x_353_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_320_, v___f_319_, v_e_315_, v___x_349_);
v___y_342_ = v___x_353_;
goto v___jp_341_;
}
v___jp_322_:
{
lean_object* v___x_325_; lean_object* v_cache_326_; lean_object* v_zetaDeltaFVarIds_327_; lean_object* v_postponed_328_; lean_object* v_diag_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_339_; 
v___x_325_ = lean_st_ref_take(v___y_317_);
v_cache_326_ = lean_ctor_get(v___x_325_, 1);
v_zetaDeltaFVarIds_327_ = lean_ctor_get(v___x_325_, 2);
v_postponed_328_ = lean_ctor_get(v___x_325_, 3);
v_diag_329_ = lean_ctor_get(v___x_325_, 4);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v___x_325_, 0);
lean_dec(v_unused_340_);
v___x_331_ = v___x_325_;
v_isShared_332_ = v_isSharedCheck_339_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_diag_329_);
lean_inc(v_postponed_328_);
lean_inc(v_zetaDeltaFVarIds_327_);
lean_inc(v_cache_326_);
lean_dec(v___x_325_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_339_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v_mctx_324_);
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_mctx_324_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_cache_326_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_zetaDeltaFVarIds_327_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_postponed_328_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_diag_329_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_st_ref_put(v___y_317_, v___x_334_);
v___x_336_ = lean_box(v_fst_323_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
v___jp_341_:
{
lean_object* v_snd_343_; lean_object* v_fst_344_; lean_object* v_mctx_345_; uint8_t v___x_346_; 
v_snd_343_ = lean_ctor_get(v___y_342_, 1);
lean_inc(v_snd_343_);
v_fst_344_ = lean_ctor_get(v___y_342_, 0);
lean_inc(v_fst_344_);
lean_dec_ref(v___y_342_);
v_mctx_345_ = lean_ctor_get(v_snd_343_, 1);
lean_inc_ref(v_mctx_345_);
lean_dec(v_snd_343_);
v___x_346_ = lean_unbox(v_fst_344_);
lean_dec(v_fst_344_);
v_fst_323_ = v___x_346_;
v_mctx_324_ = v_mctx_345_;
goto v___jp_322_;
}
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_315_ = stack[0].m_obj;
lean_object* v_fvarId_316_ = stack[1].m_obj;
lean_object* v___y_317_ = stack[2].m_obj;
lean_object* v_res_354_;
v_res_354_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_315_, v_fvarId_316_, v___y_317_);
stack->m_obj
 = v_res_354_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___boxed(lean_object* v_e_355_, lean_object* v_fvarId_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_355_, v_fvarId_356_, v___y_357_);
lean_dec(v___y_357_);
return v_res_359_;
}
}
lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(lean_object* v_e_360_, lean_object* v_fvarId_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_360_, v_fvarId_361_, v___y_363_);
return v___x_367_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_360_ = stack[0].m_obj;
lean_object* v_fvarId_361_ = stack[1].m_obj;
lean_object* v___y_362_ = stack[2].m_obj;
lean_object* v___y_363_ = stack[3].m_obj;
lean_object* v___y_364_ = stack[4].m_obj;
lean_object* v___y_365_ = stack[5].m_obj;
lean_object* v_res_368_;
v_res_368_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(v_e_360_, v_fvarId_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___boxed(lean_object* v_e_369_, lean_object* v_fvarId_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(v_e_369_, v_fvarId_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_376_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(lean_object* v_mvarId_377_, lean_object* v_x_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_377_, v_x_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_a_393_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_384_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_384_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_377_ = stack[0].m_obj;
lean_object* v_x_378_ = stack[1].m_obj;
lean_object* v___y_379_ = stack[2].m_obj;
lean_object* v___y_380_ = stack[3].m_obj;
lean_object* v___y_381_ = stack[4].m_obj;
lean_object* v___y_382_ = stack[5].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_377_, v_x_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg___boxed(lean_object* v_mvarId_402_, lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_402_, v_x_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_409_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(lean_object* v_00_u03b1_410_, lean_object* v_mvarId_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_411_, v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v___x_418_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_411_ = stack[1].m_obj;
lean_object* v_x_412_ = stack[2].m_obj;
lean_object* v___y_413_ = stack[3].m_obj;
lean_object* v___y_414_ = stack[4].m_obj;
lean_object* v___y_415_ = stack[5].m_obj;
lean_object* v___y_416_ = stack[6].m_obj;
lean_object* v_res_419_;
v_res_419_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(lean_box(0), v_mvarId_411_, v_x_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
stack->m_obj
 = v_res_419_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___boxed(lean_object* v_00_u03b1_420_, lean_object* v_mvarId_421_, lean_object* v_x_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(v_00_u03b1_420_, v_mvarId_421_, v_x_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_428_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(lean_object* v_mvarId_432_, lean_object* v_as_433_, size_t v_sz_434_, size_t v_i_435_, lean_object* v_b_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_usize_dec_lt(v_i_435_, v_sz_434_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
lean_dec(v_mvarId_432_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v_b_436_);
return v___x_443_;
}
else
{
lean_object* v_snd_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_546_; 
v_snd_444_ = lean_ctor_get(v_b_436_, 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_b_436_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v_b_436_, 0);
lean_dec(v_unused_547_);
v___x_446_ = v_b_436_;
v_isShared_447_ = v_isSharedCheck_546_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_snd_444_);
lean_dec(v_b_436_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_546_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v_a_450_; lean_object* v_a_457_; 
v___x_448_ = lean_box(0);
v_a_457_ = lean_array_uget(v_as_433_, v_i_435_);
if (lean_obj_tag(v_a_457_) == 0)
{
v_a_450_ = v_snd_444_;
goto v___jp_449_;
}
else
{
lean_object* v_val_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_545_; 
v_val_458_ = lean_ctor_get(v_a_457_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_a_457_);
if (v_isSharedCheck_545_ == 0)
{
v___x_460_ = v_a_457_;
v_isShared_461_ = v_isSharedCheck_545_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_val_458_);
lean_dec(v_a_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_545_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = lean_box(0);
v___x_463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
v___x_464_ = l_Lean_LocalDecl_type(v_val_458_);
lean_dec(v_val_458_);
v___x_465_ = l_Lean_Meta_matchEq_x3f(v___x_464_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
if (lean_obj_tag(v_a_466_) == 1)
{
lean_object* v_val_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_536_; 
v_val_467_ = lean_ctor_get(v_a_466_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_a_466_);
if (v_isSharedCheck_536_ == 0)
{
v___x_469_ = v_a_466_;
v_isShared_470_ = v_isSharedCheck_536_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_val_467_);
lean_dec(v_a_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_536_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v_snd_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_534_; 
v_snd_471_ = lean_ctor_get(v_val_467_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_val_467_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v_val_467_, 0);
lean_dec(v_unused_535_);
v___x_473_ = v_val_467_;
v_isShared_474_ = v_isSharedCheck_534_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snd_471_);
lean_dec(v_val_467_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_534_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_fst_475_; lean_object* v_snd_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_533_; 
v_fst_475_ = lean_ctor_get(v_snd_471_, 0);
v_snd_476_ = lean_ctor_get(v_snd_471_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_snd_471_);
if (v_isSharedCheck_533_ == 0)
{
v___x_478_ = v_snd_471_;
v_isShared_479_ = v_isSharedCheck_533_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_snd_476_);
lean_inc(v_fst_475_);
lean_dec(v_snd_471_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_533_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
uint8_t v___x_480_; 
v___x_480_ = l_Lean_Expr_isFVar(v_fst_475_);
if (v___x_480_ == 0)
{
lean_del_object(v___x_478_);
lean_dec(v_snd_476_);
lean_dec(v_fst_475_);
lean_del_object(v___x_473_);
lean_del_object(v___x_469_);
lean_del_object(v___x_460_);
lean_dec(v_snd_444_);
v_a_450_ = v___x_463_;
goto v___jp_449_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = l_Lean_Expr_fvarId_x21(v_fst_475_);
lean_dec(v_fst_475_);
lean_inc(v___x_481_);
v___x_482_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_476_, v___x_481_, v___y_438_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; uint8_t v___x_484_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = lean_unbox(v_a_483_);
lean_dec(v_a_483_);
if (v___x_484_ == 0)
{
if (v___x_480_ == 0)
{
lean_dec(v___x_481_);
lean_del_object(v___x_478_);
lean_del_object(v___x_473_);
lean_del_object(v___x_469_);
lean_del_object(v___x_460_);
lean_dec(v_snd_444_);
v_a_450_ = v___x_463_;
goto v___jp_449_;
}
else
{
lean_object* v___x_485_; 
lean_inc(v_mvarId_432_);
v___x_485_ = l_Lean_Meta_subst_x3f(v_mvarId_432_, v___x_481_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_516_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_516_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_516_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_516_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
if (lean_obj_tag(v_a_486_) == 0)
{
lean_del_object(v___x_488_);
lean_del_object(v___x_478_);
lean_del_object(v___x_473_);
lean_del_object(v___x_469_);
lean_del_object(v___x_460_);
lean_dec(v_snd_444_);
v_a_450_ = v___x_463_;
goto v___jp_449_;
}
else
{
lean_object* v_val_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_515_; 
lean_del_object(v___x_446_);
lean_dec(v_mvarId_432_);
v_val_490_ = lean_ctor_get(v_a_486_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_a_486_);
if (v_isSharedCheck_515_ == 0)
{
v___x_492_ = v_a_486_;
v_isShared_493_ = v_isSharedCheck_515_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_val_490_);
lean_dec(v_a_486_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_515_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_mk_empty_array_with_capacity(v___x_494_);
v___x_496_ = lean_array_push(v___x_495_, v_val_490_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_496_);
v___x_498_ = v___x_492_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_514_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_500_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_462_);
lean_ctor_set(v___x_478_, 0, v___x_498_);
v___x_500_ = v___x_478_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_462_);
v___x_500_ = v_reuseFailAlloc_513_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 0);
lean_ctor_set(v___x_460_, 0, v___x_500_);
v___x_502_ = v___x_460_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_512_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_502_);
v___x_504_ = v___x_469_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_511_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v_snd_444_);
lean_ctor_set(v___x_473_, 0, v___x_504_);
v___x_506_ = v___x_473_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_snd_444_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_506_);
v___x_508_ = v___x_488_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
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
}
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_del_object(v___x_478_);
lean_del_object(v___x_473_);
lean_del_object(v___x_469_);
lean_del_object(v___x_460_);
lean_del_object(v___x_446_);
lean_dec(v_snd_444_);
lean_dec(v_mvarId_432_);
v_a_517_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_485_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_485_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
else
{
lean_dec(v___x_481_);
lean_del_object(v___x_478_);
lean_del_object(v___x_473_);
lean_del_object(v___x_469_);
lean_del_object(v___x_460_);
lean_dec(v_snd_444_);
v_a_450_ = v___x_463_;
goto v___jp_449_;
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v___x_481_);
lean_del_object(v___x_478_);
lean_del_object(v___x_473_);
lean_del_object(v___x_469_);
lean_del_object(v___x_460_);
lean_del_object(v___x_446_);
lean_dec(v_snd_444_);
lean_dec(v_mvarId_432_);
v_a_525_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_482_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_482_);
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
}
}
}
else
{
lean_dec(v_a_466_);
lean_del_object(v___x_460_);
lean_dec(v_snd_444_);
v_a_450_ = v___x_463_;
goto v___jp_449_;
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_del_object(v___x_460_);
lean_del_object(v___x_446_);
lean_dec(v_snd_444_);
lean_dec(v_mvarId_432_);
v_a_537_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_465_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_465_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
v___jp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v_a_450_);
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_452_ = v___x_446_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_a_450_);
v___x_452_ = v_reuseFailAlloc_456_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
size_t v___x_453_; size_t v___x_454_; 
v___x_453_ = ((size_t)1ULL);
v___x_454_ = lean_usize_add(v_i_435_, v___x_453_);
v_i_435_ = v___x_454_;
v_b_436_ = v___x_452_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_432_ = stack[0].m_obj;
lean_object* v_as_433_ = stack[1].m_obj;
size_t v_sz_434_ = stack[2].m_num;
size_t v_i_435_ = stack[3].m_num;
lean_object* v_b_436_ = stack[4].m_obj;
lean_object* v___y_437_ = stack[5].m_obj;
lean_object* v___y_438_ = stack[6].m_obj;
lean_object* v___y_439_ = stack[7].m_obj;
lean_object* v___y_440_ = stack[8].m_obj;
lean_object* v_res_548_;
v_res_548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_432_, v_as_433_, v_sz_434_, v_i_435_, v_b_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_mvarId_549_, lean_object* v_as_550_, lean_object* v_sz_551_, lean_object* v_i_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
size_t v_sz_boxed_559_; size_t v_i_boxed_560_; lean_object* v_res_561_; 
v_sz_boxed_559_ = lean_unbox_usize(v_sz_551_);
lean_dec(v_sz_551_);
v_i_boxed_560_ = lean_unbox_usize(v_i_552_);
lean_dec(v_i_552_);
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_549_, v_as_550_, v_sz_boxed_559_, v_i_boxed_560_, v_b_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec_ref(v_as_550_);
return v_res_561_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(lean_object* v_mvarId_562_, lean_object* v_as_563_, size_t v_sz_564_, size_t v_i_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
uint8_t v___x_572_; 
v___x_572_ = lean_usize_dec_lt(v_i_565_, v_sz_564_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec(v_mvarId_562_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v_b_566_);
return v___x_573_;
}
else
{
lean_object* v_snd_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_676_; 
v_snd_574_ = lean_ctor_get(v_b_566_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_b_566_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v_b_566_, 0);
lean_dec(v_unused_677_);
v___x_576_ = v_b_566_;
v_isShared_577_ = v_isSharedCheck_676_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_snd_574_);
lean_dec(v_b_566_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_676_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v_a_580_; lean_object* v_a_587_; 
v___x_578_ = lean_box(0);
v_a_587_ = lean_array_uget(v_as_563_, v_i_565_);
if (lean_obj_tag(v_a_587_) == 0)
{
v_a_580_ = v_snd_574_;
goto v___jp_579_;
}
else
{
lean_object* v_val_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_675_; 
v_val_588_ = lean_ctor_get(v_a_587_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v_a_587_);
if (v_isSharedCheck_675_ == 0)
{
v___x_590_ = v_a_587_;
v_isShared_591_ = v_isSharedCheck_675_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_val_588_);
lean_dec(v_a_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_675_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = lean_box(0);
v___x_593_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
v___x_594_ = l_Lean_LocalDecl_type(v_val_588_);
lean_dec(v_val_588_);
v___x_595_ = l_Lean_Meta_matchEq_x3f(v___x_594_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
if (lean_obj_tag(v_a_596_) == 1)
{
lean_object* v_val_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_666_; 
v_val_597_ = lean_ctor_get(v_a_596_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_666_ == 0)
{
v___x_599_ = v_a_596_;
v_isShared_600_ = v_isSharedCheck_666_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_val_597_);
lean_dec(v_a_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_666_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v_snd_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_664_; 
v_snd_601_ = lean_ctor_get(v_val_597_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_val_597_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v_val_597_, 0);
lean_dec(v_unused_665_);
v___x_603_ = v_val_597_;
v_isShared_604_ = v_isSharedCheck_664_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_snd_601_);
lean_dec(v_val_597_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_664_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_fst_605_; lean_object* v_snd_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_663_; 
v_fst_605_ = lean_ctor_get(v_snd_601_, 0);
v_snd_606_ = lean_ctor_get(v_snd_601_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_snd_601_);
if (v_isSharedCheck_663_ == 0)
{
v___x_608_ = v_snd_601_;
v_isShared_609_ = v_isSharedCheck_663_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snd_606_);
lean_inc(v_fst_605_);
lean_dec(v_snd_601_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_663_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
uint8_t v___x_610_; 
v___x_610_ = l_Lean_Expr_isFVar(v_fst_605_);
if (v___x_610_ == 0)
{
lean_del_object(v___x_608_);
lean_dec(v_snd_606_);
lean_dec(v_fst_605_);
lean_del_object(v___x_603_);
lean_del_object(v___x_599_);
lean_del_object(v___x_590_);
lean_dec(v_snd_574_);
v_a_580_ = v___x_593_;
goto v___jp_579_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = l_Lean_Expr_fvarId_x21(v_fst_605_);
lean_dec(v_fst_605_);
lean_inc(v___x_611_);
v___x_612_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_606_, v___x_611_, v___y_568_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; uint8_t v___x_614_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v___x_614_ = lean_unbox(v_a_613_);
lean_dec(v_a_613_);
if (v___x_614_ == 0)
{
if (v___x_610_ == 0)
{
lean_dec(v___x_611_);
lean_del_object(v___x_608_);
lean_del_object(v___x_603_);
lean_del_object(v___x_599_);
lean_del_object(v___x_590_);
lean_dec(v_snd_574_);
v_a_580_ = v___x_593_;
goto v___jp_579_;
}
else
{
lean_object* v___x_615_; 
lean_inc(v_mvarId_562_);
v___x_615_ = l_Lean_Meta_subst_x3f(v_mvarId_562_, v___x_611_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_646_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_646_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_646_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_646_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
if (lean_obj_tag(v_a_616_) == 0)
{
lean_del_object(v___x_618_);
lean_del_object(v___x_608_);
lean_del_object(v___x_603_);
lean_del_object(v___x_599_);
lean_del_object(v___x_590_);
lean_dec(v_snd_574_);
v_a_580_ = v___x_593_;
goto v___jp_579_;
}
else
{
lean_object* v_val_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_645_; 
lean_del_object(v___x_576_);
lean_dec(v_mvarId_562_);
v_val_620_ = lean_ctor_get(v_a_616_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v_a_616_);
if (v_isSharedCheck_645_ == 0)
{
v___x_622_ = v_a_616_;
v_isShared_623_ = v_isSharedCheck_645_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_val_620_);
lean_dec(v_a_616_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_645_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_mk_empty_array_with_capacity(v___x_624_);
v___x_626_ = lean_array_push(v___x_625_, v_val_620_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_626_);
v___x_628_ = v___x_622_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_644_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_630_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_592_);
lean_ctor_set(v___x_608_, 0, v___x_628_);
v___x_630_ = v___x_608_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_592_);
v___x_630_ = v_reuseFailAlloc_643_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_632_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set_tag(v___x_590_, 0);
lean_ctor_set(v___x_590_, 0, v___x_630_);
v___x_632_ = v___x_590_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_642_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_632_);
v___x_634_ = v___x_599_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_641_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 1, v_snd_574_);
lean_ctor_set(v___x_603_, 0, v___x_634_);
v___x_636_ = v___x_603_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_snd_574_);
v___x_636_ = v_reuseFailAlloc_640_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_636_);
v___x_638_ = v___x_618_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
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
}
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_del_object(v___x_608_);
lean_del_object(v___x_603_);
lean_del_object(v___x_599_);
lean_del_object(v___x_590_);
lean_del_object(v___x_576_);
lean_dec(v_snd_574_);
lean_dec(v_mvarId_562_);
v_a_647_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_615_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_615_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
else
{
lean_dec(v___x_611_);
lean_del_object(v___x_608_);
lean_del_object(v___x_603_);
lean_del_object(v___x_599_);
lean_del_object(v___x_590_);
lean_dec(v_snd_574_);
v_a_580_ = v___x_593_;
goto v___jp_579_;
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec(v___x_611_);
lean_del_object(v___x_608_);
lean_del_object(v___x_603_);
lean_del_object(v___x_599_);
lean_del_object(v___x_590_);
lean_del_object(v___x_576_);
lean_dec(v_snd_574_);
lean_dec(v_mvarId_562_);
v_a_655_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_612_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_612_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
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
lean_dec(v_a_596_);
lean_del_object(v___x_590_);
lean_dec(v_snd_574_);
v_a_580_ = v___x_593_;
goto v___jp_579_;
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_del_object(v___x_590_);
lean_del_object(v___x_576_);
lean_dec(v_snd_574_);
lean_dec(v_mvarId_562_);
v_a_667_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_595_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_595_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
v___jp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 1, v_a_580_);
lean_ctor_set(v___x_576_, 0, v___x_578_);
v___x_582_ = v___x_576_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_a_580_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
size_t v___x_583_; size_t v___x_584_; lean_object* v___x_585_; 
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_565_, v___x_583_);
v___x_585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_562_, v_as_563_, v_sz_564_, v___x_584_, v___x_582_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
return v___x_585_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_562_ = stack[0].m_obj;
lean_object* v_as_563_ = stack[1].m_obj;
size_t v_sz_564_ = stack[2].m_num;
size_t v_i_565_ = stack[3].m_num;
lean_object* v_b_566_ = stack[4].m_obj;
lean_object* v___y_567_ = stack[5].m_obj;
lean_object* v___y_568_ = stack[6].m_obj;
lean_object* v___y_569_ = stack[7].m_obj;
lean_object* v___y_570_ = stack[8].m_obj;
lean_object* v_res_678_;
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_562_, v_as_563_, v_sz_564_, v_i_565_, v_b_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4___boxed(lean_object* v_mvarId_679_, lean_object* v_as_680_, lean_object* v_sz_681_, lean_object* v_i_682_, lean_object* v_b_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
size_t v_sz_boxed_689_; size_t v_i_boxed_690_; lean_object* v_res_691_; 
v_sz_boxed_689_ = lean_unbox_usize(v_sz_681_);
lean_dec(v_sz_681_);
v_i_boxed_690_ = lean_unbox_usize(v_i_682_);
lean_dec(v_i_682_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_679_, v_as_680_, v_sz_boxed_689_, v_i_boxed_690_, v_b_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v_as_680_);
return v_res_691_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(lean_object* v_init_692_, lean_object* v_mvarId_693_, lean_object* v_n_694_, lean_object* v_b_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
if (lean_obj_tag(v_n_694_) == 0)
{
lean_object* v_cs_701_; lean_object* v___x_702_; lean_object* v___x_703_; size_t v_sz_704_; size_t v___x_705_; lean_object* v___x_706_; 
v_cs_701_ = lean_ctor_get(v_n_694_, 0);
v___x_702_ = lean_box(0);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v_b_695_);
v_sz_704_ = lean_array_size(v_cs_701_);
v___x_705_ = ((size_t)0ULL);
v___x_706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_692_, v_mvarId_693_, v_cs_701_, v_sz_704_, v___x_705_, v___x_703_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_721_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_721_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_721_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_721_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_fst_711_; 
v_fst_711_ = lean_ctor_get(v_a_707_, 0);
if (lean_obj_tag(v_fst_711_) == 0)
{
lean_object* v_snd_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v_snd_712_ = lean_ctor_get(v_a_707_, 1);
lean_inc(v_snd_712_);
lean_dec(v_a_707_);
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v_snd_712_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_713_);
v___x_715_ = v___x_709_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
else
{
lean_object* v_val_717_; lean_object* v___x_719_; 
lean_inc_ref(v_fst_711_);
lean_dec(v_a_707_);
v_val_717_ = lean_ctor_get(v_fst_711_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v_fst_711_, 1);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v_val_717_);
v___x_719_ = v___x_709_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_val_717_);
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
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
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
lean_object* v_vs_730_; lean_object* v___x_731_; lean_object* v___x_732_; size_t v_sz_733_; size_t v___x_734_; lean_object* v___x_735_; 
v_vs_730_ = lean_ctor_get(v_n_694_, 0);
v___x_731_ = lean_box(0);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_b_695_);
v_sz_733_ = lean_array_size(v_vs_730_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_693_, v_vs_730_, v_sz_733_, v___x_734_, v___x_732_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_750_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_750_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_fst_740_; 
v_fst_740_ = lean_ctor_get(v_a_736_, 0);
if (lean_obj_tag(v_fst_740_) == 0)
{
lean_object* v_snd_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v_snd_741_ = lean_ctor_get(v_a_736_, 1);
lean_inc(v_snd_741_);
lean_dec(v_a_736_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_snd_741_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_742_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
else
{
lean_object* v_val_746_; lean_object* v___x_748_; 
lean_inc_ref(v_fst_740_);
lean_dec(v_a_736_);
v_val_746_ = lean_ctor_get(v_fst_740_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v_fst_740_, 1);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_val_746_);
v___x_748_ = v___x_738_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_val_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_a_751_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_735_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_735_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_692_ = stack[0].m_obj;
lean_object* v_mvarId_693_ = stack[1].m_obj;
lean_object* v_n_694_ = stack[2].m_obj;
lean_object* v_b_695_ = stack[3].m_obj;
lean_object* v___y_696_ = stack[4].m_obj;
lean_object* v___y_697_ = stack[5].m_obj;
lean_object* v___y_698_ = stack[6].m_obj;
lean_object* v___y_699_ = stack[7].m_obj;
lean_object* v_res_759_;
v_res_759_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_692_, v_mvarId_693_, v_n_694_, v_b_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
stack->m_obj
 = v_res_759_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(lean_object* v_init_760_, lean_object* v_mvarId_761_, lean_object* v_as_762_, size_t v_sz_763_, size_t v_i_764_, lean_object* v_b_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = lean_usize_dec_lt(v_i_764_, v_sz_763_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec(v_mvarId_761_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_b_765_);
return v___x_772_;
}
else
{
lean_object* v_snd_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_807_; 
v_snd_773_ = lean_ctor_get(v_b_765_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_b_765_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_b_765_, 0);
lean_dec(v_unused_808_);
v___x_775_ = v_b_765_;
v_isShared_776_ = v_isSharedCheck_807_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_snd_773_);
lean_dec(v_b_765_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_807_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v_a_778_; lean_object* v___x_779_; 
v___x_777_ = lean_box(0);
v_a_778_ = lean_array_uget_borrowed(v_as_762_, v_i_764_);
lean_inc(v_snd_773_);
lean_inc(v_mvarId_761_);
v___x_779_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_760_, v_mvarId_761_, v_a_778_, v_snd_773_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_798_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_798_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_798_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_798_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
if (lean_obj_tag(v_a_780_) == 0)
{
lean_object* v___x_784_; lean_object* v___x_786_; 
lean_dec(v_mvarId_761_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_a_780_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_784_);
v___x_786_ = v___x_775_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_snd_773_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_786_);
v___x_788_ = v___x_782_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; 
lean_del_object(v___x_782_);
lean_dec(v_snd_773_);
v_a_791_ = lean_ctor_get(v_a_780_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v_a_780_, 1);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v_a_791_);
lean_ctor_set(v___x_775_, 0, v___x_777_);
v___x_793_ = v___x_775_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_a_791_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
size_t v___x_794_; size_t v___x_795_; 
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_add(v_i_764_, v___x_794_);
v_i_764_ = v___x_795_;
v_b_765_ = v___x_793_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_del_object(v___x_775_);
lean_dec(v_snd_773_);
lean_dec(v_mvarId_761_);
v_a_799_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_779_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_779_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_760_ = stack[0].m_obj;
lean_object* v_mvarId_761_ = stack[1].m_obj;
lean_object* v_as_762_ = stack[2].m_obj;
size_t v_sz_763_ = stack[3].m_num;
size_t v_i_764_ = stack[4].m_num;
lean_object* v_b_765_ = stack[5].m_obj;
lean_object* v___y_766_ = stack[6].m_obj;
lean_object* v___y_767_ = stack[7].m_obj;
lean_object* v___y_768_ = stack[8].m_obj;
lean_object* v___y_769_ = stack[9].m_obj;
lean_object* v_res_809_;
v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_760_, v_mvarId_761_, v_as_762_, v_sz_763_, v_i_764_, v_b_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
stack->m_obj
 = v_res_809_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3___boxed(lean_object* v_init_810_, lean_object* v_mvarId_811_, lean_object* v_as_812_, lean_object* v_sz_813_, lean_object* v_i_814_, lean_object* v_b_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
size_t v_sz_boxed_821_; size_t v_i_boxed_822_; lean_object* v_res_823_; 
v_sz_boxed_821_ = lean_unbox_usize(v_sz_813_);
lean_dec(v_sz_813_);
v_i_boxed_822_ = lean_unbox_usize(v_i_814_);
lean_dec(v_i_814_);
v_res_823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_810_, v_mvarId_811_, v_as_812_, v_sz_boxed_821_, v_i_boxed_822_, v_b_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec_ref(v_as_812_);
lean_dec_ref(v_init_810_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1___boxed(lean_object* v_init_824_, lean_object* v_mvarId_825_, lean_object* v_n_826_, lean_object* v_b_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_824_, v_mvarId_825_, v_n_826_, v_b_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec_ref(v_n_826_);
lean_dec_ref(v_init_824_);
return v_res_833_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(lean_object* v_mvarId_837_, lean_object* v_as_838_, size_t v_sz_839_, size_t v_i_840_, lean_object* v_b_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = lean_usize_dec_lt(v_i_840_, v_sz_839_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec(v_mvarId_837_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_b_841_);
return v___x_848_;
}
else
{
lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_944_; 
v_snd_849_ = lean_ctor_get(v_b_841_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_b_841_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v_b_841_, 0);
lean_dec(v_unused_945_);
v___x_851_ = v_b_841_;
v_isShared_852_ = v_isSharedCheck_944_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_dec(v_b_841_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_944_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v_a_855_; lean_object* v_a_862_; 
v___x_853_ = lean_box(0);
v_a_862_ = lean_array_uget_borrowed(v_as_838_, v_i_840_);
if (lean_obj_tag(v_a_862_) == 0)
{
v_a_855_ = v_snd_849_;
goto v___jp_854_;
}
else
{
lean_object* v_val_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_val_863_ = lean_ctor_get(v_a_862_, 0);
v___x_864_ = lean_box(0);
v___x_865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
v___x_866_ = l_Lean_LocalDecl_type(v_val_863_);
v___x_867_ = l_Lean_Meta_matchEq_x3f(v___x_866_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
if (lean_obj_tag(v_a_868_) == 1)
{
lean_object* v_val_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_935_; 
v_val_869_ = lean_ctor_get(v_a_868_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v_a_868_);
if (v_isSharedCheck_935_ == 0)
{
v___x_871_ = v_a_868_;
v_isShared_872_ = v_isSharedCheck_935_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_val_869_);
lean_dec(v_a_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_935_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_snd_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_933_; 
v_snd_873_ = lean_ctor_get(v_val_869_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_val_869_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; 
v_unused_934_ = lean_ctor_get(v_val_869_, 0);
lean_dec(v_unused_934_);
v___x_875_ = v_val_869_;
v_isShared_876_ = v_isSharedCheck_933_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_snd_873_);
lean_dec(v_val_869_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_933_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_fst_877_; lean_object* v_snd_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_932_; 
v_fst_877_ = lean_ctor_get(v_snd_873_, 0);
v_snd_878_ = lean_ctor_get(v_snd_873_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_snd_873_);
if (v_isSharedCheck_932_ == 0)
{
v___x_880_ = v_snd_873_;
v_isShared_881_ = v_isSharedCheck_932_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_snd_878_);
lean_inc(v_fst_877_);
lean_dec(v_snd_873_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_932_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
uint8_t v___x_882_; 
v___x_882_ = l_Lean_Expr_isFVar(v_fst_877_);
if (v___x_882_ == 0)
{
lean_del_object(v___x_880_);
lean_dec(v_snd_878_);
lean_dec(v_fst_877_);
lean_del_object(v___x_875_);
lean_del_object(v___x_871_);
lean_dec(v_snd_849_);
v_a_855_ = v___x_865_;
goto v___jp_854_;
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = l_Lean_Expr_fvarId_x21(v_fst_877_);
lean_dec(v_fst_877_);
lean_inc(v___x_883_);
v___x_884_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_878_, v___x_883_, v___y_843_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; uint8_t v___x_886_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v___x_886_ = lean_unbox(v_a_885_);
lean_dec(v_a_885_);
if (v___x_886_ == 0)
{
if (v___x_882_ == 0)
{
lean_dec(v___x_883_);
lean_del_object(v___x_880_);
lean_del_object(v___x_875_);
lean_del_object(v___x_871_);
lean_dec(v_snd_849_);
v_a_855_ = v___x_865_;
goto v___jp_854_;
}
else
{
lean_object* v___x_887_; 
lean_inc(v_mvarId_837_);
v___x_887_ = l_Lean_Meta_subst_x3f(v_mvarId_837_, v___x_883_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_915_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_915_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_915_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_915_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
if (lean_obj_tag(v_a_888_) == 0)
{
lean_del_object(v___x_890_);
lean_del_object(v___x_880_);
lean_del_object(v___x_875_);
lean_del_object(v___x_871_);
lean_dec(v_snd_849_);
v_a_855_ = v___x_865_;
goto v___jp_854_;
}
else
{
lean_object* v_val_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_914_; 
lean_del_object(v___x_851_);
lean_dec(v_mvarId_837_);
v_val_892_ = lean_ctor_get(v_a_888_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v_a_888_);
if (v_isSharedCheck_914_ == 0)
{
v___x_894_ = v_a_888_;
v_isShared_895_ = v_isSharedCheck_914_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_val_892_);
lean_dec(v_a_888_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_914_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_mk_empty_array_with_capacity(v___x_896_);
v___x_898_ = lean_array_push(v___x_897_, v_val_892_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_898_);
v___x_900_ = v___x_894_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_913_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_864_);
lean_ctor_set(v___x_880_, 0, v___x_900_);
v___x_902_ = v___x_880_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_864_);
v___x_902_ = v_reuseFailAlloc_912_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_904_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_902_);
v___x_904_ = v___x_871_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_911_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v_snd_849_);
lean_ctor_set(v___x_875_, 0, v___x_904_);
v___x_906_ = v___x_875_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_snd_849_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_906_);
v___x_908_ = v___x_890_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
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
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_del_object(v___x_880_);
lean_del_object(v___x_875_);
lean_del_object(v___x_871_);
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_mvarId_837_);
v_a_916_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_887_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_887_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
else
{
lean_dec(v___x_883_);
lean_del_object(v___x_880_);
lean_del_object(v___x_875_);
lean_del_object(v___x_871_);
lean_dec(v_snd_849_);
v_a_855_ = v___x_865_;
goto v___jp_854_;
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v___x_883_);
lean_del_object(v___x_880_);
lean_del_object(v___x_875_);
lean_del_object(v___x_871_);
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_mvarId_837_);
v_a_924_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_884_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_884_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
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
lean_dec(v_a_868_);
lean_dec(v_snd_849_);
v_a_855_ = v___x_865_;
goto v___jp_854_;
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_mvarId_837_);
v_a_936_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_867_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_867_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
v___jp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v_a_855_);
lean_ctor_set(v___x_851_, 0, v___x_853_);
v___x_857_ = v___x_851_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_a_855_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
size_t v___x_858_; size_t v___x_859_; 
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_add(v_i_840_, v___x_858_);
v_i_840_ = v___x_859_;
v_b_841_ = v___x_857_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_837_ = stack[0].m_obj;
lean_object* v_as_838_ = stack[1].m_obj;
size_t v_sz_839_ = stack[2].m_num;
size_t v_i_840_ = stack[3].m_num;
lean_object* v_b_841_ = stack[4].m_obj;
lean_object* v___y_842_ = stack[5].m_obj;
lean_object* v___y_843_ = stack[6].m_obj;
lean_object* v___y_844_ = stack[7].m_obj;
lean_object* v___y_845_ = stack[8].m_obj;
lean_object* v_res_946_;
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_837_, v_as_838_, v_sz_839_, v_i_840_, v_b_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___boxed(lean_object* v_mvarId_947_, lean_object* v_as_948_, lean_object* v_sz_949_, lean_object* v_i_950_, lean_object* v_b_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
size_t v_sz_boxed_957_; size_t v_i_boxed_958_; lean_object* v_res_959_; 
v_sz_boxed_957_ = lean_unbox_usize(v_sz_949_);
lean_dec(v_sz_949_);
v_i_boxed_958_ = lean_unbox_usize(v_i_950_);
lean_dec(v_i_950_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_947_, v_as_948_, v_sz_boxed_957_, v_i_boxed_958_, v_b_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v_as_948_);
return v_res_959_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(lean_object* v_mvarId_960_, lean_object* v_as_961_, size_t v_sz_962_, size_t v_i_963_, lean_object* v_b_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v___x_970_; 
v___x_970_ = lean_usize_dec_lt(v_i_963_, v_sz_962_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
lean_dec(v_mvarId_960_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v_b_964_);
return v___x_971_;
}
else
{
lean_object* v_snd_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1067_; 
v_snd_972_ = lean_ctor_get(v_b_964_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_b_964_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_b_964_, 0);
lean_dec(v_unused_1068_);
v___x_974_ = v_b_964_;
v_isShared_975_ = v_isSharedCheck_1067_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_snd_972_);
lean_dec(v_b_964_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1067_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v_a_978_; lean_object* v_a_985_; 
v___x_976_ = lean_box(0);
v_a_985_ = lean_array_uget_borrowed(v_as_961_, v_i_963_);
if (lean_obj_tag(v_a_985_) == 0)
{
v_a_978_ = v_snd_972_;
goto v___jp_977_;
}
else
{
lean_object* v_val_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_val_986_ = lean_ctor_get(v_a_985_, 0);
v___x_987_ = lean_box(0);
v___x_988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
v___x_989_ = l_Lean_LocalDecl_type(v_val_986_);
v___x_990_ = l_Lean_Meta_matchEq_x3f(v___x_989_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
if (lean_obj_tag(v_a_991_) == 1)
{
lean_object* v_val_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1058_; 
v_val_992_ = lean_ctor_get(v_a_991_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_a_991_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_994_ = v_a_991_;
v_isShared_995_ = v_isSharedCheck_1058_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_val_992_);
lean_dec(v_a_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1058_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_snd_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1056_; 
v_snd_996_ = lean_ctor_get(v_val_992_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_val_992_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; 
v_unused_1057_ = lean_ctor_get(v_val_992_, 0);
lean_dec(v_unused_1057_);
v___x_998_ = v_val_992_;
v_isShared_999_ = v_isSharedCheck_1056_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_snd_996_);
lean_dec(v_val_992_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1056_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_fst_1000_; lean_object* v_snd_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1055_; 
v_fst_1000_ = lean_ctor_get(v_snd_996_, 0);
v_snd_1001_ = lean_ctor_get(v_snd_996_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_snd_996_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1003_ = v_snd_996_;
v_isShared_1004_ = v_isSharedCheck_1055_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_snd_1001_);
lean_inc(v_fst_1000_);
lean_dec(v_snd_996_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1055_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
uint8_t v___x_1005_; 
v___x_1005_ = l_Lean_Expr_isFVar(v_fst_1000_);
if (v___x_1005_ == 0)
{
lean_del_object(v___x_1003_);
lean_dec(v_snd_1001_);
lean_dec(v_fst_1000_);
lean_del_object(v___x_998_);
lean_del_object(v___x_994_);
lean_dec(v_snd_972_);
v_a_978_ = v___x_988_;
goto v___jp_977_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = l_Lean_Expr_fvarId_x21(v_fst_1000_);
lean_dec(v_fst_1000_);
lean_inc(v___x_1006_);
v___x_1007_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_1001_, v___x_1006_, v___y_966_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; uint8_t v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = lean_unbox(v_a_1008_);
lean_dec(v_a_1008_);
if (v___x_1009_ == 0)
{
if (v___x_1005_ == 0)
{
lean_dec(v___x_1006_);
lean_del_object(v___x_1003_);
lean_del_object(v___x_998_);
lean_del_object(v___x_994_);
lean_dec(v_snd_972_);
v_a_978_ = v___x_988_;
goto v___jp_977_;
}
else
{
lean_object* v___x_1010_; 
lean_inc(v_mvarId_960_);
v___x_1010_ = l_Lean_Meta_subst_x3f(v_mvarId_960_, v___x_1006_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1038_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1038_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1038_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
if (lean_obj_tag(v_a_1011_) == 0)
{
lean_del_object(v___x_1013_);
lean_del_object(v___x_1003_);
lean_del_object(v___x_998_);
lean_del_object(v___x_994_);
lean_dec(v_snd_972_);
v_a_978_ = v___x_988_;
goto v___jp_977_;
}
else
{
lean_object* v_val_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1037_; 
lean_del_object(v___x_974_);
lean_dec(v_mvarId_960_);
v_val_1015_ = lean_ctor_get(v_a_1011_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_a_1011_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1017_ = v_a_1011_;
v_isShared_1018_ = v_isSharedCheck_1037_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_val_1015_);
lean_dec(v_a_1011_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1037_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_mk_empty_array_with_capacity(v___x_1019_);
v___x_1021_ = lean_array_push(v___x_1020_, v_val_1015_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1021_);
v___x_1023_ = v___x_1017_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1025_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___x_987_);
lean_ctor_set(v___x_1003_, 0, v___x_1023_);
v___x_1025_ = v___x_1003_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_987_);
v___x_1025_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1027_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_1025_);
v___x_1027_ = v___x_994_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v_snd_972_);
lean_ctor_set(v___x_998_, 0, v___x_1027_);
v___x_1029_ = v___x_998_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_snd_972_);
v___x_1029_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1031_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1029_);
v___x_1031_ = v___x_1013_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
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
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_del_object(v___x_1003_);
lean_del_object(v___x_998_);
lean_del_object(v___x_994_);
lean_del_object(v___x_974_);
lean_dec(v_snd_972_);
lean_dec(v_mvarId_960_);
v_a_1039_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1010_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1010_);
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
else
{
lean_dec(v___x_1006_);
lean_del_object(v___x_1003_);
lean_del_object(v___x_998_);
lean_del_object(v___x_994_);
lean_dec(v_snd_972_);
v_a_978_ = v___x_988_;
goto v___jp_977_;
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v___x_1006_);
lean_del_object(v___x_1003_);
lean_del_object(v___x_998_);
lean_del_object(v___x_994_);
lean_del_object(v___x_974_);
lean_dec(v_snd_972_);
lean_dec(v_mvarId_960_);
v_a_1047_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1007_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1007_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
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
lean_dec(v_a_991_);
lean_dec(v_snd_972_);
v_a_978_ = v___x_988_;
goto v___jp_977_;
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_del_object(v___x_974_);
lean_dec(v_snd_972_);
lean_dec(v_mvarId_960_);
v_a_1059_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_990_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_990_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
v___jp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_a_978_);
lean_ctor_set(v___x_974_, 0, v___x_976_);
v___x_980_ = v___x_974_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_a_978_);
v___x_980_ = v_reuseFailAlloc_984_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; 
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_add(v_i_963_, v___x_981_);
v___x_983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_960_, v_as_961_, v_sz_962_, v___x_982_, v___x_980_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_983_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_960_ = stack[0].m_obj;
lean_object* v_as_961_ = stack[1].m_obj;
size_t v_sz_962_ = stack[2].m_num;
size_t v_i_963_ = stack[3].m_num;
lean_object* v_b_964_ = stack[4].m_obj;
lean_object* v___y_965_ = stack[5].m_obj;
lean_object* v___y_966_ = stack[6].m_obj;
lean_object* v___y_967_ = stack[7].m_obj;
lean_object* v___y_968_ = stack[8].m_obj;
lean_object* v_res_1069_;
v_res_1069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_960_, v_as_961_, v_sz_962_, v_i_963_, v_b_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
stack->m_obj
 = v_res_1069_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2___boxed(lean_object* v_mvarId_1070_, lean_object* v_as_1071_, lean_object* v_sz_1072_, lean_object* v_i_1073_, lean_object* v_b_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
size_t v_sz_boxed_1080_; size_t v_i_boxed_1081_; lean_object* v_res_1082_; 
v_sz_boxed_1080_ = lean_unbox_usize(v_sz_1072_);
lean_dec(v_sz_1072_);
v_i_boxed_1081_ = lean_unbox_usize(v_i_1073_);
lean_dec(v_i_1073_);
v_res_1082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1070_, v_as_1071_, v_sz_boxed_1080_, v_i_boxed_1081_, v_b_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec_ref(v_as_1071_);
return v_res_1082_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(lean_object* v_mvarId_1083_, lean_object* v_t_1084_, lean_object* v_init_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_root_1091_; lean_object* v_tail_1092_; lean_object* v___x_1093_; 
v_root_1091_ = lean_ctor_get(v_t_1084_, 0);
v_tail_1092_ = lean_ctor_get(v_t_1084_, 1);
lean_inc(v_mvarId_1083_);
lean_inc_ref(v_init_1085_);
v___x_1093_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_1085_, v_mvarId_1083_, v_root_1091_, v_init_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec_ref(v_init_1085_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1130_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1130_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1130_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
if (lean_obj_tag(v_a_1094_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; 
lean_dec(v_mvarId_1083_);
v_a_1098_ = lean_ctor_get(v_a_1094_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v_a_1094_, 1);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v_a_1098_);
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; size_t v_sz_1105_; size_t v___x_1106_; lean_object* v___x_1107_; 
lean_del_object(v___x_1096_);
v_a_1102_ = lean_ctor_get(v_a_1094_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v_a_1094_, 1);
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v_a_1102_);
v_sz_1105_ = lean_array_size(v_tail_1092_);
v___x_1106_ = ((size_t)0ULL);
v___x_1107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1083_, v_tail_1092_, v_sz_1105_, v___x_1106_, v___x_1104_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1121_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1121_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1121_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v_fst_1112_; 
v_fst_1112_ = lean_ctor_get(v_a_1108_, 0);
if (lean_obj_tag(v_fst_1112_) == 0)
{
lean_object* v_snd_1113_; lean_object* v___x_1115_; 
v_snd_1113_ = lean_ctor_get(v_a_1108_, 1);
lean_inc(v_snd_1113_);
lean_dec(v_a_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v_snd_1113_);
v___x_1115_ = v___x_1110_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_snd_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
else
{
lean_object* v_val_1117_; lean_object* v___x_1119_; 
lean_inc_ref(v_fst_1112_);
lean_dec(v_a_1108_);
v_val_1117_ = lean_ctor_get(v_fst_1112_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v_fst_1112_, 1);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v_val_1117_);
v___x_1119_ = v___x_1110_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_val_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_a_1122_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1107_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1107_);
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
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_mvarId_1083_);
v_a_1131_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1093_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1093_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1083_ = stack[0].m_obj;
lean_object* v_t_1084_ = stack[1].m_obj;
lean_object* v_init_1085_ = stack[2].m_obj;
lean_object* v___y_1086_ = stack[3].m_obj;
lean_object* v___y_1087_ = stack[4].m_obj;
lean_object* v___y_1088_ = stack[5].m_obj;
lean_object* v___y_1089_ = stack[6].m_obj;
lean_object* v_res_1139_;
v_res_1139_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1083_, v_t_1084_, v_init_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
stack->m_obj
 = v_res_1139_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1___boxed(lean_object* v_mvarId_1140_, lean_object* v_t_1141_, lean_object* v_init_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1140_, v_t_1141_, v_init_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec_ref(v_t_1141_);
return v_res_1148_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(lean_object* v_mvarId_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_lctx_1161_; lean_object* v_decls_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_lctx_1161_ = lean_ctor_get(v___y_1156_, 2);
v_decls_1162_ = lean_ctor_get(v_lctx_1161_, 1);
v___x_1163_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0));
v___x_1164_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1155_, v_decls_1162_, v___x_1163_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1176_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1176_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1176_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_fst_1169_; 
v_fst_1169_ = lean_ctor_get(v_a_1165_, 0);
lean_inc(v_fst_1169_);
lean_dec(v_a_1165_);
if (lean_obj_tag(v_fst_1169_) == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_del_object(v___x_1167_);
v___x_1170_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2);
v___x_1171_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1170_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
return v___x_1171_;
}
else
{
lean_object* v_val_1172_; lean_object* v___x_1174_; 
v_val_1172_ = lean_ctor_get(v_fst_1169_, 0);
lean_inc(v_val_1172_);
lean_dec_ref_known(v_fst_1169_, 1);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v_val_1172_);
v___x_1174_ = v___x_1167_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_val_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
v_a_1177_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1164_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1164_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1155_ = stack[0].m_obj;
lean_object* v___y_1156_ = stack[1].m_obj;
lean_object* v___y_1157_ = stack[2].m_obj;
lean_object* v___y_1158_ = stack[3].m_obj;
lean_object* v___y_1159_ = stack[4].m_obj;
lean_object* v_res_1185_;
v_res_1185_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(v_mvarId_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
stack->m_obj
 = v_res_1185_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed(lean_object* v_mvarId_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(v_mvarId_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1192_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(lean_object* v_mvarId_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v___f_1199_; lean_object* v___x_1200_; 
lean_inc(v_mvarId_1193_);
v___f_1199_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1199_, 0, v_mvarId_1193_);
v___x_1200_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_1193_, v___f_1199_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
return v___x_1200_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1193_ = stack[0].m_obj;
lean_object* v_a_1194_ = stack[1].m_obj;
lean_object* v_a_1195_ = stack[2].m_obj;
lean_object* v_a_1196_ = stack[3].m_obj;
lean_object* v_a_1197_ = stack[4].m_obj;
lean_object* v_res_1201_;
v_res_1201_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v_mvarId_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_);
stack->m_obj
 = v_res_1201_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___boxed(lean_object* v_mvarId_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v_mvarId_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
return v_res_1208_;
}
}
uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object* v_x_1216_){
_start:
{
lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1218_ = lean_name_eq(v_x_1216_, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1216_ = stack[0].m_obj;
uint8_t v_res_1219_;
v_res_1219_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(v_x_1216_);
stack->m_num = v_res_1219_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object* v_x_1220_){
_start:
{
uint8_t v_res_1221_; lean_object* v_r_1222_; 
v_res_1221_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(v_x_1220_);
lean_dec(v_x_1220_);
v_r_1222_ = lean_box(v_res_1221_);
return v_r_1222_;
}
}
uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object* v_e_1223_){
_start:
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1225_ = l_Lean_Expr_isConstOf(v_e_1223_, v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1223_ = stack[0].m_obj;
uint8_t v_res_1226_;
v_res_1226_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(v_e_1223_);
stack->m_num = v_res_1226_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object* v_e_1227_){
_start:
{
uint8_t v_res_1228_; lean_object* v_r_1229_; 
v_res_1228_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(v_e_1227_);
lean_dec_ref(v_e_1227_);
v_r_1229_ = lean_box(v_res_1228_);
return v_r_1229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2));
v___x_1234_ = l_Lean_stringToMessageData(v___x_1233_);
return v___x_1234_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object* v_mvarId_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___f_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; 
v___f_1241_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0));
v___f_1242_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1));
lean_inc(v_mvarId_1235_);
v___x_1243_ = l_Lean_MVarId_getType(v_mvarId_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1245_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v___x_1245_ = lean_find_expr(v___f_1242_, v_a_1244_);
lean_dec(v_a_1244_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec(v_mvarId_1235_);
v___x_1246_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3);
v___x_1247_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1246_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_object* v___x_1256_; 
lean_dec_ref_known(v___x_1245_, 1);
v___x_1256_ = l_Lean_MVarId_deltaTarget(v_mvarId_1235_, v___f_1241_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
return v___x_1256_;
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_mvarId_1235_);
v_a_1257_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1243_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1243_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1235_ = stack[0].m_obj;
lean_object* v_a_1236_ = stack[1].m_obj;
lean_object* v_a_1237_ = stack[2].m_obj;
lean_object* v_a_1238_ = stack[3].m_obj;
lean_object* v_a_1239_ = stack[4].m_obj;
lean_object* v_res_1265_;
v_res_1265_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_mvarId_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
stack->m_obj
 = v_res_1265_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object* v_mvarId_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_mvarId_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
return v_res_1272_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = l_Lean_maxRecDepthErrorMessage;
v___x_1279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3);
v___x_1281_ = l_Lean_MessageData_ofFormat(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4);
v___x_1283_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2));
v___x_1284_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
lean_ctor_set(v___x_1284_, 1, v___x_1282_);
return v___x_1284_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(lean_object* v_ref_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v_ref_1285_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1285_ = stack[0].m_obj;
lean_object* v_res_1290_;
v_res_1290_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1285_);
stack->m_obj
 = v_res_1290_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___boxed(lean_object* v_ref_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1291_);
return v_res_1293_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object* v_00_u03b1_1294_, lean_object* v_ref_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1295_);
return v___x_1301_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1295_ = stack[1].m_obj;
lean_object* v___y_1296_ = stack[2].m_obj;
lean_object* v___y_1297_ = stack[3].m_obj;
lean_object* v___y_1298_ = stack[4].m_obj;
lean_object* v___y_1299_ = stack[5].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_box(0), v_ref_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object* v_00_u03b1_1303_, lean_object* v_ref_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v_00_u03b1_1303_, v_ref_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1310_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object* v_a_1311_, lean_object* v_____r_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1318_ = lean_unsigned_to_nat(1u);
v___x_1319_ = lean_mk_empty_array_with_capacity(v___x_1318_);
v___x_1320_ = lean_array_push(v___x_1319_, v_a_1311_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1311_ = stack[0].m_obj;
lean_object* v_____r_1312_ = stack[1].m_obj;
lean_object* v___y_1313_ = stack[2].m_obj;
lean_object* v___y_1314_ = stack[3].m_obj;
lean_object* v___y_1315_ = stack[4].m_obj;
lean_object* v___y_1316_ = stack[5].m_obj;
lean_object* v_res_1322_;
v_res_1322_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1311_, v_____r_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
stack->m_obj
 = v_res_1322_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object* v_a_1323_, lean_object* v_____r_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1323_, v_____r_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1330_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1331_; double v___x_1332_; 
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_float_of_nat(v___x_1331_);
return v___x_1332_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object* v_cls_1336_, lean_object* v_msg_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_ref_1343_; lean_object* v___x_1344_; lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1390_; 
v_ref_1343_ = lean_ctor_get(v___y_1340_, 2);
v___x_1344_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1390_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1390_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v_traceState_1350_; lean_object* v_env_1351_; lean_object* v_nextMacroScope_1352_; lean_object* v_ngen_1353_; lean_object* v_auxDeclNGen_1354_; lean_object* v_cache_1355_; lean_object* v_recordedDeps_1356_; lean_object* v_messages_1357_; lean_object* v_infoState_1358_; lean_object* v_snapshotTasks_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1389_; 
v___x_1349_ = lean_st_ref_take(v___y_1341_);
v_traceState_1350_ = lean_ctor_get(v___x_1349_, 4);
v_env_1351_ = lean_ctor_get(v___x_1349_, 0);
v_nextMacroScope_1352_ = lean_ctor_get(v___x_1349_, 1);
v_ngen_1353_ = lean_ctor_get(v___x_1349_, 2);
v_auxDeclNGen_1354_ = lean_ctor_get(v___x_1349_, 3);
v_cache_1355_ = lean_ctor_get(v___x_1349_, 5);
v_recordedDeps_1356_ = lean_ctor_get(v___x_1349_, 6);
v_messages_1357_ = lean_ctor_get(v___x_1349_, 7);
v_infoState_1358_ = lean_ctor_get(v___x_1349_, 8);
v_snapshotTasks_1359_ = lean_ctor_get(v___x_1349_, 9);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1361_ = v___x_1349_;
v_isShared_1362_ = v_isSharedCheck_1389_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_snapshotTasks_1359_);
lean_inc(v_infoState_1358_);
lean_inc(v_messages_1357_);
lean_inc(v_recordedDeps_1356_);
lean_inc(v_cache_1355_);
lean_inc(v_traceState_1350_);
lean_inc(v_auxDeclNGen_1354_);
lean_inc(v_ngen_1353_);
lean_inc(v_nextMacroScope_1352_);
lean_inc(v_env_1351_);
lean_dec(v___x_1349_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1389_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
uint64_t v_tid_1363_; lean_object* v_traces_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1388_; 
v_tid_1363_ = lean_ctor_get_uint64(v_traceState_1350_, sizeof(void*)*1);
v_traces_1364_ = lean_ctor_get(v_traceState_1350_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_traceState_1350_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1366_ = v_traceState_1350_;
v_isShared_1367_ = v_isSharedCheck_1388_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_traces_1364_);
lean_dec(v_traceState_1350_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1388_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; double v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_box(0);
v___x_1370_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0);
v___x_1371_ = 0;
v___x_1372_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1));
v___x_1373_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1373_, 0, v_cls_1336_);
lean_ctor_set(v___x_1373_, 1, v___x_1369_);
lean_ctor_set(v___x_1373_, 2, v___x_1372_);
lean_ctor_set_float(v___x_1373_, sizeof(void*)*3, v___x_1370_);
lean_ctor_set_float(v___x_1373_, sizeof(void*)*3 + 8, v___x_1370_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 16, v___x_1371_);
v___x_1374_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2));
v___x_1375_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v_a_1345_);
lean_ctor_set(v___x_1375_, 2, v___x_1374_);
lean_inc(v_ref_1343_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_ref_1343_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Lean_PersistentArray_push___redArg(v_traces_1364_, v___x_1376_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1377_);
v___x_1379_ = v___x_1366_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1377_);
lean_ctor_set_uint64(v_reuseFailAlloc_1387_, sizeof(void*)*1, v_tid_1363_);
v___x_1379_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 4, v___x_1379_);
v___x_1381_ = v___x_1361_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_env_1351_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_nextMacroScope_1352_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_ngen_1353_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_auxDeclNGen_1354_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1386_, 5, v_cache_1355_);
lean_ctor_set(v_reuseFailAlloc_1386_, 6, v_recordedDeps_1356_);
lean_ctor_set(v_reuseFailAlloc_1386_, 7, v_messages_1357_);
lean_ctor_set(v_reuseFailAlloc_1386_, 8, v_infoState_1358_);
lean_ctor_set(v_reuseFailAlloc_1386_, 9, v_snapshotTasks_1359_);
v___x_1381_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = lean_st_ref_put(v___y_1341_, v___x_1381_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1368_);
v___x_1384_ = v___x_1347_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1368_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1336_ = stack[0].m_obj;
lean_object* v_msg_1337_ = stack[1].m_obj;
lean_object* v___y_1338_ = stack[2].m_obj;
lean_object* v___y_1339_ = stack[3].m_obj;
lean_object* v___y_1340_ = stack[4].m_obj;
lean_object* v___y_1341_ = stack[5].m_obj;
lean_object* v_res_1391_;
v_res_1391_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1336_, v_msg_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
stack->m_obj
 = v_res_1391_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object* v_cls_1392_, lean_object* v_msg_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1392_, v_msg_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0));
v___x_1402_ = l_Lean_stringToMessageData(v___x_1401_);
return v___x_1402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2));
v___x_1405_ = l_Lean_stringToMessageData(v___x_1404_);
return v___x_1405_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4));
v___x_1408_ = l_Lean_stringToMessageData(v___x_1407_);
return v___x_1408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1411_ = l_Lean_stringToMessageData(v___x_1410_);
return v___x_1411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16(void){
_start:
{
lean_object* v_cls_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_cls_1425_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1426_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15));
v___x_1427_ = l_Lean_Name_append(v___x_1426_, v_cls_1425_);
return v___x_1427_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17));
v___x_1430_ = l_Lean_stringToMessageData(v___x_1429_);
return v___x_1430_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1431_, lean_object* v_mvarId_1432_, lean_object* v_depth_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v_a_1444_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; uint8_t v___y_1481_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; uint8_t v___y_1506_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v_a_1530_; uint8_t v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; uint8_t v___y_1542_; uint8_t v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v_a_1584_; uint8_t v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; lean_object* v___y_1595_; uint8_t v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; uint8_t v___y_1607_; lean_object* v___y_1631_; uint8_t v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; uint8_t v___y_1639_; lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; uint8_t v___y_1664_; uint8_t v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; uint8_t v___y_1689_; lean_object* v___y_1707_; uint8_t v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; uint8_t v___y_1715_; uint8_t v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; uint8_t v___y_1744_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v_toCold_1795_; lean_object* v_currRecDepth_1796_; lean_object* v_ref_1797_; uint16_t v_optionFlags_1798_; uint8_t v_suppressElabErrors_1799_; uint8_t v_isRecordingDeps_1800_; lean_object* v_options_1801_; lean_object* v_maxRecDepth_1802_; lean_object* v_inheritedTraceOptions_1803_; lean_object* v_cls_1804_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_toCold_1795_ = lean_ctor_get(v_a_1436_, 0);
v_currRecDepth_1796_ = lean_ctor_get(v_a_1436_, 1);
v_ref_1797_ = lean_ctor_get(v_a_1436_, 2);
v_optionFlags_1798_ = lean_ctor_get_uint16(v_a_1436_, sizeof(void*)*3);
v_suppressElabErrors_1799_ = lean_ctor_get_uint8(v_a_1436_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1800_ = lean_ctor_get_uint8(v_a_1436_, sizeof(void*)*3 + 3);
v_options_1801_ = lean_ctor_get(v_toCold_1795_, 2);
v_maxRecDepth_1802_ = lean_ctor_get(v_toCold_1795_, 3);
v_inheritedTraceOptions_1803_ = lean_ctor_get(v_toCold_1795_, 11);
v_cls_1804_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_nat_dec_eq(v_maxRecDepth_1802_, v___x_1816_);
if (v___x_1817_ == 0)
{
uint8_t v___x_1818_; 
v___x_1818_ = lean_nat_dec_eq(v_currRecDepth_1796_, v_maxRecDepth_1802_);
if (v___x_1818_ == 0)
{
goto v___jp_1805_;
}
else
{
lean_object* v___x_1819_; 
lean_dec(v_mvarId_1432_);
lean_dec(v_matchDeclName_1431_);
lean_inc(v_ref_1797_);
v___x_1819_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1797_);
return v___x_1819_;
}
}
else
{
goto v___jp_1805_;
}
v___jp_1439_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_array_get_size(v_a_1444_);
v___x_1447_ = lean_box(0);
v___x_1448_ = lean_nat_dec_lt(v___x_1445_, v___x_1446_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec_ref(v_a_1444_);
lean_dec_ref(v___y_1441_);
lean_dec(v_matchDeclName_1431_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
return v___x_1449_;
}
else
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_nat_dec_le(v___x_1446_, v___x_1446_);
if (v___x_1450_ == 0)
{
if (v___x_1448_ == 0)
{
lean_object* v___x_1451_; 
lean_dec_ref(v_a_1444_);
lean_dec_ref(v___y_1441_);
lean_dec(v_matchDeclName_1431_);
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1447_);
return v___x_1451_;
}
else
{
size_t v___x_1452_; size_t v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = ((size_t)0ULL);
v___x_1453_ = lean_usize_of_nat(v___x_1446_);
v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1433_, v_matchDeclName_1431_, v_a_1444_, v___x_1452_, v___x_1453_, v___x_1447_, v___y_1440_, v___y_1443_, v___y_1441_, v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec_ref(v_a_1444_);
return v___x_1454_;
}
}
else
{
size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = ((size_t)0ULL);
v___x_1456_ = lean_usize_of_nat(v___x_1446_);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1433_, v_matchDeclName_1431_, v_a_1444_, v___x_1455_, v___x_1456_, v___x_1447_, v___y_1440_, v___y_1443_, v___y_1441_, v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec_ref(v_a_1444_);
return v___x_1457_;
}
}
}
v___jp_1458_:
{
if (lean_obj_tag(v___y_1463_) == 0)
{
lean_object* v_a_1464_; 
v_a_1464_ = lean_ctor_get(v___y_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___y_1463_, 1);
v___y_1440_ = v___y_1459_;
v___y_1441_ = v___y_1460_;
v___y_1442_ = v___y_1461_;
v___y_1443_ = v___y_1462_;
v_a_1444_ = v_a_1464_;
goto v___jp_1439_;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v___y_1460_);
lean_dec(v_matchDeclName_1431_);
v_a_1465_ = lean_ctor_get(v___y_1463_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___y_1463_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___y_1463_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___y_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
v___jp_1473_:
{
if (v___y_1481_ == 0)
{
lean_object* v___x_1482_; 
lean_dec_ref(v___y_1474_);
v___x_1482_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1475_, v___y_1480_, v___y_1479_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1496_; 
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v___x_1482_, 0);
lean_dec(v_unused_1497_);
v___x_1484_ = v___x_1482_;
v_isShared_1485_ = v_isSharedCheck_1496_;
goto v_resetjp_1483_;
}
else
{
lean_dec(v___x_1482_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1496_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1486_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1431_);
v___x_1487_ = l_Lean_MessageData_ofName(v_matchDeclName_1431_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set_tag(v___x_1484_, 1);
lean_ctor_set(v___x_1484_, 0, v___y_1478_);
v___x_1492_ = v___x_1484_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___y_1478_);
v___x_1492_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1490_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1493_, v___y_1476_, v___y_1480_, v___y_1477_, v___y_1479_);
v___y_1459_ = v___y_1476_;
v___y_1460_ = v___y_1477_;
v___y_1461_ = v___y_1479_;
v___y_1462_ = v___y_1480_;
v___y_1463_ = v___x_1494_;
goto v___jp_1458_;
}
}
}
else
{
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v_matchDeclName_1431_);
return v___x_1482_;
}
}
else
{
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1475_);
v___y_1459_ = v___y_1476_;
v___y_1460_ = v___y_1477_;
v___y_1461_ = v___y_1479_;
v___y_1462_ = v___y_1480_;
v___y_1463_ = v___y_1474_;
goto v___jp_1458_;
}
}
v___jp_1498_:
{
if (v___y_1506_ == 0)
{
lean_object* v___x_1507_; 
lean_dec_ref(v___y_1499_);
v___x_1507_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1504_, v___y_1505_, v___y_1503_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; 
lean_dec_ref_known(v___x_1507_, 1);
v___x_1508_ = l_Lean_Meta_saveState___redArg(v___y_1505_, v___y_1503_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1510_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
lean_inc(v___y_1502_);
v___x_1510_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1502_, v___y_1500_, v___y_1505_, v___y_1501_, v___y_1503_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_dec(v_a_1509_);
lean_dec(v___y_1502_);
v___y_1459_ = v___y_1500_;
v___y_1460_ = v___y_1501_;
v___y_1461_ = v___y_1503_;
v___y_1462_ = v___y_1505_;
v___y_1463_ = v___x_1510_;
goto v___jp_1458_;
}
else
{
lean_object* v_a_1511_; uint8_t v___x_1512_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v___x_1512_ = l_Lean_Exception_isInterrupt(v_a_1511_);
if (v___x_1512_ == 0)
{
uint8_t v___x_1513_; 
lean_inc(v_a_1511_);
v___x_1513_ = l_Lean_Exception_isRuntime(v_a_1511_);
v___y_1474_ = v___x_1510_;
v___y_1475_ = v_a_1509_;
v___y_1476_ = v___y_1500_;
v___y_1477_ = v___y_1501_;
v___y_1478_ = v___y_1502_;
v___y_1479_ = v___y_1503_;
v___y_1480_ = v___y_1505_;
v___y_1481_ = v___x_1513_;
goto v___jp_1473_;
}
else
{
v___y_1474_ = v___x_1510_;
v___y_1475_ = v_a_1509_;
v___y_1476_ = v___y_1500_;
v___y_1477_ = v___y_1501_;
v___y_1478_ = v___y_1502_;
v___y_1479_ = v___y_1503_;
v___y_1480_ = v___y_1505_;
v___y_1481_ = v___x_1512_;
goto v___jp_1473_;
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v_matchDeclName_1431_);
v_a_1514_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1508_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1508_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v_matchDeclName_1431_);
return v___x_1507_;
}
}
else
{
lean_object* v___x_1522_; 
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v_matchDeclName_1431_);
v___x_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___y_1499_);
return v___x_1522_;
}
}
v___jp_1523_:
{
uint8_t v___x_1531_; 
v___x_1531_ = l_Lean_Exception_isInterrupt(v_a_1530_);
if (v___x_1531_ == 0)
{
uint8_t v___x_1532_; 
lean_inc_ref(v_a_1530_);
v___x_1532_ = l_Lean_Exception_isRuntime(v_a_1530_);
v___y_1499_ = v_a_1530_;
v___y_1500_ = v___y_1524_;
v___y_1501_ = v___y_1525_;
v___y_1502_ = v___y_1527_;
v___y_1503_ = v___y_1526_;
v___y_1504_ = v___y_1528_;
v___y_1505_ = v___y_1529_;
v___y_1506_ = v___x_1532_;
goto v___jp_1498_;
}
else
{
v___y_1499_ = v_a_1530_;
v___y_1500_ = v___y_1524_;
v___y_1501_ = v___y_1525_;
v___y_1502_ = v___y_1527_;
v___y_1503_ = v___y_1526_;
v___y_1504_ = v___y_1528_;
v___y_1505_ = v___y_1529_;
v___y_1506_ = v___x_1531_;
goto v___jp_1498_;
}
}
v___jp_1533_:
{
if (v___y_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_dec_ref(v___y_1535_);
v___x_1543_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1541_, v___y_1540_, v___y_1539_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec_ref_known(v___x_1543_, 1);
v___x_1544_ = lean_box(0);
v___x_1545_ = l_Lean_Meta_saveState___redArg(v___y_1540_, v___y_1539_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
lean_inc(v___y_1538_);
v___x_1547_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1538_, v___x_1544_, v___y_1534_, v___y_1536_, v___y_1540_, v___y_1537_, v___y_1539_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
if (lean_obj_tag(v_a_1548_) == 1)
{
lean_object* v_val_1549_; lean_object* v_fst_1550_; lean_object* v_snd_1551_; lean_object* v_mvarId_1552_; lean_object* v_fvarId_1553_; lean_object* v___x_1554_; 
v_val_1549_ = lean_ctor_get(v_a_1548_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_a_1548_, 1);
v_fst_1550_ = lean_ctor_get(v_val_1549_, 0);
lean_inc(v_fst_1550_);
v_snd_1551_ = lean_ctor_get(v_val_1549_, 1);
lean_inc(v_snd_1551_);
lean_dec(v_val_1549_);
v_mvarId_1552_ = lean_ctor_get(v_fst_1550_, 0);
lean_inc(v_mvarId_1552_);
v_fvarId_1553_ = lean_ctor_get(v_fst_1550_, 1);
lean_inc(v_fvarId_1553_);
lean_dec(v_fst_1550_);
v___x_1554_ = l_Lean_Meta_trySubst(v_mvarId_1552_, v_fvarId_1553_, v___y_1536_, v___y_1540_, v___y_1537_, v___y_1539_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v_mvarId_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec(v_a_1546_);
lean_dec(v___y_1538_);
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v_mvarId_1556_ = lean_ctor_get(v_snd_1551_, 0);
lean_inc(v_mvarId_1556_);
lean_dec(v_snd_1551_);
v___x_1557_ = lean_unsigned_to_nat(2u);
v___x_1558_ = lean_mk_empty_array_with_capacity(v___x_1557_);
v___x_1559_ = lean_array_push(v___x_1558_, v_a_1555_);
v___x_1560_ = lean_array_push(v___x_1559_, v_mvarId_1556_);
v___y_1440_ = v___y_1536_;
v___y_1441_ = v___y_1537_;
v___y_1442_ = v___y_1539_;
v___y_1443_ = v___y_1540_;
v_a_1444_ = v___x_1560_;
goto v___jp_1439_;
}
else
{
lean_object* v_a_1561_; 
lean_dec(v_snd_1551_);
v_a_1561_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1554_, 1);
v___y_1524_ = v___y_1536_;
v___y_1525_ = v___y_1537_;
v___y_1526_ = v___y_1539_;
v___y_1527_ = v___y_1538_;
v___y_1528_ = v_a_1546_;
v___y_1529_ = v___y_1540_;
v_a_1530_ = v_a_1561_;
goto v___jp_1523_;
}
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec(v_a_1548_);
v___x_1562_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1563_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1562_, v___y_1536_, v___y_1540_, v___y_1537_, v___y_1539_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; 
lean_dec(v_a_1546_);
lean_dec(v___y_1538_);
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___y_1440_ = v___y_1536_;
v___y_1441_ = v___y_1537_;
v___y_1442_ = v___y_1539_;
v___y_1443_ = v___y_1540_;
v_a_1444_ = v_a_1564_;
goto v___jp_1439_;
}
else
{
lean_object* v_a_1565_; 
v_a_1565_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1563_, 1);
v___y_1524_ = v___y_1536_;
v___y_1525_ = v___y_1537_;
v___y_1526_ = v___y_1539_;
v___y_1527_ = v___y_1538_;
v___y_1528_ = v_a_1546_;
v___y_1529_ = v___y_1540_;
v_a_1530_ = v_a_1565_;
goto v___jp_1523_;
}
}
}
else
{
lean_object* v_a_1566_; 
v_a_1566_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1547_, 1);
v___y_1524_ = v___y_1536_;
v___y_1525_ = v___y_1537_;
v___y_1526_ = v___y_1539_;
v___y_1527_ = v___y_1538_;
v___y_1528_ = v_a_1546_;
v___y_1529_ = v___y_1540_;
v_a_1530_ = v_a_1566_;
goto v___jp_1523_;
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_matchDeclName_1431_);
v_a_1567_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1545_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1545_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_matchDeclName_1431_);
return v___x_1543_;
}
}
else
{
lean_object* v___x_1575_; 
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v_matchDeclName_1431_);
v___x_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___y_1535_);
return v___x_1575_;
}
}
v___jp_1576_:
{
uint8_t v___x_1585_; 
v___x_1585_ = l_Lean_Exception_isInterrupt(v_a_1584_);
if (v___x_1585_ == 0)
{
uint8_t v___x_1586_; 
lean_inc_ref(v_a_1584_);
v___x_1586_ = l_Lean_Exception_isRuntime(v_a_1584_);
v___y_1534_ = v___y_1577_;
v___y_1535_ = v_a_1584_;
v___y_1536_ = v___y_1578_;
v___y_1537_ = v___y_1579_;
v___y_1538_ = v___y_1581_;
v___y_1539_ = v___y_1580_;
v___y_1540_ = v___y_1582_;
v___y_1541_ = v___y_1583_;
v___y_1542_ = v___x_1586_;
goto v___jp_1533_;
}
else
{
v___y_1534_ = v___y_1577_;
v___y_1535_ = v_a_1584_;
v___y_1536_ = v___y_1578_;
v___y_1537_ = v___y_1579_;
v___y_1538_ = v___y_1581_;
v___y_1539_ = v___y_1580_;
v___y_1540_ = v___y_1582_;
v___y_1541_ = v___y_1583_;
v___y_1542_ = v___x_1585_;
goto v___jp_1533_;
}
}
v___jp_1587_:
{
if (lean_obj_tag(v___y_1595_) == 0)
{
lean_object* v_a_1596_; 
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1591_);
v_a_1596_ = lean_ctor_get(v___y_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___y_1595_, 1);
v___y_1440_ = v___y_1589_;
v___y_1441_ = v___y_1590_;
v___y_1442_ = v___y_1592_;
v___y_1443_ = v___y_1593_;
v_a_1444_ = v_a_1596_;
goto v___jp_1439_;
}
else
{
lean_object* v_a_1597_; 
v_a_1597_ = lean_ctor_get(v___y_1595_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___y_1595_, 1);
v___y_1577_ = v___y_1588_;
v___y_1578_ = v___y_1589_;
v___y_1579_ = v___y_1590_;
v___y_1580_ = v___y_1592_;
v___y_1581_ = v___y_1591_;
v___y_1582_ = v___y_1593_;
v___y_1583_ = v___y_1594_;
v_a_1584_ = v_a_1597_;
goto v___jp_1576_;
}
}
v___jp_1598_:
{
if (v___y_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref(v___y_1605_);
v___x_1608_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1601_, v___y_1606_, v___y_1604_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref_known(v___x_1608_, 1);
v___x_1609_ = l_Lean_Meta_saveState___redArg(v___y_1606_, v___y_1604_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
lean_inc(v___y_1603_);
v___x_1611_ = l_Lean_Meta_simpIfTarget(v___y_1603_, v___y_1599_, v___y_1599_, v___y_1600_, v___y_1606_, v___y_1602_, v___y_1604_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; uint8_t v___x_1613_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___x_1613_ = l_Lean_instBEqMVarId_beq(v_a_1612_, v___y_1603_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1612_, v___x_1614_, v___y_1600_, v___y_1606_, v___y_1602_, v___y_1604_);
v___y_1588_ = v___y_1599_;
v___y_1589_ = v___y_1600_;
v___y_1590_ = v___y_1602_;
v___y_1591_ = v___y_1603_;
v___y_1592_ = v___y_1604_;
v___y_1593_ = v___y_1606_;
v___y_1594_ = v_a_1610_;
v___y_1595_ = v___x_1615_;
goto v___jp_1587_;
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1617_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1616_, v___y_1600_, v___y_1606_, v___y_1602_, v___y_1604_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1619_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1612_, v_a_1618_, v___y_1600_, v___y_1606_, v___y_1602_, v___y_1604_);
v___y_1588_ = v___y_1599_;
v___y_1589_ = v___y_1600_;
v___y_1590_ = v___y_1602_;
v___y_1591_ = v___y_1603_;
v___y_1592_ = v___y_1604_;
v___y_1593_ = v___y_1606_;
v___y_1594_ = v_a_1610_;
v___y_1595_ = v___x_1619_;
goto v___jp_1587_;
}
else
{
lean_object* v_a_1620_; 
lean_dec(v_a_1612_);
v_a_1620_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1617_, 1);
v___y_1577_ = v___y_1599_;
v___y_1578_ = v___y_1600_;
v___y_1579_ = v___y_1602_;
v___y_1580_ = v___y_1604_;
v___y_1581_ = v___y_1603_;
v___y_1582_ = v___y_1606_;
v___y_1583_ = v_a_1610_;
v_a_1584_ = v_a_1620_;
goto v___jp_1576_;
}
}
}
else
{
lean_object* v_a_1621_; 
v_a_1621_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1611_, 1);
v___y_1577_ = v___y_1599_;
v___y_1578_ = v___y_1600_;
v___y_1579_ = v___y_1602_;
v___y_1580_ = v___y_1604_;
v___y_1581_ = v___y_1603_;
v___y_1582_ = v___y_1606_;
v___y_1583_ = v_a_1610_;
v_a_1584_ = v_a_1621_;
goto v___jp_1576_;
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v_matchDeclName_1431_);
v_a_1622_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1609_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1609_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v_matchDeclName_1431_);
return v___x_1608_;
}
}
else
{
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1601_);
v___y_1459_ = v___y_1600_;
v___y_1460_ = v___y_1602_;
v___y_1461_ = v___y_1604_;
v___y_1462_ = v___y_1606_;
v___y_1463_ = v___y_1605_;
goto v___jp_1458_;
}
}
v___jp_1630_:
{
if (v___y_1639_ == 0)
{
lean_object* v___x_1640_; 
lean_dec_ref(v___y_1631_);
v___x_1640_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1637_, v___y_1638_, v___y_1636_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v___x_1641_; 
lean_dec_ref_known(v___x_1640_, 1);
v___x_1641_ = l_Lean_Meta_saveState___redArg(v___y_1638_, v___y_1636_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1643_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
lean_inc(v___y_1635_);
v___x_1643_ = l_Lean_Meta_splitSparseCasesOn(v___y_1635_, v___y_1633_, v___y_1638_, v___y_1634_, v___y_1636_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_dec(v_a_1642_);
lean_dec(v___y_1635_);
v___y_1459_ = v___y_1633_;
v___y_1460_ = v___y_1634_;
v___y_1461_ = v___y_1636_;
v___y_1462_ = v___y_1638_;
v___y_1463_ = v___x_1643_;
goto v___jp_1458_;
}
else
{
lean_object* v_a_1644_; uint8_t v___x_1645_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v___x_1645_ = l_Lean_Exception_isInterrupt(v_a_1644_);
if (v___x_1645_ == 0)
{
uint8_t v___x_1646_; 
lean_inc(v_a_1644_);
v___x_1646_ = l_Lean_Exception_isRuntime(v_a_1644_);
v___y_1599_ = v___y_1632_;
v___y_1600_ = v___y_1633_;
v___y_1601_ = v_a_1642_;
v___y_1602_ = v___y_1634_;
v___y_1603_ = v___y_1635_;
v___y_1604_ = v___y_1636_;
v___y_1605_ = v___x_1643_;
v___y_1606_ = v___y_1638_;
v___y_1607_ = v___x_1646_;
goto v___jp_1598_;
}
else
{
v___y_1599_ = v___y_1632_;
v___y_1600_ = v___y_1633_;
v___y_1601_ = v_a_1642_;
v___y_1602_ = v___y_1634_;
v___y_1603_ = v___y_1635_;
v___y_1604_ = v___y_1636_;
v___y_1605_ = v___x_1643_;
v___y_1606_ = v___y_1638_;
v___y_1607_ = v___x_1645_;
goto v___jp_1598_;
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_matchDeclName_1431_);
v_a_1647_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1641_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1641_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
else
{
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_matchDeclName_1431_);
return v___x_1640_;
}
}
else
{
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1635_);
v___y_1459_ = v___y_1633_;
v___y_1460_ = v___y_1634_;
v___y_1461_ = v___y_1636_;
v___y_1462_ = v___y_1638_;
v___y_1463_ = v___y_1631_;
goto v___jp_1458_;
}
}
v___jp_1655_:
{
if (v___y_1664_ == 0)
{
lean_object* v___x_1665_; 
lean_dec_ref(v___y_1656_);
v___x_1665_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1662_, v___y_1663_, v___y_1661_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v___x_1666_; 
lean_dec_ref_known(v___x_1665_, 1);
v___x_1666_ = l_Lean_Meta_saveState___redArg(v___y_1663_, v___y_1661_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
lean_inc(v___y_1660_);
v___x_1668_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1660_, v___y_1658_, v___y_1663_, v___y_1659_, v___y_1661_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_dec(v_a_1667_);
lean_dec(v___y_1660_);
v___y_1459_ = v___y_1658_;
v___y_1460_ = v___y_1659_;
v___y_1461_ = v___y_1661_;
v___y_1462_ = v___y_1663_;
v___y_1463_ = v___x_1668_;
goto v___jp_1458_;
}
else
{
lean_object* v_a_1669_; uint8_t v___x_1670_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v___x_1670_ = l_Lean_Exception_isInterrupt(v_a_1669_);
if (v___x_1670_ == 0)
{
uint8_t v___x_1671_; 
lean_inc(v_a_1669_);
v___x_1671_ = l_Lean_Exception_isRuntime(v_a_1669_);
v___y_1631_ = v___x_1668_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___y_1658_;
v___y_1634_ = v___y_1659_;
v___y_1635_ = v___y_1660_;
v___y_1636_ = v___y_1661_;
v___y_1637_ = v_a_1667_;
v___y_1638_ = v___y_1663_;
v___y_1639_ = v___x_1671_;
goto v___jp_1630_;
}
else
{
v___y_1631_ = v___x_1668_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___y_1658_;
v___y_1634_ = v___y_1659_;
v___y_1635_ = v___y_1660_;
v___y_1636_ = v___y_1661_;
v___y_1637_ = v_a_1667_;
v___y_1638_ = v___y_1663_;
v___y_1639_ = v___x_1670_;
goto v___jp_1630_;
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v_matchDeclName_1431_);
v_a_1672_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1666_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1666_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v_matchDeclName_1431_);
return v___x_1665_;
}
}
else
{
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1660_);
v___y_1459_ = v___y_1658_;
v___y_1460_ = v___y_1659_;
v___y_1461_ = v___y_1661_;
v___y_1462_ = v___y_1663_;
v___y_1463_ = v___y_1656_;
goto v___jp_1458_;
}
}
v___jp_1680_:
{
if (v___y_1689_ == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref(v___y_1688_);
v___x_1690_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1684_, v___y_1687_, v___y_1686_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; 
lean_dec_ref_known(v___x_1690_, 1);
v___x_1691_ = l_Lean_Meta_saveState___redArg(v___y_1687_, v___y_1686_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1693_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
lean_inc(v___y_1685_);
v___x_1693_ = l_Lean_Meta_casesOnStuckLHS(v___y_1685_, v___y_1682_, v___y_1687_, v___y_1683_, v___y_1686_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_dec(v_a_1692_);
lean_dec(v___y_1685_);
v___y_1459_ = v___y_1682_;
v___y_1460_ = v___y_1683_;
v___y_1461_ = v___y_1686_;
v___y_1462_ = v___y_1687_;
v___y_1463_ = v___x_1693_;
goto v___jp_1458_;
}
else
{
lean_object* v_a_1694_; uint8_t v___x_1695_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v___x_1695_ = l_Lean_Exception_isInterrupt(v_a_1694_);
if (v___x_1695_ == 0)
{
uint8_t v___x_1696_; 
lean_inc(v_a_1694_);
v___x_1696_ = l_Lean_Exception_isRuntime(v_a_1694_);
v___y_1656_ = v___x_1693_;
v___y_1657_ = v___y_1681_;
v___y_1658_ = v___y_1682_;
v___y_1659_ = v___y_1683_;
v___y_1660_ = v___y_1685_;
v___y_1661_ = v___y_1686_;
v___y_1662_ = v_a_1692_;
v___y_1663_ = v___y_1687_;
v___y_1664_ = v___x_1696_;
goto v___jp_1655_;
}
else
{
v___y_1656_ = v___x_1693_;
v___y_1657_ = v___y_1681_;
v___y_1658_ = v___y_1682_;
v___y_1659_ = v___y_1683_;
v___y_1660_ = v___y_1685_;
v___y_1661_ = v___y_1686_;
v___y_1662_ = v_a_1692_;
v___y_1663_ = v___y_1687_;
v___y_1664_ = v___x_1695_;
goto v___jp_1655_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1683_);
lean_dec(v_matchDeclName_1431_);
v_a_1697_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1691_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1691_);
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
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1683_);
lean_dec(v_matchDeclName_1431_);
return v___x_1690_;
}
}
else
{
lean_object* v___x_1705_; 
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_matchDeclName_1431_);
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___y_1688_);
return v___x_1705_;
}
}
v___jp_1706_:
{
if (v___y_1715_ == 0)
{
lean_object* v___x_1716_; 
lean_dec_ref(v___y_1707_);
v___x_1716_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1710_, v___y_1714_, v___y_1713_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref_known(v___x_1716_, 1);
v___x_1717_ = l_Lean_Meta_saveState___redArg(v___y_1714_, v___y_1713_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
lean_inc(v___y_1712_);
v___x_1719_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1712_, v___y_1709_, v___y_1714_, v___y_1711_, v___y_1713_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v_a_1718_);
lean_dec(v___y_1712_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = lean_mk_empty_array_with_capacity(v___x_1721_);
v___x_1723_ = lean_array_push(v___x_1722_, v_a_1720_);
v___y_1440_ = v___y_1709_;
v___y_1441_ = v___y_1711_;
v___y_1442_ = v___y_1713_;
v___y_1443_ = v___y_1714_;
v_a_1444_ = v___x_1723_;
goto v___jp_1439_;
}
else
{
lean_object* v_a_1724_; uint8_t v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1725_ = l_Lean_Exception_isInterrupt(v_a_1724_);
if (v___x_1725_ == 0)
{
uint8_t v___x_1726_; 
lean_inc(v_a_1724_);
v___x_1726_ = l_Lean_Exception_isRuntime(v_a_1724_);
v___y_1681_ = v___y_1708_;
v___y_1682_ = v___y_1709_;
v___y_1683_ = v___y_1711_;
v___y_1684_ = v_a_1718_;
v___y_1685_ = v___y_1712_;
v___y_1686_ = v___y_1713_;
v___y_1687_ = v___y_1714_;
v___y_1688_ = v_a_1724_;
v___y_1689_ = v___x_1726_;
goto v___jp_1680_;
}
else
{
v___y_1681_ = v___y_1708_;
v___y_1682_ = v___y_1709_;
v___y_1683_ = v___y_1711_;
v___y_1684_ = v_a_1718_;
v___y_1685_ = v___y_1712_;
v___y_1686_ = v___y_1713_;
v___y_1687_ = v___y_1714_;
v___y_1688_ = v_a_1724_;
v___y_1689_ = v___x_1725_;
goto v___jp_1680_;
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v_matchDeclName_1431_);
v_a_1727_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1717_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1717_);
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
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v_matchDeclName_1431_);
return v___x_1716_;
}
}
else
{
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_matchDeclName_1431_);
return v___y_1707_;
}
}
v___jp_1735_:
{
if (v___y_1744_ == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref(v___y_1738_);
v___x_1745_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1737_, v___y_1743_, v___y_1742_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec_ref_known(v___x_1745_, 1);
v___x_1746_ = lean_unsigned_to_nat(16u);
v___x_1747_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*1, v___y_1736_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*1 + 1, v___y_1736_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*1 + 2, v___y_1736_);
v___x_1748_ = l_Lean_Meta_saveState___redArg(v___y_1743_, v___y_1742_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
lean_inc(v___y_1741_);
v___x_1750_ = l_Lean_MVarId_contradiction(v___y_1741_, v___x_1747_, v___y_1739_, v___y_1743_, v___y_1740_, v___y_1742_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v___x_1751_; 
lean_dec_ref_known(v___x_1750_, 1);
lean_dec(v_a_1749_);
lean_dec(v___y_1741_);
v___x_1751_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1440_ = v___y_1739_;
v___y_1441_ = v___y_1740_;
v___y_1442_ = v___y_1742_;
v___y_1443_ = v___y_1743_;
v_a_1444_ = v___x_1751_;
goto v___jp_1439_;
}
else
{
lean_object* v_a_1752_; uint8_t v___x_1753_; 
v_a_1752_ = lean_ctor_get(v___x_1750_, 0);
v___x_1753_ = l_Lean_Exception_isInterrupt(v_a_1752_);
if (v___x_1753_ == 0)
{
uint8_t v___x_1754_; 
lean_inc(v_a_1752_);
v___x_1754_ = l_Lean_Exception_isRuntime(v_a_1752_);
v___y_1707_ = v___x_1750_;
v___y_1708_ = v___y_1736_;
v___y_1709_ = v___y_1739_;
v___y_1710_ = v_a_1749_;
v___y_1711_ = v___y_1740_;
v___y_1712_ = v___y_1741_;
v___y_1713_ = v___y_1742_;
v___y_1714_ = v___y_1743_;
v___y_1715_ = v___x_1754_;
goto v___jp_1706_;
}
else
{
v___y_1707_ = v___x_1750_;
v___y_1708_ = v___y_1736_;
v___y_1709_ = v___y_1739_;
v___y_1710_ = v_a_1749_;
v___y_1711_ = v___y_1740_;
v___y_1712_ = v___y_1741_;
v___y_1713_ = v___y_1742_;
v___y_1714_ = v___y_1743_;
v___y_1715_ = v___x_1753_;
goto v___jp_1706_;
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref_known(v___x_1747_, 1);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v_matchDeclName_1431_);
v_a_1755_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1748_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1748_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v_matchDeclName_1431_);
return v___x_1745_;
}
}
else
{
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___y_1737_);
lean_dec(v_matchDeclName_1431_);
return v___y_1738_;
}
}
v___jp_1763_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1769_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1432_, v___x_1768_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = 1;
v___x_1772_ = l_Lean_Meta_saveState___redArg(v___y_1765_, v___y_1767_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
lean_inc(v_a_1770_);
v___x_1774_ = l_Lean_MVarId_refl(v_a_1770_, v___x_1771_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v___x_1775_; 
lean_dec_ref_known(v___x_1774_, 1);
lean_dec(v_a_1773_);
lean_dec(v_a_1770_);
v___x_1775_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1440_ = v___y_1764_;
v___y_1441_ = v___y_1766_;
v___y_1442_ = v___y_1767_;
v___y_1443_ = v___y_1765_;
v_a_1444_ = v___x_1775_;
goto v___jp_1439_;
}
else
{
lean_object* v_a_1776_; uint8_t v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1774_, 0);
v___x_1777_ = l_Lean_Exception_isInterrupt(v_a_1776_);
if (v___x_1777_ == 0)
{
uint8_t v___x_1778_; 
lean_inc(v_a_1776_);
v___x_1778_ = l_Lean_Exception_isRuntime(v_a_1776_);
v___y_1736_ = v___x_1771_;
v___y_1737_ = v_a_1773_;
v___y_1738_ = v___x_1774_;
v___y_1739_ = v___y_1764_;
v___y_1740_ = v___y_1766_;
v___y_1741_ = v_a_1770_;
v___y_1742_ = v___y_1767_;
v___y_1743_ = v___y_1765_;
v___y_1744_ = v___x_1778_;
goto v___jp_1735_;
}
else
{
v___y_1736_ = v___x_1771_;
v___y_1737_ = v_a_1773_;
v___y_1738_ = v___x_1774_;
v___y_1739_ = v___y_1764_;
v___y_1740_ = v___y_1766_;
v___y_1741_ = v_a_1770_;
v___y_1742_ = v___y_1767_;
v___y_1743_ = v___y_1765_;
v___y_1744_ = v___x_1777_;
goto v___jp_1735_;
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_a_1770_);
lean_dec_ref(v___y_1766_);
lean_dec(v_matchDeclName_1431_);
v_a_1779_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1772_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1772_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v___y_1766_);
lean_dec(v_matchDeclName_1431_);
v_a_1787_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1769_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1769_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
v___jp_1805_:
{
uint8_t v_hasTrace_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_hasTrace_1806_ = lean_ctor_get_uint8(v_options_1801_, sizeof(void*)*1);
v___x_1807_ = lean_unsigned_to_nat(1u);
v___x_1808_ = lean_nat_add(v_currRecDepth_1796_, v___x_1807_);
lean_inc(v_ref_1797_);
lean_inc_ref(v_toCold_1795_);
v___x_1809_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1809_, 0, v_toCold_1795_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
lean_ctor_set(v___x_1809_, 2, v_ref_1797_);
lean_ctor_set_uint16(v___x_1809_, sizeof(void*)*3, v_optionFlags_1798_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*3 + 2, v_suppressElabErrors_1799_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*3 + 3, v_isRecordingDeps_1800_);
if (v_hasTrace_1806_ == 0)
{
v___y_1764_ = v_a_1434_;
v___y_1765_ = v_a_1435_;
v___y_1766_ = v___x_1809_;
v___y_1767_ = v_a_1437_;
goto v___jp_1763_;
}
else
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1811_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1803_, v_options_1801_, v___x_1810_);
if (v___x_1811_ == 0)
{
v___y_1764_ = v_a_1434_;
v___y_1765_ = v_a_1435_;
v___y_1766_ = v___x_1809_;
v___y_1767_ = v_a_1437_;
goto v___jp_1763_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1812_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1432_);
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_mvarId_1432_);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1812_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1804_, v___x_1814_, v_a_1434_, v_a_1435_, v___x_1809_, v_a_1437_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_dec_ref_known(v___x_1815_, 1);
v___y_1764_ = v_a_1434_;
v___y_1765_ = v_a_1435_;
v___y_1766_ = v___x_1809_;
v___y_1767_ = v_a_1437_;
goto v___jp_1763_;
}
else
{
lean_dec_ref_known(v___x_1809_, 3);
lean_dec(v_mvarId_1432_);
lean_dec(v_matchDeclName_1431_);
return v___x_1815_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_1431_ = stack[0].m_obj;
lean_object* v_mvarId_1432_ = stack[1].m_obj;
lean_object* v_depth_1433_ = stack[2].m_obj;
lean_object* v_a_1434_ = stack[3].m_obj;
lean_object* v_a_1435_ = stack[4].m_obj;
lean_object* v_a_1436_ = stack[5].m_obj;
lean_object* v_a_1437_ = stack[6].m_obj;
lean_object* v_res_1820_;
v_res_1820_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1431_, v_mvarId_1432_, v_depth_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
stack->m_obj
 = v_res_1820_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1821_, lean_object* v_matchDeclName_1822_, lean_object* v_as_1823_, size_t v_i_1824_, size_t v_stop_1825_, lean_object* v_b_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
uint8_t v___x_1832_; 
v___x_1832_ = lean_usize_dec_eq(v_i_1824_, v_stop_1825_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1833_ = lean_array_uget_borrowed(v_as_1823_, v_i_1824_);
v___x_1834_ = lean_unsigned_to_nat(1u);
v___x_1835_ = lean_nat_add(v_depth_1821_, v___x_1834_);
lean_inc(v___x_1833_);
lean_inc(v_matchDeclName_1822_);
v___x_1836_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1822_, v___x_1833_, v___x_1835_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___x_1835_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; size_t v___x_1838_; size_t v___x_1839_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = ((size_t)1ULL);
v___x_1839_ = lean_usize_add(v_i_1824_, v___x_1838_);
v_i_1824_ = v___x_1839_;
v_b_1826_ = v_a_1837_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1822_);
return v___x_1836_;
}
}
else
{
lean_object* v___x_1841_; 
lean_dec(v_matchDeclName_1822_);
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_b_1826_);
return v___x_1841_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_depth_1821_ = stack[0].m_obj;
lean_object* v_matchDeclName_1822_ = stack[1].m_obj;
lean_object* v_as_1823_ = stack[2].m_obj;
size_t v_i_1824_ = stack[3].m_num;
size_t v_stop_1825_ = stack[4].m_num;
lean_object* v_b_1826_ = stack[5].m_obj;
lean_object* v___y_1827_ = stack[6].m_obj;
lean_object* v___y_1828_ = stack[7].m_obj;
lean_object* v___y_1829_ = stack[8].m_obj;
lean_object* v___y_1830_ = stack[9].m_obj;
lean_object* v_res_1842_;
v_res_1842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1821_, v_matchDeclName_1822_, v_as_1823_, v_i_1824_, v_stop_1825_, v_b_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
stack->m_obj
 = v_res_1842_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1843_, lean_object* v_matchDeclName_1844_, lean_object* v_as_1845_, lean_object* v_i_1846_, lean_object* v_stop_1847_, lean_object* v_b_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
size_t v_i_boxed_1854_; size_t v_stop_boxed_1855_; lean_object* v_res_1856_; 
v_i_boxed_1854_ = lean_unbox_usize(v_i_1846_);
lean_dec(v_i_1846_);
v_stop_boxed_1855_ = lean_unbox_usize(v_stop_1847_);
lean_dec(v_stop_1847_);
v_res_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1843_, v_matchDeclName_1844_, v_as_1845_, v_i_boxed_1854_, v_stop_boxed_1855_, v_b_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec_ref(v_as_1845_);
lean_dec(v_depth_1843_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1857_, lean_object* v_mvarId_1858_, lean_object* v_depth_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1857_, v_mvarId_1858_, v_depth_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_depth_1859_);
return v_res_1865_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1866_, lean_object* v___y_1867_){
_start:
{
uint8_t v___x_1869_; 
v___x_1869_ = l_Lean_Expr_hasMVar(v_e_1866_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_e_1866_);
return v___x_1870_;
}
else
{
lean_object* v___x_1871_; lean_object* v_mctx_1872_; lean_object* v___x_1873_; lean_object* v_fst_1874_; lean_object* v_snd_1875_; lean_object* v___x_1876_; lean_object* v_cache_1877_; lean_object* v_zetaDeltaFVarIds_1878_; lean_object* v_postponed_1879_; lean_object* v_diag_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1889_; 
v___x_1871_ = lean_st_ref_get(v___y_1867_);
v_mctx_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc_ref(v_mctx_1872_);
lean_dec(v___x_1871_);
v___x_1873_ = l_Lean_instantiateMVarsCore(v_mctx_1872_, v_e_1866_);
v_fst_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_fst_1874_);
v_snd_1875_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_snd_1875_);
lean_dec_ref(v___x_1873_);
v___x_1876_ = lean_st_ref_take(v___y_1867_);
v_cache_1877_ = lean_ctor_get(v___x_1876_, 1);
v_zetaDeltaFVarIds_1878_ = lean_ctor_get(v___x_1876_, 2);
v_postponed_1879_ = lean_ctor_get(v___x_1876_, 3);
v_diag_1880_ = lean_ctor_get(v___x_1876_, 4);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v___x_1876_, 0);
lean_dec(v_unused_1890_);
v___x_1882_ = v___x_1876_;
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_diag_1880_);
lean_inc(v_postponed_1879_);
lean_inc(v_zetaDeltaFVarIds_1878_);
lean_inc(v_cache_1877_);
lean_dec(v___x_1876_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1889_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v_snd_1875_);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_snd_1875_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_cache_1877_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_zetaDeltaFVarIds_1878_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_postponed_1879_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_diag_1880_);
v___x_1885_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_st_ref_put(v___y_1867_, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_fst_1874_);
return v___x_1887_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1866_ = stack[0].m_obj;
lean_object* v___y_1867_ = stack[1].m_obj;
lean_object* v_res_1891_;
v_res_1891_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1866_, v___y_1867_);
stack->m_obj
 = v_res_1891_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1892_, v___y_1893_);
lean_dec(v___y_1893_);
return v_res_1895_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1896_, v___y_1898_);
return v___x_1902_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1896_ = stack[0].m_obj;
lean_object* v___y_1897_ = stack[1].m_obj;
lean_object* v___y_1898_ = stack[2].m_obj;
lean_object* v___y_1899_ = stack[3].m_obj;
lean_object* v___y_1900_ = stack[4].m_obj;
lean_object* v_res_1903_;
v_res_1903_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
stack->m_obj
 = v_res_1903_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v_res_1910_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1911_, lean_object* v_localInsts_1912_, lean_object* v_x_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1911_, v_localInsts_1912_, v_x_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_a_1928_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1919_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1919_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1911_ = stack[0].m_obj;
lean_object* v_localInsts_1912_ = stack[1].m_obj;
lean_object* v_x_1913_ = stack[2].m_obj;
lean_object* v___y_1914_ = stack[3].m_obj;
lean_object* v___y_1915_ = stack[4].m_obj;
lean_object* v___y_1916_ = stack[5].m_obj;
lean_object* v___y_1917_ = stack[6].m_obj;
lean_object* v_res_1936_;
v_res_1936_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1911_, v_localInsts_1912_, v_x_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
stack->m_obj
 = v_res_1936_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1937_, lean_object* v_localInsts_1938_, lean_object* v_x_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1937_, v_localInsts_1938_, v_x_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
return v_res_1945_;
}
}
lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1946_, lean_object* v_lctx_1947_, lean_object* v_localInsts_1948_, lean_object* v_x_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1947_, v_localInsts_1948_, v_x_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1947_ = stack[1].m_obj;
lean_object* v_localInsts_1948_ = stack[2].m_obj;
lean_object* v_x_1949_ = stack[3].m_obj;
lean_object* v___y_1950_ = stack[4].m_obj;
lean_object* v___y_1951_ = stack[5].m_obj;
lean_object* v___y_1952_ = stack[6].m_obj;
lean_object* v___y_1953_ = stack[7].m_obj;
lean_object* v_res_1956_;
v_res_1956_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_box(0), v_lctx_1947_, v_localInsts_1948_, v_x_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
stack->m_obj
 = v_res_1956_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1957_, lean_object* v_lctx_1958_, lean_object* v_localInsts_1959_, lean_object* v_x_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1957_, v_lctx_1958_, v_localInsts_1959_, v_x_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
return v_res_1966_;
}
}
uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1967_, lean_object* v_x_1968_){
_start:
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_name_eq(v_x_1968_, v_matchDeclName_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_proveCondEqThm___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_1967_ = stack[0].m_obj;
lean_object* v_x_1968_ = stack[1].m_obj;
uint8_t v_res_1970_;
v_res_1970_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1967_, v_x_1968_);
stack->m_num = v_res_1970_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1971_, lean_object* v_x_1972_){
_start:
{
uint8_t v_res_1973_; lean_object* v_r_1974_; 
v_res_1973_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1971_, v_x_1972_);
lean_dec(v_x_1972_);
lean_dec(v_matchDeclName_1971_);
v_r_1974_ = lean_box(v_res_1973_);
return v_r_1974_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1975_, lean_object* v_a_1976_, lean_object* v_b_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_nat_dec_lt(v_a_1976_, v_upperBound_1975_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_dec(v_a_1976_);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v_b_1977_);
return v___x_1984_;
}
else
{
uint8_t v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = 0;
v___x_1986_ = l_Lean_Meta_introSubstEq(v_b_1977_, v___x_1985_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v_snd_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v_snd_1988_ = lean_ctor_get(v_a_1987_, 1);
lean_inc(v_snd_1988_);
lean_dec(v_a_1987_);
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = lean_nat_add(v_a_1976_, v___x_1989_);
lean_dec(v_a_1976_);
v_a_1976_ = v___x_1990_;
v_b_1977_ = v_snd_1988_;
goto _start;
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_a_1976_);
v_a_1992_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1986_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1986_);
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
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1975_ = stack[0].m_obj;
lean_object* v_a_1976_ = stack[1].m_obj;
lean_object* v_b_1977_ = stack[2].m_obj;
lean_object* v___y_1978_ = stack[3].m_obj;
lean_object* v___y_1979_ = stack[4].m_obj;
lean_object* v___y_1980_ = stack[5].m_obj;
lean_object* v___y_1981_ = stack[6].m_obj;
lean_object* v_res_2000_;
v_res_2000_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1975_, v_a_1976_, v_b_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
stack->m_obj
 = v_res_2000_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_2001_, lean_object* v_a_2002_, lean_object* v_b_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2001_, v_a_2002_, v_b_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v_upperBound_2001_);
return v_res_2009_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_2012_ = l_Lean_stringToMessageData(v___x_2011_);
return v___x_2012_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_2015_ = l_Lean_stringToMessageData(v___x_2014_);
return v___x_2015_;
}
}
lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_2016_, lean_object* v___f_2017_, lean_object* v_matchDeclName_2018_, lean_object* v___x_2019_, lean_object* v_heqNum_2020_, lean_object* v_heqPos_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2181_; 
v___x_2027_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_2016_, v___y_2023_);
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2181_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2181_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_box(0);
v___x_2033_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2028_, v___x_2032_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2180_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2180_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2180_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; uint8_t v___y_2045_; lean_object* v_mvarId_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v_toCold_2102_; lean_object* v_options_2103_; lean_object* v_inheritedTraceOptions_2104_; uint8_t v_hasTrace_2105_; lean_object* v___x_2106_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; 
v_toCold_2102_ = lean_ctor_get(v___y_2024_, 0);
v_options_2103_ = lean_ctor_get(v_toCold_2102_, 2);
v_inheritedTraceOptions_2104_ = lean_ctor_get(v_toCold_2102_, 11);
v_hasTrace_2105_ = lean_ctor_get_uint8(v_options_2103_, sizeof(void*)*1);
v___x_2106_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2105_ == 0)
{
v___y_2108_ = v___y_2022_;
v___y_2109_ = v___y_2023_;
v___y_2110_ = v___y_2024_;
v___y_2111_ = v___y_2025_;
goto v___jp_2107_;
}
else
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2166_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2104_, v_options_2103_, v___x_2165_);
if (v___x_2166_ == 0)
{
v___y_2108_ = v___y_2022_;
v___y_2109_ = v___y_2023_;
v___y_2110_ = v___y_2024_;
v___y_2111_ = v___y_2025_;
goto v___jp_2107_;
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2167_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2168_ = l_Lean_Expr_mvarId_x21(v_a_2034_);
v___x_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2167_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2106_, v___x_2170_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_dec_ref_known(v___x_2171_, 1);
v___y_2108_ = v___y_2022_;
v___y_2109_ = v___y_2023_;
v___y_2110_ = v___y_2024_;
v___y_2111_ = v___y_2025_;
goto v___jp_2107_;
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_del_object(v___x_2036_);
lean_dec(v_a_2034_);
lean_del_object(v___x_2030_);
lean_dec(v_heqPos_2021_);
lean_dec(v___x_2019_);
lean_dec(v_matchDeclName_2018_);
lean_dec_ref(v___f_2017_);
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
v___jp_2038_:
{
if (v___y_2045_ == 0)
{
lean_object* v___x_2046_; 
lean_dec_ref(v___y_2043_);
lean_del_object(v___x_2036_);
v___x_2046_ = l_Lean_MVarId_deltaTarget(v___y_2042_, v___f_2017_, v___y_2041_, v___y_2039_, v___y_2040_, v___y_2044_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v___x_2048_ = l_Lean_MVarId_heqOfEq(v_a_2047_, v___y_2041_, v___y_2039_, v___y_2040_, v___y_2044_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_2018_, v_a_2049_, v___x_2019_, v___y_2041_, v___y_2039_, v___y_2040_, v___y_2044_);
lean_dec(v___x_2019_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v___x_2051_; 
lean_dec_ref_known(v___x_2050_, 1);
v___x_2051_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2034_, v___y_2039_);
return v___x_2051_;
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec(v_a_2034_);
v_a_2052_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2050_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2050_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_2034_);
lean_dec(v___x_2019_);
lean_dec(v_matchDeclName_2018_);
v_a_2060_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2048_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2048_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_2034_);
lean_dec(v___x_2019_);
lean_dec(v_matchDeclName_2018_);
v_a_2068_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2046_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2046_);
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
else
{
lean_object* v___x_2077_; 
lean_dec(v___y_2042_);
lean_dec(v_a_2034_);
lean_dec(v___x_2019_);
lean_dec(v_matchDeclName_2018_);
lean_dec_ref(v___f_2017_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 1);
lean_ctor_set(v___x_2036_, 0, v___y_2043_);
v___x_2077_ = v___x_2036_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___y_2043_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
v___jp_2079_:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_MVarId_intros(v_mvarId_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v_snd_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v_snd_2087_ = lean_ctor_get(v_a_2086_, 1);
lean_inc_n(v_snd_2087_, 2);
lean_dec(v_a_2086_);
v___x_2088_ = 1;
v___x_2089_ = l_Lean_MVarId_refl(v_snd_2087_, v___x_2088_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v___x_2090_; 
lean_dec_ref_known(v___x_2089_, 1);
lean_dec(v_snd_2087_);
lean_del_object(v___x_2036_);
lean_dec(v___x_2019_);
lean_dec(v_matchDeclName_2018_);
lean_dec_ref(v___f_2017_);
v___x_2090_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2034_, v___y_2082_);
return v___x_2090_;
}
else
{
lean_object* v_a_2091_; uint8_t v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2092_ = l_Lean_Exception_isInterrupt(v_a_2091_);
if (v___x_2092_ == 0)
{
uint8_t v___x_2093_; 
lean_inc(v_a_2091_);
v___x_2093_ = l_Lean_Exception_isRuntime(v_a_2091_);
v___y_2039_ = v___y_2082_;
v___y_2040_ = v___y_2083_;
v___y_2041_ = v___y_2081_;
v___y_2042_ = v_snd_2087_;
v___y_2043_ = v_a_2091_;
v___y_2044_ = v___y_2084_;
v___y_2045_ = v___x_2093_;
goto v___jp_2038_;
}
else
{
v___y_2039_ = v___y_2082_;
v___y_2040_ = v___y_2083_;
v___y_2041_ = v___y_2081_;
v___y_2042_ = v_snd_2087_;
v___y_2043_ = v_a_2091_;
v___y_2044_ = v___y_2084_;
v___y_2045_ = v___x_2092_;
goto v___jp_2038_;
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_del_object(v___x_2036_);
lean_dec(v_a_2034_);
lean_dec(v___x_2019_);
lean_dec(v_matchDeclName_2018_);
lean_dec_ref(v___f_2017_);
v_a_2094_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2085_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2085_);
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
v___jp_2107_:
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = l_Lean_Expr_mvarId_x21(v_a_2034_);
v___x_2113_ = lean_nat_dec_lt(v___x_2019_, v_heqNum_2020_);
if (v___x_2113_ == 0)
{
lean_del_object(v___x_2030_);
lean_dec(v_heqPos_2021_);
v_mvarId_2080_ = v___x_2112_;
v___y_2081_ = v___y_2108_;
v___y_2082_ = v___y_2109_;
v___y_2083_ = v___y_2110_;
v___y_2084_ = v___y_2111_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2114_; uint8_t v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = lean_box(0);
v___x_2115_ = 0;
v___x_2116_ = l_Lean_Meta_introNCore(v___x_2112_, v_heqPos_2021_, v___x_2114_, v___x_2115_, v___x_2115_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_snd_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2155_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v_snd_2118_ = lean_ctor_get(v_a_2117_, 1);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_a_2117_);
if (v_isSharedCheck_2155_ == 0)
{
lean_object* v_unused_2156_; 
v_unused_2156_ = lean_ctor_get(v_a_2117_, 0);
lean_dec(v_unused_2156_);
v___x_2120_ = v_a_2117_;
v_isShared_2121_ = v_isSharedCheck_2155_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_snd_2118_);
lean_dec(v_a_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2155_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; 
lean_inc(v___x_2019_);
v___x_2122_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_2020_, v___x_2019_, v_snd_2118_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_toCold_2123_; lean_object* v_options_2124_; uint8_t v_hasTrace_2125_; 
v_toCold_2123_ = lean_ctor_get(v___y_2110_, 0);
v_options_2124_ = lean_ctor_get(v_toCold_2123_, 2);
v_hasTrace_2125_ = lean_ctor_get_uint8(v_options_2124_, sizeof(void*)*1);
if (v_hasTrace_2125_ == 0)
{
lean_object* v_a_2126_; 
lean_del_object(v___x_2120_);
lean_del_object(v___x_2030_);
v_a_2126_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2122_, 1);
v_mvarId_2080_ = v_a_2126_;
v___y_2081_ = v___y_2108_;
v___y_2082_ = v___y_2109_;
v___y_2083_ = v___y_2110_;
v___y_2084_ = v___y_2111_;
goto v___jp_2079_;
}
else
{
lean_object* v_a_2127_; lean_object* v_inheritedTraceOptions_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v_a_2127_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2122_, 1);
v_inheritedTraceOptions_2128_ = lean_ctor_get(v_toCold_2123_, 11);
v___x_2129_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2128_, v_options_2124_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_del_object(v___x_2120_);
lean_del_object(v___x_2030_);
v_mvarId_2080_ = v_a_2127_;
v___y_2081_ = v___y_2108_;
v___y_2082_ = v___y_2109_;
v___y_2083_ = v___y_2110_;
v___y_2084_ = v___y_2111_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2127_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 1);
lean_ctor_set(v___x_2030_, 0, v_a_2127_);
v___x_2133_ = v___x_2030_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2127_);
v___x_2133_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set_tag(v___x_2120_, 7);
lean_ctor_set(v___x_2120_, 1, v___x_2133_);
lean_ctor_set(v___x_2120_, 0, v___x_2131_);
v___x_2135_ = v___x_2120_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2106_, v___x_2135_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_dec_ref_known(v___x_2136_, 1);
v_mvarId_2080_ = v_a_2127_;
v___y_2081_ = v___y_2108_;
v___y_2082_ = v___y_2109_;
v___y_2083_ = v___y_2110_;
v___y_2084_ = v___y_2111_;
goto v___jp_2079_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_a_2127_);
lean_del_object(v___x_2036_);
lean_dec(v_a_2034_);
lean_dec(v___x_2019_);
lean_dec(v_matchDeclName_2018_);
lean_dec_ref(v___f_2017_);
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
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
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_del_object(v___x_2120_);
lean_del_object(v___x_2036_);
lean_dec(v_a_2034_);
lean_del_object(v___x_2030_);
lean_dec(v___x_2019_);
lean_dec(v_matchDeclName_2018_);
lean_dec_ref(v___f_2017_);
v_a_2147_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2122_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2122_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_del_object(v___x_2036_);
lean_dec(v_a_2034_);
lean_del_object(v___x_2030_);
lean_dec(v___x_2019_);
lean_dec(v_matchDeclName_2018_);
lean_dec_ref(v___f_2017_);
v_a_2157_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2116_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2116_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2030_);
lean_dec(v_heqPos_2021_);
lean_dec(v___x_2019_);
lean_dec(v_matchDeclName_2018_);
lean_dec_ref(v___f_2017_);
return v___x_2033_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_proveCondEqThm___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2016_ = stack[0].m_obj;
lean_object* v___f_2017_ = stack[1].m_obj;
lean_object* v_matchDeclName_2018_ = stack[2].m_obj;
lean_object* v___x_2019_ = stack[3].m_obj;
lean_object* v_heqNum_2020_ = stack[4].m_obj;
lean_object* v_heqPos_2021_ = stack[5].m_obj;
lean_object* v___y_2022_ = stack[6].m_obj;
lean_object* v___y_2023_ = stack[7].m_obj;
lean_object* v___y_2024_ = stack[8].m_obj;
lean_object* v___y_2025_ = stack[9].m_obj;
lean_object* v_res_2182_;
v_res_2182_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2016_, v___f_2017_, v_matchDeclName_2018_, v___x_2019_, v_heqNum_2020_, v_heqPos_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
stack->m_obj
 = v_res_2182_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2183_, lean_object* v___f_2184_, lean_object* v_matchDeclName_2185_, lean_object* v___x_2186_, lean_object* v_heqNum_2187_, lean_object* v_heqPos_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2183_, v___f_2184_, v_matchDeclName_2185_, v___x_2186_, v_heqNum_2187_, v_heqPos_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v_heqNum_2187_);
return v_res_2194_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_unsigned_to_nat(32u);
v___x_2199_ = lean_mk_empty_array_with_capacity(v___x_2198_);
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2201_ = ((size_t)5ULL);
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = lean_unsigned_to_nat(32u);
v___x_2204_ = lean_mk_empty_array_with_capacity(v___x_2203_);
v___x_2205_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2206_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v___x_2204_);
lean_ctor_set(v___x_2206_, 2, v___x_2202_);
lean_ctor_set(v___x_2206_, 3, v___x_2202_);
lean_ctor_set_usize(v___x_2206_, 4, v___x_2201_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2207_ = lean_box(1);
v___x_2208_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2209_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2208_);
lean_ctor_set(v___x_2210_, 2, v___x_2207_);
return v___x_2210_;
}
}
lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2213_, lean_object* v_type_2214_, lean_object* v_heqPos_2215_, lean_object* v_heqNum_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v___f_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_inc(v_matchDeclName_2213_);
v___f_2222_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2222_, 0, v_matchDeclName_2213_);
v___x_2223_ = lean_unsigned_to_nat(0u);
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 11, 6);
lean_closure_set(v___f_2224_, 0, v_type_2214_);
lean_closure_set(v___f_2224_, 1, v___f_2222_);
lean_closure_set(v___f_2224_, 2, v_matchDeclName_2213_);
lean_closure_set(v___f_2224_, 3, v___x_2223_);
lean_closure_set(v___f_2224_, 4, v_heqNum_2216_);
lean_closure_set(v___f_2224_, 5, v_heqPos_2215_);
v___x_2225_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2226_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2227_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2225_, v___x_2226_, v___f_2224_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
return v___x_2227_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_proveCondEqThm_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_2213_ = stack[0].m_obj;
lean_object* v_type_2214_ = stack[1].m_obj;
lean_object* v_heqPos_2215_ = stack[2].m_obj;
lean_object* v_heqNum_2216_ = stack[3].m_obj;
lean_object* v_a_2217_ = stack[4].m_obj;
lean_object* v_a_2218_ = stack[5].m_obj;
lean_object* v_a_2219_ = stack[6].m_obj;
lean_object* v_a_2220_ = stack[7].m_obj;
lean_object* v_res_2228_;
v_res_2228_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2213_, v_type_2214_, v_heqPos_2215_, v_heqNum_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
stack->m_obj
 = v_res_2228_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2229_, lean_object* v_type_2230_, lean_object* v_heqPos_2231_, lean_object* v_heqNum_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2229_, v_type_2230_, v_heqPos_2231_, v_heqNum_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
return v_res_2238_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2239_, lean_object* v_inst_2240_, lean_object* v_R_2241_, lean_object* v_a_2242_, lean_object* v_b_2243_, lean_object* v_c_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2239_, v_a_2242_, v_b_2243_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2239_ = stack[0].m_obj;
lean_object* v_a_2242_ = stack[3].m_obj;
lean_object* v_b_2243_ = stack[4].m_obj;
lean_object* v___y_2245_ = stack[6].m_obj;
lean_object* v___y_2246_ = stack[7].m_obj;
lean_object* v___y_2247_ = stack[8].m_obj;
lean_object* v___y_2248_ = stack[9].m_obj;
lean_object* v_res_2251_;
v_res_2251_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2239_, lean_box(0), lean_box(0), v_a_2242_, v_b_2243_, lean_box(0), v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
stack->m_obj
 = v_res_2251_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2252_, lean_object* v_inst_2253_, lean_object* v_R_2254_, lean_object* v_a_2255_, lean_object* v_b_2256_, lean_object* v_c_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2252_, v_inst_2253_, v_R_2254_, v_a_2255_, v_b_2256_, v_c_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v_upperBound_2252_);
return v_res_2263_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2264_, lean_object* v_b_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
lean_inc(v___y_2269_);
lean_inc_ref(v___y_2268_);
lean_inc(v___y_2267_);
lean_inc_ref(v___y_2266_);
v___x_2271_ = lean_apply_6(v_k_2264_, v_b_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, lean_box(0));
return v___x_2271_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2264_ = stack[0].m_obj;
lean_object* v_b_2265_ = stack[1].m_obj;
lean_object* v___y_2266_ = stack[2].m_obj;
lean_object* v___y_2267_ = stack[3].m_obj;
lean_object* v___y_2268_ = stack[4].m_obj;
lean_object* v___y_2269_ = stack[5].m_obj;
lean_object* v_res_2272_;
v_res_2272_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2264_, v_b_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
stack->m_obj
 = v_res_2272_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2273_, lean_object* v_b_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2273_, v_b_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
return v_res_2280_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2281_, uint8_t v_bi_2282_, lean_object* v_type_2283_, lean_object* v_k_2284_, uint8_t v_kind_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___f_2291_; lean_object* v___x_2292_; 
v___f_2291_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2291_, 0, v_k_2284_);
v___x_2292_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2281_, v_bi_2282_, v_type_2283_, v___f_2291_, v_kind_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
v_a_2301_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2292_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2292_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2281_ = stack[0].m_obj;
uint8_t v_bi_2282_ = stack[1].m_num;
lean_object* v_type_2283_ = stack[2].m_obj;
lean_object* v_k_2284_ = stack[3].m_obj;
uint8_t v_kind_2285_ = stack[4].m_num;
lean_object* v___y_2286_ = stack[5].m_obj;
lean_object* v___y_2287_ = stack[6].m_obj;
lean_object* v___y_2288_ = stack[7].m_obj;
lean_object* v___y_2289_ = stack[8].m_obj;
lean_object* v_res_2309_;
v_res_2309_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2281_, v_bi_2282_, v_type_2283_, v_k_2284_, v_kind_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
stack->m_obj
 = v_res_2309_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2310_, lean_object* v_bi_2311_, lean_object* v_type_2312_, lean_object* v_k_2313_, lean_object* v_kind_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
uint8_t v_bi_boxed_2320_; uint8_t v_kind_boxed_2321_; lean_object* v_res_2322_; 
v_bi_boxed_2320_ = lean_unbox(v_bi_2311_);
v_kind_boxed_2321_ = lean_unbox(v_kind_2314_);
v_res_2322_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2310_, v_bi_boxed_2320_, v_type_2312_, v_k_2313_, v_kind_boxed_2321_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2322_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2323_, lean_object* v_name_2324_, uint8_t v_bi_2325_, lean_object* v_type_2326_, lean_object* v_k_2327_, uint8_t v_kind_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2324_, v_bi_2325_, v_type_2326_, v_k_2327_, v_kind_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
return v___x_2334_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2324_ = stack[1].m_obj;
uint8_t v_bi_2325_ = stack[2].m_num;
lean_object* v_type_2326_ = stack[3].m_obj;
lean_object* v_k_2327_ = stack[4].m_obj;
uint8_t v_kind_2328_ = stack[5].m_num;
lean_object* v___y_2329_ = stack[6].m_obj;
lean_object* v___y_2330_ = stack[7].m_obj;
lean_object* v___y_2331_ = stack[8].m_obj;
lean_object* v___y_2332_ = stack[9].m_obj;
lean_object* v_res_2335_;
v_res_2335_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_box(0), v_name_2324_, v_bi_2325_, v_type_2326_, v_k_2327_, v_kind_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
stack->m_obj
 = v_res_2335_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2336_, lean_object* v_name_2337_, lean_object* v_bi_2338_, lean_object* v_type_2339_, lean_object* v_k_2340_, lean_object* v_kind_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
uint8_t v_bi_boxed_2347_; uint8_t v_kind_boxed_2348_; lean_object* v_res_2349_; 
v_bi_boxed_2347_ = lean_unbox(v_bi_2338_);
v_kind_boxed_2348_ = lean_unbox(v_kind_2341_);
v_res_2349_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2336_, v_name_2337_, v_bi_boxed_2347_, v_type_2339_, v_k_2340_, v_kind_boxed_2348_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2350_, lean_object* v_altsNew_2351_, lean_object* v_discrs_2352_, lean_object* v_patterns_2353_, lean_object* v_alts_2354_, lean_object* v_k_2355_, lean_object* v_altNew_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2350_, v_altsNew_2351_, v_discrs_2352_, v_patterns_2353_, v_alts_2354_, v_k_2355_, v_altNew_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v_i_2350_);
return v_res_2362_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2363_, lean_object* v_patterns_2364_, lean_object* v_alts_2365_, lean_object* v_k_2366_, lean_object* v_i_2367_, lean_object* v_altsNew_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2374_ = lean_array_get_size(v_alts_2365_);
v___x_2375_ = lean_nat_dec_lt(v_i_2367_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; 
lean_dec(v_i_2367_);
lean_dec_ref(v_alts_2365_);
lean_dec_ref(v_patterns_2364_);
lean_dec_ref(v_discrs_2363_);
lean_inc(v_a_2372_);
lean_inc_ref(v_a_2371_);
lean_inc(v_a_2370_);
lean_inc_ref(v_a_2369_);
v___x_2376_ = lean_apply_6(v_k_2366_, v_altsNew_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, lean_box(0));
return v___x_2376_;
}
else
{
lean_object* v___f_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_inc_ref(v_alts_2365_);
lean_inc_ref(v_patterns_2364_);
lean_inc_ref(v_discrs_2363_);
lean_inc(v_i_2367_);
v___f_2377_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2377_, 0, v_i_2367_);
lean_closure_set(v___f_2377_, 1, v_altsNew_2368_);
lean_closure_set(v___f_2377_, 2, v_discrs_2363_);
lean_closure_set(v___f_2377_, 3, v_patterns_2364_);
lean_closure_set(v___f_2377_, 4, v_alts_2365_);
lean_closure_set(v___f_2377_, 5, v_k_2366_);
v___x_2378_ = lean_array_fget(v_alts_2365_, v_i_2367_);
lean_dec(v_i_2367_);
lean_dec_ref(v_alts_2365_);
v___x_2379_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2378_, v_a_2369_, v_a_2371_, v_a_2372_);
lean_dec(v___x_2378_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v___x_2381_ = l_Lean_LocalDecl_type(v_a_2380_);
v___x_2382_ = l_Lean_Expr_replaceFVars(v___x_2381_, v_discrs_2363_, v_patterns_2364_);
lean_dec_ref(v_patterns_2364_);
lean_dec_ref(v_discrs_2363_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = l_Lean_LocalDecl_userName(v_a_2380_);
v___x_2384_ = l_Lean_LocalDecl_binderInfo(v_a_2380_);
lean_dec(v_a_2380_);
v___x_2385_ = 0;
v___x_2386_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2383_, v___x_2384_, v___x_2382_, v___f_2377_, v___x_2385_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
return v___x_2386_;
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec_ref(v___f_2377_);
lean_dec_ref(v_patterns_2364_);
lean_dec_ref(v_discrs_2363_);
v_a_2387_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2379_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2379_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_discrs_2363_ = stack[0].m_obj;
lean_object* v_patterns_2364_ = stack[1].m_obj;
lean_object* v_alts_2365_ = stack[2].m_obj;
lean_object* v_k_2366_ = stack[3].m_obj;
lean_object* v_i_2367_ = stack[4].m_obj;
lean_object* v_altsNew_2368_ = stack[5].m_obj;
lean_object* v_a_2369_ = stack[6].m_obj;
lean_object* v_a_2370_ = stack[7].m_obj;
lean_object* v_a_2371_ = stack[8].m_obj;
lean_object* v_a_2372_ = stack[9].m_obj;
lean_object* v_res_2395_;
v_res_2395_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2363_, v_patterns_2364_, v_alts_2365_, v_k_2366_, v_i_2367_, v_altsNew_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
stack->m_obj
 = v_res_2395_;
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2396_, lean_object* v_altsNew_2397_, lean_object* v_discrs_2398_, lean_object* v_patterns_2399_, lean_object* v_alts_2400_, lean_object* v_k_2401_, lean_object* v_altNew_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2408_ = lean_unsigned_to_nat(1u);
v___x_2409_ = lean_nat_add(v_i_2396_, v___x_2408_);
v___x_2410_ = lean_array_push(v_altsNew_2397_, v_altNew_2402_);
v___x_2411_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2398_, v_patterns_2399_, v_alts_2400_, v_k_2401_, v___x_2409_, v___x_2410_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2411_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_2396_ = stack[0].m_obj;
lean_object* v_altsNew_2397_ = stack[1].m_obj;
lean_object* v_discrs_2398_ = stack[2].m_obj;
lean_object* v_patterns_2399_ = stack[3].m_obj;
lean_object* v_alts_2400_ = stack[4].m_obj;
lean_object* v_k_2401_ = stack[5].m_obj;
lean_object* v_altNew_2402_ = stack[6].m_obj;
lean_object* v___y_2403_ = stack[7].m_obj;
lean_object* v___y_2404_ = stack[8].m_obj;
lean_object* v___y_2405_ = stack[9].m_obj;
lean_object* v___y_2406_ = stack[10].m_obj;
lean_object* v_res_2412_;
v_res_2412_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2396_, v_altsNew_2397_, v_discrs_2398_, v_patterns_2399_, v_alts_2400_, v_k_2401_, v_altNew_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
stack->m_obj
 = v_res_2412_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2413_, lean_object* v_patterns_2414_, lean_object* v_alts_2415_, lean_object* v_k_2416_, lean_object* v_i_2417_, lean_object* v_altsNew_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2413_, v_patterns_2414_, v_alts_2415_, v_k_2416_, v_i_2417_, v_altsNew_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
return v_res_2424_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2425_, lean_object* v_discrs_2426_, lean_object* v_patterns_2427_, lean_object* v_alts_2428_, lean_object* v_k_2429_, lean_object* v_i_2430_, lean_object* v_altsNew_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2426_, v_patterns_2427_, v_alts_2428_, v_k_2429_, v_i_2430_, v_altsNew_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
return v___x_2437_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_discrs_2426_ = stack[1].m_obj;
lean_object* v_patterns_2427_ = stack[2].m_obj;
lean_object* v_alts_2428_ = stack[3].m_obj;
lean_object* v_k_2429_ = stack[4].m_obj;
lean_object* v_i_2430_ = stack[5].m_obj;
lean_object* v_altsNew_2431_ = stack[6].m_obj;
lean_object* v_a_2432_ = stack[7].m_obj;
lean_object* v_a_2433_ = stack[8].m_obj;
lean_object* v_a_2434_ = stack[9].m_obj;
lean_object* v_a_2435_ = stack[10].m_obj;
lean_object* v_res_2438_;
v_res_2438_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_box(0), v_discrs_2426_, v_patterns_2427_, v_alts_2428_, v_k_2429_, v_i_2430_, v_altsNew_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
stack->m_obj
 = v_res_2438_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2439_, lean_object* v_discrs_2440_, lean_object* v_patterns_2441_, lean_object* v_alts_2442_, lean_object* v_k_2443_, lean_object* v_i_2444_, lean_object* v_altsNew_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2439_, v_discrs_2440_, v_patterns_2441_, v_alts_2442_, v_k_2443_, v_i_2444_, v_altsNew_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
return v_res_2451_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2454_, lean_object* v_discrs_2455_, lean_object* v_patterns_2456_, lean_object* v_alts_2457_, lean_object* v_k_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = lean_unsigned_to_nat(0u);
v___x_2465_ = lean_nat_dec_eq(v_numDiscrEqs_2454_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2467_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2455_, v_patterns_2456_, v_alts_2457_, v_k_2458_, v___x_2464_, v___x_2466_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
return v___x_2467_;
}
else
{
lean_object* v___x_2468_; 
lean_dec_ref(v_patterns_2456_);
lean_dec_ref(v_discrs_2455_);
lean_inc(v_a_2462_);
lean_inc_ref(v_a_2461_);
lean_inc(v_a_2460_);
lean_inc_ref(v_a_2459_);
v___x_2468_ = lean_apply_6(v_k_2458_, v_alts_2457_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, lean_box(0));
return v___x_2468_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_numDiscrEqs_2454_ = stack[0].m_obj;
lean_object* v_discrs_2455_ = stack[1].m_obj;
lean_object* v_patterns_2456_ = stack[2].m_obj;
lean_object* v_alts_2457_ = stack[3].m_obj;
lean_object* v_k_2458_ = stack[4].m_obj;
lean_object* v_a_2459_ = stack[5].m_obj;
lean_object* v_a_2460_ = stack[6].m_obj;
lean_object* v_a_2461_ = stack[7].m_obj;
lean_object* v_a_2462_ = stack[8].m_obj;
lean_object* v_res_2469_;
v_res_2469_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2454_, v_discrs_2455_, v_patterns_2456_, v_alts_2457_, v_k_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
stack->m_obj
 = v_res_2469_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2470_, lean_object* v_discrs_2471_, lean_object* v_patterns_2472_, lean_object* v_alts_2473_, lean_object* v_k_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2470_, v_discrs_2471_, v_patterns_2472_, v_alts_2473_, v_k_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_numDiscrEqs_2470_);
return v_res_2480_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2481_, lean_object* v_numDiscrEqs_2482_, lean_object* v_discrs_2483_, lean_object* v_patterns_2484_, lean_object* v_alts_2485_, lean_object* v_k_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2482_, v_discrs_2483_, v_patterns_2484_, v_alts_2485_, v_k_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_0interp(lean_interpreter_value* stack)
{
lean_object* v_numDiscrEqs_2482_ = stack[1].m_obj;
lean_object* v_discrs_2483_ = stack[2].m_obj;
lean_object* v_patterns_2484_ = stack[3].m_obj;
lean_object* v_alts_2485_ = stack[4].m_obj;
lean_object* v_k_2486_ = stack[5].m_obj;
lean_object* v_a_2487_ = stack[6].m_obj;
lean_object* v_a_2488_ = stack[7].m_obj;
lean_object* v_a_2489_ = stack[8].m_obj;
lean_object* v_a_2490_ = stack[9].m_obj;
lean_object* v_res_2493_;
v_res_2493_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_box(0), v_numDiscrEqs_2482_, v_discrs_2483_, v_patterns_2484_, v_alts_2485_, v_k_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_);
stack->m_obj
 = v_res_2493_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2494_, lean_object* v_numDiscrEqs_2495_, lean_object* v_discrs_2496_, lean_object* v_patterns_2497_, lean_object* v_alts_2498_, lean_object* v_k_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2494_, v_numDiscrEqs_2495_, v_discrs_2496_, v_patterns_2497_, v_alts_2498_, v_k_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_numDiscrEqs_2495_);
return v_res_2505_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(lean_object* v_declName_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; lean_object* v_env_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2509_ = lean_st_ref_get(v___y_2507_);
v_env_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc_ref(v_env_2510_);
lean_dec(v___x_2509_);
v___x_2511_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2510_, v_declName_2506_);
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2506_ = stack[0].m_obj;
lean_object* v___y_2507_ = stack[1].m_obj;
lean_object* v_res_2513_;
v_res_2513_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2506_, v___y_2507_);
stack->m_obj
 = v_res_2513_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg___boxed(lean_object* v_declName_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2514_, v___y_2515_);
lean_dec(v___y_2515_);
return v_res_2517_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_declName_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2518_, v___y_2522_);
return v___x_2524_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2518_ = stack[0].m_obj;
lean_object* v___y_2519_ = stack[1].m_obj;
lean_object* v___y_2520_ = stack[2].m_obj;
lean_object* v___y_2521_ = stack[3].m_obj;
lean_object* v___y_2522_ = stack[4].m_obj;
lean_object* v_res_2525_;
v_res_2525_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v_declName_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
stack->m_obj
 = v_res_2525_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___boxed(lean_object* v_declName_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v_declName_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2532_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v___f_2540_; lean_object* v___x_14366__overap_2541_; lean_object* v___x_2542_; 
v___f_2540_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14366__overap_2541_ = lean_panic_fn_borrowed(v___f_2540_, v_msg_2534_);
lean_inc(v___y_2538_);
lean_inc_ref(v___y_2537_);
lean_inc(v___y_2536_);
lean_inc_ref(v___y_2535_);
v___x_2542_ = lean_apply_5(v___x_14366__overap_2541_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, lean_box(0));
return v___x_2542_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2534_ = stack[0].m_obj;
lean_object* v___y_2535_ = stack[1].m_obj;
lean_object* v___y_2536_ = stack[2].m_obj;
lean_object* v___y_2537_ = stack[3].m_obj;
lean_object* v___y_2538_ = stack[4].m_obj;
lean_object* v_res_2543_;
v_res_2543_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
stack->m_obj
 = v_res_2543_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2550_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2551_, lean_object* v_b_2552_, lean_object* v_c_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; 
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
v___x_2559_ = lean_apply_7(v_k_2551_, v_b_2552_, v_c_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, lean_box(0));
return v___x_2559_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2551_ = stack[0].m_obj;
lean_object* v_b_2552_ = stack[1].m_obj;
lean_object* v_c_2553_ = stack[2].m_obj;
lean_object* v___y_2554_ = stack[3].m_obj;
lean_object* v___y_2555_ = stack[4].m_obj;
lean_object* v___y_2556_ = stack[5].m_obj;
lean_object* v___y_2557_ = stack[6].m_obj;
lean_object* v_res_2560_;
v_res_2560_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2551_, v_b_2552_, v_c_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
stack->m_obj
 = v_res_2560_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2561_, lean_object* v_b_2562_, lean_object* v_c_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2561_, v_b_2562_, v_c_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v_res_2569_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2570_, lean_object* v_k_2571_, uint8_t v_cleanupAnnotations_2572_, uint8_t v_whnfType_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___f_2579_; lean_object* v___x_2580_; 
v___f_2579_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2579_, 0, v_k_2571_);
v___x_2580_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2570_, v___f_2579_, v_cleanupAnnotations_2572_, v_whnfType_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v_a_2589_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2580_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2580_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2570_ = stack[0].m_obj;
lean_object* v_k_2571_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_2572_ = stack[2].m_num;
uint8_t v_whnfType_2573_ = stack[3].m_num;
lean_object* v___y_2574_ = stack[4].m_obj;
lean_object* v___y_2575_ = stack[5].m_obj;
lean_object* v___y_2576_ = stack[6].m_obj;
lean_object* v___y_2577_ = stack[7].m_obj;
lean_object* v_res_2597_;
v_res_2597_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2570_, v_k_2571_, v_cleanupAnnotations_2572_, v_whnfType_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
stack->m_obj
 = v_res_2597_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2598_, lean_object* v_k_2599_, lean_object* v_cleanupAnnotations_2600_, lean_object* v_whnfType_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2607_; uint8_t v_whnfType_boxed_2608_; lean_object* v_res_2609_; 
v_cleanupAnnotations_boxed_2607_ = lean_unbox(v_cleanupAnnotations_2600_);
v_whnfType_boxed_2608_ = lean_unbox(v_whnfType_2601_);
v_res_2609_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2598_, v_k_2599_, v_cleanupAnnotations_boxed_2607_, v_whnfType_boxed_2608_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
return v_res_2609_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2610_, lean_object* v_type_2611_, lean_object* v_k_2612_, uint8_t v_cleanupAnnotations_2613_, uint8_t v_whnfType_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2611_, v_k_2612_, v_cleanupAnnotations_2613_, v_whnfType_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2611_ = stack[1].m_obj;
lean_object* v_k_2612_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2613_ = stack[3].m_num;
uint8_t v_whnfType_2614_ = stack[4].m_num;
lean_object* v___y_2615_ = stack[5].m_obj;
lean_object* v___y_2616_ = stack[6].m_obj;
lean_object* v___y_2617_ = stack[7].m_obj;
lean_object* v___y_2618_ = stack[8].m_obj;
lean_object* v_res_2621_;
v_res_2621_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_box(0), v_type_2611_, v_k_2612_, v_cleanupAnnotations_2613_, v_whnfType_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
stack->m_obj
 = v_res_2621_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2622_, lean_object* v_type_2623_, lean_object* v_k_2624_, lean_object* v_cleanupAnnotations_2625_, lean_object* v_whnfType_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2632_; uint8_t v_whnfType_boxed_2633_; lean_object* v_res_2634_; 
v_cleanupAnnotations_boxed_2632_ = lean_unbox(v_cleanupAnnotations_2625_);
v_whnfType_boxed_2633_ = lean_unbox(v_whnfType_2626_);
v_res_2634_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2622_, v_type_2623_, v_k_2624_, v_cleanupAnnotations_boxed_2632_, v_whnfType_boxed_2633_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2634_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2635_, lean_object* v_splitterName_2636_, lean_object* v_matcherInput_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_matchType_2643_; lean_object* v_discrInfos_2644_; lean_object* v_lhss_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2665_; 
v_matchType_2643_ = lean_ctor_get(v_matcherInput_2637_, 1);
v_discrInfos_2644_ = lean_ctor_get(v_matcherInput_2637_, 2);
v_lhss_2645_ = lean_ctor_get(v_matcherInput_2637_, 3);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_matcherInput_2637_);
if (v_isSharedCheck_2665_ == 0)
{
lean_object* v_unused_2666_; lean_object* v_unused_2667_; 
v_unused_2666_ = lean_ctor_get(v_matcherInput_2637_, 4);
lean_dec(v_unused_2666_);
v_unused_2667_ = lean_ctor_get(v_matcherInput_2637_, 0);
lean_dec(v_unused_2667_);
v___x_2647_ = v_matcherInput_2637_;
v_isShared_2648_ = v_isSharedCheck_2665_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_lhss_2645_);
lean_inc(v_discrInfos_2644_);
lean_inc(v_matchType_2643_);
lean_dec(v_matcherInput_2637_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2665_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_overlaps_2635_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 4, v___x_2649_);
lean_ctor_set(v___x_2647_, 0, v_splitterName_2636_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_splitterName_2636_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_matchType_2643_);
lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_discrInfos_2644_);
lean_ctor_set(v_reuseFailAlloc_2664_, 3, v_lhss_2645_);
lean_ctor_set(v_reuseFailAlloc_2664_, 4, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_Meta_Match_mkMatcher(v___x_2651_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v_addMatcher_2654_; lean_object* v___x_2655_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
v_addMatcher_2654_ = lean_ctor_get(v_a_2653_, 3);
lean_inc_ref(v_addMatcher_2654_);
lean_dec(v_a_2653_);
lean_inc(v___y_2641_);
lean_inc_ref(v___y_2640_);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
v___x_2655_ = lean_apply_5(v_addMatcher_2654_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, lean_box(0));
return v___x_2655_;
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
v_a_2656_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2652_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2652_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_overlaps_2635_ = stack[0].m_obj;
lean_object* v_splitterName_2636_ = stack[1].m_obj;
lean_object* v_matcherInput_2637_ = stack[2].m_obj;
lean_object* v___y_2638_ = stack[3].m_obj;
lean_object* v___y_2639_ = stack[4].m_obj;
lean_object* v___y_2640_ = stack[5].m_obj;
lean_object* v___y_2641_ = stack[6].m_obj;
lean_object* v_res_2668_;
v_res_2668_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2635_, v_splitterName_2636_, v_matcherInput_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
stack->m_obj
 = v_res_2668_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2669_, lean_object* v_splitterName_2670_, lean_object* v_matcherInput_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2669_, v_splitterName_2670_, v_matcherInput_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
return v_res_2677_;
}
}
uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2678_, lean_object* v_ys_2679_, lean_object* v_x_2680_){
_start:
{
lean_object* v_zero_2681_; uint8_t v_isZero_2682_; 
v_zero_2681_ = lean_unsigned_to_nat(0u);
v_isZero_2682_ = lean_nat_dec_eq(v_x_2680_, v_zero_2681_);
if (v_isZero_2682_ == 1)
{
lean_dec(v_x_2680_);
return v_isZero_2682_;
}
else
{
lean_object* v_one_2683_; lean_object* v_n_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v_one_2683_ = lean_unsigned_to_nat(1u);
v_n_2684_ = lean_nat_sub(v_x_2680_, v_one_2683_);
lean_dec(v_x_2680_);
v___x_2685_ = lean_array_fget_borrowed(v_xs_2678_, v_n_2684_);
v___x_2686_ = lean_array_fget_borrowed(v_ys_2679_, v_n_2684_);
v___x_2687_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_dec(v_n_2684_);
return v___x_2687_;
}
else
{
v_x_2680_ = v_n_2684_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2678_ = stack[0].m_obj;
lean_object* v_ys_2679_ = stack[1].m_obj;
lean_object* v_x_2680_ = stack[2].m_obj;
uint8_t v_res_2689_;
v_res_2689_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2678_, v_ys_2679_, v_x_2680_);
stack->m_num = v_res_2689_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2713_, size_t v_sz_2714_, size_t v_i_2715_, lean_object* v_b_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
uint8_t v___x_2722_; 
v___x_2722_ = lean_usize_dec_lt(v_i_2715_, v_sz_2714_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; 
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
lean_object* v_a_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; 
v_a_2740_ = lean_array_uget_borrowed(v_as_2713_, v_i_2715_);
v___x_2741_ = lean_array_fget(v_array_2729_, v_start_2730_);
v___x_2742_ = lean_unsigned_to_nat(1u);
v___x_2743_ = lean_nat_add(v_start_2730_, v___x_2742_);
lean_dec(v_start_2730_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 1, v___x_2743_);
v___x_2745_ = v___x_2738_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_array_2729_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v___x_2743_);
lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_stop_2731_);
v___x_2745_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
lean_object* v___x_2746_; 
lean_inc(v_a_2740_);
v___x_2746_ = l_Lean_Meta_mkEqHEq(v_a_2740_, v___x_2741_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2748_ = l_Lean_mkArrow(v_a_2747_, v_fst_2725_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 1, v___x_2745_);
lean_ctor_set(v___x_2727_, 0, v_a_2749_);
v___x_2751_ = v___x_2727_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v___x_2745_);
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
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v___x_2745_);
lean_del_object(v___x_2727_);
v_a_2756_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2748_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2748_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec_ref(v___x_2745_);
lean_del_object(v___x_2727_);
lean_dec(v_fst_2725_);
v_a_2764_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2746_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2746_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2713_ = stack[0].m_obj;
size_t v_sz_2714_ = stack[1].m_num;
size_t v_i_2715_ = stack[2].m_num;
lean_object* v_b_2716_ = stack[3].m_obj;
lean_object* v___y_2717_ = stack[4].m_obj;
lean_object* v___y_2718_ = stack[5].m_obj;
lean_object* v___y_2719_ = stack[6].m_obj;
lean_object* v___y_2720_ = stack[7].m_obj;
lean_object* v_res_2778_;
v_res_2778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2713_, v_sz_2714_, v_i_2715_, v_b_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
stack->m_obj
 = v_res_2778_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2779_, lean_object* v_sz_2780_, lean_object* v_i_2781_, lean_object* v_b_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
size_t v_sz_boxed_2788_; size_t v_i_boxed_2789_; lean_object* v_res_2790_; 
v_sz_boxed_2788_ = lean_unbox_usize(v_sz_2780_);
lean_dec(v_sz_2780_);
v_i_boxed_2789_ = lean_unbox_usize(v_i_2781_);
lean_dec(v_i_2781_);
v_res_2790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2779_, v_sz_boxed_2788_, v_i_boxed_2789_, v_b_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec_ref(v_as_2779_);
return v_res_2790_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2791_, lean_object* v___x_2792_, lean_object* v_as_2793_, size_t v_sz_2794_, size_t v_i_2795_, lean_object* v_b_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_a_2803_; uint8_t v___x_2807_; 
v___x_2807_ = lean_usize_dec_lt(v_i_2795_, v_sz_2794_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; 
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v_b_2796_);
return v___x_2808_;
}
else
{
lean_object* v___x_2809_; lean_object* v_a_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2809_ = l_Lean_instInhabitedExpr;
v_a_2810_ = lean_array_uget_borrowed(v_as_2793_, v_i_2795_);
v___x_2811_ = lean_array_get_borrowed(v___x_2809_, v___x_2791_, v_a_2810_);
lean_inc(v___x_2811_);
v___x_2812_ = l_Lean_Meta_instantiateForall(v___x_2811_, v___x_2792_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v___x_2814_ = lean_array_get_size(v___x_2792_);
v___x_2815_ = l_Lean_Meta_Match_simpH_x3f(v_a_2813_, v___x_2814_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
if (lean_obj_tag(v_a_2816_) == 1)
{
lean_object* v_val_2817_; lean_object* v___x_2818_; 
v_val_2817_ = lean_ctor_get(v_a_2816_, 0);
lean_inc(v_val_2817_);
lean_dec_ref_known(v_a_2816_, 1);
v___x_2818_ = lean_array_push(v_b_2796_, v_val_2817_);
v_a_2803_ = v___x_2818_;
goto v___jp_2802_;
}
else
{
lean_dec(v_a_2816_);
v_a_2803_ = v_b_2796_;
goto v___jp_2802_;
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v_b_2796_);
v_a_2819_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2815_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2815_);
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
lean_dec_ref(v_b_2796_);
v_a_2827_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2812_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2812_);
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
v___jp_2802_:
{
size_t v___x_2804_; size_t v___x_2805_; 
v___x_2804_ = ((size_t)1ULL);
v___x_2805_ = lean_usize_add(v_i_2795_, v___x_2804_);
v_i_2795_ = v___x_2805_;
v_b_2796_ = v_a_2803_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2791_ = stack[0].m_obj;
lean_object* v___x_2792_ = stack[1].m_obj;
lean_object* v_as_2793_ = stack[2].m_obj;
size_t v_sz_2794_ = stack[3].m_num;
size_t v_i_2795_ = stack[4].m_num;
lean_object* v_b_2796_ = stack[5].m_obj;
lean_object* v___y_2797_ = stack[6].m_obj;
lean_object* v___y_2798_ = stack[7].m_obj;
lean_object* v___y_2799_ = stack[8].m_obj;
lean_object* v___y_2800_ = stack[9].m_obj;
lean_object* v_res_2835_;
v_res_2835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2791_, v___x_2792_, v_as_2793_, v_sz_2794_, v_i_2795_, v_b_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
stack->m_obj
 = v_res_2835_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2836_, lean_object* v___x_2837_, lean_object* v_as_2838_, lean_object* v_sz_2839_, lean_object* v_i_2840_, lean_object* v_b_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
size_t v_sz_boxed_2847_; size_t v_i_boxed_2848_; lean_object* v_res_2849_; 
v_sz_boxed_2847_ = lean_unbox_usize(v_sz_2839_);
lean_dec(v_sz_2839_);
v_i_boxed_2848_ = lean_unbox_usize(v_i_2840_);
lean_dec(v_i_2840_);
v_res_2849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2836_, v___x_2837_, v_as_2838_, v_sz_boxed_2847_, v_i_boxed_2848_, v_b_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec_ref(v_as_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v___x_2836_);
return v_res_2849_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v___x_2853_, lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v___x_2856_, lean_object* v___x_2857_, lean_object* v_rhsArgs_2858_, lean_object* v_a_2859_, lean_object* v_ys_2860_, uint8_t v___x_2861_, uint8_t v___x_2862_, uint8_t v___x_2863_, lean_object* v_matchDeclName_2864_, lean_object* v___x_2865_, lean_object* v___x_2866_, lean_object* v___x_2867_, lean_object* v___x_2868_, lean_object* v___x_2869_, lean_object* v_argMask_2870_, lean_object* v_a_2871_, lean_object* v_alts_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2878_ = lean_array_get_borrowed(v___x_2850_, v_alts_2872_, v_a_2851_);
v___x_2879_ = l_Lean_ConstantInfo_name(v_a_2852_);
v___x_2880_ = l_Lean_mkConst(v___x_2879_, v___x_2853_);
v___x_2881_ = l_Subarray_copy___redArg(v___x_2854_);
v___x_2882_ = lean_mk_empty_array_with_capacity(v___x_2855_);
v___x_2883_ = lean_array_push(v___x_2882_, v___x_2856_);
v___x_2884_ = l_Array_append___redArg(v___x_2881_, v___x_2883_);
lean_dec_ref(v___x_2883_);
lean_inc_ref(v___x_2884_);
v___x_2885_ = l_Array_append___redArg(v___x_2884_, v___x_2857_);
v___x_2886_ = l_Array_append___redArg(v___x_2885_, v_alts_2872_);
v___x_2887_ = l_Lean_mkAppN(v___x_2880_, v___x_2886_);
lean_dec_ref(v___x_2886_);
lean_inc(v___x_2878_);
v___x_2888_ = l_Lean_mkAppN(v___x_2878_, v_rhsArgs_2858_);
v___x_2889_ = l_Lean_Meta_mkEq(v___x_2887_, v___x_2888_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2891_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = l_Lean_mkArrowN(v_a_2859_, v_a_2890_, v___y_2875_, v___y_2876_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
v___x_2893_ = l_Array_append___redArg(v___x_2884_, v_ys_2860_);
v___x_2894_ = l_Array_append___redArg(v___x_2893_, v_alts_2872_);
v___x_2895_ = l_Lean_Meta_mkForallFVars(v___x_2894_, v_a_2892_, v___x_2861_, v___x_2862_, v___x_2862_, v___x_2863_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec_ref(v___x_2894_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v___x_2897_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2896_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc_n(v_a_2898_, 2);
lean_dec_ref_known(v___x_2897_, 1);
lean_inc(v___x_2865_);
v___x_2899_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2864_, v_a_2898_, v___x_2865_, v___x_2865_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 1);
lean_inc(v___x_2866_);
v___x_2901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2866_);
lean_ctor_set(v___x_2901_, 1, v___x_2867_);
lean_ctor_set(v___x_2901_, 2, v_a_2898_);
v___x_2902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2866_);
lean_ctor_set(v___x_2902_, 1, v___x_2868_);
v___x_2903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v_a_2900_);
lean_ctor_set(v___x_2903_, 2, v___x_2902_);
v___x_2904_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
v___x_2905_ = l_Lean_addDecl(v___x_2904_, v___x_2861_, v___y_2875_, v___y_2876_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2914_; 
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; 
v_unused_2915_ = lean_ctor_get(v___x_2905_, 0);
lean_dec(v_unused_2915_);
v___x_2907_ = v___x_2905_;
v_isShared_2908_ = v_isSharedCheck_2914_;
goto v_resetjp_2906_;
}
else
{
lean_dec(v___x_2905_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2914_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2869_);
lean_ctor_set(v___x_2909_, 1, v_argMask_2870_);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v_a_2871_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2910_);
v___x_2912_ = v___x_2907_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v_a_2871_);
lean_dec_ref(v_argMask_2870_);
lean_dec_ref(v___x_2869_);
v_a_2916_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2905_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2905_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v_argMask_2870_);
lean_dec_ref(v___x_2869_);
lean_dec(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec(v___x_2866_);
v_a_2924_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2899_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2899_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec_ref(v_a_2871_);
lean_dec_ref(v_argMask_2870_);
lean_dec_ref(v___x_2869_);
lean_dec(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec(v___x_2866_);
lean_dec(v___x_2865_);
lean_dec(v_matchDeclName_2864_);
v_a_2932_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2897_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2897_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec_ref(v_a_2871_);
lean_dec_ref(v_argMask_2870_);
lean_dec_ref(v___x_2869_);
lean_dec(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec(v___x_2866_);
lean_dec(v___x_2865_);
lean_dec(v_matchDeclName_2864_);
v_a_2940_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2895_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2895_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec_ref(v___x_2884_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v_argMask_2870_);
lean_dec_ref(v___x_2869_);
lean_dec(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec(v___x_2866_);
lean_dec(v___x_2865_);
lean_dec(v_matchDeclName_2864_);
v_a_2948_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2891_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2891_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec_ref(v___x_2884_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v_argMask_2870_);
lean_dec_ref(v___x_2869_);
lean_dec(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec(v___x_2866_);
lean_dec(v___x_2865_);
lean_dec(v_matchDeclName_2864_);
v_a_2956_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2889_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2889_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2850_ = stack[0].m_obj;
lean_object* v_a_2851_ = stack[1].m_obj;
lean_object* v_a_2852_ = stack[2].m_obj;
lean_object* v___x_2853_ = stack[3].m_obj;
lean_object* v___x_2854_ = stack[4].m_obj;
lean_object* v___x_2855_ = stack[5].m_obj;
lean_object* v___x_2856_ = stack[6].m_obj;
lean_object* v___x_2857_ = stack[7].m_obj;
lean_object* v_rhsArgs_2858_ = stack[8].m_obj;
lean_object* v_a_2859_ = stack[9].m_obj;
lean_object* v_ys_2860_ = stack[10].m_obj;
uint8_t v___x_2861_ = stack[11].m_num;
uint8_t v___x_2862_ = stack[12].m_num;
uint8_t v___x_2863_ = stack[13].m_num;
lean_object* v_matchDeclName_2864_ = stack[14].m_obj;
lean_object* v___x_2865_ = stack[15].m_obj;
lean_object* v___x_2866_ = stack[16].m_obj;
lean_object* v___x_2867_ = stack[17].m_obj;
lean_object* v___x_2868_ = stack[18].m_obj;
lean_object* v___x_2869_ = stack[19].m_obj;
lean_object* v_argMask_2870_ = stack[20].m_obj;
lean_object* v_a_2871_ = stack[21].m_obj;
lean_object* v_alts_2872_ = stack[22].m_obj;
lean_object* v___y_2873_ = stack[23].m_obj;
lean_object* v___y_2874_ = stack[24].m_obj;
lean_object* v___y_2875_ = stack[25].m_obj;
lean_object* v___y_2876_ = stack[26].m_obj;
lean_object* v_res_2964_;
v_res_2964_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2850_, v_a_2851_, v_a_2852_, v___x_2853_, v___x_2854_, v___x_2855_, v___x_2856_, v___x_2857_, v_rhsArgs_2858_, v_a_2859_, v_ys_2860_, v___x_2861_, v___x_2862_, v___x_2863_, v_matchDeclName_2864_, v___x_2865_, v___x_2866_, v___x_2867_, v___x_2868_, v___x_2869_, v_argMask_2870_, v_a_2871_, v_alts_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
stack->m_obj
 = v_res_2964_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2965_ = _args[0];
lean_object* v_a_2966_ = _args[1];
lean_object* v_a_2967_ = _args[2];
lean_object* v___x_2968_ = _args[3];
lean_object* v___x_2969_ = _args[4];
lean_object* v___x_2970_ = _args[5];
lean_object* v___x_2971_ = _args[6];
lean_object* v___x_2972_ = _args[7];
lean_object* v_rhsArgs_2973_ = _args[8];
lean_object* v_a_2974_ = _args[9];
lean_object* v_ys_2975_ = _args[10];
lean_object* v___x_2976_ = _args[11];
lean_object* v___x_2977_ = _args[12];
lean_object* v___x_2978_ = _args[13];
lean_object* v_matchDeclName_2979_ = _args[14];
lean_object* v___x_2980_ = _args[15];
lean_object* v___x_2981_ = _args[16];
lean_object* v___x_2982_ = _args[17];
lean_object* v___x_2983_ = _args[18];
lean_object* v___x_2984_ = _args[19];
lean_object* v_argMask_2985_ = _args[20];
lean_object* v_a_2986_ = _args[21];
lean_object* v_alts_2987_ = _args[22];
lean_object* v___y_2988_ = _args[23];
lean_object* v___y_2989_ = _args[24];
lean_object* v___y_2990_ = _args[25];
lean_object* v___y_2991_ = _args[26];
lean_object* v___y_2992_ = _args[27];
_start:
{
uint8_t v___x_18849__boxed_2993_; uint8_t v___x_18850__boxed_2994_; uint8_t v___x_18851__boxed_2995_; lean_object* v_res_2996_; 
v___x_18849__boxed_2993_ = lean_unbox(v___x_2976_);
v___x_18850__boxed_2994_ = lean_unbox(v___x_2977_);
v___x_18851__boxed_2995_ = lean_unbox(v___x_2978_);
v_res_2996_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2965_, v_a_2966_, v_a_2967_, v___x_2968_, v___x_2969_, v___x_2970_, v___x_2971_, v___x_2972_, v_rhsArgs_2973_, v_a_2974_, v_ys_2975_, v___x_18849__boxed_2993_, v___x_18850__boxed_2994_, v___x_18851__boxed_2995_, v_matchDeclName_2979_, v___x_2980_, v___x_2981_, v___x_2982_, v___x_2983_, v___x_2984_, v_argMask_2985_, v_a_2986_, v_alts_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v_alts_2987_);
lean_dec_ref(v_ys_2975_);
lean_dec_ref(v_a_2974_);
lean_dec_ref(v_rhsArgs_2973_);
lean_dec_ref(v___x_2972_);
lean_dec(v___x_2970_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v___x_2965_);
return v_res_2996_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2997_; lean_object* v_dummy_2998_; 
v___x_2997_ = lean_box(0);
v_dummy_2998_ = l_Lean_Expr_sort___override(v___x_2997_);
return v_dummy_2998_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = lean_box(0);
v___x_3003_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_3004_ = l_Lean_mkConst(v___x_3003_, v___x_3002_);
return v___x_3004_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_3007_ = l_Lean_stringToMessageData(v___x_3006_);
return v___x_3007_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_3008_, lean_object* v_overlaps_3009_, lean_object* v_a_3010_, lean_object* v_fst_3011_, lean_object* v___x_3012_, lean_object* v___x_3013_, lean_object* v___x_3014_, uint8_t v___x_3015_, lean_object* v___x_3016_, lean_object* v_a_3017_, lean_object* v___x_3018_, lean_object* v___x_3019_, lean_object* v___x_3020_, lean_object* v_matchDeclName_3021_, lean_object* v___x_3022_, lean_object* v___x_3023_, lean_object* v___x_3024_, lean_object* v___x_3025_, lean_object* v___x_3026_, lean_object* v_ys_3027_, lean_object* v___eqs_3028_, lean_object* v_rhsArgs_3029_, lean_object* v_argMask_3030_, lean_object* v_altResultType_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_dummy_3037_; lean_object* v_nargs_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; size_t v_sz_3043_; size_t v___x_3044_; lean_object* v___x_3045_; 
v_dummy_3037_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_3038_ = l_Lean_Expr_getAppNumArgs(v_altResultType_3031_);
lean_inc(v_nargs_3038_);
v___x_3039_ = lean_mk_array(v_nargs_3038_, v_dummy_3037_);
v___x_3040_ = lean_nat_sub(v_nargs_3038_, v___x_3008_);
lean_dec(v_nargs_3038_);
v___x_3041_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_3031_, v___x_3039_, v___x_3040_);
v___x_3042_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_3009_, v_a_3010_);
v_sz_3043_ = lean_array_size(v___x_3042_);
v___x_3044_ = ((size_t)0ULL);
lean_inc_ref(v___x_3012_);
v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_3011_, v___x_3041_, v___x_3042_, v_sz_3043_, v___x_3044_, v___x_3012_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec_ref(v___x_3042_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; uint8_t v___y_3052_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v_toCold_3105_; lean_object* v_options_3106_; uint8_t v_hasTrace_3107_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v_toCold_3105_ = lean_ctor_get(v___y_3034_, 0);
v_options_3106_ = lean_ctor_get(v_toCold_3105_, 2);
v_hasTrace_3107_ = lean_ctor_get_uint8(v_options_3106_, sizeof(void*)*1);
if (v_hasTrace_3107_ == 0)
{
v___y_3096_ = v___y_3032_;
v___y_3097_ = v___y_3033_;
v___y_3098_ = v___y_3034_;
v___y_3099_ = v___y_3035_;
goto v___jp_3095_;
}
else
{
lean_object* v_inheritedTraceOptions_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_inheritedTraceOptions_3108_ = lean_ctor_get(v_toCold_3105_, 11);
v___x_3109_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3110_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_3111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3108_, v_options_3106_, v___x_3110_);
if (v___x_3111_ == 0)
{
v___y_3096_ = v___y_3032_;
v___y_3097_ = v___y_3033_;
v___y_3098_ = v___y_3034_;
v___y_3099_ = v___y_3035_;
goto v___jp_3095_;
}
else
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3112_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_3046_);
v___x_3113_ = lean_array_to_list(v_a_3046_);
v___x_3114_ = lean_box(0);
v___x_3115_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3113_, v___x_3114_);
v___x_3116_ = l_Lean_MessageData_ofList(v___x_3115_);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3112_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3109_, v___x_3117_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref_known(v___x_3118_, 1);
v___y_3096_ = v___y_3032_;
v___y_3097_ = v___y_3033_;
v___y_3098_ = v___y_3034_;
v___y_3099_ = v___y_3035_;
goto v___jp_3095_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_a_3046_);
lean_dec_ref(v___x_3041_);
lean_dec_ref(v_argMask_3030_);
lean_dec_ref(v_rhsArgs_3029_);
lean_dec_ref(v_ys_3027_);
lean_dec_ref(v___x_3025_);
lean_dec(v___x_3024_);
lean_dec(v___x_3023_);
lean_dec(v___x_3022_);
lean_dec(v_matchDeclName_3021_);
lean_dec_ref(v___x_3020_);
lean_dec_ref(v___x_3019_);
lean_dec(v___x_3018_);
lean_dec_ref(v_a_3017_);
lean_dec_ref(v___x_3016_);
lean_dec_ref(v___x_3014_);
lean_dec(v___x_3013_);
lean_dec_ref(v___x_3012_);
lean_dec(v_a_3010_);
lean_dec(v___x_3008_);
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
v___jp_3047_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; size_t v_sz_3063_; lean_object* v___x_3064_; 
v___x_3053_ = lean_array_get_size(v_ys_3027_);
v___x_3054_ = lean_array_get_size(v_a_3046_);
v___x_3055_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3055_, 0, v___x_3053_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*2, v___y_3052_);
v___x_3056_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_3041_);
v___x_3057_ = l_Array_reverse___redArg(v___x_3041_);
v___x_3058_ = lean_array_get_size(v___x_3057_);
lean_inc(v___x_3013_);
v___x_3059_ = l_Array_toSubarray___redArg(v___x_3057_, v___x_3013_, v___x_3058_);
lean_inc_ref(v___x_3014_);
v___x_3060_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_3014_, v___x_3012_);
v___x_3061_ = l_Array_reverse___redArg(v___x_3060_);
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3056_);
lean_ctor_set(v___x_3062_, 1, v___x_3059_);
v_sz_3063_ = lean_array_size(v___x_3061_);
v___x_3064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3061_, v_sz_3063_, v___x_3044_, v___x_3062_, v___y_3051_, v___y_3049_, v___y_3048_, v___y_3050_);
lean_dec_ref(v___x_3061_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v_fst_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; uint8_t v___x_3070_; lean_object* v___x_3071_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v_fst_3066_ = lean_ctor_get(v_a_3065_, 0);
lean_inc(v_fst_3066_);
lean_dec(v_a_3065_);
v___x_3067_ = l_Subarray_copy___redArg(v___x_3014_);
lean_inc_ref(v___x_3067_);
v___x_3068_ = l_Array_append___redArg(v___x_3067_, v_ys_3027_);
v___x_3069_ = 0;
v___x_3070_ = 1;
v___x_3071_ = l_Lean_Meta_mkForallFVars(v___x_3068_, v_fst_3066_, v___x_3069_, v___x_3015_, v___x_3015_, v___x_3070_, v___y_3051_, v___y_3049_, v___y_3048_, v___y_3050_);
lean_dec_ref(v___x_3068_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___x_3073_ = lean_box(v___x_3069_);
v___x_3074_ = lean_box(v___x_3015_);
v___x_3075_ = lean_box(v___x_3070_);
lean_inc_ref(v___x_3041_);
v___f_3076_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_3076_, 0, v___x_3016_);
lean_closure_set(v___f_3076_, 1, v_a_3010_);
lean_closure_set(v___f_3076_, 2, v_a_3017_);
lean_closure_set(v___f_3076_, 3, v___x_3018_);
lean_closure_set(v___f_3076_, 4, v___x_3019_);
lean_closure_set(v___f_3076_, 5, v___x_3008_);
lean_closure_set(v___f_3076_, 6, v___x_3020_);
lean_closure_set(v___f_3076_, 7, v___x_3041_);
lean_closure_set(v___f_3076_, 8, v_rhsArgs_3029_);
lean_closure_set(v___f_3076_, 9, v_a_3046_);
lean_closure_set(v___f_3076_, 10, v_ys_3027_);
lean_closure_set(v___f_3076_, 11, v___x_3073_);
lean_closure_set(v___f_3076_, 12, v___x_3074_);
lean_closure_set(v___f_3076_, 13, v___x_3075_);
lean_closure_set(v___f_3076_, 14, v_matchDeclName_3021_);
lean_closure_set(v___f_3076_, 15, v___x_3013_);
lean_closure_set(v___f_3076_, 16, v___x_3022_);
lean_closure_set(v___f_3076_, 17, v___x_3023_);
lean_closure_set(v___f_3076_, 18, v___x_3024_);
lean_closure_set(v___f_3076_, 19, v___x_3055_);
lean_closure_set(v___f_3076_, 20, v_argMask_3030_);
lean_closure_set(v___f_3076_, 21, v_a_3072_);
v___x_3077_ = l_Subarray_copy___redArg(v___x_3025_);
v___x_3078_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_3026_, v___x_3067_, v___x_3041_, v___x_3077_, v___f_3076_, v___y_3051_, v___y_3049_, v___y_3048_, v___y_3050_);
return v___x_3078_;
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref(v___x_3067_);
lean_dec_ref_known(v___x_3055_, 2);
lean_dec(v_a_3046_);
lean_dec_ref(v___x_3041_);
lean_dec_ref(v_argMask_3030_);
lean_dec_ref(v_rhsArgs_3029_);
lean_dec_ref(v_ys_3027_);
lean_dec_ref(v___x_3025_);
lean_dec(v___x_3024_);
lean_dec(v___x_3023_);
lean_dec(v___x_3022_);
lean_dec(v_matchDeclName_3021_);
lean_dec_ref(v___x_3020_);
lean_dec_ref(v___x_3019_);
lean_dec(v___x_3018_);
lean_dec_ref(v_a_3017_);
lean_dec_ref(v___x_3016_);
lean_dec(v___x_3013_);
lean_dec(v_a_3010_);
lean_dec(v___x_3008_);
v_a_3079_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3071_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3071_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec_ref_known(v___x_3055_, 2);
lean_dec(v_a_3046_);
lean_dec_ref(v___x_3041_);
lean_dec_ref(v_argMask_3030_);
lean_dec_ref(v_rhsArgs_3029_);
lean_dec_ref(v_ys_3027_);
lean_dec_ref(v___x_3025_);
lean_dec(v___x_3024_);
lean_dec(v___x_3023_);
lean_dec(v___x_3022_);
lean_dec(v_matchDeclName_3021_);
lean_dec_ref(v___x_3020_);
lean_dec_ref(v___x_3019_);
lean_dec(v___x_3018_);
lean_dec_ref(v_a_3017_);
lean_dec_ref(v___x_3016_);
lean_dec_ref(v___x_3014_);
lean_dec(v___x_3013_);
lean_dec(v_a_3010_);
lean_dec(v___x_3008_);
v_a_3087_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3064_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3064_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
v___jp_3095_:
{
lean_object* v___x_3100_; uint8_t v___x_3101_; 
v___x_3100_ = lean_array_get_size(v_ys_3027_);
v___x_3101_ = lean_nat_dec_eq(v___x_3100_, v___x_3013_);
if (v___x_3101_ == 0)
{
v___y_3048_ = v___y_3098_;
v___y_3049_ = v___y_3097_;
v___y_3050_ = v___y_3099_;
v___y_3051_ = v___y_3096_;
v___y_3052_ = v___x_3101_;
goto v___jp_3047_;
}
else
{
lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = lean_array_get_size(v_a_3046_);
v___x_3103_ = lean_nat_dec_eq(v___x_3102_, v___x_3013_);
if (v___x_3103_ == 0)
{
v___y_3048_ = v___y_3098_;
v___y_3049_ = v___y_3097_;
v___y_3050_ = v___y_3099_;
v___y_3051_ = v___y_3096_;
v___y_3052_ = v___x_3103_;
goto v___jp_3047_;
}
else
{
uint8_t v___x_3104_; 
v___x_3104_ = lean_nat_dec_eq(v___x_3026_, v___x_3013_);
v___y_3048_ = v___y_3098_;
v___y_3049_ = v___y_3097_;
v___y_3050_ = v___y_3099_;
v___y_3051_ = v___y_3096_;
v___y_3052_ = v___x_3104_;
goto v___jp_3047_;
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v___x_3041_);
lean_dec_ref(v_argMask_3030_);
lean_dec_ref(v_rhsArgs_3029_);
lean_dec_ref(v_ys_3027_);
lean_dec_ref(v___x_3025_);
lean_dec(v___x_3024_);
lean_dec(v___x_3023_);
lean_dec(v___x_3022_);
lean_dec(v_matchDeclName_3021_);
lean_dec_ref(v___x_3020_);
lean_dec_ref(v___x_3019_);
lean_dec(v___x_3018_);
lean_dec_ref(v_a_3017_);
lean_dec_ref(v___x_3016_);
lean_dec_ref(v___x_3014_);
lean_dec(v___x_3013_);
lean_dec_ref(v___x_3012_);
lean_dec(v_a_3010_);
lean_dec(v___x_3008_);
v_a_3127_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3045_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3045_);
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
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3008_ = stack[0].m_obj;
lean_object* v_overlaps_3009_ = stack[1].m_obj;
lean_object* v_a_3010_ = stack[2].m_obj;
lean_object* v_fst_3011_ = stack[3].m_obj;
lean_object* v___x_3012_ = stack[4].m_obj;
lean_object* v___x_3013_ = stack[5].m_obj;
lean_object* v___x_3014_ = stack[6].m_obj;
uint8_t v___x_3015_ = stack[7].m_num;
lean_object* v___x_3016_ = stack[8].m_obj;
lean_object* v_a_3017_ = stack[9].m_obj;
lean_object* v___x_3018_ = stack[10].m_obj;
lean_object* v___x_3019_ = stack[11].m_obj;
lean_object* v___x_3020_ = stack[12].m_obj;
lean_object* v_matchDeclName_3021_ = stack[13].m_obj;
lean_object* v___x_3022_ = stack[14].m_obj;
lean_object* v___x_3023_ = stack[15].m_obj;
lean_object* v___x_3024_ = stack[16].m_obj;
lean_object* v___x_3025_ = stack[17].m_obj;
lean_object* v___x_3026_ = stack[18].m_obj;
lean_object* v_ys_3027_ = stack[19].m_obj;
lean_object* v___eqs_3028_ = stack[20].m_obj;
lean_object* v_rhsArgs_3029_ = stack[21].m_obj;
lean_object* v_argMask_3030_ = stack[22].m_obj;
lean_object* v_altResultType_3031_ = stack[23].m_obj;
lean_object* v___y_3032_ = stack[24].m_obj;
lean_object* v___y_3033_ = stack[25].m_obj;
lean_object* v___y_3034_ = stack[26].m_obj;
lean_object* v___y_3035_ = stack[27].m_obj;
lean_object* v_res_3135_;
v_res_3135_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3008_, v_overlaps_3009_, v_a_3010_, v_fst_3011_, v___x_3012_, v___x_3013_, v___x_3014_, v___x_3015_, v___x_3016_, v_a_3017_, v___x_3018_, v___x_3019_, v___x_3020_, v_matchDeclName_3021_, v___x_3022_, v___x_3023_, v___x_3024_, v___x_3025_, v___x_3026_, v_ys_3027_, v___eqs_3028_, v_rhsArgs_3029_, v_argMask_3030_, v_altResultType_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
stack->m_obj
 = v_res_3135_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3136_ = _args[0];
lean_object* v_overlaps_3137_ = _args[1];
lean_object* v_a_3138_ = _args[2];
lean_object* v_fst_3139_ = _args[3];
lean_object* v___x_3140_ = _args[4];
lean_object* v___x_3141_ = _args[5];
lean_object* v___x_3142_ = _args[6];
lean_object* v___x_3143_ = _args[7];
lean_object* v___x_3144_ = _args[8];
lean_object* v_a_3145_ = _args[9];
lean_object* v___x_3146_ = _args[10];
lean_object* v___x_3147_ = _args[11];
lean_object* v___x_3148_ = _args[12];
lean_object* v_matchDeclName_3149_ = _args[13];
lean_object* v___x_3150_ = _args[14];
lean_object* v___x_3151_ = _args[15];
lean_object* v___x_3152_ = _args[16];
lean_object* v___x_3153_ = _args[17];
lean_object* v___x_3154_ = _args[18];
lean_object* v_ys_3155_ = _args[19];
lean_object* v___eqs_3156_ = _args[20];
lean_object* v_rhsArgs_3157_ = _args[21];
lean_object* v_argMask_3158_ = _args[22];
lean_object* v_altResultType_3159_ = _args[23];
lean_object* v___y_3160_ = _args[24];
lean_object* v___y_3161_ = _args[25];
lean_object* v___y_3162_ = _args[26];
lean_object* v___y_3163_ = _args[27];
lean_object* v___y_3164_ = _args[28];
_start:
{
uint8_t v___x_19247__boxed_3165_; lean_object* v_res_3166_; 
v___x_19247__boxed_3165_ = lean_unbox(v___x_3143_);
v_res_3166_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3136_, v_overlaps_3137_, v_a_3138_, v_fst_3139_, v___x_3140_, v___x_3141_, v___x_3142_, v___x_19247__boxed_3165_, v___x_3144_, v_a_3145_, v___x_3146_, v___x_3147_, v___x_3148_, v_matchDeclName_3149_, v___x_3150_, v___x_3151_, v___x_3152_, v___x_3153_, v___x_3154_, v_ys_3155_, v___eqs_3156_, v_rhsArgs_3157_, v_argMask_3158_, v_altResultType_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec_ref(v___eqs_3156_);
lean_dec(v___x_3154_);
lean_dec(v_fst_3139_);
lean_dec_ref(v_overlaps_3137_);
return v_res_3166_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3167_, lean_object* v_val_3168_, lean_object* v_baseName_3169_, lean_object* v___x_3170_, lean_object* v_a_3171_, lean_object* v___x_3172_, lean_object* v___x_3173_, lean_object* v___x_3174_, lean_object* v_matchDeclName_3175_, lean_object* v___x_3176_, lean_object* v___x_3177_, lean_object* v___x_3178_, lean_object* v_a_3179_, lean_object* v_b_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_nat_dec_lt(v_a_3179_, v_upperBound_3167_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
lean_dec(v_a_3179_);
lean_dec(v___x_3178_);
lean_dec_ref(v___x_3177_);
lean_dec(v___x_3176_);
lean_dec(v_matchDeclName_3175_);
lean_dec_ref(v___x_3174_);
lean_dec_ref(v___x_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_a_3171_);
lean_dec_ref(v___x_3170_);
lean_dec(v_baseName_3169_);
lean_dec_ref(v_val_3168_);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v_b_3180_);
return v___x_3187_;
}
else
{
lean_object* v_snd_3188_; lean_object* v_snd_3189_; lean_object* v_snd_3190_; lean_object* v_fst_3191_; lean_object* v_fst_3192_; lean_object* v_fst_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3276_; 
v_snd_3188_ = lean_ctor_get(v_b_3180_, 1);
lean_inc(v_snd_3188_);
v_snd_3189_ = lean_ctor_get(v_snd_3188_, 1);
lean_inc(v_snd_3189_);
v_snd_3190_ = lean_ctor_get(v_snd_3189_, 1);
lean_inc(v_snd_3190_);
v_fst_3191_ = lean_ctor_get(v_b_3180_, 0);
lean_inc(v_fst_3191_);
lean_dec_ref(v_b_3180_);
v_fst_3192_ = lean_ctor_get(v_snd_3188_, 0);
lean_inc(v_fst_3192_);
lean_dec(v_snd_3188_);
v_fst_3193_ = lean_ctor_get(v_snd_3189_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_snd_3189_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; 
v_unused_3277_ = lean_ctor_get(v_snd_3189_, 1);
lean_dec(v_unused_3277_);
v___x_3195_ = v_snd_3189_;
v_isShared_3196_ = v_isSharedCheck_3276_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_fst_3193_);
lean_dec(v_snd_3189_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3276_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_fst_3197_; lean_object* v_snd_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3275_; 
v_fst_3197_ = lean_ctor_get(v_snd_3190_, 0);
v_snd_3198_ = lean_ctor_get(v_snd_3190_, 1);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_snd_3190_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3200_ = v_snd_3190_;
v_isShared_3201_ = v_isSharedCheck_3275_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_snd_3198_);
lean_inc(v_fst_3197_);
lean_dec(v_snd_3190_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3275_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v_altInfos_3202_; lean_object* v_overlaps_3203_; lean_object* v_start_3204_; lean_object* v_stop_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___f_3217_; lean_object* v___x_3218_; lean_object* v___y_3220_; lean_object* v___x_3271_; uint8_t v___x_3272_; 
v_altInfos_3202_ = lean_ctor_get(v_val_3168_, 2);
v_overlaps_3203_ = lean_ctor_get(v_val_3168_, 5);
v_start_3204_ = lean_ctor_get(v___x_3177_, 1);
v_stop_3205_ = lean_ctor_get(v___x_3177_, 2);
v___x_3206_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3207_ = l_Lean_instInhabitedExpr;
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3210_ = lean_box(0);
v___x_3211_ = lean_unsigned_to_nat(1u);
v___x_3212_ = lean_array_get_borrowed(v___x_3206_, v_altInfos_3202_, v_a_3179_);
v___x_3213_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3169_);
v___x_3214_ = l_Lean_Name_str___override(v_baseName_3169_, v___x_3213_);
lean_inc(v_fst_3193_);
v___x_3215_ = lean_name_append_index_after(v___x_3214_, v_fst_3193_);
v___x_3216_ = lean_box(v___x_3186_);
lean_inc(v___x_3178_);
lean_inc_ref(v___x_3177_);
lean_inc(v___x_3176_);
lean_inc(v___x_3215_);
lean_inc(v_matchDeclName_3175_);
lean_inc_ref(v___x_3174_);
lean_inc_ref(v___x_3173_);
lean_inc(v___x_3172_);
lean_inc_ref(v_a_3171_);
lean_inc_ref(v___x_3170_);
lean_inc(v_fst_3192_);
lean_inc(v_a_3179_);
lean_inc_ref(v_overlaps_3203_);
v___f_3217_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3217_, 0, v___x_3211_);
lean_closure_set(v___f_3217_, 1, v_overlaps_3203_);
lean_closure_set(v___f_3217_, 2, v_a_3179_);
lean_closure_set(v___f_3217_, 3, v_fst_3192_);
lean_closure_set(v___f_3217_, 4, v___x_3209_);
lean_closure_set(v___f_3217_, 5, v___x_3208_);
lean_closure_set(v___f_3217_, 6, v___x_3170_);
lean_closure_set(v___f_3217_, 7, v___x_3216_);
lean_closure_set(v___f_3217_, 8, v___x_3207_);
lean_closure_set(v___f_3217_, 9, v_a_3171_);
lean_closure_set(v___f_3217_, 10, v___x_3172_);
lean_closure_set(v___f_3217_, 11, v___x_3173_);
lean_closure_set(v___f_3217_, 12, v___x_3174_);
lean_closure_set(v___f_3217_, 13, v_matchDeclName_3175_);
lean_closure_set(v___f_3217_, 14, v___x_3215_);
lean_closure_set(v___f_3217_, 15, v___x_3176_);
lean_closure_set(v___f_3217_, 16, v___x_3210_);
lean_closure_set(v___f_3217_, 17, v___x_3177_);
lean_closure_set(v___f_3217_, 18, v___x_3178_);
v___x_3218_ = lean_array_push(v_fst_3191_, v___x_3215_);
v___x_3271_ = lean_nat_sub(v_stop_3205_, v_start_3204_);
v___x_3272_ = lean_nat_dec_lt(v_a_3179_, v___x_3271_);
lean_dec(v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; 
v___x_3273_ = l_outOfBounds___redArg(v___x_3207_);
v___y_3220_ = v___x_3273_;
goto v___jp_3219_;
}
else
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Subarray_get___redArg(v___x_3177_, v_a_3179_);
v___y_3220_ = v___x_3274_;
goto v___jp_3219_;
}
v___jp_3219_:
{
lean_object* v___x_3221_; 
lean_inc(v___y_3184_);
lean_inc_ref(v___y_3183_);
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
v___x_3221_ = lean_infer_type(v___y_3220_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___x_3223_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3221_, 1);
lean_inc(v___x_3178_);
lean_inc(v___x_3212_);
v___x_3223_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3222_, v___x_3212_, v___x_3178_, v___f_3217_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v_snd_3225_; lean_object* v_fst_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3254_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3223_, 1);
v_snd_3225_ = lean_ctor_get(v_a_3224_, 1);
v_fst_3226_ = lean_ctor_get(v_a_3224_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v_a_3224_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3228_ = v_a_3224_;
v_isShared_3229_ = v_isSharedCheck_3254_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_snd_3225_);
lean_inc(v_fst_3226_);
lean_dec(v_a_3224_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3254_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_fst_3230_; lean_object* v_snd_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3253_; 
v_fst_3230_ = lean_ctor_get(v_snd_3225_, 0);
v_snd_3231_ = lean_ctor_get(v_snd_3225_, 1);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_snd_3225_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3233_ = v_snd_3225_;
v_isShared_3234_ = v_isSharedCheck_3253_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_snd_3231_);
lean_inc(v_fst_3230_);
lean_dec(v_snd_3225_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3253_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3235_ = lean_array_push(v_fst_3192_, v_fst_3226_);
v___x_3236_ = lean_array_push(v_fst_3197_, v_fst_3230_);
v___x_3237_ = lean_array_push(v_snd_3198_, v_snd_3231_);
v___x_3238_ = lean_nat_add(v_fst_3193_, v___x_3211_);
lean_dec(v_fst_3193_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v___x_3237_);
lean_ctor_set(v___x_3233_, 0, v___x_3236_);
v___x_3240_ = v___x_3233_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v___x_3237_);
v___x_3240_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3242_; 
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 1, v___x_3240_);
lean_ctor_set(v___x_3228_, 0, v___x_3238_);
v___x_3242_ = v___x_3228_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 1, v___x_3242_);
lean_ctor_set(v___x_3200_, 0, v___x_3235_);
v___x_3244_ = v___x_3200_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3246_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 1, v___x_3244_);
lean_ctor_set(v___x_3195_, 0, v___x_3218_);
v___x_3246_ = v___x_3195_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3218_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_nat_add(v_a_3179_, v___x_3211_);
lean_dec(v_a_3179_);
v_a_3179_ = v___x_3247_;
v_b_3180_ = v___x_3246_;
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
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec_ref(v___x_3218_);
lean_del_object(v___x_3200_);
lean_dec(v_snd_3198_);
lean_dec(v_fst_3197_);
lean_del_object(v___x_3195_);
lean_dec(v_fst_3193_);
lean_dec(v_fst_3192_);
lean_dec(v_a_3179_);
lean_dec(v___x_3178_);
lean_dec_ref(v___x_3177_);
lean_dec(v___x_3176_);
lean_dec(v_matchDeclName_3175_);
lean_dec_ref(v___x_3174_);
lean_dec_ref(v___x_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_a_3171_);
lean_dec_ref(v___x_3170_);
lean_dec(v_baseName_3169_);
lean_dec_ref(v_val_3168_);
v_a_3255_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3223_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3223_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref(v___x_3218_);
lean_dec_ref(v___f_3217_);
lean_del_object(v___x_3200_);
lean_dec(v_snd_3198_);
lean_dec(v_fst_3197_);
lean_del_object(v___x_3195_);
lean_dec(v_fst_3193_);
lean_dec(v_fst_3192_);
lean_dec(v_a_3179_);
lean_dec(v___x_3178_);
lean_dec_ref(v___x_3177_);
lean_dec(v___x_3176_);
lean_dec(v_matchDeclName_3175_);
lean_dec_ref(v___x_3174_);
lean_dec_ref(v___x_3173_);
lean_dec(v___x_3172_);
lean_dec_ref(v_a_3171_);
lean_dec_ref(v___x_3170_);
lean_dec(v_baseName_3169_);
lean_dec_ref(v_val_3168_);
v_a_3263_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3221_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3221_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3167_ = stack[0].m_obj;
lean_object* v_val_3168_ = stack[1].m_obj;
lean_object* v_baseName_3169_ = stack[2].m_obj;
lean_object* v___x_3170_ = stack[3].m_obj;
lean_object* v_a_3171_ = stack[4].m_obj;
lean_object* v___x_3172_ = stack[5].m_obj;
lean_object* v___x_3173_ = stack[6].m_obj;
lean_object* v___x_3174_ = stack[7].m_obj;
lean_object* v_matchDeclName_3175_ = stack[8].m_obj;
lean_object* v___x_3176_ = stack[9].m_obj;
lean_object* v___x_3177_ = stack[10].m_obj;
lean_object* v___x_3178_ = stack[11].m_obj;
lean_object* v_a_3179_ = stack[12].m_obj;
lean_object* v_b_3180_ = stack[13].m_obj;
lean_object* v___y_3181_ = stack[14].m_obj;
lean_object* v___y_3182_ = stack[15].m_obj;
lean_object* v___y_3183_ = stack[16].m_obj;
lean_object* v___y_3184_ = stack[17].m_obj;
lean_object* v_res_3278_;
v_res_3278_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3167_, v_val_3168_, v_baseName_3169_, v___x_3170_, v_a_3171_, v___x_3172_, v___x_3173_, v___x_3174_, v_matchDeclName_3175_, v___x_3176_, v___x_3177_, v___x_3178_, v_a_3179_, v_b_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
stack->m_obj
 = v_res_3278_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_3279_ = _args[0];
lean_object* v_val_3280_ = _args[1];
lean_object* v_baseName_3281_ = _args[2];
lean_object* v___x_3282_ = _args[3];
lean_object* v_a_3283_ = _args[4];
lean_object* v___x_3284_ = _args[5];
lean_object* v___x_3285_ = _args[6];
lean_object* v___x_3286_ = _args[7];
lean_object* v_matchDeclName_3287_ = _args[8];
lean_object* v___x_3288_ = _args[9];
lean_object* v___x_3289_ = _args[10];
lean_object* v___x_3290_ = _args[11];
lean_object* v_a_3291_ = _args[12];
lean_object* v_b_3292_ = _args[13];
lean_object* v___y_3293_ = _args[14];
lean_object* v___y_3294_ = _args[15];
lean_object* v___y_3295_ = _args[16];
lean_object* v___y_3296_ = _args[17];
lean_object* v___y_3297_ = _args[18];
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3279_, v_val_3280_, v_baseName_3281_, v___x_3282_, v_a_3283_, v___x_3284_, v___x_3285_, v___x_3286_, v_matchDeclName_3287_, v___x_3288_, v___x_3289_, v___x_3290_, v_a_3291_, v_b_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v_upperBound_3279_);
return v_res_3298_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3302_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3303_ = lean_unsigned_to_nat(6u);
v___x_3304_ = lean_unsigned_to_nat(233u);
v___x_3305_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3306_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3307_ = l_mkPanicMessageWithDecl(v___x_3306_, v___x_3305_, v___x_3304_, v___x_3303_, v___x_3302_);
return v___x_3307_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3320_, lean_object* v_matchDeclName_3321_, lean_object* v_numParams_3322_, lean_object* v_val_3323_, lean_object* v___x_3324_, lean_object* v_numDiscrs_3325_, lean_object* v_baseName_3326_, lean_object* v_a_3327_, lean_object* v___x_3328_, lean_object* v___x_3329_, lean_object* v___x_3330_, lean_object* v_uElimPos_x3f_3331_, lean_object* v_discrInfos_3332_, lean_object* v_overlaps_3333_, lean_object* v___f_3334_, lean_object* v___x_3335_, lean_object* v_altInfos_3336_, lean_object* v_xs_3337_, lean_object* v___matchResultType_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; uint8_t v___y_3356_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v_lower_3364_; lean_object* v_upper_3365_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3358_ = lean_box(0);
v___x_3359_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3322_);
lean_inc_ref(v_xs_3337_);
v___x_3360_ = l_Array_toSubarray___redArg(v_xs_3337_, v___x_3359_, v_numParams_3322_);
v___x_3361_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3323_);
v___x_3362_ = lean_array_get(v___x_3324_, v_xs_3337_, v___x_3361_);
lean_dec(v___x_3361_);
v___x_3418_ = lean_array_get_size(v_xs_3337_);
v___x_3419_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3323_);
v___x_3420_ = lean_nat_sub(v___x_3418_, v___x_3419_);
lean_dec(v___x_3419_);
v___x_3421_ = lean_nat_dec_le(v___x_3420_, v___x_3359_);
if (v___x_3421_ == 0)
{
v_lower_3364_ = v___x_3420_;
v_upper_3365_ = v___x_3418_;
goto v___jp_3363_;
}
else
{
lean_dec(v___x_3420_);
v_lower_3364_ = v___x_3359_;
v_upper_3365_ = v___x_3418_;
goto v___jp_3363_;
}
v___jp_3344_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3346_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3345_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
return v___x_3346_;
}
v___jp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3350_, 0, v___y_3349_);
lean_ctor_set(v___x_3350_, 1, v_splitterName_3320_);
lean_ctor_set(v___x_3350_, 2, v___y_3348_);
v___x_3351_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3321_, v___x_3350_, v___y_3342_);
return v___x_3351_;
}
v___jp_3352_:
{
lean_object* v___x_3357_; 
lean_inc(v_matchDeclName_3321_);
v___x_3357_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3321_, v___y_3356_, v___y_3353_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_dec_ref_known(v___x_3357_, 1);
v___y_3348_ = v___y_3355_;
v___y_3349_ = v___y_3354_;
goto v___jp_3347_;
}
else
{
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v_matchDeclName_3321_);
lean_dec(v_splitterName_3320_);
return v___x_3357_;
}
}
v___jp_3363_:
{
lean_object* v___x_3366_; lean_object* v_start_3367_; lean_object* v_stop_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_inc_ref(v_xs_3337_);
v___x_3366_ = l_Array_toSubarray___redArg(v_xs_3337_, v_lower_3364_, v_upper_3365_);
v_start_3367_ = lean_ctor_get(v___x_3366_, 1);
v_stop_3368_ = lean_ctor_get(v___x_3366_, 2);
v___x_3369_ = lean_unsigned_to_nat(1u);
v___x_3370_ = lean_nat_add(v_numParams_3322_, v___x_3369_);
v___x_3371_ = lean_nat_add(v___x_3370_, v_numDiscrs_3325_);
v___x_3372_ = lean_nat_sub(v_stop_3368_, v_start_3367_);
v___x_3373_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3374_ = l_Array_toSubarray___redArg(v_xs_3337_, v___x_3370_, v___x_3371_);
lean_inc(v___x_3329_);
lean_inc(v_matchDeclName_3321_);
lean_inc(v___x_3328_);
v___x_3375_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3372_, v_val_3323_, v_baseName_3326_, v___x_3374_, v_a_3327_, v___x_3328_, v___x_3360_, v___x_3362_, v_matchDeclName_3321_, v___x_3329_, v___x_3366_, v___x_3330_, v___x_3359_, v___x_3373_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___x_3372_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v_snd_3377_; lean_object* v_snd_3378_; lean_object* v_snd_3379_; lean_object* v_fst_3380_; lean_object* v_fst_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3408_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3375_, 1);
v_snd_3377_ = lean_ctor_get(v_a_3376_, 1);
v_snd_3378_ = lean_ctor_get(v_snd_3377_, 1);
v_snd_3379_ = lean_ctor_get(v_snd_3378_, 1);
lean_inc(v_snd_3379_);
v_fst_3380_ = lean_ctor_get(v_a_3376_, 0);
lean_inc(v_fst_3380_);
lean_dec(v_a_3376_);
v_fst_3381_ = lean_ctor_get(v_snd_3379_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_snd_3379_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; 
v_unused_3409_ = lean_ctor_get(v_snd_3379_, 1);
lean_dec(v_unused_3409_);
v___x_3383_ = v_snd_3379_;
v_isShared_3384_ = v_isSharedCheck_3408_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_fst_3381_);
lean_dec(v_snd_3379_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3408_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3385_; uint8_t v___x_3386_; 
lean_inc_ref(v_overlaps_3333_);
lean_inc(v_fst_3381_);
v___x_3385_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3385_, 0, v_numParams_3322_);
lean_ctor_set(v___x_3385_, 1, v_numDiscrs_3325_);
lean_ctor_set(v___x_3385_, 2, v_fst_3381_);
lean_ctor_set(v___x_3385_, 3, v_uElimPos_x3f_3331_);
lean_ctor_set(v___x_3385_, 4, v_discrInfos_3332_);
lean_ctor_set(v___x_3385_, 5, v_overlaps_3333_);
v___x_3386_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3333_);
lean_dec_ref(v_overlaps_3333_);
if (v___x_3386_ == 0)
{
uint8_t v___x_3387_; 
lean_del_object(v___x_3383_);
lean_dec(v_fst_3381_);
lean_dec_ref(v___x_3335_);
lean_dec(v___x_3329_);
lean_dec(v___x_3328_);
v___x_3387_ = 1;
v___y_3353_ = v___f_3334_;
v___y_3354_ = v_fst_3380_;
v___y_3355_ = v___x_3385_;
v___y_3356_ = v___x_3387_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3388_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3389_ = lean_find_expr(v___x_3388_, v___x_3335_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
lean_dec_ref(v___f_3334_);
v___x_3390_ = lean_array_get_size(v_altInfos_3336_);
v___x_3391_ = lean_array_get_size(v_fst_3381_);
v___x_3392_ = lean_nat_dec_eq(v___x_3390_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_dec_ref_known(v___x_3385_, 6);
lean_del_object(v___x_3383_);
lean_dec(v_fst_3381_);
lean_dec(v_fst_3380_);
lean_dec_ref(v___x_3335_);
lean_dec(v___x_3329_);
lean_dec(v___x_3328_);
lean_dec(v_matchDeclName_3321_);
lean_dec(v_splitterName_3320_);
goto v___jp_3344_;
}
else
{
uint8_t v___x_3393_; 
v___x_3393_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3336_, v_fst_3381_, v___x_3390_);
lean_dec(v_fst_3381_);
if (v___x_3393_ == 0)
{
lean_dec_ref_known(v___x_3385_, 6);
lean_del_object(v___x_3383_);
lean_dec(v_fst_3380_);
lean_dec_ref(v___x_3335_);
lean_dec(v___x_3329_);
lean_dec(v___x_3328_);
lean_dec(v_matchDeclName_3321_);
lean_dec(v_splitterName_3320_);
goto v___jp_3344_;
}
else
{
uint8_t v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; uint8_t v___x_3398_; lean_object* v___x_3400_; 
v___x_3394_ = 0;
lean_inc_n(v_splitterName_3320_, 2);
v___x_3395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3395_, 0, v_splitterName_3320_);
lean_ctor_set(v___x_3395_, 1, v___x_3329_);
lean_ctor_set(v___x_3395_, 2, v___x_3335_);
lean_inc(v_matchDeclName_3321_);
v___x_3396_ = l_Lean_mkConst(v_matchDeclName_3321_, v___x_3328_);
v___x_3397_ = lean_box(1);
v___x_3398_ = 1;
if (v_isShared_3384_ == 0)
{
lean_ctor_set_tag(v___x_3383_, 1);
lean_ctor_set(v___x_3383_, 1, v___x_3358_);
lean_ctor_set(v___x_3383_, 0, v_splitterName_3320_);
v___x_3400_ = v___x_3383_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_splitterName_3320_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v___x_3358_);
v___x_3400_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3401_, 0, v___x_3395_);
lean_ctor_set(v___x_3401_, 1, v___x_3396_);
lean_ctor_set(v___x_3401_, 2, v___x_3397_);
lean_ctor_set(v___x_3401_, 3, v___x_3400_);
lean_ctor_set_uint8(v___x_3401_, sizeof(void*)*4, v___x_3398_);
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_inc_ref(v___x_3402_);
v___x_3403_ = l_Lean_addDecl(v___x_3402_, v___x_3394_, v___y_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3403_) == 0)
{
uint8_t v___x_3404_; lean_object* v___x_3405_; 
lean_dec_ref_known(v___x_3403_, 1);
v___x_3404_ = 0;
lean_inc(v_splitterName_3320_);
v___x_3405_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3320_, v___x_3404_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v___x_3406_; 
lean_dec_ref_known(v___x_3405_, 1);
v___x_3406_ = l_Lean_compileDecl(v___x_3402_, v___x_3394_, v___y_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec_ref_known(v___x_3406_, 1);
v___y_3348_ = v___x_3385_;
v___y_3349_ = v_fst_3380_;
goto v___jp_3347_;
}
else
{
lean_dec_ref_known(v___x_3385_, 6);
lean_dec(v_fst_3380_);
lean_dec(v_matchDeclName_3321_);
lean_dec(v_splitterName_3320_);
return v___x_3406_;
}
}
else
{
lean_dec_ref_known(v___x_3402_, 1);
lean_dec_ref_known(v___x_3385_, 6);
lean_dec(v_fst_3380_);
lean_dec(v_matchDeclName_3321_);
lean_dec(v_splitterName_3320_);
return v___x_3405_;
}
}
else
{
lean_dec_ref_known(v___x_3402_, 1);
lean_dec_ref_known(v___x_3385_, 6);
lean_dec(v_fst_3380_);
lean_dec(v_matchDeclName_3321_);
lean_dec(v_splitterName_3320_);
return v___x_3403_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3389_, 1);
lean_del_object(v___x_3383_);
lean_dec(v_fst_3381_);
lean_dec_ref(v___x_3335_);
lean_dec(v___x_3329_);
lean_dec(v___x_3328_);
v___y_3353_ = v___f_3334_;
v___y_3354_ = v_fst_3380_;
v___y_3355_ = v___x_3385_;
v___y_3356_ = v___x_3386_;
goto v___jp_3352_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec_ref(v___x_3335_);
lean_dec_ref(v___f_3334_);
lean_dec_ref(v_overlaps_3333_);
lean_dec_ref(v_discrInfos_3332_);
lean_dec(v_uElimPos_x3f_3331_);
lean_dec(v___x_3329_);
lean_dec(v___x_3328_);
lean_dec(v_numDiscrs_3325_);
lean_dec(v_numParams_3322_);
lean_dec(v_matchDeclName_3321_);
lean_dec(v_splitterName_3320_);
v_a_3410_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3375_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3375_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_splitterName_3320_ = stack[0].m_obj;
lean_object* v_matchDeclName_3321_ = stack[1].m_obj;
lean_object* v_numParams_3322_ = stack[2].m_obj;
lean_object* v_val_3323_ = stack[3].m_obj;
lean_object* v___x_3324_ = stack[4].m_obj;
lean_object* v_numDiscrs_3325_ = stack[5].m_obj;
lean_object* v_baseName_3326_ = stack[6].m_obj;
lean_object* v_a_3327_ = stack[7].m_obj;
lean_object* v___x_3328_ = stack[8].m_obj;
lean_object* v___x_3329_ = stack[9].m_obj;
lean_object* v___x_3330_ = stack[10].m_obj;
lean_object* v_uElimPos_x3f_3331_ = stack[11].m_obj;
lean_object* v_discrInfos_3332_ = stack[12].m_obj;
lean_object* v_overlaps_3333_ = stack[13].m_obj;
lean_object* v___f_3334_ = stack[14].m_obj;
lean_object* v___x_3335_ = stack[15].m_obj;
lean_object* v_altInfos_3336_ = stack[16].m_obj;
lean_object* v_xs_3337_ = stack[17].m_obj;
lean_object* v___matchResultType_3338_ = stack[18].m_obj;
lean_object* v___y_3339_ = stack[19].m_obj;
lean_object* v___y_3340_ = stack[20].m_obj;
lean_object* v___y_3341_ = stack[21].m_obj;
lean_object* v___y_3342_ = stack[22].m_obj;
lean_object* v_res_3422_;
v_res_3422_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3320_, v_matchDeclName_3321_, v_numParams_3322_, v_val_3323_, v___x_3324_, v_numDiscrs_3325_, v_baseName_3326_, v_a_3327_, v___x_3328_, v___x_3329_, v___x_3330_, v_uElimPos_x3f_3331_, v_discrInfos_3332_, v_overlaps_3333_, v___f_3334_, v___x_3335_, v_altInfos_3336_, v_xs_3337_, v___matchResultType_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
stack->m_obj
 = v_res_3422_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3423_ = _args[0];
lean_object* v_matchDeclName_3424_ = _args[1];
lean_object* v_numParams_3425_ = _args[2];
lean_object* v_val_3426_ = _args[3];
lean_object* v___x_3427_ = _args[4];
lean_object* v_numDiscrs_3428_ = _args[5];
lean_object* v_baseName_3429_ = _args[6];
lean_object* v_a_3430_ = _args[7];
lean_object* v___x_3431_ = _args[8];
lean_object* v___x_3432_ = _args[9];
lean_object* v___x_3433_ = _args[10];
lean_object* v_uElimPos_x3f_3434_ = _args[11];
lean_object* v_discrInfos_3435_ = _args[12];
lean_object* v_overlaps_3436_ = _args[13];
lean_object* v___f_3437_ = _args[14];
lean_object* v___x_3438_ = _args[15];
lean_object* v_altInfos_3439_ = _args[16];
lean_object* v_xs_3440_ = _args[17];
lean_object* v___matchResultType_3441_ = _args[18];
lean_object* v___y_3442_ = _args[19];
lean_object* v___y_3443_ = _args[20];
lean_object* v___y_3444_ = _args[21];
lean_object* v___y_3445_ = _args[22];
lean_object* v___y_3446_ = _args[23];
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3423_, v_matchDeclName_3424_, v_numParams_3425_, v_val_3426_, v___x_3427_, v_numDiscrs_3428_, v_baseName_3429_, v_a_3430_, v___x_3431_, v___x_3432_, v___x_3433_, v_uElimPos_x3f_3434_, v_discrInfos_3435_, v_overlaps_3436_, v___f_3437_, v___x_3438_, v_altInfos_3439_, v_xs_3440_, v___matchResultType_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v___matchResultType_3441_);
lean_dec_ref(v_altInfos_3439_);
lean_dec_ref(v___x_3427_);
return v_res_3447_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
return v___x_3449_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3450_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_3451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3452_ = lean_unsigned_to_nat(0u);
v___x_3453_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
lean_ctor_set(v___x_3453_, 2, v___x_3452_);
lean_ctor_set(v___x_3453_, 3, v___x_3452_);
lean_ctor_set(v___x_3453_, 4, v___x_3451_);
lean_ctor_set(v___x_3453_, 5, v___x_3451_);
lean_ctor_set(v___x_3453_, 6, v___x_3451_);
lean_ctor_set(v___x_3453_, 7, v___x_3451_);
lean_ctor_set(v___x_3453_, 8, v___x_3451_);
lean_ctor_set(v___x_3453_, 9, v___x_3451_);
lean_ctor_set(v___x_3453_, 10, v___x_3451_);
lean_ctor_set(v___x_3453_, 11, v___x_3450_);
return v___x_3453_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3454_ = lean_box(1);
v___x_3455_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3456_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
lean_ctor_set(v___x_3457_, 1, v___x_3455_);
lean_ctor_set(v___x_3457_, 2, v___x_3454_);
return v___x_3457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3));
v___x_3460_ = l_Lean_stringToMessageData(v___x_3459_);
return v___x_3460_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_3463_ = l_Lean_stringToMessageData(v___x_3462_);
return v___x_3463_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_3466_ = l_Lean_stringToMessageData(v___x_3465_);
return v___x_3466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_3469_ = l_Lean_stringToMessageData(v___x_3468_);
return v___x_3469_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_3472_ = l_Lean_stringToMessageData(v___x_3471_);
return v___x_3472_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_3475_ = l_Lean_stringToMessageData(v___x_3474_);
return v___x_3475_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_3478_ = l_Lean_stringToMessageData(v___x_3477_);
return v___x_3478_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17));
v___x_3481_ = l_Lean_stringToMessageData(v___x_3480_);
return v___x_3481_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__20(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19));
v___x_3484_ = l_Lean_stringToMessageData(v___x_3483_);
return v___x_3484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__22(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__21));
v___x_3487_ = l_Lean_stringToMessageData(v___x_3486_);
return v___x_3487_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__24(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__23));
v___x_3490_ = l_Lean_stringToMessageData(v___x_3489_);
return v___x_3490_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3491_, lean_object* v_declHint_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v_env_3497_; uint8_t v___x_3498_; 
v___x_3495_ = lean_box(0);
v___x_3496_ = lean_st_ref_get(v___y_3493_);
v_env_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc_ref(v_env_3497_);
lean_dec(v___x_3496_);
v___x_3498_ = l_Lean_Name_isAnonymous(v_declHint_3492_);
if (v___x_3498_ == 0)
{
uint8_t v_isExporting_3499_; 
v_isExporting_3499_ = lean_ctor_get_uint8(v_env_3497_, sizeof(void*)*13);
if (v_isExporting_3499_ == 0)
{
lean_object* v___x_3500_; 
lean_dec_ref(v_env_3497_);
lean_dec(v_declHint_3492_);
v___x_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3500_, 0, v_msg_3491_);
return v___x_3500_;
}
else
{
lean_object* v___x_3501_; uint8_t v___x_3502_; 
lean_inc_ref(v_env_3497_);
v___x_3501_ = l_Lean_Environment_setExporting(v_env_3497_, v___x_3498_);
lean_inc(v_declHint_3492_);
lean_inc_ref(v___x_3501_);
v___x_3502_ = l_Lean_Environment_contains(v___x_3501_, v_declHint_3492_, v_isExporting_3499_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; 
lean_dec_ref(v___x_3501_);
lean_dec_ref(v_env_3497_);
lean_dec(v_declHint_3492_);
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_msg_3491_);
return v___x_3503_;
}
else
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v_c_3509_; lean_object* v___x_3510_; 
v___x_3504_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3505_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3506_ = l_Lean_Options_empty;
v___x_3507_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3501_);
lean_ctor_set(v___x_3507_, 1, v___x_3504_);
lean_ctor_set(v___x_3507_, 2, v___x_3505_);
lean_ctor_set(v___x_3507_, 3, v___x_3506_);
lean_inc(v_declHint_3492_);
v___x_3508_ = l_Lean_MessageData_ofConstName(v_declHint_3492_, v___x_3498_);
v_c_3509_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3509_, 0, v___x_3507_);
lean_ctor_set(v_c_3509_, 1, v___x_3508_);
v___x_3510_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3497_, v_declHint_3492_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
lean_dec_ref(v_env_3497_);
lean_dec(v_declHint_3492_);
v___x_3511_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_3512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
lean_ctor_set(v___x_3512_, 1, v_c_3509_);
v___x_3513_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_3514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3512_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
v___x_3515_ = l_Lean_MessageData_note(v___x_3514_);
v___x_3516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3516_, 0, v_msg_3491_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
v___x_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
return v___x_3517_;
}
else
{
lean_object* v_val_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3574_; 
v_val_3518_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3520_ = v___x_3510_;
v_isShared_3521_ = v_isSharedCheck_3574_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_val_3518_);
lean_dec(v___x_3510_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3574_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3522_; lean_object* v_modules_3523_; lean_object* v_moduleNames_3524_; lean_object* v_mod_3525_; uint8_t v___y_3527_; uint8_t v___x_3557_; 
v___x_3522_ = l_Lean_Environment_header(v_env_3497_);
lean_dec_ref(v_env_3497_);
v_modules_3523_ = lean_ctor_get(v___x_3522_, 3);
lean_inc_ref(v_modules_3523_);
v_moduleNames_3524_ = lean_ctor_get(v___x_3522_, 4);
lean_inc_ref(v_moduleNames_3524_);
lean_dec_ref(v___x_3522_);
v_mod_3525_ = lean_array_get(v___x_3495_, v_moduleNames_3524_, v_val_3518_);
lean_dec_ref(v_moduleNames_3524_);
v___x_3557_ = l_Lean_isPrivateName(v_declHint_3492_);
lean_dec(v_declHint_3492_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3558_ = lean_array_get_size(v_modules_3523_);
v___x_3559_ = lean_nat_dec_lt(v_val_3518_, v___x_3558_);
if (v___x_3559_ == 0)
{
lean_dec_ref(v_modules_3523_);
lean_dec(v_val_3518_);
v___y_3527_ = v___x_3557_;
goto v___jp_3526_;
}
else
{
lean_object* v___x_3560_; lean_object* v_toImport_3561_; uint8_t v_isExported_3562_; 
v___x_3560_ = lean_array_fget(v_modules_3523_, v_val_3518_);
lean_dec(v_val_3518_);
lean_dec_ref(v_modules_3523_);
v_toImport_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc_ref(v_toImport_3561_);
lean_dec(v___x_3560_);
v_isExported_3562_ = lean_ctor_get_uint8(v_toImport_3561_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_3561_);
v___y_3527_ = v_isExported_3562_;
goto v___jp_3526_;
}
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec_ref(v_modules_3523_);
lean_del_object(v___x_3520_);
lean_dec(v_val_3518_);
v___x_3563_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
lean_ctor_set(v___x_3564_, 1, v_c_3509_);
v___x_3565_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__22);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = l_Lean_MessageData_ofName(v_mod_3525_);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__24);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = l_Lean_MessageData_note(v___x_3570_);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v_msg_3491_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
v___jp_3526_:
{
if (v___y_3527_ == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3528_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_3529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v_c_3509_);
v___x_3530_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_3531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3529_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = l_Lean_MessageData_ofName(v_mod_3525_);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3531_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = l_Lean_MessageData_note(v___x_3535_);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v_msg_3491_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set_tag(v___x_3520_, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3537_);
v___x_3539_ = v___x_3520_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3555_; 
v___x_3541_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_3542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
lean_ctor_set(v___x_3542_, 1, v_c_3509_);
v___x_3543_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3542_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = l_Lean_MessageData_ofName(v_mod_3525_);
lean_inc_ref(v___x_3545_);
v___x_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3544_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18);
v___x_3548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3546_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v___x_3545_);
v___x_3550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__20);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = l_Lean_MessageData_note(v___x_3551_);
v___x_3553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3553_, 0, v_msg_3491_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set_tag(v___x_3520_, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3553_);
v___x_3555_ = v___x_3520_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
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
lean_object* v___x_3575_; 
lean_dec_ref(v_env_3497_);
lean_dec(v_declHint_3492_);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v_msg_3491_);
return v___x_3575_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3491_ = stack[0].m_obj;
lean_object* v_declHint_3492_ = stack[1].m_obj;
lean_object* v___y_3493_ = stack[2].m_obj;
lean_object* v_res_3576_;
v_res_3576_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3491_, v_declHint_3492_, v___y_3493_);
stack->m_obj
 = v_res_3576_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3577_, lean_object* v_declHint_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3577_, v_declHint_3578_, v___y_3579_);
lean_dec(v___y_3579_);
return v_res_3581_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3582_, lean_object* v_declHint_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3599_; 
v___x_3589_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3582_, v_declHint_3583_, v___y_3587_);
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3599_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3599_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3597_; 
v___x_3594_ = l_Lean_unknownIdentifierMessageTag;
v___x_3595_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
lean_ctor_set(v___x_3595_, 1, v_a_3590_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3595_);
v___x_3597_ = v___x_3592_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3595_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3582_ = stack[0].m_obj;
lean_object* v_declHint_3583_ = stack[1].m_obj;
lean_object* v___y_3584_ = stack[2].m_obj;
lean_object* v___y_3585_ = stack[3].m_obj;
lean_object* v___y_3586_ = stack[4].m_obj;
lean_object* v___y_3587_ = stack[5].m_obj;
lean_object* v_res_3600_;
v_res_3600_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3582_, v_declHint_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
stack->m_obj
 = v_res_3600_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3601_, lean_object* v_declHint_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3601_, v_declHint_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
return v_res_3608_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3609_, lean_object* v_msg_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_toCold_3616_; lean_object* v_currRecDepth_3617_; lean_object* v_ref_3618_; uint16_t v_optionFlags_3619_; uint8_t v_suppressElabErrors_3620_; uint8_t v_isRecordingDeps_3621_; lean_object* v_ref_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_toCold_3616_ = lean_ctor_get(v___y_3613_, 0);
v_currRecDepth_3617_ = lean_ctor_get(v___y_3613_, 1);
v_ref_3618_ = lean_ctor_get(v___y_3613_, 2);
v_optionFlags_3619_ = lean_ctor_get_uint16(v___y_3613_, sizeof(void*)*3);
v_suppressElabErrors_3620_ = lean_ctor_get_uint8(v___y_3613_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3621_ = lean_ctor_get_uint8(v___y_3613_, sizeof(void*)*3 + 3);
v_ref_3622_ = l_Lean_replaceRef(v_ref_3609_, v_ref_3618_);
lean_inc(v_currRecDepth_3617_);
lean_inc_ref(v_toCold_3616_);
v___x_3623_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3623_, 0, v_toCold_3616_);
lean_ctor_set(v___x_3623_, 1, v_currRecDepth_3617_);
lean_ctor_set(v___x_3623_, 2, v_ref_3622_);
lean_ctor_set_uint16(v___x_3623_, sizeof(void*)*3, v_optionFlags_3619_);
lean_ctor_set_uint8(v___x_3623_, sizeof(void*)*3 + 2, v_suppressElabErrors_3620_);
lean_ctor_set_uint8(v___x_3623_, sizeof(void*)*3 + 3, v_isRecordingDeps_3621_);
v___x_3624_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3610_, v___y_3611_, v___y_3612_, v___x_3623_, v___y_3614_);
lean_dec_ref_known(v___x_3623_, 3);
return v___x_3624_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3609_ = stack[0].m_obj;
lean_object* v_msg_3610_ = stack[1].m_obj;
lean_object* v___y_3611_ = stack[2].m_obj;
lean_object* v___y_3612_ = stack[3].m_obj;
lean_object* v___y_3613_ = stack[4].m_obj;
lean_object* v___y_3614_ = stack[5].m_obj;
lean_object* v_res_3625_;
v_res_3625_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3609_, v_msg_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
stack->m_obj
 = v_res_3625_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3626_, lean_object* v_msg_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3626_, v_msg_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v_ref_3626_);
return v_res_3633_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3634_, lean_object* v_msg_3635_, lean_object* v_declHint_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; lean_object* v_a_3643_; lean_object* v___x_3644_; 
v___x_3642_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3635_, v_declHint_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
lean_dec_ref(v___x_3642_);
v___x_3644_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3634_, v_a_3643_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
return v___x_3644_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3634_ = stack[0].m_obj;
lean_object* v_msg_3635_ = stack[1].m_obj;
lean_object* v_declHint_3636_ = stack[2].m_obj;
lean_object* v___y_3637_ = stack[3].m_obj;
lean_object* v___y_3638_ = stack[4].m_obj;
lean_object* v___y_3639_ = stack[5].m_obj;
lean_object* v___y_3640_ = stack[6].m_obj;
lean_object* v_res_3645_;
v_res_3645_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3634_, v_msg_3635_, v_declHint_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
stack->m_obj
 = v_res_3645_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3646_, lean_object* v_msg_3647_, lean_object* v_declHint_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3646_, v_msg_3647_, v_declHint_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v_ref_3646_);
return v_res_3654_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3657_ = l_Lean_stringToMessageData(v___x_3656_);
return v___x_3657_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3660_ = l_Lean_stringToMessageData(v___x_3659_);
return v___x_3660_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3661_, lean_object* v_constName_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; uint8_t v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3668_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3669_ = 0;
lean_inc(v_constName_3662_);
v___x_3670_ = l_Lean_MessageData_ofConstName(v_constName_3662_, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3668_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v___x_3672_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3671_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3661_, v___x_3673_, v_constName_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
return v___x_3674_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3661_ = stack[0].m_obj;
lean_object* v_constName_3662_ = stack[1].m_obj;
lean_object* v___y_3663_ = stack[2].m_obj;
lean_object* v___y_3664_ = stack[3].m_obj;
lean_object* v___y_3665_ = stack[4].m_obj;
lean_object* v___y_3666_ = stack[5].m_obj;
lean_object* v_res_3675_;
v_res_3675_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3661_, v_constName_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
stack->m_obj
 = v_res_3675_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3676_, lean_object* v_constName_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3676_, v_constName_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v_ref_3676_);
return v_res_3683_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_ref_3690_; lean_object* v___x_3691_; 
v_ref_3690_ = lean_ctor_get(v___y_3687_, 2);
v___x_3691_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3690_, v_constName_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3691_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3684_ = stack[0].m_obj;
lean_object* v___y_3685_ = stack[1].m_obj;
lean_object* v___y_3686_ = stack[2].m_obj;
lean_object* v___y_3687_ = stack[3].m_obj;
lean_object* v___y_3688_ = stack[4].m_obj;
lean_object* v_res_3692_;
v_res_3692_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
stack->m_obj
 = v_res_3692_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
return v_res_3699_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3706_; lean_object* v_env_3707_; uint8_t v___x_3708_; lean_object* v___x_3709_; 
v___x_3706_ = lean_st_ref_get(v___y_3704_);
v_env_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc_ref(v_env_3707_);
lean_dec(v___x_3706_);
v___x_3708_ = 0;
lean_inc(v_constName_3700_);
v___x_3709_ = l_Lean_Environment_find_x3f(v_env_3707_, v_constName_3700_, v___x_3708_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v___x_3710_; 
v___x_3710_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3710_;
}
else
{
lean_object* v_val_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v_constName_3700_);
v_val_3711_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3709_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_val_3711_);
lean_dec(v___x_3709_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set_tag(v___x_3713_, 0);
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_val_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3700_ = stack[0].m_obj;
lean_object* v___y_3701_ = stack[1].m_obj;
lean_object* v___y_3702_ = stack[2].m_obj;
lean_object* v___y_3703_ = stack[3].m_obj;
lean_object* v___y_3704_ = stack[4].m_obj;
lean_object* v_res_3719_;
v_res_3719_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
stack->m_obj
 = v_res_3719_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_a_3727_, lean_object* v_a_3728_){
_start:
{
if (lean_obj_tag(v_a_3727_) == 0)
{
lean_object* v___x_3729_; 
v___x_3729_ = l_List_reverse___redArg(v_a_3728_);
return v___x_3729_;
}
else
{
lean_object* v_head_3730_; lean_object* v_tail_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3740_; 
v_head_3730_ = lean_ctor_get(v_a_3727_, 0);
v_tail_3731_ = lean_ctor_get(v_a_3727_, 1);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_a_3727_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3733_ = v_a_3727_;
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_tail_3731_);
lean_inc(v_head_3730_);
lean_dec(v_a_3727_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; lean_object* v___x_3737_; 
v___x_3735_ = l_Lean_mkLevelParam(v_head_3730_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 1, v_a_3728_);
lean_ctor_set(v___x_3733_, 0, v___x_3735_);
v___x_3737_ = v___x_3733_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_a_3728_);
v___x_3737_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
v_a_3727_ = v_tail_3731_;
v_a_3728_ = v___x_3737_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3743_ = l_Lean_stringToMessageData(v___x_3742_);
return v___x_3743_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3744_, lean_object* v_baseName_3745_, lean_object* v_splitterName_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_){
_start:
{
lean_object* v___x_3752_; uint8_t v_foApprox_3753_; uint8_t v_ctxApprox_3754_; uint8_t v_quasiPatternApprox_3755_; uint8_t v_constApprox_3756_; uint8_t v_isDefEqStuckEx_3757_; uint8_t v_unificationHints_3758_; uint8_t v_proofIrrelevance_3759_; uint8_t v_assignSyntheticOpaque_3760_; uint8_t v_offsetCnstrs_3761_; uint8_t v_transparency_3762_; uint8_t v_univApprox_3763_; uint8_t v_iota_3764_; uint8_t v_beta_3765_; uint8_t v_proj_3766_; uint8_t v_zeta_3767_; uint8_t v_zetaDelta_3768_; uint8_t v_zetaUnused_3769_; uint8_t v_zetaHave_3770_; uint8_t v_canUnfoldPredicateConfig_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3834_; 
v___x_3752_ = l_Lean_Meta_Context_config(v_a_3747_);
v_foApprox_3753_ = lean_ctor_get_uint8(v___x_3752_, 0);
v_ctxApprox_3754_ = lean_ctor_get_uint8(v___x_3752_, 1);
v_quasiPatternApprox_3755_ = lean_ctor_get_uint8(v___x_3752_, 2);
v_constApprox_3756_ = lean_ctor_get_uint8(v___x_3752_, 3);
v_isDefEqStuckEx_3757_ = lean_ctor_get_uint8(v___x_3752_, 4);
v_unificationHints_3758_ = lean_ctor_get_uint8(v___x_3752_, 5);
v_proofIrrelevance_3759_ = lean_ctor_get_uint8(v___x_3752_, 6);
v_assignSyntheticOpaque_3760_ = lean_ctor_get_uint8(v___x_3752_, 7);
v_offsetCnstrs_3761_ = lean_ctor_get_uint8(v___x_3752_, 8);
v_transparency_3762_ = lean_ctor_get_uint8(v___x_3752_, 9);
v_univApprox_3763_ = lean_ctor_get_uint8(v___x_3752_, 11);
v_iota_3764_ = lean_ctor_get_uint8(v___x_3752_, 12);
v_beta_3765_ = lean_ctor_get_uint8(v___x_3752_, 13);
v_proj_3766_ = lean_ctor_get_uint8(v___x_3752_, 14);
v_zeta_3767_ = lean_ctor_get_uint8(v___x_3752_, 15);
v_zetaDelta_3768_ = lean_ctor_get_uint8(v___x_3752_, 16);
v_zetaUnused_3769_ = lean_ctor_get_uint8(v___x_3752_, 17);
v_zetaHave_3770_ = lean_ctor_get_uint8(v___x_3752_, 18);
v_canUnfoldPredicateConfig_3771_ = lean_ctor_get_uint8(v___x_3752_, 19);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3773_ = v___x_3752_;
v_isShared_3774_ = v_isSharedCheck_3834_;
goto v_resetjp_3772_;
}
else
{
lean_dec(v___x_3752_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3834_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
uint8_t v_trackZetaDelta_3775_; lean_object* v_zetaDeltaSet_3776_; lean_object* v_lctx_3777_; lean_object* v_localInstances_3778_; lean_object* v_defEqCtx_x3f_3779_; lean_object* v_synthPendingDepth_3780_; lean_object* v_customCanUnfoldPredicate_x3f_3781_; uint8_t v_univApprox_3782_; uint8_t v_inTypeClassResolution_3783_; uint8_t v_cacheInferType_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3832_; 
v_trackZetaDelta_3775_ = lean_ctor_get_uint8(v_a_3747_, sizeof(void*)*7);
v_zetaDeltaSet_3776_ = lean_ctor_get(v_a_3747_, 1);
v_lctx_3777_ = lean_ctor_get(v_a_3747_, 2);
v_localInstances_3778_ = lean_ctor_get(v_a_3747_, 3);
v_defEqCtx_x3f_3779_ = lean_ctor_get(v_a_3747_, 4);
v_synthPendingDepth_3780_ = lean_ctor_get(v_a_3747_, 5);
v_customCanUnfoldPredicate_x3f_3781_ = lean_ctor_get(v_a_3747_, 6);
v_univApprox_3782_ = lean_ctor_get_uint8(v_a_3747_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3783_ = lean_ctor_get_uint8(v_a_3747_, sizeof(void*)*7 + 2);
v_cacheInferType_3784_ = lean_ctor_get_uint8(v_a_3747_, sizeof(void*)*7 + 3);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_a_3747_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v_a_3747_, 0);
lean_dec(v_unused_3833_);
v___x_3786_ = v_a_3747_;
v_isShared_3787_ = v_isSharedCheck_3832_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3781_);
lean_inc(v_synthPendingDepth_3780_);
lean_inc(v_defEqCtx_x3f_3779_);
lean_inc(v_localInstances_3778_);
lean_inc(v_lctx_3777_);
lean_inc(v_zetaDeltaSet_3776_);
lean_dec(v_a_3747_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3832_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
uint8_t v___x_3788_; lean_object* v___x_3790_; 
v___x_3788_ = 2;
if (v_isShared_3774_ == 0)
{
v___x_3790_ = v___x_3773_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 0, v_foApprox_3753_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 1, v_ctxApprox_3754_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 2, v_quasiPatternApprox_3755_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 3, v_constApprox_3756_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 4, v_isDefEqStuckEx_3757_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 5, v_unificationHints_3758_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 6, v_proofIrrelevance_3759_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 7, v_assignSyntheticOpaque_3760_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 8, v_offsetCnstrs_3761_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 9, v_transparency_3762_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 11, v_univApprox_3763_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 12, v_iota_3764_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 13, v_beta_3765_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 14, v_proj_3766_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 15, v_zeta_3767_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 16, v_zetaDelta_3768_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 17, v_zetaUnused_3769_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 18, v_zetaHave_3770_);
lean_ctor_set_uint8(v_reuseFailAlloc_3831_, 19, v_canUnfoldPredicateConfig_3771_);
v___x_3790_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
uint64_t v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3795_; 
lean_ctor_set_uint8(v___x_3790_, 10, v___x_3788_);
v___x_3791_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3790_);
v___x_3792_ = l_Lean_instInhabitedExpr;
v___x_3793_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3793_, 0, v___x_3790_);
lean_ctor_set_uint64(v___x_3793_, sizeof(void*)*1, v___x_3791_);
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 0, v___x_3793_);
v___x_3795_ = v___x_3786_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3793_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_zetaDeltaSet_3776_);
lean_ctor_set(v_reuseFailAlloc_3830_, 2, v_lctx_3777_);
lean_ctor_set(v_reuseFailAlloc_3830_, 3, v_localInstances_3778_);
lean_ctor_set(v_reuseFailAlloc_3830_, 4, v_defEqCtx_x3f_3779_);
lean_ctor_set(v_reuseFailAlloc_3830_, 5, v_synthPendingDepth_3780_);
lean_ctor_set(v_reuseFailAlloc_3830_, 6, v_customCanUnfoldPredicate_x3f_3781_);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, sizeof(void*)*7, v_trackZetaDelta_3775_);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, sizeof(void*)*7 + 1, v_univApprox_3782_);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3783_);
lean_ctor_set_uint8(v_reuseFailAlloc_3830_, sizeof(void*)*7 + 3, v_cacheInferType_3784_);
v___x_3795_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3796_; 
lean_inc(v_matchDeclName_3744_);
v___x_3796_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3744_, v___x_3795_, v_a_3748_, v_a_3749_, v_a_3750_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v_a_3802_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
v___x_3798_ = l_Lean_ConstantInfo_levelParams(v_a_3797_);
v___x_3799_ = lean_box(0);
lean_inc(v___x_3798_);
v___x_3800_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v___x_3798_, v___x_3799_);
lean_inc(v_matchDeclName_3744_);
v___x_3801_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_3744_, v_a_3750_);
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref(v___x_3801_);
if (lean_obj_tag(v_a_3802_) == 1)
{
lean_object* v_val_3803_; lean_object* v_numParams_3804_; lean_object* v_numDiscrs_3805_; lean_object* v_altInfos_3806_; lean_object* v_uElimPos_x3f_3807_; lean_object* v_discrInfos_3808_; lean_object* v_overlaps_3809_; lean_object* v___f_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___f_3813_; uint8_t v___x_3814_; lean_object* v___x_3815_; 
v_val_3803_ = lean_ctor_get(v_a_3802_, 0);
lean_inc(v_val_3803_);
lean_dec_ref_known(v_a_3802_, 1);
v_numParams_3804_ = lean_ctor_get(v_val_3803_, 0);
lean_inc(v_numParams_3804_);
v_numDiscrs_3805_ = lean_ctor_get(v_val_3803_, 1);
lean_inc(v_numDiscrs_3805_);
v_altInfos_3806_ = lean_ctor_get(v_val_3803_, 2);
lean_inc_ref(v_altInfos_3806_);
v_uElimPos_x3f_3807_ = lean_ctor_get(v_val_3803_, 3);
lean_inc(v_uElimPos_x3f_3807_);
v_discrInfos_3808_ = lean_ctor_get(v_val_3803_, 4);
lean_inc_ref(v_discrInfos_3808_);
v_overlaps_3809_ = lean_ctor_get(v_val_3803_, 5);
lean_inc_ref_n(v_overlaps_3809_, 2);
lean_inc(v_splitterName_3746_);
v___f_3810_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3810_, 0, v_overlaps_3809_);
lean_closure_set(v___f_3810_, 1, v_splitterName_3746_);
v___x_3811_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3808_);
v___x_3812_ = l_Lean_ConstantInfo_type(v_a_3797_);
lean_inc_ref(v___x_3812_);
v___f_3813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3813_, 0, v_splitterName_3746_);
lean_closure_set(v___f_3813_, 1, v_matchDeclName_3744_);
lean_closure_set(v___f_3813_, 2, v_numParams_3804_);
lean_closure_set(v___f_3813_, 3, v_val_3803_);
lean_closure_set(v___f_3813_, 4, v___x_3792_);
lean_closure_set(v___f_3813_, 5, v_numDiscrs_3805_);
lean_closure_set(v___f_3813_, 6, v_baseName_3745_);
lean_closure_set(v___f_3813_, 7, v_a_3797_);
lean_closure_set(v___f_3813_, 8, v___x_3800_);
lean_closure_set(v___f_3813_, 9, v___x_3798_);
lean_closure_set(v___f_3813_, 10, v___x_3811_);
lean_closure_set(v___f_3813_, 11, v_uElimPos_x3f_3807_);
lean_closure_set(v___f_3813_, 12, v_discrInfos_3808_);
lean_closure_set(v___f_3813_, 13, v_overlaps_3809_);
lean_closure_set(v___f_3813_, 14, v___f_3810_);
lean_closure_set(v___f_3813_, 15, v___x_3812_);
lean_closure_set(v___f_3813_, 16, v_altInfos_3806_);
v___x_3814_ = 0;
v___x_3815_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3812_, v___f_3813_, v___x_3814_, v___x_3814_, v___x_3795_, v_a_3748_, v_a_3749_, v_a_3750_);
lean_dec_ref(v___x_3795_);
return v___x_3815_;
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
lean_dec(v_a_3802_);
lean_dec(v___x_3800_);
lean_dec(v___x_3798_);
lean_dec(v_a_3797_);
lean_dec(v_splitterName_3746_);
lean_dec(v_baseName_3745_);
v___x_3816_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3817_ = l_Lean_MessageData_ofName(v_matchDeclName_3744_);
v___x_3818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3818_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3820_, v___x_3795_, v_a_3748_, v_a_3749_, v_a_3750_);
lean_dec_ref(v___x_3795_);
return v___x_3821_;
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref(v___x_3795_);
lean_dec(v_splitterName_3746_);
lean_dec(v_baseName_3745_);
lean_dec(v_matchDeclName_3744_);
v_a_3822_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3796_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3796_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_3744_ = stack[0].m_obj;
lean_object* v_baseName_3745_ = stack[1].m_obj;
lean_object* v_splitterName_3746_ = stack[2].m_obj;
lean_object* v_a_3747_ = stack[3].m_obj;
lean_object* v_a_3748_ = stack[4].m_obj;
lean_object* v_a_3749_ = stack[5].m_obj;
lean_object* v_a_3750_ = stack[6].m_obj;
lean_object* v_res_3835_;
v_res_3835_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3744_, v_baseName_3745_, v_splitterName_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
stack->m_obj
 = v_res_3835_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3836_, lean_object* v_baseName_3837_, lean_object* v_splitterName_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3836_, v_baseName_3837_, v_splitterName_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
return v_res_3844_;
}
}
uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3845_, lean_object* v_ys_3846_, lean_object* v_hsz_3847_, lean_object* v_x_3848_, lean_object* v_x_3849_){
_start:
{
uint8_t v___x_3850_; 
v___x_3850_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3845_, v_ys_3846_, v_x_3848_);
return v___x_3850_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_3845_ = stack[0].m_obj;
lean_object* v_ys_3846_ = stack[1].m_obj;
lean_object* v_x_3848_ = stack[3].m_obj;
uint8_t v_res_3851_;
v_res_3851_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3845_, v_ys_3846_, lean_box(0), v_x_3848_, lean_box(0));
stack->m_num = v_res_3851_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3852_, lean_object* v_ys_3853_, lean_object* v_hsz_3854_, lean_object* v_x_3855_, lean_object* v_x_3856_){
_start:
{
uint8_t v_res_3857_; lean_object* v_r_3858_; 
v_res_3857_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3852_, v_ys_3853_, v_hsz_3854_, v_x_3855_, v_x_3856_);
lean_dec_ref(v_ys_3853_);
lean_dec_ref(v_xs_3852_);
v_r_3858_ = lean_box(v_res_3857_);
return v_r_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3859_, lean_object* v_R_3860_, lean_object* v_a_3861_, lean_object* v_b_3862_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3861_, v_b_3862_);
return v___x_3863_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3864_, lean_object* v_val_3865_, lean_object* v_baseName_3866_, lean_object* v___x_3867_, lean_object* v_a_3868_, lean_object* v___x_3869_, lean_object* v___x_3870_, lean_object* v___x_3871_, lean_object* v_matchDeclName_3872_, lean_object* v___x_3873_, lean_object* v___x_3874_, lean_object* v___x_3875_, lean_object* v_inst_3876_, lean_object* v_R_3877_, lean_object* v_a_3878_, lean_object* v_b_3879_, lean_object* v_c_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3864_, v_val_3865_, v_baseName_3866_, v___x_3867_, v_a_3868_, v___x_3869_, v___x_3870_, v___x_3871_, v_matchDeclName_3872_, v___x_3873_, v___x_3874_, v___x_3875_, v_a_3878_, v_b_3879_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3886_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3864_ = stack[0].m_obj;
lean_object* v_val_3865_ = stack[1].m_obj;
lean_object* v_baseName_3866_ = stack[2].m_obj;
lean_object* v___x_3867_ = stack[3].m_obj;
lean_object* v_a_3868_ = stack[4].m_obj;
lean_object* v___x_3869_ = stack[5].m_obj;
lean_object* v___x_3870_ = stack[6].m_obj;
lean_object* v___x_3871_ = stack[7].m_obj;
lean_object* v_matchDeclName_3872_ = stack[8].m_obj;
lean_object* v___x_3873_ = stack[9].m_obj;
lean_object* v___x_3874_ = stack[10].m_obj;
lean_object* v___x_3875_ = stack[11].m_obj;
lean_object* v_a_3878_ = stack[14].m_obj;
lean_object* v_b_3879_ = stack[15].m_obj;
lean_object* v___y_3881_ = stack[17].m_obj;
lean_object* v___y_3882_ = stack[18].m_obj;
lean_object* v___y_3883_ = stack[19].m_obj;
lean_object* v___y_3884_ = stack[20].m_obj;
lean_object* v_res_3887_;
v_res_3887_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3864_, v_val_3865_, v_baseName_3866_, v___x_3867_, v_a_3868_, v___x_3869_, v___x_3870_, v___x_3871_, v_matchDeclName_3872_, v___x_3873_, v___x_3874_, v___x_3875_, lean_box(0), lean_box(0), v_a_3878_, v_b_3879_, lean_box(0), v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
stack->m_obj
 = v_res_3887_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3888_ = _args[0];
lean_object* v_val_3889_ = _args[1];
lean_object* v_baseName_3890_ = _args[2];
lean_object* v___x_3891_ = _args[3];
lean_object* v_a_3892_ = _args[4];
lean_object* v___x_3893_ = _args[5];
lean_object* v___x_3894_ = _args[6];
lean_object* v___x_3895_ = _args[7];
lean_object* v_matchDeclName_3896_ = _args[8];
lean_object* v___x_3897_ = _args[9];
lean_object* v___x_3898_ = _args[10];
lean_object* v___x_3899_ = _args[11];
lean_object* v_inst_3900_ = _args[12];
lean_object* v_R_3901_ = _args[13];
lean_object* v_a_3902_ = _args[14];
lean_object* v_b_3903_ = _args[15];
lean_object* v_c_3904_ = _args[16];
lean_object* v___y_3905_ = _args[17];
lean_object* v___y_3906_ = _args[18];
lean_object* v___y_3907_ = _args[19];
lean_object* v___y_3908_ = _args[20];
lean_object* v___y_3909_ = _args[21];
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3888_, v_val_3889_, v_baseName_3890_, v___x_3891_, v_a_3892_, v___x_3893_, v___x_3894_, v___x_3895_, v_matchDeclName_3896_, v___x_3897_, v___x_3898_, v___x_3899_, v_inst_3900_, v_R_3901_, v_a_3902_, v_b_3903_, v_c_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v_upperBound_3888_);
return v_res_3910_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3911_, lean_object* v_constName_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
return v___x_3918_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3912_ = stack[1].m_obj;
lean_object* v___y_3913_ = stack[2].m_obj;
lean_object* v___y_3914_ = stack[3].m_obj;
lean_object* v___y_3915_ = stack[4].m_obj;
lean_object* v___y_3916_ = stack[5].m_obj;
lean_object* v_res_3919_;
v_res_3919_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_box(0), v_constName_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
stack->m_obj
 = v_res_3919_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3920_, lean_object* v_constName_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3920_, v_constName_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
return v_res_3927_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3928_, lean_object* v_ref_3929_, lean_object* v_constName_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3929_, v_constName_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
return v___x_3936_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3929_ = stack[1].m_obj;
lean_object* v_constName_3930_ = stack[2].m_obj;
lean_object* v___y_3931_ = stack[3].m_obj;
lean_object* v___y_3932_ = stack[4].m_obj;
lean_object* v___y_3933_ = stack[5].m_obj;
lean_object* v___y_3934_ = stack[6].m_obj;
lean_object* v_res_3937_;
v_res_3937_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_box(0), v_ref_3929_, v_constName_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
stack->m_obj
 = v_res_3937_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3938_, lean_object* v_ref_3939_, lean_object* v_constName_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3938_, v_ref_3939_, v_constName_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v_ref_3939_);
return v_res_3946_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3947_, lean_object* v_ref_3948_, lean_object* v_msg_3949_, lean_object* v_declHint_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3948_, v_msg_3949_, v_declHint_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
return v___x_3956_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3948_ = stack[1].m_obj;
lean_object* v_msg_3949_ = stack[2].m_obj;
lean_object* v_declHint_3950_ = stack[3].m_obj;
lean_object* v___y_3951_ = stack[4].m_obj;
lean_object* v___y_3952_ = stack[5].m_obj;
lean_object* v___y_3953_ = stack[6].m_obj;
lean_object* v___y_3954_ = stack[7].m_obj;
lean_object* v_res_3957_;
v_res_3957_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_box(0), v_ref_3948_, v_msg_3949_, v_declHint_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
stack->m_obj
 = v_res_3957_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3958_, lean_object* v_ref_3959_, lean_object* v_msg_3960_, lean_object* v_declHint_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3958_, v_ref_3959_, v_msg_3960_, v_declHint_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v_ref_3959_);
return v_res_3967_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3968_, lean_object* v_declHint_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3968_, v_declHint_3969_, v___y_3973_);
return v___x_3975_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3968_ = stack[0].m_obj;
lean_object* v_declHint_3969_ = stack[1].m_obj;
lean_object* v___y_3970_ = stack[2].m_obj;
lean_object* v___y_3971_ = stack[3].m_obj;
lean_object* v___y_3972_ = stack[4].m_obj;
lean_object* v___y_3973_ = stack[5].m_obj;
lean_object* v_res_3976_;
v_res_3976_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3968_, v_declHint_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_);
stack->m_obj
 = v_res_3976_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3977_, lean_object* v_declHint_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3977_, v_declHint_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
return v_res_3984_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3985_, lean_object* v_ref_3986_, lean_object* v_msg_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v___x_3993_; 
v___x_3993_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3986_, v_msg_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
return v___x_3993_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3986_ = stack[1].m_obj;
lean_object* v_msg_3987_ = stack[2].m_obj;
lean_object* v___y_3988_ = stack[3].m_obj;
lean_object* v___y_3989_ = stack[4].m_obj;
lean_object* v___y_3990_ = stack[5].m_obj;
lean_object* v___y_3991_ = stack[6].m_obj;
lean_object* v_res_3994_;
v_res_3994_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_box(0), v_ref_3986_, v_msg_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
stack->m_obj
 = v_res_3994_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3995_, lean_object* v_ref_3996_, lean_object* v_msg_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3995_, v_ref_3996_, v_msg_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v_ref_3996_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_4004_, lean_object* v_vals_4005_, lean_object* v_i_4006_, lean_object* v_k_4007_){
_start:
{
lean_object* v___x_4008_; uint8_t v___x_4009_; 
v___x_4008_ = lean_array_get_size(v_keys_4004_);
v___x_4009_ = lean_nat_dec_lt(v_i_4006_, v___x_4008_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; 
lean_dec(v_i_4006_);
v___x_4010_ = lean_box(0);
return v___x_4010_;
}
else
{
lean_object* v_k_x27_4011_; uint8_t v___x_4012_; 
v_k_x27_4011_ = lean_array_fget_borrowed(v_keys_4004_, v_i_4006_);
v___x_4012_ = lean_name_eq(v_k_4007_, v_k_x27_4011_);
if (v___x_4012_ == 0)
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4013_ = lean_unsigned_to_nat(1u);
v___x_4014_ = lean_nat_add(v_i_4006_, v___x_4013_);
lean_dec(v_i_4006_);
v_i_4006_ = v___x_4014_;
goto _start;
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_array_fget_borrowed(v_vals_4005_, v_i_4006_);
lean_dec(v_i_4006_);
lean_inc(v___x_4016_);
v___x_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
return v___x_4017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_4018_, lean_object* v_vals_4019_, lean_object* v_i_4020_, lean_object* v_k_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4018_, v_vals_4019_, v_i_4020_, v_k_4021_);
lean_dec(v_k_4021_);
lean_dec_ref(v_vals_4019_);
lean_dec_ref(v_keys_4018_);
return v_res_4022_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_4023_, size_t v_x_4024_, lean_object* v_x_4025_){
_start:
{
if (lean_obj_tag(v_x_4023_) == 0)
{
lean_object* v_es_4026_; lean_object* v___x_4027_; size_t v___x_4028_; size_t v___x_4029_; lean_object* v_j_4030_; lean_object* v___x_4031_; 
v_es_4026_ = lean_ctor_get(v_x_4023_, 0);
v___x_4027_ = lean_box(2);
v___x_4028_ = ((size_t)31ULL);
v___x_4029_ = lean_usize_land(v_x_4024_, v___x_4028_);
v_j_4030_ = lean_usize_to_nat(v___x_4029_);
v___x_4031_ = lean_array_get_borrowed(v___x_4027_, v_es_4026_, v_j_4030_);
lean_dec(v_j_4030_);
switch(lean_obj_tag(v___x_4031_))
{
case 0:
{
lean_object* v_key_4032_; lean_object* v_val_4033_; uint8_t v___x_4034_; 
v_key_4032_ = lean_ctor_get(v___x_4031_, 0);
v_val_4033_ = lean_ctor_get(v___x_4031_, 1);
v___x_4034_ = lean_name_eq(v_x_4025_, v_key_4032_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; 
v___x_4035_ = lean_box(0);
return v___x_4035_;
}
else
{
lean_object* v___x_4036_; 
lean_inc(v_val_4033_);
v___x_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4036_, 0, v_val_4033_);
return v___x_4036_;
}
}
case 1:
{
lean_object* v_node_4037_; size_t v___x_4038_; size_t v___x_4039_; 
v_node_4037_ = lean_ctor_get(v___x_4031_, 0);
v___x_4038_ = ((size_t)5ULL);
v___x_4039_ = lean_usize_shift_right(v_x_4024_, v___x_4038_);
v_x_4023_ = v_node_4037_;
v_x_4024_ = v___x_4039_;
goto _start;
}
default: 
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_box(0);
return v___x_4041_;
}
}
}
else
{
lean_object* v_ks_4042_; lean_object* v_vs_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v_ks_4042_ = lean_ctor_get(v_x_4023_, 0);
v_vs_4043_ = lean_ctor_get(v_x_4023_, 1);
v___x_4044_ = lean_unsigned_to_nat(0u);
v___x_4045_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_4042_, v_vs_4043_, v___x_4044_, v_x_4025_);
return v___x_4045_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4023_ = stack[0].m_obj;
size_t v_x_4024_ = stack[1].m_num;
lean_object* v_x_4025_ = stack[2].m_obj;
lean_object* v_res_4046_;
v_res_4046_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4023_, v_x_4024_, v_x_4025_);
stack->m_obj
 = v_res_4046_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_4047_, lean_object* v_x_4048_, lean_object* v_x_4049_){
_start:
{
size_t v_x_718__boxed_4050_; lean_object* v_res_4051_; 
v_x_718__boxed_4050_ = lean_unbox_usize(v_x_4048_);
lean_dec(v_x_4048_);
v_res_4051_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4047_, v_x_718__boxed_4050_, v_x_4049_);
lean_dec(v_x_4049_);
lean_dec_ref(v_x_4047_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_4052_, lean_object* v_x_4053_){
_start:
{
uint64_t v___y_4055_; 
if (lean_obj_tag(v_x_4053_) == 0)
{
uint64_t v___x_4058_; 
v___x_4058_ = 1723ULL;
v___y_4055_ = v___x_4058_;
goto v___jp_4054_;
}
else
{
uint64_t v_hash_4059_; 
v_hash_4059_ = lean_ctor_get_uint64(v_x_4053_, sizeof(void*)*2);
v___y_4055_ = v_hash_4059_;
goto v___jp_4054_;
}
v___jp_4054_:
{
size_t v___x_4056_; lean_object* v___x_4057_; 
v___x_4056_ = lean_uint64_to_usize(v___y_4055_);
v___x_4057_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4052_, v___x_4056_, v_x_4053_);
return v___x_4057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_4060_, lean_object* v_x_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4060_, v_x_4061_);
lean_dec(v_x_4061_);
lean_dec_ref(v_x_4060_);
return v_res_4062_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_4070_ = l_Lean_stringToMessageData(v___x_4069_);
return v___x_4070_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_4073_ = l_Lean_stringToMessageData(v___x_4072_);
return v___x_4073_;
}
}
lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v_env_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4080_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_4081_ = lean_st_ref_get(v_a_4078_);
v_env_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc_ref(v_env_4082_);
lean_dec(v___x_4081_);
lean_inc_n(v_matchDeclName_4074_, 3);
v___x_4083_ = l_Lean_mkPrivateName(v_env_4082_, v_matchDeclName_4074_);
lean_dec_ref(v_env_4082_);
v___x_4084_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_4083_);
v___x_4085_ = l_Lean_Name_append(v___x_4083_, v___x_4084_);
lean_inc_n(v___x_4085_, 2);
v___x_4086_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_4086_, 0, v_matchDeclName_4074_);
lean_closure_set(v___x_4086_, 1, v___x_4083_);
lean_closure_set(v___x_4086_, 2, v___x_4085_);
v___x_4087_ = l_Lean_Meta_realizeConst(v_matchDeclName_4074_, v___x_4085_, v___x_4086_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4116_; 
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4116_ == 0)
{
lean_object* v_unused_4117_; 
v_unused_4117_ = lean_ctor_get(v___x_4087_, 0);
lean_dec(v_unused_4117_);
v___x_4089_ = v___x_4087_;
v_isShared_4090_ = v_isSharedCheck_4116_;
goto v_resetjp_4088_;
}
else
{
lean_dec(v___x_4087_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4116_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4091_; lean_object* v_env_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; uint8_t v___x_4095_; lean_object* v___x_4096_; lean_object* v_map_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4114_; 
v___x_4091_ = lean_st_ref_get(v_a_4078_);
v_env_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc_ref(v_env_4092_);
lean_dec(v___x_4091_);
v___x_4093_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_4094_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_4095_ = 0;
v___x_4096_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4080_, v___x_4093_, v_env_4092_, v___x_4094_, v___x_4085_, v___x_4095_);
v_map_4097_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4114_ == 0)
{
lean_object* v_unused_4115_; 
v_unused_4115_ = lean_ctor_get(v___x_4096_, 1);
lean_dec(v_unused_4115_);
v___x_4099_ = v___x_4096_;
v_isShared_4100_ = v_isSharedCheck_4114_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_map_4097_);
lean_dec(v___x_4096_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4114_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_4097_, v_matchDeclName_4074_);
lean_dec_ref(v_map_4097_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4105_; 
lean_del_object(v___x_4089_);
v___x_4102_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_4103_ = l_Lean_MessageData_ofName(v_matchDeclName_4074_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set_tag(v___x_4099_, 7);
lean_ctor_set(v___x_4099_, 1, v___x_4103_);
lean_ctor_set(v___x_4099_, 0, v___x_4102_);
v___x_4105_ = v___x_4099_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4109_, 1, v___x_4103_);
v___x_4105_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4106_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_4107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4105_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_4107_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_);
lean_dec(v_a_4078_);
lean_dec_ref(v_a_4077_);
lean_dec(v_a_4076_);
lean_dec_ref(v_a_4075_);
return v___x_4108_;
}
}
else
{
lean_object* v_val_4110_; lean_object* v___x_4112_; 
lean_del_object(v___x_4099_);
lean_dec(v_a_4078_);
lean_dec_ref(v_a_4077_);
lean_dec(v_a_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_matchDeclName_4074_);
v_val_4110_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_val_4110_);
lean_dec_ref_known(v___x_4101_, 1);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v_val_4110_);
v___x_4112_ = v___x_4089_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_val_4110_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec(v___x_4085_);
lean_dec(v_a_4078_);
lean_dec_ref(v_a_4077_);
lean_dec(v_a_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_matchDeclName_4074_);
v_a_4118_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4087_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4087_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
}
LEAN_EXPORT void lean_get_match_equations_for_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_4074_ = stack[0].m_obj;
lean_object* v_a_4075_ = stack[1].m_obj;
lean_object* v_a_4076_ = stack[2].m_obj;
lean_object* v_a_4077_ = stack[3].m_obj;
lean_object* v_a_4078_ = stack[4].m_obj;
lean_object* v_res_4126_;
v_res_4126_ = lean_get_match_equations_for(v_matchDeclName_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_);
stack->m_obj
 = v_res_4126_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = lean_get_match_equations_for(v_matchDeclName_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4134_, lean_object* v_x_4135_, lean_object* v_x_4136_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4135_, v_x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4138_, lean_object* v_x_4139_, lean_object* v_x_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4138_, v_x_4139_, v_x_4140_);
lean_dec(v_x_4140_);
lean_dec_ref(v_x_4139_);
return v_res_4141_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4142_, lean_object* v_x_4143_, size_t v_x_4144_, lean_object* v_x_4145_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4143_, v_x_4144_, v_x_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4143_ = stack[1].m_obj;
size_t v_x_4144_ = stack[2].m_num;
lean_object* v_x_4145_ = stack[3].m_obj;
lean_object* v_res_4147_;
v_res_4147_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_box(0), v_x_4143_, v_x_4144_, v_x_4145_);
stack->m_obj
 = v_res_4147_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4148_, lean_object* v_x_4149_, lean_object* v_x_4150_, lean_object* v_x_4151_){
_start:
{
size_t v_x_1007__boxed_4152_; lean_object* v_res_4153_; 
v_x_1007__boxed_4152_ = lean_unbox_usize(v_x_4150_);
lean_dec(v_x_4150_);
v_res_4153_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4148_, v_x_4149_, v_x_1007__boxed_4152_, v_x_4151_);
lean_dec(v_x_4151_);
lean_dec_ref(v_x_4149_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4154_, lean_object* v_keys_4155_, lean_object* v_vals_4156_, lean_object* v_heq_4157_, lean_object* v_i_4158_, lean_object* v_k_4159_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4155_, v_vals_4156_, v_i_4158_, v_k_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4161_, lean_object* v_keys_4162_, lean_object* v_vals_4163_, lean_object* v_heq_4164_, lean_object* v_i_4165_, lean_object* v_k_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4161_, v_keys_4162_, v_vals_4163_, v_heq_4164_, v_i_4165_, v_k_4166_);
lean_dec(v_k_4166_);
lean_dec_ref(v_vals_4163_);
lean_dec_ref(v_keys_4162_);
return v_res_4167_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4168_, lean_object* v_k_4169_, uint8_t v_cleanupAnnotations_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v___f_4176_; uint8_t v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___f_4176_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4176_, 0, v_k_4169_);
v___x_4177_ = 0;
v___x_4178_ = lean_box(0);
v___x_4179_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4177_, v___x_4178_, v_type_4168_, v___f_4176_, v_cleanupAnnotations_4170_, v___x_4177_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
v_a_4188_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4179_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4179_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4168_ = stack[0].m_obj;
lean_object* v_k_4169_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_4170_ = stack[2].m_num;
lean_object* v___y_4171_ = stack[3].m_obj;
lean_object* v___y_4172_ = stack[4].m_obj;
lean_object* v___y_4173_ = stack[5].m_obj;
lean_object* v___y_4174_ = stack[6].m_obj;
lean_object* v_res_4196_;
v_res_4196_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4168_, v_k_4169_, v_cleanupAnnotations_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
stack->m_obj
 = v_res_4196_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4197_, lean_object* v_k_4198_, lean_object* v_cleanupAnnotations_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4205_; lean_object* v_res_4206_; 
v_cleanupAnnotations_boxed_4205_ = lean_unbox(v_cleanupAnnotations_4199_);
v_res_4206_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4197_, v_k_4198_, v_cleanupAnnotations_boxed_4205_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
return v_res_4206_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4207_, lean_object* v_type_4208_, lean_object* v_k_4209_, uint8_t v_cleanupAnnotations_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4208_, v_k_4209_, v_cleanupAnnotations_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
return v___x_4216_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4208_ = stack[1].m_obj;
lean_object* v_k_4209_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_4210_ = stack[3].m_num;
lean_object* v___y_4211_ = stack[4].m_obj;
lean_object* v___y_4212_ = stack[5].m_obj;
lean_object* v___y_4213_ = stack[6].m_obj;
lean_object* v___y_4214_ = stack[7].m_obj;
lean_object* v_res_4217_;
v_res_4217_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_box(0), v_type_4208_, v_k_4209_, v_cleanupAnnotations_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
stack->m_obj
 = v_res_4217_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4218_, lean_object* v_type_4219_, lean_object* v_k_4220_, lean_object* v_cleanupAnnotations_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4227_; lean_object* v_res_4228_; 
v_cleanupAnnotations_boxed_4227_ = lean_unbox(v_cleanupAnnotations_4221_);
v_res_4228_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4218_, v_type_4219_, v_k_4220_, v_cleanupAnnotations_boxed_4227_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
return v_res_4228_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_msg_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___f_4235_; lean_object* v___x_18841__overap_4236_; lean_object* v___x_4237_; 
v___f_4235_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_18841__overap_4236_ = lean_panic_fn_borrowed(v___f_4235_, v_msg_4229_);
lean_inc(v___y_4233_);
lean_inc_ref(v___y_4232_);
lean_inc(v___y_4231_);
lean_inc_ref(v___y_4230_);
v___x_4237_ = lean_apply_5(v___x_18841__overap_4236_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, lean_box(0));
return v___x_4237_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4229_ = stack[0].m_obj;
lean_object* v___y_4230_ = stack[1].m_obj;
lean_object* v___y_4231_ = stack[2].m_obj;
lean_object* v___y_4232_ = stack[3].m_obj;
lean_object* v___y_4233_ = stack[4].m_obj;
lean_object* v_res_4238_;
v_res_4238_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_msg_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
stack->m_obj
 = v_res_4238_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_msg_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_msg_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4246_){
_start:
{
uint8_t v_foApprox_4247_; uint8_t v_ctxApprox_4248_; uint8_t v_quasiPatternApprox_4249_; uint8_t v_constApprox_4250_; uint8_t v_isDefEqStuckEx_4251_; uint8_t v_unificationHints_4252_; uint8_t v_proofIrrelevance_4253_; uint8_t v_assignSyntheticOpaque_4254_; uint8_t v_offsetCnstrs_4255_; uint8_t v_transparency_4256_; uint8_t v_univApprox_4257_; uint8_t v_iota_4258_; uint8_t v_beta_4259_; uint8_t v_proj_4260_; uint8_t v_zeta_4261_; uint8_t v_zetaDelta_4262_; uint8_t v_zetaUnused_4263_; uint8_t v_zetaHave_4264_; uint8_t v_canUnfoldPredicateConfig_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4273_; 
v_foApprox_4247_ = lean_ctor_get_uint8(v_c_4246_, 0);
v_ctxApprox_4248_ = lean_ctor_get_uint8(v_c_4246_, 1);
v_quasiPatternApprox_4249_ = lean_ctor_get_uint8(v_c_4246_, 2);
v_constApprox_4250_ = lean_ctor_get_uint8(v_c_4246_, 3);
v_isDefEqStuckEx_4251_ = lean_ctor_get_uint8(v_c_4246_, 4);
v_unificationHints_4252_ = lean_ctor_get_uint8(v_c_4246_, 5);
v_proofIrrelevance_4253_ = lean_ctor_get_uint8(v_c_4246_, 6);
v_assignSyntheticOpaque_4254_ = lean_ctor_get_uint8(v_c_4246_, 7);
v_offsetCnstrs_4255_ = lean_ctor_get_uint8(v_c_4246_, 8);
v_transparency_4256_ = lean_ctor_get_uint8(v_c_4246_, 9);
v_univApprox_4257_ = lean_ctor_get_uint8(v_c_4246_, 11);
v_iota_4258_ = lean_ctor_get_uint8(v_c_4246_, 12);
v_beta_4259_ = lean_ctor_get_uint8(v_c_4246_, 13);
v_proj_4260_ = lean_ctor_get_uint8(v_c_4246_, 14);
v_zeta_4261_ = lean_ctor_get_uint8(v_c_4246_, 15);
v_zetaDelta_4262_ = lean_ctor_get_uint8(v_c_4246_, 16);
v_zetaUnused_4263_ = lean_ctor_get_uint8(v_c_4246_, 17);
v_zetaHave_4264_ = lean_ctor_get_uint8(v_c_4246_, 18);
v_canUnfoldPredicateConfig_4265_ = lean_ctor_get_uint8(v_c_4246_, 19);
v_isSharedCheck_4273_ = !lean_is_exclusive(v_c_4246_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4267_ = v_c_4246_;
v_isShared_4268_ = v_isSharedCheck_4273_;
goto v_resetjp_4266_;
}
else
{
lean_dec(v_c_4246_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4273_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
uint8_t v___x_4269_; lean_object* v___x_4271_; 
v___x_4269_ = 2;
if (v_isShared_4268_ == 0)
{
v___x_4271_ = v___x_4267_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 0, v_foApprox_4247_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 1, v_ctxApprox_4248_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 2, v_quasiPatternApprox_4249_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 3, v_constApprox_4250_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 4, v_isDefEqStuckEx_4251_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 5, v_unificationHints_4252_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 6, v_proofIrrelevance_4253_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 7, v_assignSyntheticOpaque_4254_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 8, v_offsetCnstrs_4255_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 9, v_transparency_4256_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 11, v_univApprox_4257_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 12, v_iota_4258_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 13, v_beta_4259_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 14, v_proj_4260_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 15, v_zeta_4261_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 16, v_zetaDelta_4262_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 17, v_zetaUnused_4263_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 18, v_zetaHave_4264_);
lean_ctor_set_uint8(v_reuseFailAlloc_4272_, 19, v_canUnfoldPredicateConfig_4265_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
lean_ctor_set_uint8(v___x_4271_, 10, v___x_4269_);
return v___x_4271_;
}
}
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4274_, lean_object* v_t_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v_dummy_4281_; lean_object* v_nargs_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_dummy_4281_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4282_ = l_Lean_Expr_getAppNumArgs(v_t_4275_);
lean_inc(v_nargs_4282_);
v___x_4283_ = lean_mk_array(v_nargs_4282_, v_dummy_4281_);
v___x_4284_ = lean_unsigned_to_nat(1u);
v___x_4285_ = lean_nat_sub(v_nargs_4282_, v___x_4284_);
lean_dec(v_nargs_4282_);
v___x_4286_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4275_, v___x_4283_, v___x_4285_);
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4274_ = stack[0].m_obj;
lean_object* v_t_4275_ = stack[1].m_obj;
lean_object* v___y_4276_ = stack[2].m_obj;
lean_object* v___y_4277_ = stack[3].m_obj;
lean_object* v___y_4278_ = stack[4].m_obj;
lean_object* v___y_4279_ = stack[5].m_obj;
lean_object* v_res_4288_;
v_res_4288_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4274_, v_t_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
stack->m_obj
 = v_res_4288_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4289_, lean_object* v_t_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4289_, v_t_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec_ref(v_x_4289_);
return v_res_4296_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4297_, lean_object* v_x_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4304_, 0, v_snd_4297_);
return v___x_4304_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_4297_ = stack[0].m_obj;
lean_object* v_x_4298_ = stack[1].m_obj;
lean_object* v___y_4299_ = stack[2].m_obj;
lean_object* v___y_4300_ = stack[3].m_obj;
lean_object* v___y_4301_ = stack[4].m_obj;
lean_object* v___y_4302_ = stack[5].m_obj;
lean_object* v_res_4305_;
v_res_4305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4297_, v_x_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
stack->m_obj
 = v_res_4305_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4306_, lean_object* v_x_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4306_, v_x_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec_ref(v_x_4307_);
return v_res_4313_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4314_, size_t v_i_4315_, lean_object* v_bs_4316_){
_start:
{
uint8_t v___x_4317_; 
v___x_4317_ = lean_usize_dec_lt(v_i_4315_, v_sz_4314_);
if (v___x_4317_ == 0)
{
return v_bs_4316_;
}
else
{
lean_object* v_v_4318_; lean_object* v_fst_4319_; lean_object* v_snd_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4334_; 
v_v_4318_ = lean_array_uget(v_bs_4316_, v_i_4315_);
v_fst_4319_ = lean_ctor_get(v_v_4318_, 0);
v_snd_4320_ = lean_ctor_get(v_v_4318_, 1);
v_isSharedCheck_4334_ = !lean_is_exclusive(v_v_4318_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4322_ = v_v_4318_;
v_isShared_4323_ = v_isSharedCheck_4334_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_snd_4320_);
lean_inc(v_fst_4319_);
lean_dec(v_v_4318_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4334_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4324_; lean_object* v_bs_x27_4325_; lean_object* v___f_4326_; lean_object* v___x_4328_; 
v___x_4324_ = lean_unsigned_to_nat(0u);
v_bs_x27_4325_ = lean_array_uset(v_bs_4316_, v_i_4315_, v___x_4324_);
v___f_4326_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4326_, 0, v_snd_4320_);
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 1, v___f_4326_);
v___x_4328_ = v___x_4322_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_fst_4319_);
lean_ctor_set(v_reuseFailAlloc_4333_, 1, v___f_4326_);
v___x_4328_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
size_t v___x_4329_; size_t v___x_4330_; lean_object* v___x_4331_; 
v___x_4329_ = ((size_t)1ULL);
v___x_4330_ = lean_usize_add(v_i_4315_, v___x_4329_);
v___x_4331_ = lean_array_uset(v_bs_x27_4325_, v_i_4315_, v___x_4328_);
v_i_4315_ = v___x_4330_;
v_bs_4316_ = v___x_4331_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4314_ = stack[0].m_num;
size_t v_i_4315_ = stack[1].m_num;
lean_object* v_bs_4316_ = stack[2].m_obj;
lean_object* v_res_4335_;
v_res_4335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4314_, v_i_4315_, v_bs_4316_);
stack->m_obj
 = v_res_4335_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4336_, lean_object* v_i_4337_, lean_object* v_bs_4338_){
_start:
{
size_t v_sz_boxed_4339_; size_t v_i_boxed_4340_; lean_object* v_res_4341_; 
v_sz_boxed_4339_ = lean_unbox_usize(v_sz_4336_);
lean_dec(v_sz_4336_);
v_i_boxed_4340_ = lean_unbox_usize(v_i_4337_);
lean_dec(v_i_4337_);
v_res_4341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4339_, v_i_boxed_4340_, v_bs_4338_);
return v_res_4341_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4342_, size_t v_i_4343_, lean_object* v_bs_4344_){
_start:
{
uint8_t v___x_4345_; 
v___x_4345_ = lean_usize_dec_lt(v_i_4343_, v_sz_4342_);
if (v___x_4345_ == 0)
{
return v_bs_4344_;
}
else
{
lean_object* v_v_4346_; lean_object* v_fst_4347_; lean_object* v_snd_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4364_; 
v_v_4346_ = lean_array_uget(v_bs_4344_, v_i_4343_);
v_fst_4347_ = lean_ctor_get(v_v_4346_, 0);
v_snd_4348_ = lean_ctor_get(v_v_4346_, 1);
v_isSharedCheck_4364_ = !lean_is_exclusive(v_v_4346_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4350_ = v_v_4346_;
v_isShared_4351_ = v_isSharedCheck_4364_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_snd_4348_);
lean_inc(v_fst_4347_);
lean_dec(v_v_4346_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4364_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4352_; lean_object* v_bs_x27_4353_; uint8_t v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4352_ = lean_unsigned_to_nat(0u);
v_bs_x27_4353_ = lean_array_uset(v_bs_4344_, v_i_4343_, v___x_4352_);
v___x_4354_ = 0;
v___x_4355_ = lean_box(v___x_4354_);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 0, v___x_4355_);
v___x_4357_ = v___x_4350_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_snd_4348_);
v___x_4357_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4358_; size_t v___x_4359_; size_t v___x_4360_; lean_object* v___x_4361_; 
v___x_4358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4358_, 0, v_fst_4347_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
v___x_4359_ = ((size_t)1ULL);
v___x_4360_ = lean_usize_add(v_i_4343_, v___x_4359_);
v___x_4361_ = lean_array_uset(v_bs_x27_4353_, v_i_4343_, v___x_4358_);
v_i_4343_ = v___x_4360_;
v_bs_4344_ = v___x_4361_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4342_ = stack[0].m_num;
size_t v_i_4343_ = stack[1].m_num;
lean_object* v_bs_4344_ = stack[2].m_obj;
lean_object* v_res_4365_;
v_res_4365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4342_, v_i_4343_, v_bs_4344_);
stack->m_obj
 = v_res_4365_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4366_, lean_object* v_i_4367_, lean_object* v_bs_4368_){
_start:
{
size_t v_sz_boxed_4369_; size_t v_i_boxed_4370_; lean_object* v_res_4371_; 
v_sz_boxed_4369_ = lean_unbox_usize(v_sz_4366_);
lean_dec(v_sz_4366_);
v_i_boxed_4370_ = lean_unbox_usize(v_i_4367_);
lean_dec(v_i_4367_);
v_res_4371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4369_, v_i_boxed_4370_, v_bs_4368_);
return v_res_4371_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4372_, lean_object* v___x_4373_, lean_object* v_a_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v___x_20547__overap_4380_; lean_object* v___x_4381_; 
v___x_20547__overap_4380_ = l_instInhabitedOfMonad___redArg(v___x_4372_, v___x_4373_);
lean_inc(v___y_4378_);
lean_inc_ref(v___y_4377_);
lean_inc(v___y_4376_);
lean_inc_ref(v___y_4375_);
v___x_4381_ = lean_apply_5(v___x_20547__overap_4380_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, lean_box(0));
return v___x_4381_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4372_ = stack[0].m_obj;
lean_object* v___x_4373_ = stack[1].m_obj;
lean_object* v_a_4374_ = stack[2].m_obj;
lean_object* v___y_4375_ = stack[3].m_obj;
lean_object* v___y_4376_ = stack[4].m_obj;
lean_object* v___y_4377_ = stack[5].m_obj;
lean_object* v___y_4378_ = stack[6].m_obj;
lean_object* v_res_4382_;
v_res_4382_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4372_, v___x_4373_, v_a_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
stack->m_obj
 = v_res_4382_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4383_, lean_object* v___x_4384_, lean_object* v_a_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4383_, v___x_4384_, v_a_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec_ref(v_a_4385_);
return v_res_4391_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_instMonadEIO___redArg();
return v___x_4392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4394_ = l_StateRefT_x27_instMonad___redArg(v___x_4393_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4399_, lean_object* v_declInfos_4400_, lean_object* v_k_4401_, lean_object* v_kind_4402_, lean_object* v_x_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
uint8_t v_kind_boxed_4409_; lean_object* v_res_4410_; 
v_kind_boxed_4409_ = lean_unbox(v_kind_4402_);
v_res_4410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4399_, v_declInfos_4400_, v_k_4401_, v_kind_boxed_4409_, v_x_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
return v_res_4410_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4411_, lean_object* v_k_4412_, uint8_t v_kind_4413_, lean_object* v_acc_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; lean_object* v_toApplicative_4421_; lean_object* v_toFunctor_4422_; lean_object* v_toSeq_4423_; lean_object* v_toSeqLeft_4424_; lean_object* v_toSeqRight_4425_; lean_object* v___f_4426_; lean_object* v___f_4427_; lean_object* v___f_4428_; lean_object* v___f_4429_; lean_object* v___x_4430_; lean_object* v___f_4431_; lean_object* v___f_4432_; lean_object* v___f_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v_toApplicative_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4487_; 
v___x_4420_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4421_ = lean_ctor_get(v___x_4420_, 0);
v_toFunctor_4422_ = lean_ctor_get(v_toApplicative_4421_, 0);
v_toSeq_4423_ = lean_ctor_get(v_toApplicative_4421_, 2);
v_toSeqLeft_4424_ = lean_ctor_get(v_toApplicative_4421_, 3);
v_toSeqRight_4425_ = lean_ctor_get(v_toApplicative_4421_, 4);
v___f_4426_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4427_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4422_, 2);
v___f_4428_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4428_, 0, v_toFunctor_4422_);
v___f_4429_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4429_, 0, v_toFunctor_4422_);
v___x_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___f_4428_);
lean_ctor_set(v___x_4430_, 1, v___f_4429_);
lean_inc(v_toSeqRight_4425_);
v___f_4431_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4431_, 0, v_toSeqRight_4425_);
lean_inc(v_toSeqLeft_4424_);
v___f_4432_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4432_, 0, v_toSeqLeft_4424_);
lean_inc(v_toSeq_4423_);
v___f_4433_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4433_, 0, v_toSeq_4423_);
v___x_4434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4430_);
lean_ctor_set(v___x_4434_, 1, v___f_4426_);
lean_ctor_set(v___x_4434_, 2, v___f_4433_);
lean_ctor_set(v___x_4434_, 3, v___f_4432_);
lean_ctor_set(v___x_4434_, 4, v___f_4431_);
v___x_4435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
lean_ctor_set(v___x_4435_, 1, v___f_4427_);
v___x_4436_ = l_StateRefT_x27_instMonad___redArg(v___x_4435_);
v_toApplicative_4437_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4487_ == 0)
{
lean_object* v_unused_4488_; 
v_unused_4488_ = lean_ctor_get(v___x_4436_, 1);
lean_dec(v_unused_4488_);
v___x_4439_ = v___x_4436_;
v_isShared_4440_ = v_isSharedCheck_4487_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_toApplicative_4437_);
lean_dec(v___x_4436_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4487_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v_toFunctor_4441_; lean_object* v_toSeq_4442_; lean_object* v_toSeqLeft_4443_; lean_object* v_toSeqRight_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4485_; 
v_toFunctor_4441_ = lean_ctor_get(v_toApplicative_4437_, 0);
v_toSeq_4442_ = lean_ctor_get(v_toApplicative_4437_, 2);
v_toSeqLeft_4443_ = lean_ctor_get(v_toApplicative_4437_, 3);
v_toSeqRight_4444_ = lean_ctor_get(v_toApplicative_4437_, 4);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_toApplicative_4437_);
if (v_isSharedCheck_4485_ == 0)
{
lean_object* v_unused_4486_; 
v_unused_4486_ = lean_ctor_get(v_toApplicative_4437_, 1);
lean_dec(v_unused_4486_);
v___x_4446_ = v_toApplicative_4437_;
v_isShared_4447_ = v_isSharedCheck_4485_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_toSeqRight_4444_);
lean_inc(v_toSeqLeft_4443_);
lean_inc(v_toSeq_4442_);
lean_inc(v_toFunctor_4441_);
lean_dec(v_toApplicative_4437_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4485_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___f_4448_; lean_object* v___f_4449_; lean_object* v___f_4450_; lean_object* v___f_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___f_4454_; lean_object* v___f_4455_; lean_object* v___x_4457_; 
v___f_4448_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4449_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4441_);
v___f_4450_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4450_, 0, v_toFunctor_4441_);
v___f_4451_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4451_, 0, v_toFunctor_4441_);
v___x_4452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___f_4450_);
lean_ctor_set(v___x_4452_, 1, v___f_4451_);
v___f_4453_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4453_, 0, v_toSeqRight_4444_);
v___f_4454_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4454_, 0, v_toSeqLeft_4443_);
v___f_4455_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4455_, 0, v_toSeq_4442_);
if (v_isShared_4447_ == 0)
{
lean_ctor_set(v___x_4446_, 4, v___f_4453_);
lean_ctor_set(v___x_4446_, 3, v___f_4454_);
lean_ctor_set(v___x_4446_, 2, v___f_4455_);
lean_ctor_set(v___x_4446_, 1, v___f_4448_);
lean_ctor_set(v___x_4446_, 0, v___x_4452_);
v___x_4457_ = v___x_4446_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4452_);
lean_ctor_set(v_reuseFailAlloc_4484_, 1, v___f_4448_);
lean_ctor_set(v_reuseFailAlloc_4484_, 2, v___f_4455_);
lean_ctor_set(v_reuseFailAlloc_4484_, 3, v___f_4454_);
lean_ctor_set(v_reuseFailAlloc_4484_, 4, v___f_4453_);
v___x_4457_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4459_; 
if (v_isShared_4440_ == 0)
{
lean_ctor_set(v___x_4439_, 1, v___f_4449_);
lean_ctor_set(v___x_4439_, 0, v___x_4457_);
v___x_4459_ = v___x_4439_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4457_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v___f_4449_);
v___x_4459_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; uint8_t v___x_4462_; 
v___x_4460_ = lean_array_get_size(v_acc_4414_);
v___x_4461_ = lean_array_get_size(v_declInfos_4411_);
v___x_4462_ = lean_nat_dec_lt(v___x_4460_, v___x_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; 
lean_dec_ref(v___x_4459_);
lean_dec_ref(v_declInfos_4411_);
lean_inc(v___y_4418_);
lean_inc_ref(v___y_4417_);
lean_inc(v___y_4416_);
lean_inc_ref(v___y_4415_);
v___x_4463_ = lean_apply_6(v_k_4412_, v_acc_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, lean_box(0));
return v___x_4463_;
}
else
{
lean_object* v___x_4464_; uint8_t v___x_4465_; lean_object* v___x_4466_; lean_object* v___f_4467_; lean_object* v___f_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v_snd_4473_; lean_object* v_fst_4474_; lean_object* v_fst_4475_; lean_object* v_snd_4476_; lean_object* v___x_4477_; lean_object* v___f_4478_; lean_object* v___x_4479_; 
v___x_4464_ = lean_box(0);
v___x_4465_ = 0;
v___x_4466_ = l_Lean_instInhabitedExpr;
v___f_4467_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4467_, 0, v___x_4459_);
lean_closure_set(v___f_4467_, 1, v___x_4466_);
v___f_4468_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4468_, 0, v___f_4467_);
v___x_4469_ = lean_box(v___x_4465_);
v___x_4470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
lean_ctor_set(v___x_4470_, 1, v___f_4468_);
v___x_4471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4464_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
v___x_4472_ = lean_array_get(v___x_4471_, v_declInfos_4411_, v___x_4460_);
lean_dec_ref_known(v___x_4471_, 2);
v_snd_4473_ = lean_ctor_get(v___x_4472_, 1);
lean_inc(v_snd_4473_);
v_fst_4474_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_fst_4474_);
lean_dec(v___x_4472_);
v_fst_4475_ = lean_ctor_get(v_snd_4473_, 0);
lean_inc(v_fst_4475_);
v_snd_4476_ = lean_ctor_get(v_snd_4473_, 1);
lean_inc(v_snd_4476_);
lean_dec(v_snd_4473_);
v___x_4477_ = lean_box(v_kind_4413_);
lean_inc_ref(v_acc_4414_);
v___f_4478_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4478_, 0, v_acc_4414_);
lean_closure_set(v___f_4478_, 1, v_declInfos_4411_);
lean_closure_set(v___f_4478_, 2, v_k_4412_);
lean_closure_set(v___f_4478_, 3, v___x_4477_);
lean_inc(v___y_4418_);
lean_inc_ref(v___y_4417_);
lean_inc(v___y_4416_);
lean_inc_ref(v___y_4415_);
v___x_4479_ = lean_apply_6(v_snd_4476_, v_acc_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, lean_box(0));
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; uint8_t v___x_4481_; lean_object* v___x_4482_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref_known(v___x_4479_, 1);
v___x_4481_ = lean_unbox(v_fst_4475_);
lean_dec(v_fst_4475_);
v___x_4482_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4474_, v___x_4481_, v_a_4480_, v___f_4478_, v_kind_4413_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
return v___x_4482_;
}
else
{
lean_dec_ref(v___f_4478_);
lean_dec(v_fst_4475_);
lean_dec(v_fst_4474_);
return v___x_4479_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_4411_ = stack[0].m_obj;
lean_object* v_k_4412_ = stack[1].m_obj;
uint8_t v_kind_4413_ = stack[2].m_num;
lean_object* v_acc_4414_ = stack[3].m_obj;
lean_object* v___y_4415_ = stack[4].m_obj;
lean_object* v___y_4416_ = stack[5].m_obj;
lean_object* v___y_4417_ = stack[6].m_obj;
lean_object* v___y_4418_ = stack[7].m_obj;
lean_object* v_res_4489_;
v_res_4489_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4411_, v_k_4412_, v_kind_4413_, v_acc_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
stack->m_obj
 = v_res_4489_;
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4490_, lean_object* v_declInfos_4491_, lean_object* v_k_4492_, uint8_t v_kind_4493_, lean_object* v_x_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4500_ = lean_array_push(v_acc_4490_, v_x_4494_);
v___x_4501_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4491_, v_k_4492_, v_kind_4493_, v___x_4500_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4501_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_4490_ = stack[0].m_obj;
lean_object* v_declInfos_4491_ = stack[1].m_obj;
lean_object* v_k_4492_ = stack[2].m_obj;
uint8_t v_kind_4493_ = stack[3].m_num;
lean_object* v_x_4494_ = stack[4].m_obj;
lean_object* v___y_4495_ = stack[5].m_obj;
lean_object* v___y_4496_ = stack[6].m_obj;
lean_object* v___y_4497_ = stack[7].m_obj;
lean_object* v___y_4498_ = stack[8].m_obj;
lean_object* v_res_4502_;
v_res_4502_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4490_, v_declInfos_4491_, v_k_4492_, v_kind_4493_, v_x_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
stack->m_obj
 = v_res_4502_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4503_, lean_object* v_k_4504_, lean_object* v_kind_4505_, lean_object* v_acc_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
uint8_t v_kind_boxed_4512_; lean_object* v_res_4513_; 
v_kind_boxed_4512_ = lean_unbox(v_kind_4505_);
v_res_4513_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4503_, v_k_4504_, v_kind_boxed_4512_, v_acc_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
return v_res_4513_;
}
}
lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4514_, lean_object* v_k_4515_, uint8_t v_kind_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4522_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4523_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4514_, v_k_4515_, v_kind_4516_, v___x_4522_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
return v___x_4523_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_4514_ = stack[0].m_obj;
lean_object* v_k_4515_ = stack[1].m_obj;
uint8_t v_kind_4516_ = stack[2].m_num;
lean_object* v___y_4517_ = stack[3].m_obj;
lean_object* v___y_4518_ = stack[4].m_obj;
lean_object* v___y_4519_ = stack[5].m_obj;
lean_object* v___y_4520_ = stack[6].m_obj;
lean_object* v_res_4524_;
v_res_4524_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4514_, v_k_4515_, v_kind_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
stack->m_obj
 = v_res_4524_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4525_, lean_object* v_k_4526_, lean_object* v_kind_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
uint8_t v_kind_boxed_4533_; lean_object* v_res_4534_; 
v_kind_boxed_4533_ = lean_unbox(v_kind_4527_);
v_res_4534_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4525_, v_k_4526_, v_kind_boxed_4533_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
return v_res_4534_;
}
}
lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4535_, lean_object* v_k_4536_, uint8_t v_kind_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
size_t v_sz_4543_; size_t v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; 
v_sz_4543_ = lean_array_size(v_declInfos_4535_);
v___x_4544_ = ((size_t)0ULL);
v___x_4545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4543_, v___x_4544_, v_declInfos_4535_);
v___x_4546_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4545_, v_k_4536_, v_kind_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
return v___x_4546_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_4535_ = stack[0].m_obj;
lean_object* v_k_4536_ = stack[1].m_obj;
uint8_t v_kind_4537_ = stack[2].m_num;
lean_object* v___y_4538_ = stack[3].m_obj;
lean_object* v___y_4539_ = stack[4].m_obj;
lean_object* v___y_4540_ = stack[5].m_obj;
lean_object* v___y_4541_ = stack[6].m_obj;
lean_object* v_res_4547_;
v_res_4547_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4535_, v_k_4536_, v_kind_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
stack->m_obj
 = v_res_4547_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4548_, lean_object* v_k_4549_, lean_object* v_kind_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_){
_start:
{
uint8_t v_kind_boxed_4556_; lean_object* v_res_4557_; 
v_kind_boxed_4556_ = lean_unbox(v_kind_4550_);
v_res_4557_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4548_, v_k_4549_, v_kind_boxed_4556_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
return v_res_4557_;
}
}
lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4558_, lean_object* v_k_4559_, uint8_t v_kind_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
size_t v_sz_4566_; size_t v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v_sz_4566_ = lean_array_size(v_declInfos_4558_);
v___x_4567_ = ((size_t)0ULL);
v___x_4568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4566_, v___x_4567_, v_declInfos_4558_);
v___x_4569_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4568_, v_k_4559_, v_kind_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
return v___x_4569_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_4558_ = stack[0].m_obj;
lean_object* v_k_4559_ = stack[1].m_obj;
uint8_t v_kind_4560_ = stack[2].m_num;
lean_object* v___y_4561_ = stack[3].m_obj;
lean_object* v___y_4562_ = stack[4].m_obj;
lean_object* v___y_4563_ = stack[5].m_obj;
lean_object* v___y_4564_ = stack[6].m_obj;
lean_object* v_res_4570_;
v_res_4570_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4558_, v_k_4559_, v_kind_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
stack->m_obj
 = v_res_4570_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4571_, lean_object* v_k_4572_, lean_object* v_kind_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v_kind_boxed_4579_; lean_object* v_res_4580_; 
v_kind_boxed_4579_ = lean_unbox(v_kind_4573_);
v_res_4580_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4571_, v_k_4572_, v_kind_boxed_4579_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
return v_res_4580_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(lean_object* v_a_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_array_4591_; lean_object* v_start_4592_; lean_object* v_stop_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4651_; 
v_array_4591_ = lean_ctor_get(v_a_4584_, 0);
v_start_4592_ = lean_ctor_get(v_a_4584_, 1);
v_stop_4593_ = lean_ctor_get(v_a_4584_, 2);
v_isSharedCheck_4651_ = !lean_is_exclusive(v_a_4584_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4595_ = v_a_4584_;
v_isShared_4596_ = v_isSharedCheck_4651_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_stop_4593_);
lean_inc(v_start_4592_);
lean_inc(v_array_4591_);
lean_dec(v_a_4584_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4651_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
uint8_t v___x_4597_; 
v___x_4597_ = lean_nat_dec_lt(v_start_4592_, v_stop_4593_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; 
lean_del_object(v___x_4595_);
lean_dec(v_stop_4593_);
lean_dec(v_start_4592_);
lean_dec_ref(v_array_4591_);
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v_b_4585_);
return v___x_4598_;
}
else
{
lean_object* v_snd_4599_; lean_object* v_fst_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4650_; 
v_snd_4599_ = lean_ctor_get(v_b_4585_, 1);
v_fst_4600_ = lean_ctor_get(v_b_4585_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v_b_4585_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4602_ = v_b_4585_;
v_isShared_4603_ = v_isSharedCheck_4650_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_snd_4599_);
lean_inc(v_fst_4600_);
lean_dec(v_b_4585_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4650_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v_array_4604_; lean_object* v_start_4605_; lean_object* v_stop_4606_; uint8_t v___x_4607_; 
v_array_4604_ = lean_ctor_get(v_snd_4599_, 0);
v_start_4605_ = lean_ctor_get(v_snd_4599_, 1);
v_stop_4606_ = lean_ctor_get(v_snd_4599_, 2);
v___x_4607_ = lean_nat_dec_lt(v_start_4605_, v_stop_4606_);
if (v___x_4607_ == 0)
{
lean_object* v___x_4609_; 
lean_del_object(v___x_4595_);
lean_dec(v_stop_4593_);
lean_dec(v_start_4592_);
lean_dec_ref(v_array_4591_);
if (v_isShared_4603_ == 0)
{
v___x_4609_ = v___x_4602_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_fst_4600_);
lean_ctor_set(v_reuseFailAlloc_4611_, 1, v_snd_4599_);
v___x_4609_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4610_; 
v___x_4610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4609_);
return v___x_4610_;
}
}
else
{
lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4646_; 
lean_inc(v_stop_4606_);
lean_inc(v_start_4605_);
lean_inc_ref(v_array_4604_);
v_isSharedCheck_4646_ = !lean_is_exclusive(v_snd_4599_);
if (v_isSharedCheck_4646_ == 0)
{
lean_object* v_unused_4647_; lean_object* v_unused_4648_; lean_object* v_unused_4649_; 
v_unused_4647_ = lean_ctor_get(v_snd_4599_, 2);
lean_dec(v_unused_4647_);
v_unused_4648_ = lean_ctor_get(v_snd_4599_, 1);
lean_dec(v_unused_4648_);
v_unused_4649_ = lean_ctor_get(v_snd_4599_, 0);
lean_dec(v_unused_4649_);
v___x_4613_ = v_snd_4599_;
v_isShared_4614_ = v_isSharedCheck_4646_;
goto v_resetjp_4612_;
}
else
{
lean_dec(v_snd_4599_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4646_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4618_; 
v___x_4615_ = lean_unsigned_to_nat(1u);
v___x_4616_ = lean_nat_add(v_start_4592_, v___x_4615_);
lean_inc_ref(v_array_4591_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 2, v_stop_4593_);
lean_ctor_set(v___x_4613_, 1, v___x_4616_);
lean_ctor_set(v___x_4613_, 0, v_array_4591_);
v___x_4618_ = v___x_4613_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_array_4591_);
lean_ctor_set(v_reuseFailAlloc_4645_, 1, v___x_4616_);
lean_ctor_set(v_reuseFailAlloc_4645_, 2, v_stop_4593_);
v___x_4618_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4619_ = lean_array_fget(v_array_4591_, v_start_4592_);
lean_dec(v_start_4592_);
lean_dec_ref(v_array_4591_);
v___x_4620_ = lean_array_fget(v_array_4604_, v_start_4605_);
v___x_4621_ = lean_nat_add(v_start_4605_, v___x_4615_);
lean_dec(v_start_4605_);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 2, v_stop_4606_);
lean_ctor_set(v___x_4595_, 1, v___x_4621_);
lean_ctor_set(v___x_4595_, 0, v_array_4604_);
v___x_4623_ = v___x_4595_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_array_4604_);
lean_ctor_set(v_reuseFailAlloc_4644_, 1, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4644_, 2, v_stop_4606_);
v___x_4623_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4624_; 
v___x_4624_ = l_Lean_Meta_mkEqHEq(v___x_4619_, v___x_4620_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4631_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4625_);
lean_dec_ref_known(v___x_4624_, 1);
v___x_4626_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__1));
v___x_4627_ = lean_array_get_size(v_fst_4600_);
v___x_4628_ = lean_nat_add(v___x_4627_, v___x_4615_);
v___x_4629_ = lean_name_append_index_after(v___x_4626_, v___x_4628_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 1, v_a_4625_);
lean_ctor_set(v___x_4602_, 0, v___x_4629_);
v___x_4631_ = v___x_4602_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4635_, 1, v_a_4625_);
v___x_4631_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = lean_array_push(v_fst_4600_, v___x_4631_);
v___x_4633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4632_);
lean_ctor_set(v___x_4633_, 1, v___x_4623_);
v_a_4584_ = v___x_4618_;
v_b_4585_ = v___x_4633_;
goto _start;
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec_ref(v___x_4623_);
lean_dec_ref(v___x_4618_);
lean_del_object(v___x_4602_);
lean_dec(v_fst_4600_);
v_a_4636_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4624_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4624_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
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
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4584_ = stack[0].m_obj;
lean_object* v_b_4585_ = stack[1].m_obj;
lean_object* v___y_4586_ = stack[2].m_obj;
lean_object* v___y_4587_ = stack[3].m_obj;
lean_object* v___y_4588_ = stack[4].m_obj;
lean_object* v___y_4589_ = stack[5].m_obj;
lean_object* v_res_4652_;
v_res_4652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_4584_, v_b_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
stack->m_obj
 = v_res_4652_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___boxed(lean_object* v_a_4653_, lean_object* v_b_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
lean_object* v_res_4660_; 
v_res_4660_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_4653_, v_b_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
return v_res_4660_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v___x_4661_, lean_object* v_a_4662_, lean_object* v___x_4663_, lean_object* v_as_4664_, size_t v_sz_4665_, size_t v_i_4666_, lean_object* v_b_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_a_4674_; uint8_t v___x_4678_; 
v___x_4678_ = lean_usize_dec_lt(v_i_4666_, v_sz_4665_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4679_; 
lean_dec(v___x_4663_);
v___x_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4679_, 0, v_b_4667_);
return v___x_4679_;
}
else
{
lean_object* v___x_4680_; lean_object* v_a_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4680_ = l_Lean_instInhabitedExpr;
v_a_4681_ = lean_array_uget_borrowed(v_as_4664_, v_i_4666_);
v___x_4682_ = lean_array_get_borrowed(v___x_4680_, v___x_4661_, v_a_4681_);
lean_inc(v___x_4682_);
v___x_4683_ = l_Lean_Meta_instantiateForall(v___x_4682_, v_a_4662_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4685_; 
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc(v_a_4684_);
lean_dec_ref_known(v___x_4683_, 1);
lean_inc(v___x_4663_);
v___x_4685_ = l_Lean_Meta_Match_simpH_x3f(v_a_4684_, v___x_4663_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
if (lean_obj_tag(v___x_4685_) == 0)
{
lean_object* v_a_4686_; 
v_a_4686_ = lean_ctor_get(v___x_4685_, 0);
lean_inc(v_a_4686_);
lean_dec_ref_known(v___x_4685_, 1);
if (lean_obj_tag(v_a_4686_) == 1)
{
lean_object* v_val_4687_; lean_object* v___x_4688_; 
v_val_4687_ = lean_ctor_get(v_a_4686_, 0);
lean_inc(v_val_4687_);
lean_dec_ref_known(v_a_4686_, 1);
v___x_4688_ = lean_array_push(v_b_4667_, v_val_4687_);
v_a_4674_ = v___x_4688_;
goto v___jp_4673_;
}
else
{
lean_dec(v_a_4686_);
v_a_4674_ = v_b_4667_;
goto v___jp_4673_;
}
}
else
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
lean_dec_ref(v_b_4667_);
lean_dec(v___x_4663_);
v_a_4689_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4691_ = v___x_4685_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4685_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_a_4689_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec_ref(v_b_4667_);
lean_dec(v___x_4663_);
v_a_4697_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4683_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4683_);
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
v___jp_4673_:
{
size_t v___x_4675_; size_t v___x_4676_; 
v___x_4675_ = ((size_t)1ULL);
v___x_4676_ = lean_usize_add(v_i_4666_, v___x_4675_);
v_i_4666_ = v___x_4676_;
v_b_4667_ = v_a_4674_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4661_ = stack[0].m_obj;
lean_object* v_a_4662_ = stack[1].m_obj;
lean_object* v___x_4663_ = stack[2].m_obj;
lean_object* v_as_4664_ = stack[3].m_obj;
size_t v_sz_4665_ = stack[4].m_num;
size_t v_i_4666_ = stack[5].m_num;
lean_object* v_b_4667_ = stack[6].m_obj;
lean_object* v___y_4668_ = stack[7].m_obj;
lean_object* v___y_4669_ = stack[8].m_obj;
lean_object* v___y_4670_ = stack[9].m_obj;
lean_object* v___y_4671_ = stack[10].m_obj;
lean_object* v_res_4705_;
v_res_4705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4661_, v_a_4662_, v___x_4663_, v_as_4664_, v_sz_4665_, v_i_4666_, v_b_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
stack->m_obj
 = v_res_4705_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v___x_4706_, lean_object* v_a_4707_, lean_object* v___x_4708_, lean_object* v_as_4709_, lean_object* v_sz_4710_, lean_object* v_i_4711_, lean_object* v_b_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
size_t v_sz_boxed_4718_; size_t v_i_boxed_4719_; lean_object* v_res_4720_; 
v_sz_boxed_4718_ = lean_unbox_usize(v_sz_4710_);
lean_dec(v_sz_4710_);
v_i_boxed_4719_ = lean_unbox_usize(v_i_4711_);
lean_dec(v_i_4711_);
v_res_4720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4706_, v_a_4707_, v___x_4708_, v_as_4709_, v_sz_boxed_4718_, v_i_boxed_4719_, v_b_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec_ref(v_as_4709_);
lean_dec_ref(v_a_4707_);
lean_dec_ref(v___x_4706_);
return v_res_4720_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4721_, lean_object* v_args_4722_, lean_object* v___x_4723_, lean_object* v_overlaps_4724_, lean_object* v_a_4725_, lean_object* v_fst_4726_, lean_object* v_a_4727_, lean_object* v___x_4728_, lean_object* v___x_4729_, lean_object* v___x_4730_, lean_object* v___x_4731_, lean_object* v_altVars_4732_, uint8_t v___x_4733_, uint8_t v___x_4734_, lean_object* v_a_4735_, lean_object* v___x_4736_, lean_object* v___x_4737_, lean_object* v___x_4738_, lean_object* v___x_4739_, lean_object* v___x_4740_, lean_object* v___x_4741_, lean_object* v___x_4742_, lean_object* v_matchDeclName_4743_, lean_object* v___x_4744_, lean_object* v___x_4745_, lean_object* v___x_4746_, lean_object* v_heqs_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = l_Lean_mkAppN(v___y_4721_, v_args_4722_);
lean_inc_ref(v_heqs_4747_);
v___x_4754_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4753_, v_heqs_4747_, v___x_4723_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; lean_object* v___x_4756_; size_t v_sz_4757_; size_t v___x_4758_; lean_object* v___x_4759_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
lean_inc(v_a_4755_);
lean_dec_ref_known(v___x_4754_, 1);
v___x_4756_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4724_, v_a_4725_);
v_sz_4757_ = lean_array_size(v___x_4756_);
v___x_4758_ = ((size_t)0ULL);
lean_inc_ref(v___x_4729_);
v___x_4759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_fst_4726_, v_a_4727_, v___x_4728_, v___x_4756_, v_sz_4757_, v___x_4758_, v___x_4729_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec_ref(v___x_4756_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v___y_4762_; lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v___y_4765_; lean_object* v_toCold_4872_; lean_object* v_options_4873_; uint8_t v_hasTrace_4874_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_a_4760_);
lean_dec_ref_known(v___x_4759_, 1);
v_toCold_4872_ = lean_ctor_get(v___y_4750_, 0);
v_options_4873_ = lean_ctor_get(v_toCold_4872_, 2);
v_hasTrace_4874_ = lean_ctor_get_uint8(v_options_4873_, sizeof(void*)*1);
if (v_hasTrace_4874_ == 0)
{
v___y_4762_ = v___y_4748_;
v___y_4763_ = v___y_4749_;
v___y_4764_ = v___y_4750_;
v___y_4765_ = v___y_4751_;
goto v___jp_4761_;
}
else
{
lean_object* v_inheritedTraceOptions_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; uint8_t v___x_4878_; 
v_inheritedTraceOptions_4875_ = lean_ctor_get(v_toCold_4872_, 11);
v___x_4876_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4877_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4878_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4875_, v_options_4873_, v___x_4877_);
if (v___x_4878_ == 0)
{
v___y_4762_ = v___y_4748_;
v___y_4763_ = v___y_4749_;
v___y_4764_ = v___y_4750_;
v___y_4765_ = v___y_4751_;
goto v___jp_4761_;
}
else
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4879_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4760_);
v___x_4880_ = lean_array_to_list(v_a_4760_);
v___x_4881_ = lean_box(0);
v___x_4882_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4880_, v___x_4881_);
v___x_4883_ = l_Lean_MessageData_ofList(v___x_4882_);
v___x_4884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4879_);
lean_ctor_set(v___x_4884_, 1, v___x_4883_);
v___x_4885_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4876_, v___x_4884_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_dec_ref_known(v___x_4885_, 1);
v___y_4762_ = v___y_4748_;
v___y_4763_ = v___y_4749_;
v___y_4764_ = v___y_4750_;
v___y_4765_ = v___y_4751_;
goto v___jp_4761_;
}
else
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
lean_dec(v_a_4760_);
lean_dec(v_a_4755_);
lean_dec_ref(v_heqs_4747_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
lean_dec(v_matchDeclName_4743_);
lean_dec_ref(v___x_4740_);
lean_dec_ref(v___x_4739_);
lean_dec_ref(v___x_4737_);
lean_dec(v___x_4736_);
lean_dec_ref(v___x_4731_);
lean_dec(v___x_4730_);
lean_dec_ref(v___x_4729_);
lean_dec_ref(v_a_4727_);
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4888_ = v___x_4885_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4885_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4886_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
}
v___jp_4761_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; size_t v_sz_4773_; lean_object* v___x_4774_; 
v___x_4766_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4767_ = l_Array_reverse___redArg(v_a_4727_);
v___x_4768_ = lean_array_get_size(v___x_4767_);
v___x_4769_ = l_Array_toSubarray___redArg(v___x_4767_, v___x_4730_, v___x_4768_);
lean_inc_ref(v___x_4731_);
v___x_4770_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4731_, v___x_4729_);
v___x_4771_ = l_Array_reverse___redArg(v___x_4770_);
v___x_4772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4766_);
lean_ctor_set(v___x_4772_, 1, v___x_4769_);
v_sz_4773_ = lean_array_size(v___x_4771_);
v___x_4774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4771_, v_sz_4773_, v___x_4758_, v___x_4772_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec_ref(v___x_4771_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_object* v_a_4775_; lean_object* v_fst_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4862_; 
v_a_4775_ = lean_ctor_get(v___x_4774_, 0);
lean_inc(v_a_4775_);
lean_dec_ref_known(v___x_4774_, 1);
v_fst_4776_ = lean_ctor_get(v_a_4775_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v_a_4775_);
if (v_isSharedCheck_4862_ == 0)
{
lean_object* v_unused_4863_; 
v_unused_4863_ = lean_ctor_get(v_a_4775_, 1);
lean_dec(v_unused_4863_);
v___x_4778_ = v_a_4775_;
v_isShared_4779_ = v_isSharedCheck_4862_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_fst_4776_);
lean_dec(v_a_4775_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4862_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; lean_object* v___x_4783_; 
v___x_4780_ = l_Subarray_copy___redArg(v___x_4731_);
lean_inc_ref(v___x_4780_);
v___x_4781_ = l_Array_append___redArg(v___x_4780_, v_altVars_4732_);
v___x_4782_ = 1;
v___x_4783_ = l_Lean_Meta_mkForallFVars(v___x_4781_, v_fst_4776_, v___x_4733_, v___x_4734_, v___x_4734_, v___x_4782_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec_ref(v___x_4781_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
lean_inc(v_a_4784_);
lean_dec_ref_known(v___x_4783_, 1);
v___x_4785_ = l_Lean_ConstantInfo_name(v_a_4735_);
v___x_4786_ = l_Lean_mkConst(v___x_4785_, v___x_4736_);
lean_inc_ref(v___x_4737_);
v___x_4787_ = l_Subarray_copy___redArg(v___x_4737_);
v___x_4788_ = lean_mk_empty_array_with_capacity(v___x_4738_);
v___x_4789_ = lean_array_push(v___x_4788_, v___x_4739_);
v___x_4790_ = l_Array_append___redArg(v___x_4787_, v___x_4789_);
lean_dec_ref(v___x_4789_);
v___x_4791_ = l_Array_append___redArg(v___x_4790_, v___x_4780_);
lean_dec_ref(v___x_4780_);
v___x_4792_ = l_Subarray_copy___redArg(v___x_4740_);
v___x_4793_ = l_Array_append___redArg(v___x_4791_, v___x_4792_);
lean_dec_ref(v___x_4792_);
v___x_4794_ = l_Lean_mkAppN(v___x_4786_, v___x_4793_);
v___x_4795_ = l_Lean_Meta_mkHEq(v___x_4794_, v_a_4755_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; lean_object* v___x_4797_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4796_);
lean_dec_ref_known(v___x_4795_, 1);
v___x_4797_ = l_Lean_mkArrowN(v_a_4760_, v_a_4796_, v___y_4764_, v___y_4765_);
lean_dec(v_a_4760_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_a_4798_);
lean_dec_ref_known(v___x_4797_, 1);
v___x_4799_ = l_Array_append___redArg(v___x_4793_, v_altVars_4732_);
v___x_4800_ = l_Array_append___redArg(v___x_4799_, v_heqs_4747_);
v___x_4801_ = l_Lean_Meta_mkForallFVars(v___x_4800_, v_a_4798_, v___x_4733_, v___x_4734_, v___x_4734_, v___x_4782_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec_ref(v___x_4800_);
if (lean_obj_tag(v___x_4801_) == 0)
{
lean_object* v_a_4802_; lean_object* v___x_4803_; 
v_a_4802_ = lean_ctor_get(v___x_4801_, 0);
lean_inc(v_a_4802_);
lean_dec_ref_known(v___x_4801_, 1);
v___x_4803_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4802_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4861_; 
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4803_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4806_ = v___x_4803_;
v_isShared_4807_ = v_isSharedCheck_4861_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v___x_4803_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4861_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v_start_4808_; lean_object* v_stop_4809_; lean_object* v___x_4811_; uint8_t v_isShared_4812_; uint8_t v_isSharedCheck_4859_; 
v_start_4808_ = lean_ctor_get(v___x_4737_, 1);
v_stop_4809_ = lean_ctor_get(v___x_4737_, 2);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4859_ == 0)
{
lean_object* v_unused_4860_; 
v_unused_4860_ = lean_ctor_get(v___x_4737_, 0);
lean_dec(v_unused_4860_);
v___x_4811_ = v___x_4737_;
v_isShared_4812_ = v_isSharedCheck_4859_;
goto v_resetjp_4810_;
}
else
{
lean_inc(v_stop_4809_);
lean_inc(v_start_4808_);
lean_dec(v___x_4737_);
v___x_4811_ = lean_box(0);
v_isShared_4812_ = v_isSharedCheck_4859_;
goto v_resetjp_4810_;
}
v_resetjp_4810_:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v___x_4813_ = lean_nat_sub(v_stop_4809_, v_start_4808_);
lean_dec(v_start_4808_);
lean_dec(v_stop_4809_);
v___x_4814_ = lean_nat_add(v___x_4813_, v___x_4738_);
lean_dec(v___x_4813_);
v___x_4815_ = lean_nat_add(v___x_4814_, v___x_4741_);
lean_dec(v___x_4814_);
v___x_4816_ = lean_nat_add(v___x_4815_, v___x_4742_);
lean_dec(v___x_4815_);
v___x_4817_ = lean_array_get_size(v_altVars_4732_);
v___x_4818_ = lean_nat_add(v___x_4816_, v___x_4817_);
lean_dec(v___x_4816_);
v___x_4819_ = lean_array_get_size(v_heqs_4747_);
lean_dec_ref(v_heqs_4747_);
lean_inc(v_a_4804_);
v___x_4820_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4743_, v_a_4804_, v___x_4818_, v___x_4819_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4858_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4823_ = v___x_4820_;
v_isShared_4824_ = v_isSharedCheck_4858_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4820_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4858_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4825_; lean_object* v_env_4826_; uint8_t v___x_4827_; 
v___x_4825_ = lean_st_ref_get(v___y_4765_);
v_env_4826_ = lean_ctor_get(v___x_4825_, 0);
lean_inc_ref(v_env_4826_);
lean_dec(v___x_4825_);
lean_inc(v___x_4744_);
v___x_4827_ = l_Lean_Environment_contains(v_env_4826_, v___x_4744_, v___x_4734_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4829_; 
lean_del_object(v___x_4823_);
lean_inc(v___x_4744_);
if (v_isShared_4812_ == 0)
{
lean_ctor_set(v___x_4811_, 2, v_a_4804_);
lean_ctor_set(v___x_4811_, 1, v___x_4745_);
lean_ctor_set(v___x_4811_, 0, v___x_4744_);
v___x_4829_ = v___x_4811_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4854_, 1, v___x_4745_);
lean_ctor_set(v_reuseFailAlloc_4854_, 2, v_a_4804_);
v___x_4829_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4831_; 
if (v_isShared_4779_ == 0)
{
lean_ctor_set_tag(v___x_4778_, 1);
lean_ctor_set(v___x_4778_, 1, v___x_4746_);
lean_ctor_set(v___x_4778_, 0, v___x_4744_);
v___x_4831_ = v___x_4778_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4853_, 1, v___x_4746_);
v___x_4831_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4832_; lean_object* v___x_4834_; 
v___x_4832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4829_);
lean_ctor_set(v___x_4832_, 1, v_a_4821_);
lean_ctor_set(v___x_4832_, 2, v___x_4831_);
if (v_isShared_4807_ == 0)
{
lean_ctor_set_tag(v___x_4806_, 2);
lean_ctor_set(v___x_4806_, 0, v___x_4832_);
v___x_4834_ = v___x_4806_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4832_);
v___x_4834_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
lean_object* v___x_4835_; 
v___x_4835_ = l_Lean_addDecl(v___x_4834_, v___x_4733_, v___y_4764_, v___y_4765_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4842_ == 0)
{
lean_object* v_unused_4843_; 
v_unused_4843_ = lean_ctor_get(v___x_4835_, 0);
lean_dec(v_unused_4843_);
v___x_4837_ = v___x_4835_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_dec(v___x_4835_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
lean_ctor_set(v___x_4837_, 0, v_a_4784_);
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4784_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
else
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4851_; 
lean_dec(v_a_4784_);
v_a_4844_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4846_ = v___x_4835_;
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4835_);
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
}
}
}
else
{
lean_object* v___x_4856_; 
lean_dec(v_a_4821_);
lean_del_object(v___x_4811_);
lean_del_object(v___x_4806_);
lean_dec(v_a_4804_);
lean_del_object(v___x_4778_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
if (v_isShared_4824_ == 0)
{
lean_ctor_set(v___x_4823_, 0, v_a_4784_);
v___x_4856_ = v___x_4823_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v_a_4784_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
}
else
{
lean_del_object(v___x_4811_);
lean_del_object(v___x_4806_);
lean_dec(v_a_4804_);
lean_dec(v_a_4784_);
lean_del_object(v___x_4778_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
return v___x_4820_;
}
}
}
}
else
{
lean_dec(v_a_4784_);
lean_del_object(v___x_4778_);
lean_dec_ref(v_heqs_4747_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
lean_dec(v_matchDeclName_4743_);
lean_dec_ref(v___x_4737_);
return v___x_4803_;
}
}
else
{
lean_dec(v_a_4784_);
lean_del_object(v___x_4778_);
lean_dec_ref(v_heqs_4747_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
lean_dec(v_matchDeclName_4743_);
lean_dec_ref(v___x_4737_);
return v___x_4801_;
}
}
else
{
lean_dec_ref(v___x_4793_);
lean_dec(v_a_4784_);
lean_del_object(v___x_4778_);
lean_dec_ref(v_heqs_4747_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
lean_dec(v_matchDeclName_4743_);
lean_dec_ref(v___x_4737_);
return v___x_4797_;
}
}
else
{
lean_dec_ref(v___x_4793_);
lean_dec(v_a_4784_);
lean_del_object(v___x_4778_);
lean_dec(v_a_4760_);
lean_dec_ref(v_heqs_4747_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
lean_dec(v_matchDeclName_4743_);
lean_dec_ref(v___x_4737_);
return v___x_4795_;
}
}
else
{
lean_dec_ref(v___x_4780_);
lean_del_object(v___x_4778_);
lean_dec(v_a_4760_);
lean_dec(v_a_4755_);
lean_dec_ref(v_heqs_4747_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
lean_dec(v_matchDeclName_4743_);
lean_dec_ref(v___x_4740_);
lean_dec_ref(v___x_4739_);
lean_dec_ref(v___x_4737_);
lean_dec(v___x_4736_);
return v___x_4783_;
}
}
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4871_; 
lean_dec(v_a_4760_);
lean_dec(v_a_4755_);
lean_dec_ref(v_heqs_4747_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
lean_dec(v_matchDeclName_4743_);
lean_dec_ref(v___x_4740_);
lean_dec_ref(v___x_4739_);
lean_dec_ref(v___x_4737_);
lean_dec(v___x_4736_);
lean_dec_ref(v___x_4731_);
v_a_4864_ = lean_ctor_get(v___x_4774_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4866_ = v___x_4774_;
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4774_);
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
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4901_; 
lean_dec(v_a_4755_);
lean_dec_ref(v_heqs_4747_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
lean_dec(v_matchDeclName_4743_);
lean_dec_ref(v___x_4740_);
lean_dec_ref(v___x_4739_);
lean_dec_ref(v___x_4737_);
lean_dec(v___x_4736_);
lean_dec_ref(v___x_4731_);
lean_dec(v___x_4730_);
lean_dec_ref(v___x_4729_);
lean_dec_ref(v_a_4727_);
v_a_4894_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4896_ = v___x_4759_;
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4759_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
lean_object* v___x_4899_; 
if (v_isShared_4897_ == 0)
{
v___x_4899_ = v___x_4896_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v_a_4894_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4747_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
lean_dec(v___x_4744_);
lean_dec(v_matchDeclName_4743_);
lean_dec_ref(v___x_4740_);
lean_dec_ref(v___x_4739_);
lean_dec_ref(v___x_4737_);
lean_dec(v___x_4736_);
lean_dec_ref(v___x_4731_);
lean_dec(v___x_4730_);
lean_dec_ref(v___x_4729_);
lean_dec(v___x_4728_);
lean_dec_ref(v_a_4727_);
return v___x_4754_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4721_ = stack[0].m_obj;
lean_object* v_args_4722_ = stack[1].m_obj;
lean_object* v___x_4723_ = stack[2].m_obj;
lean_object* v_overlaps_4724_ = stack[3].m_obj;
lean_object* v_a_4725_ = stack[4].m_obj;
lean_object* v_fst_4726_ = stack[5].m_obj;
lean_object* v_a_4727_ = stack[6].m_obj;
lean_object* v___x_4728_ = stack[7].m_obj;
lean_object* v___x_4729_ = stack[8].m_obj;
lean_object* v___x_4730_ = stack[9].m_obj;
lean_object* v___x_4731_ = stack[10].m_obj;
lean_object* v_altVars_4732_ = stack[11].m_obj;
uint8_t v___x_4733_ = stack[12].m_num;
uint8_t v___x_4734_ = stack[13].m_num;
lean_object* v_a_4735_ = stack[14].m_obj;
lean_object* v___x_4736_ = stack[15].m_obj;
lean_object* v___x_4737_ = stack[16].m_obj;
lean_object* v___x_4738_ = stack[17].m_obj;
lean_object* v___x_4739_ = stack[18].m_obj;
lean_object* v___x_4740_ = stack[19].m_obj;
lean_object* v___x_4741_ = stack[20].m_obj;
lean_object* v___x_4742_ = stack[21].m_obj;
lean_object* v_matchDeclName_4743_ = stack[22].m_obj;
lean_object* v___x_4744_ = stack[23].m_obj;
lean_object* v___x_4745_ = stack[24].m_obj;
lean_object* v___x_4746_ = stack[25].m_obj;
lean_object* v_heqs_4747_ = stack[26].m_obj;
lean_object* v___y_4748_ = stack[27].m_obj;
lean_object* v___y_4749_ = stack[28].m_obj;
lean_object* v___y_4750_ = stack[29].m_obj;
lean_object* v___y_4751_ = stack[30].m_obj;
lean_object* v_res_4902_;
v_res_4902_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4721_, v_args_4722_, v___x_4723_, v_overlaps_4724_, v_a_4725_, v_fst_4726_, v_a_4727_, v___x_4728_, v___x_4729_, v___x_4730_, v___x_4731_, v_altVars_4732_, v___x_4733_, v___x_4734_, v_a_4735_, v___x_4736_, v___x_4737_, v___x_4738_, v___x_4739_, v___x_4740_, v___x_4741_, v___x_4742_, v_matchDeclName_4743_, v___x_4744_, v___x_4745_, v___x_4746_, v_heqs_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
stack->m_obj
 = v_res_4902_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4903_ = _args[0];
lean_object* v_args_4904_ = _args[1];
lean_object* v___x_4905_ = _args[2];
lean_object* v_overlaps_4906_ = _args[3];
lean_object* v_a_4907_ = _args[4];
lean_object* v_fst_4908_ = _args[5];
lean_object* v_a_4909_ = _args[6];
lean_object* v___x_4910_ = _args[7];
lean_object* v___x_4911_ = _args[8];
lean_object* v___x_4912_ = _args[9];
lean_object* v___x_4913_ = _args[10];
lean_object* v_altVars_4914_ = _args[11];
lean_object* v___x_4915_ = _args[12];
lean_object* v___x_4916_ = _args[13];
lean_object* v_a_4917_ = _args[14];
lean_object* v___x_4918_ = _args[15];
lean_object* v___x_4919_ = _args[16];
lean_object* v___x_4920_ = _args[17];
lean_object* v___x_4921_ = _args[18];
lean_object* v___x_4922_ = _args[19];
lean_object* v___x_4923_ = _args[20];
lean_object* v___x_4924_ = _args[21];
lean_object* v_matchDeclName_4925_ = _args[22];
lean_object* v___x_4926_ = _args[23];
lean_object* v___x_4927_ = _args[24];
lean_object* v___x_4928_ = _args[25];
lean_object* v_heqs_4929_ = _args[26];
lean_object* v___y_4930_ = _args[27];
lean_object* v___y_4931_ = _args[28];
lean_object* v___y_4932_ = _args[29];
lean_object* v___y_4933_ = _args[30];
lean_object* v___y_4934_ = _args[31];
_start:
{
uint8_t v___x_21671__boxed_4935_; uint8_t v___x_21672__boxed_4936_; lean_object* v_res_4937_; 
v___x_21671__boxed_4935_ = lean_unbox(v___x_4915_);
v___x_21672__boxed_4936_ = lean_unbox(v___x_4916_);
v_res_4937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4903_, v_args_4904_, v___x_4905_, v_overlaps_4906_, v_a_4907_, v_fst_4908_, v_a_4909_, v___x_4910_, v___x_4911_, v___x_4912_, v___x_4913_, v_altVars_4914_, v___x_21671__boxed_4935_, v___x_21672__boxed_4936_, v_a_4917_, v___x_4918_, v___x_4919_, v___x_4920_, v___x_4921_, v___x_4922_, v___x_4923_, v___x_4924_, v_matchDeclName_4925_, v___x_4926_, v___x_4927_, v___x_4928_, v_heqs_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___x_4924_);
lean_dec(v___x_4923_);
lean_dec(v___x_4920_);
lean_dec_ref(v_a_4917_);
lean_dec_ref(v_altVars_4914_);
lean_dec(v_fst_4908_);
lean_dec(v_a_4907_);
lean_dec_ref(v_overlaps_4906_);
lean_dec_ref(v_args_4904_);
return v_res_4937_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4940_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4941_ = lean_unsigned_to_nat(8u);
v___x_4942_ = lean_unsigned_to_nat(295u);
v___x_4943_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4944_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4945_ = l_mkPanicMessageWithDecl(v___x_4944_, v___x_4943_, v___x_4942_, v___x_4941_, v___x_4940_);
return v___x_4945_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4946_, lean_object* v___x_4947_, lean_object* v___y_4948_, lean_object* v___x_4949_, lean_object* v_overlaps_4950_, lean_object* v_a_4951_, lean_object* v_fst_4952_, lean_object* v___x_4953_, lean_object* v___x_4954_, uint8_t v___x_4955_, lean_object* v_a_4956_, lean_object* v___x_4957_, lean_object* v___x_4958_, lean_object* v___x_4959_, lean_object* v___x_4960_, lean_object* v___x_4961_, lean_object* v___x_4962_, lean_object* v_matchDeclName_4963_, lean_object* v___x_4964_, lean_object* v___x_4965_, lean_object* v___x_4966_, lean_object* v_altVars_4967_, lean_object* v_args_4968_, lean_object* v___mask_4969_, lean_object* v_altResultType_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
uint8_t v___x_4976_; lean_object* v___x_4977_; 
v___x_4976_ = 0;
v___x_4977_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4970_, v___f_4946_, v___x_4976_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v_start_4979_; lean_object* v_stop_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; uint8_t v___x_4983_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4978_);
lean_dec_ref_known(v___x_4977_, 1);
v_start_4979_ = lean_ctor_get(v___x_4947_, 1);
v_stop_4980_ = lean_ctor_get(v___x_4947_, 2);
v___x_4981_ = lean_array_get_size(v_a_4978_);
v___x_4982_ = lean_nat_sub(v_stop_4980_, v_start_4979_);
v___x_4983_ = lean_nat_dec_eq(v___x_4981_, v___x_4982_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4984_; lean_object* v___x_4985_; 
lean_dec(v___x_4982_);
lean_dec(v_a_4978_);
lean_dec_ref(v_args_4968_);
lean_dec_ref(v_altVars_4967_);
lean_dec(v___x_4966_);
lean_dec(v___x_4965_);
lean_dec(v___x_4964_);
lean_dec(v_matchDeclName_4963_);
lean_dec(v___x_4962_);
lean_dec_ref(v___x_4961_);
lean_dec_ref(v___x_4960_);
lean_dec(v___x_4959_);
lean_dec_ref(v___x_4958_);
lean_dec(v___x_4957_);
lean_dec_ref(v_a_4956_);
lean_dec(v___x_4954_);
lean_dec_ref(v___x_4953_);
lean_dec(v_fst_4952_);
lean_dec(v_a_4951_);
lean_dec_ref(v_overlaps_4950_);
lean_dec(v___x_4949_);
lean_dec_ref(v___y_4948_);
lean_dec_ref(v___x_4947_);
v___x_4984_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4985_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v___x_4984_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
return v___x_4985_;
}
else
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___f_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4986_ = lean_box(v___x_4976_);
v___x_4987_ = lean_box(v___x_4955_);
lean_inc_ref(v___x_4947_);
lean_inc(v___x_4954_);
lean_inc(v_a_4978_);
v___f_4988_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4988_, 0, v___y_4948_);
lean_closure_set(v___f_4988_, 1, v_args_4968_);
lean_closure_set(v___f_4988_, 2, v___x_4949_);
lean_closure_set(v___f_4988_, 3, v_overlaps_4950_);
lean_closure_set(v___f_4988_, 4, v_a_4951_);
lean_closure_set(v___f_4988_, 5, v_fst_4952_);
lean_closure_set(v___f_4988_, 6, v_a_4978_);
lean_closure_set(v___f_4988_, 7, v___x_4981_);
lean_closure_set(v___f_4988_, 8, v___x_4953_);
lean_closure_set(v___f_4988_, 9, v___x_4954_);
lean_closure_set(v___f_4988_, 10, v___x_4947_);
lean_closure_set(v___f_4988_, 11, v_altVars_4967_);
lean_closure_set(v___f_4988_, 12, v___x_4986_);
lean_closure_set(v___f_4988_, 13, v___x_4987_);
lean_closure_set(v___f_4988_, 14, v_a_4956_);
lean_closure_set(v___f_4988_, 15, v___x_4957_);
lean_closure_set(v___f_4988_, 16, v___x_4958_);
lean_closure_set(v___f_4988_, 17, v___x_4959_);
lean_closure_set(v___f_4988_, 18, v___x_4960_);
lean_closure_set(v___f_4988_, 19, v___x_4961_);
lean_closure_set(v___f_4988_, 20, v___x_4982_);
lean_closure_set(v___f_4988_, 21, v___x_4962_);
lean_closure_set(v___f_4988_, 22, v_matchDeclName_4963_);
lean_closure_set(v___f_4988_, 23, v___x_4964_);
lean_closure_set(v___f_4988_, 24, v___x_4965_);
lean_closure_set(v___f_4988_, 25, v___x_4966_);
v___x_4989_ = lean_mk_empty_array_with_capacity(v___x_4954_);
v___x_4990_ = l_Array_toSubarray___redArg(v_a_4978_, v___x_4954_, v___x_4981_);
v___x_4991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4991_, 0, v___x_4989_);
lean_ctor_set(v___x_4991_, 1, v___x_4990_);
v___x_4992_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v___x_4947_, v___x_4991_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v_a_4993_; lean_object* v_fst_4994_; uint8_t v___x_4995_; lean_object* v___x_4996_; 
v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
lean_inc(v_a_4993_);
lean_dec_ref_known(v___x_4992_, 1);
v_fst_4994_ = lean_ctor_get(v_a_4993_, 0);
lean_inc(v_fst_4994_);
lean_dec(v_a_4993_);
v___x_4995_ = 0;
v___x_4996_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4994_, v___f_4988_, v___x_4995_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
return v___x_4996_;
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
lean_dec_ref(v___f_4988_);
v_a_4997_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v___x_4992_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4992_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5002_; 
if (v_isShared_5000_ == 0)
{
v___x_5002_ = v___x_4999_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
}
else
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
lean_dec_ref(v_args_4968_);
lean_dec_ref(v_altVars_4967_);
lean_dec(v___x_4966_);
lean_dec(v___x_4965_);
lean_dec(v___x_4964_);
lean_dec(v_matchDeclName_4963_);
lean_dec(v___x_4962_);
lean_dec_ref(v___x_4961_);
lean_dec_ref(v___x_4960_);
lean_dec(v___x_4959_);
lean_dec_ref(v___x_4958_);
lean_dec(v___x_4957_);
lean_dec_ref(v_a_4956_);
lean_dec(v___x_4954_);
lean_dec_ref(v___x_4953_);
lean_dec(v_fst_4952_);
lean_dec(v_a_4951_);
lean_dec_ref(v_overlaps_4950_);
lean_dec(v___x_4949_);
lean_dec_ref(v___y_4948_);
lean_dec_ref(v___x_4947_);
v_a_5005_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5007_ = v___x_4977_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_4977_);
v___x_5007_ = lean_box(0);
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
v_resetjp_5006_:
{
lean_object* v___x_5010_; 
if (v_isShared_5008_ == 0)
{
v___x_5010_ = v___x_5007_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4946_ = stack[0].m_obj;
lean_object* v___x_4947_ = stack[1].m_obj;
lean_object* v___y_4948_ = stack[2].m_obj;
lean_object* v___x_4949_ = stack[3].m_obj;
lean_object* v_overlaps_4950_ = stack[4].m_obj;
lean_object* v_a_4951_ = stack[5].m_obj;
lean_object* v_fst_4952_ = stack[6].m_obj;
lean_object* v___x_4953_ = stack[7].m_obj;
lean_object* v___x_4954_ = stack[8].m_obj;
uint8_t v___x_4955_ = stack[9].m_num;
lean_object* v_a_4956_ = stack[10].m_obj;
lean_object* v___x_4957_ = stack[11].m_obj;
lean_object* v___x_4958_ = stack[12].m_obj;
lean_object* v___x_4959_ = stack[13].m_obj;
lean_object* v___x_4960_ = stack[14].m_obj;
lean_object* v___x_4961_ = stack[15].m_obj;
lean_object* v___x_4962_ = stack[16].m_obj;
lean_object* v_matchDeclName_4963_ = stack[17].m_obj;
lean_object* v___x_4964_ = stack[18].m_obj;
lean_object* v___x_4965_ = stack[19].m_obj;
lean_object* v___x_4966_ = stack[20].m_obj;
lean_object* v_altVars_4967_ = stack[21].m_obj;
lean_object* v_args_4968_ = stack[22].m_obj;
lean_object* v___mask_4969_ = stack[23].m_obj;
lean_object* v_altResultType_4970_ = stack[24].m_obj;
lean_object* v___y_4971_ = stack[25].m_obj;
lean_object* v___y_4972_ = stack[26].m_obj;
lean_object* v___y_4973_ = stack[27].m_obj;
lean_object* v___y_4974_ = stack[28].m_obj;
lean_object* v_res_5013_;
v_res_5013_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4946_, v___x_4947_, v___y_4948_, v___x_4949_, v_overlaps_4950_, v_a_4951_, v_fst_4952_, v___x_4953_, v___x_4954_, v___x_4955_, v_a_4956_, v___x_4957_, v___x_4958_, v___x_4959_, v___x_4960_, v___x_4961_, v___x_4962_, v_matchDeclName_4963_, v___x_4964_, v___x_4965_, v___x_4966_, v_altVars_4967_, v_args_4968_, v___mask_4969_, v_altResultType_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
stack->m_obj
 = v_res_5013_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_5014_ = _args[0];
lean_object* v___x_5015_ = _args[1];
lean_object* v___y_5016_ = _args[2];
lean_object* v___x_5017_ = _args[3];
lean_object* v_overlaps_5018_ = _args[4];
lean_object* v_a_5019_ = _args[5];
lean_object* v_fst_5020_ = _args[6];
lean_object* v___x_5021_ = _args[7];
lean_object* v___x_5022_ = _args[8];
lean_object* v___x_5023_ = _args[9];
lean_object* v_a_5024_ = _args[10];
lean_object* v___x_5025_ = _args[11];
lean_object* v___x_5026_ = _args[12];
lean_object* v___x_5027_ = _args[13];
lean_object* v___x_5028_ = _args[14];
lean_object* v___x_5029_ = _args[15];
lean_object* v___x_5030_ = _args[16];
lean_object* v_matchDeclName_5031_ = _args[17];
lean_object* v___x_5032_ = _args[18];
lean_object* v___x_5033_ = _args[19];
lean_object* v___x_5034_ = _args[20];
lean_object* v_altVars_5035_ = _args[21];
lean_object* v_args_5036_ = _args[22];
lean_object* v___mask_5037_ = _args[23];
lean_object* v_altResultType_5038_ = _args[24];
lean_object* v___y_5039_ = _args[25];
lean_object* v___y_5040_ = _args[26];
lean_object* v___y_5041_ = _args[27];
lean_object* v___y_5042_ = _args[28];
lean_object* v___y_5043_ = _args[29];
_start:
{
uint8_t v___x_22247__boxed_5044_; lean_object* v_res_5045_; 
v___x_22247__boxed_5044_ = lean_unbox(v___x_5023_);
v_res_5045_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_5014_, v___x_5015_, v___y_5016_, v___x_5017_, v_overlaps_5018_, v_a_5019_, v_fst_5020_, v___x_5021_, v___x_5022_, v___x_22247__boxed_5044_, v_a_5024_, v___x_5025_, v___x_5026_, v___x_5027_, v___x_5028_, v___x_5029_, v___x_5030_, v_matchDeclName_5031_, v___x_5032_, v___x_5033_, v___x_5034_, v_altVars_5035_, v_args_5036_, v___mask_5037_, v_altResultType_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec(v___y_5040_);
lean_dec_ref(v___y_5039_);
lean_dec_ref(v___mask_5037_);
return v_res_5045_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_5047_, lean_object* v_val_5048_, lean_object* v_matchDeclName_5049_, lean_object* v___x_5050_, lean_object* v___x_5051_, lean_object* v_a_5052_, lean_object* v___x_5053_, lean_object* v___x_5054_, lean_object* v___x_5055_, lean_object* v___x_5056_, lean_object* v___x_5057_, lean_object* v___x_5058_, lean_object* v_a_5059_, lean_object* v_b_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_){
_start:
{
uint8_t v___x_5066_; 
v___x_5066_ = lean_nat_dec_lt(v_a_5059_, v_upperBound_5047_);
if (v___x_5066_ == 0)
{
lean_object* v___x_5067_; 
lean_dec(v_a_5059_);
lean_dec(v___x_5058_);
lean_dec(v___x_5057_);
lean_dec_ref(v___x_5056_);
lean_dec_ref(v___x_5055_);
lean_dec_ref(v___x_5054_);
lean_dec(v___x_5053_);
lean_dec_ref(v_a_5052_);
lean_dec(v___x_5051_);
lean_dec_ref(v___x_5050_);
lean_dec(v_matchDeclName_5049_);
lean_dec_ref(v_val_5048_);
v___x_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5067_, 0, v_b_5060_);
return v___x_5067_;
}
else
{
lean_object* v_snd_5068_; lean_object* v_fst_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5133_; 
v_snd_5068_ = lean_ctor_get(v_b_5060_, 1);
v_fst_5069_ = lean_ctor_get(v_b_5060_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v_b_5060_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5071_ = v_b_5060_;
v_isShared_5072_ = v_isSharedCheck_5133_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_snd_5068_);
lean_inc(v_fst_5069_);
lean_dec(v_b_5060_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5133_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v_fst_5073_; lean_object* v_snd_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5132_; 
v_fst_5073_ = lean_ctor_get(v_snd_5068_, 0);
v_snd_5074_ = lean_ctor_get(v_snd_5068_, 1);
v_isSharedCheck_5132_ = !lean_is_exclusive(v_snd_5068_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5076_ = v_snd_5068_;
v_isShared_5077_ = v_isSharedCheck_5132_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_snd_5074_);
lean_inc(v_fst_5073_);
lean_dec(v_snd_5068_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5132_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v_altInfos_5078_; lean_object* v_overlaps_5079_; lean_object* v_start_5080_; lean_object* v_stop_5081_; lean_object* v___f_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___y_5094_; lean_object* v___x_5127_; uint8_t v___x_5128_; 
v_altInfos_5078_ = lean_ctor_get(v_val_5048_, 2);
v_overlaps_5079_ = lean_ctor_get(v_val_5048_, 5);
v_start_5080_ = lean_ctor_get(v___x_5056_, 1);
v_stop_5081_ = lean_ctor_get(v___x_5056_, 2);
v___f_5082_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_5083_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_5084_ = lean_unsigned_to_nat(0u);
v___x_5085_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_5086_ = lean_unsigned_to_nat(1u);
v___x_5087_ = lean_box(0);
v___x_5088_ = lean_array_get_borrowed(v___x_5083_, v_altInfos_5078_, v_a_5059_);
v___x_5089_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5049_);
v___x_5090_ = l_Lean_Name_str___override(v_matchDeclName_5049_, v___x_5089_);
lean_inc(v_snd_5074_);
v___x_5091_ = lean_name_append_index_after(v___x_5090_, v_snd_5074_);
lean_inc(v___x_5091_);
v___x_5092_ = lean_array_push(v_fst_5069_, v___x_5091_);
v___x_5127_ = lean_nat_sub(v_stop_5081_, v_start_5080_);
v___x_5128_ = lean_nat_dec_lt(v_a_5059_, v___x_5127_);
lean_dec(v___x_5127_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5129_ = l_Lean_instInhabitedExpr;
v___x_5130_ = l_outOfBounds___redArg(v___x_5129_);
v___y_5094_ = v___x_5130_;
goto v___jp_5093_;
}
else
{
lean_object* v___x_5131_; 
v___x_5131_ = l_Subarray_get___redArg(v___x_5056_, v_a_5059_);
v___y_5094_ = v___x_5131_;
goto v___jp_5093_;
}
v___jp_5093_:
{
lean_object* v___x_5095_; lean_object* v___f_5096_; lean_object* v___x_5097_; 
v___x_5095_ = lean_box(v___x_5066_);
lean_inc(v___x_5058_);
lean_inc(v_matchDeclName_5049_);
lean_inc(v___x_5057_);
lean_inc_ref(v___x_5056_);
lean_inc_ref(v___x_5055_);
lean_inc_ref(v___x_5054_);
lean_inc(v___x_5053_);
lean_inc_ref(v_a_5052_);
lean_inc(v_fst_5073_);
lean_inc(v_a_5059_);
lean_inc_ref(v_overlaps_5079_);
lean_inc(v___x_5051_);
lean_inc_ref(v___y_5094_);
lean_inc_ref(v___x_5050_);
v___f_5096_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 30, 21);
lean_closure_set(v___f_5096_, 0, v___f_5082_);
lean_closure_set(v___f_5096_, 1, v___x_5050_);
lean_closure_set(v___f_5096_, 2, v___y_5094_);
lean_closure_set(v___f_5096_, 3, v___x_5051_);
lean_closure_set(v___f_5096_, 4, v_overlaps_5079_);
lean_closure_set(v___f_5096_, 5, v_a_5059_);
lean_closure_set(v___f_5096_, 6, v_fst_5073_);
lean_closure_set(v___f_5096_, 7, v___x_5085_);
lean_closure_set(v___f_5096_, 8, v___x_5084_);
lean_closure_set(v___f_5096_, 9, v___x_5095_);
lean_closure_set(v___f_5096_, 10, v_a_5052_);
lean_closure_set(v___f_5096_, 11, v___x_5053_);
lean_closure_set(v___f_5096_, 12, v___x_5054_);
lean_closure_set(v___f_5096_, 13, v___x_5086_);
lean_closure_set(v___f_5096_, 14, v___x_5055_);
lean_closure_set(v___f_5096_, 15, v___x_5056_);
lean_closure_set(v___f_5096_, 16, v___x_5057_);
lean_closure_set(v___f_5096_, 17, v_matchDeclName_5049_);
lean_closure_set(v___f_5096_, 18, v___x_5091_);
lean_closure_set(v___f_5096_, 19, v___x_5058_);
lean_closure_set(v___f_5096_, 20, v___x_5087_);
lean_inc(v___y_5064_);
lean_inc_ref(v___y_5063_);
lean_inc(v___y_5062_);
lean_inc_ref(v___y_5061_);
v___x_5097_ = lean_infer_type(v___y_5094_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v_a_5098_; lean_object* v___x_5099_; 
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v___x_5097_, 1);
lean_inc(v___x_5088_);
v___x_5099_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_5098_, v___x_5088_, v___f_5096_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
if (lean_obj_tag(v___x_5099_) == 0)
{
lean_object* v_a_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5104_; 
v_a_5100_ = lean_ctor_get(v___x_5099_, 0);
lean_inc(v_a_5100_);
lean_dec_ref_known(v___x_5099_, 1);
v___x_5101_ = lean_array_push(v_fst_5073_, v_a_5100_);
v___x_5102_ = lean_nat_add(v_snd_5074_, v___x_5086_);
lean_dec(v_snd_5074_);
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 1, v___x_5102_);
lean_ctor_set(v___x_5076_, 0, v___x_5101_);
v___x_5104_ = v___x_5076_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v___x_5101_);
lean_ctor_set(v_reuseFailAlloc_5110_, 1, v___x_5102_);
v___x_5104_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
lean_object* v___x_5106_; 
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 1, v___x_5104_);
lean_ctor_set(v___x_5071_, 0, v___x_5092_);
v___x_5106_ = v___x_5071_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v___x_5092_);
lean_ctor_set(v_reuseFailAlloc_5109_, 1, v___x_5104_);
v___x_5106_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
lean_object* v___x_5107_; 
v___x_5107_ = lean_nat_add(v_a_5059_, v___x_5086_);
lean_dec(v_a_5059_);
v_a_5059_ = v___x_5107_;
v_b_5060_ = v___x_5106_;
goto _start;
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_dec_ref(v___x_5092_);
lean_del_object(v___x_5076_);
lean_dec(v_snd_5074_);
lean_dec(v_fst_5073_);
lean_del_object(v___x_5071_);
lean_dec(v_a_5059_);
lean_dec(v___x_5058_);
lean_dec(v___x_5057_);
lean_dec_ref(v___x_5056_);
lean_dec_ref(v___x_5055_);
lean_dec_ref(v___x_5054_);
lean_dec(v___x_5053_);
lean_dec_ref(v_a_5052_);
lean_dec(v___x_5051_);
lean_dec_ref(v___x_5050_);
lean_dec(v_matchDeclName_5049_);
lean_dec_ref(v_val_5048_);
v_a_5111_ = lean_ctor_get(v___x_5099_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_5099_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5099_);
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
else
{
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_dec_ref(v___f_5096_);
lean_dec_ref(v___x_5092_);
lean_del_object(v___x_5076_);
lean_dec(v_snd_5074_);
lean_dec(v_fst_5073_);
lean_del_object(v___x_5071_);
lean_dec(v_a_5059_);
lean_dec(v___x_5058_);
lean_dec(v___x_5057_);
lean_dec_ref(v___x_5056_);
lean_dec_ref(v___x_5055_);
lean_dec_ref(v___x_5054_);
lean_dec(v___x_5053_);
lean_dec_ref(v_a_5052_);
lean_dec(v___x_5051_);
lean_dec_ref(v___x_5050_);
lean_dec(v_matchDeclName_5049_);
lean_dec_ref(v_val_5048_);
v_a_5119_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_5097_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_5097_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5047_ = stack[0].m_obj;
lean_object* v_val_5048_ = stack[1].m_obj;
lean_object* v_matchDeclName_5049_ = stack[2].m_obj;
lean_object* v___x_5050_ = stack[3].m_obj;
lean_object* v___x_5051_ = stack[4].m_obj;
lean_object* v_a_5052_ = stack[5].m_obj;
lean_object* v___x_5053_ = stack[6].m_obj;
lean_object* v___x_5054_ = stack[7].m_obj;
lean_object* v___x_5055_ = stack[8].m_obj;
lean_object* v___x_5056_ = stack[9].m_obj;
lean_object* v___x_5057_ = stack[10].m_obj;
lean_object* v___x_5058_ = stack[11].m_obj;
lean_object* v_a_5059_ = stack[12].m_obj;
lean_object* v_b_5060_ = stack[13].m_obj;
lean_object* v___y_5061_ = stack[14].m_obj;
lean_object* v___y_5062_ = stack[15].m_obj;
lean_object* v___y_5063_ = stack[16].m_obj;
lean_object* v___y_5064_ = stack[17].m_obj;
lean_object* v_res_5134_;
v_res_5134_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5047_, v_val_5048_, v_matchDeclName_5049_, v___x_5050_, v___x_5051_, v_a_5052_, v___x_5053_, v___x_5054_, v___x_5055_, v___x_5056_, v___x_5057_, v___x_5058_, v_a_5059_, v_b_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
stack->m_obj
 = v_res_5134_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5135_ = _args[0];
lean_object* v_val_5136_ = _args[1];
lean_object* v_matchDeclName_5137_ = _args[2];
lean_object* v___x_5138_ = _args[3];
lean_object* v___x_5139_ = _args[4];
lean_object* v_a_5140_ = _args[5];
lean_object* v___x_5141_ = _args[6];
lean_object* v___x_5142_ = _args[7];
lean_object* v___x_5143_ = _args[8];
lean_object* v___x_5144_ = _args[9];
lean_object* v___x_5145_ = _args[10];
lean_object* v___x_5146_ = _args[11];
lean_object* v_a_5147_ = _args[12];
lean_object* v_b_5148_ = _args[13];
lean_object* v___y_5149_ = _args[14];
lean_object* v___y_5150_ = _args[15];
lean_object* v___y_5151_ = _args[16];
lean_object* v___y_5152_ = _args[17];
lean_object* v___y_5153_ = _args[18];
_start:
{
lean_object* v_res_5154_; 
v_res_5154_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5135_, v_val_5136_, v_matchDeclName_5137_, v___x_5138_, v___x_5139_, v_a_5140_, v___x_5141_, v___x_5142_, v___x_5143_, v___x_5144_, v___x_5145_, v___x_5146_, v_a_5147_, v_b_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5151_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
lean_dec(v_upperBound_5135_);
return v_res_5154_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5161_, lean_object* v___x_5162_, lean_object* v_matchDeclName_5163_, lean_object* v___x_5164_, lean_object* v_a_5165_, lean_object* v___x_5166_, lean_object* v___x_5167_, lean_object* v_xs_5168_, lean_object* v___matchResultType_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
lean_object* v_numParams_5175_; lean_object* v_numDiscrs_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v_lower_5182_; lean_object* v_upper_5183_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; uint8_t v___x_5214_; 
v_numParams_5175_ = lean_ctor_get(v_val_5161_, 0);
v_numDiscrs_5176_ = lean_ctor_get(v_val_5161_, 1);
v___x_5177_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5175_);
lean_inc_ref(v_xs_5168_);
v___x_5178_ = l_Array_toSubarray___redArg(v_xs_5168_, v___x_5177_, v_numParams_5175_);
v___x_5179_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5161_);
v___x_5180_ = lean_array_get(v___x_5162_, v_xs_5168_, v___x_5179_);
lean_dec(v___x_5179_);
v___x_5211_ = lean_array_get_size(v_xs_5168_);
v___x_5212_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5161_);
v___x_5213_ = lean_nat_sub(v___x_5211_, v___x_5212_);
lean_dec(v___x_5212_);
v___x_5214_ = lean_nat_dec_le(v___x_5213_, v___x_5177_);
if (v___x_5214_ == 0)
{
v_lower_5182_ = v___x_5213_;
v_upper_5183_ = v___x_5211_;
goto v___jp_5181_;
}
else
{
lean_dec(v___x_5213_);
v_lower_5182_ = v___x_5177_;
v_upper_5183_ = v___x_5211_;
goto v___jp_5181_;
}
v___jp_5181_:
{
lean_object* v___x_5184_; lean_object* v_start_5185_; lean_object* v_stop_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; 
lean_inc_ref(v_xs_5168_);
v___x_5184_ = l_Array_toSubarray___redArg(v_xs_5168_, v_lower_5182_, v_upper_5183_);
v_start_5185_ = lean_ctor_get(v___x_5184_, 1);
v_stop_5186_ = lean_ctor_get(v___x_5184_, 2);
v___x_5187_ = lean_unsigned_to_nat(1u);
v___x_5188_ = lean_nat_add(v_numParams_5175_, v___x_5187_);
v___x_5189_ = lean_nat_add(v___x_5188_, v_numDiscrs_5176_);
v___x_5190_ = lean_nat_sub(v_stop_5186_, v_start_5185_);
v___x_5191_ = l_Array_toSubarray___redArg(v_xs_5168_, v___x_5188_, v___x_5189_);
v___x_5192_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5190_);
v___x_5193_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5190_, v_val_5161_, v_matchDeclName_5163_, v___x_5191_, v___x_5164_, v_a_5165_, v___x_5166_, v___x_5178_, v___x_5180_, v___x_5184_, v___x_5190_, v___x_5167_, v___x_5177_, v___x_5192_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
lean_dec(v___x_5190_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5201_; 
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5201_ == 0)
{
lean_object* v_unused_5202_; 
v_unused_5202_ = lean_ctor_get(v___x_5193_, 0);
lean_dec(v_unused_5202_);
v___x_5195_ = v___x_5193_;
v_isShared_5196_ = v_isSharedCheck_5201_;
goto v_resetjp_5194_;
}
else
{
lean_dec(v___x_5193_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5201_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5197_; lean_object* v___x_5199_; 
v___x_5197_ = lean_box(0);
if (v_isShared_5196_ == 0)
{
lean_ctor_set(v___x_5195_, 0, v___x_5197_);
v___x_5199_ = v___x_5195_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v___x_5197_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
else
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5210_; 
v_a_5203_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5205_ = v___x_5193_;
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___x_5193_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v___x_5208_; 
if (v_isShared_5206_ == 0)
{
v___x_5208_ = v___x_5205_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_a_5203_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_5161_ = stack[0].m_obj;
lean_object* v___x_5162_ = stack[1].m_obj;
lean_object* v_matchDeclName_5163_ = stack[2].m_obj;
lean_object* v___x_5164_ = stack[3].m_obj;
lean_object* v_a_5165_ = stack[4].m_obj;
lean_object* v___x_5166_ = stack[5].m_obj;
lean_object* v___x_5167_ = stack[6].m_obj;
lean_object* v_xs_5168_ = stack[7].m_obj;
lean_object* v___matchResultType_5169_ = stack[8].m_obj;
lean_object* v___y_5170_ = stack[9].m_obj;
lean_object* v___y_5171_ = stack[10].m_obj;
lean_object* v___y_5172_ = stack[11].m_obj;
lean_object* v___y_5173_ = stack[12].m_obj;
lean_object* v_res_5215_;
v_res_5215_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5161_, v___x_5162_, v_matchDeclName_5163_, v___x_5164_, v_a_5165_, v___x_5166_, v___x_5167_, v_xs_5168_, v___matchResultType_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
stack->m_obj
 = v_res_5215_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5216_, lean_object* v___x_5217_, lean_object* v_matchDeclName_5218_, lean_object* v___x_5219_, lean_object* v_a_5220_, lean_object* v___x_5221_, lean_object* v___x_5222_, lean_object* v_xs_5223_, lean_object* v___matchResultType_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5216_, v___x_5217_, v_matchDeclName_5218_, v___x_5219_, v_a_5220_, v___x_5221_, v___x_5222_, v_xs_5223_, v___matchResultType_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_);
lean_dec(v___y_5228_);
lean_dec_ref(v___y_5227_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec_ref(v___matchResultType_5224_);
lean_dec_ref(v___x_5217_);
return v_res_5230_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_){
_start:
{
uint8_t v_trackZetaDelta_5237_; lean_object* v_zetaDeltaSet_5238_; lean_object* v_lctx_5239_; lean_object* v_localInstances_5240_; lean_object* v_defEqCtx_x3f_5241_; lean_object* v_synthPendingDepth_5242_; lean_object* v_customCanUnfoldPredicate_x3f_5243_; uint8_t v_univApprox_5244_; uint8_t v_inTypeClassResolution_5245_; uint8_t v_cacheInferType_5246_; lean_object* v___x_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5290_; 
v_trackZetaDelta_5237_ = lean_ctor_get_uint8(v_a_5232_, sizeof(void*)*7);
v_zetaDeltaSet_5238_ = lean_ctor_get(v_a_5232_, 1);
lean_inc(v_zetaDeltaSet_5238_);
v_lctx_5239_ = lean_ctor_get(v_a_5232_, 2);
lean_inc_ref(v_lctx_5239_);
v_localInstances_5240_ = lean_ctor_get(v_a_5232_, 3);
lean_inc_ref(v_localInstances_5240_);
v_defEqCtx_x3f_5241_ = lean_ctor_get(v_a_5232_, 4);
lean_inc(v_defEqCtx_x3f_5241_);
v_synthPendingDepth_5242_ = lean_ctor_get(v_a_5232_, 5);
lean_inc(v_synthPendingDepth_5242_);
v_customCanUnfoldPredicate_x3f_5243_ = lean_ctor_get(v_a_5232_, 6);
lean_inc(v_customCanUnfoldPredicate_x3f_5243_);
v_univApprox_5244_ = lean_ctor_get_uint8(v_a_5232_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5245_ = lean_ctor_get_uint8(v_a_5232_, sizeof(void*)*7 + 2);
v_cacheInferType_5246_ = lean_ctor_get_uint8(v_a_5232_, sizeof(void*)*7 + 3);
v___x_5247_ = l_Lean_Meta_Context_config(v_a_5232_);
v_isSharedCheck_5290_ = !lean_is_exclusive(v_a_5232_);
if (v_isSharedCheck_5290_ == 0)
{
lean_object* v_unused_5291_; lean_object* v_unused_5292_; lean_object* v_unused_5293_; lean_object* v_unused_5294_; lean_object* v_unused_5295_; lean_object* v_unused_5296_; lean_object* v_unused_5297_; 
v_unused_5291_ = lean_ctor_get(v_a_5232_, 6);
lean_dec(v_unused_5291_);
v_unused_5292_ = lean_ctor_get(v_a_5232_, 5);
lean_dec(v_unused_5292_);
v_unused_5293_ = lean_ctor_get(v_a_5232_, 4);
lean_dec(v_unused_5293_);
v_unused_5294_ = lean_ctor_get(v_a_5232_, 3);
lean_dec(v_unused_5294_);
v_unused_5295_ = lean_ctor_get(v_a_5232_, 2);
lean_dec(v_unused_5295_);
v_unused_5296_ = lean_ctor_get(v_a_5232_, 1);
lean_dec(v_unused_5296_);
v_unused_5297_ = lean_ctor_get(v_a_5232_, 0);
lean_dec(v_unused_5297_);
v___x_5249_ = v_a_5232_;
v_isShared_5250_ = v_isSharedCheck_5290_;
goto v_resetjp_5248_;
}
else
{
lean_dec(v_a_5232_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5290_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5251_; uint64_t v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5256_; 
v___x_5251_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5247_);
v___x_5252_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5251_);
v___x_5253_ = l_Lean_instInhabitedExpr;
v___x_5254_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5254_, 0, v___x_5251_);
lean_ctor_set_uint64(v___x_5254_, sizeof(void*)*1, v___x_5252_);
lean_inc(v_customCanUnfoldPredicate_x3f_5243_);
lean_inc(v_synthPendingDepth_5242_);
lean_inc(v_defEqCtx_x3f_5241_);
lean_inc_ref(v_localInstances_5240_);
lean_inc_ref(v_lctx_5239_);
lean_inc(v_zetaDeltaSet_5238_);
if (v_isShared_5250_ == 0)
{
lean_ctor_set(v___x_5249_, 0, v___x_5254_);
v___x_5256_ = v___x_5249_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v___x_5254_);
lean_ctor_set(v_reuseFailAlloc_5289_, 1, v_zetaDeltaSet_5238_);
lean_ctor_set(v_reuseFailAlloc_5289_, 2, v_lctx_5239_);
lean_ctor_set(v_reuseFailAlloc_5289_, 3, v_localInstances_5240_);
lean_ctor_set(v_reuseFailAlloc_5289_, 4, v_defEqCtx_x3f_5241_);
lean_ctor_set(v_reuseFailAlloc_5289_, 5, v_synthPendingDepth_5242_);
lean_ctor_set(v_reuseFailAlloc_5289_, 6, v_customCanUnfoldPredicate_x3f_5243_);
lean_ctor_set_uint8(v_reuseFailAlloc_5289_, sizeof(void*)*7, v_trackZetaDelta_5237_);
lean_ctor_set_uint8(v_reuseFailAlloc_5289_, sizeof(void*)*7 + 1, v_univApprox_5244_);
lean_ctor_set_uint8(v_reuseFailAlloc_5289_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5245_);
lean_ctor_set_uint8(v_reuseFailAlloc_5289_, sizeof(void*)*7 + 3, v_cacheInferType_5246_);
v___x_5256_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
lean_object* v___x_5257_; lean_object* v___x_5258_; uint64_t v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5257_ = l_Lean_Meta_Context_config(v___x_5256_);
lean_dec_ref(v___x_5256_);
v___x_5258_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5257_);
v___x_5259_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5258_);
v___x_5260_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5260_, 0, v___x_5258_);
lean_ctor_set_uint64(v___x_5260_, sizeof(void*)*1, v___x_5259_);
v___x_5261_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5261_, 0, v___x_5260_);
lean_ctor_set(v___x_5261_, 1, v_zetaDeltaSet_5238_);
lean_ctor_set(v___x_5261_, 2, v_lctx_5239_);
lean_ctor_set(v___x_5261_, 3, v_localInstances_5240_);
lean_ctor_set(v___x_5261_, 4, v_defEqCtx_x3f_5241_);
lean_ctor_set(v___x_5261_, 5, v_synthPendingDepth_5242_);
lean_ctor_set(v___x_5261_, 6, v_customCanUnfoldPredicate_x3f_5243_);
lean_ctor_set_uint8(v___x_5261_, sizeof(void*)*7, v_trackZetaDelta_5237_);
lean_ctor_set_uint8(v___x_5261_, sizeof(void*)*7 + 1, v_univApprox_5244_);
lean_ctor_set_uint8(v___x_5261_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5245_);
lean_ctor_set_uint8(v___x_5261_, sizeof(void*)*7 + 3, v_cacheInferType_5246_);
lean_inc(v_matchDeclName_5231_);
v___x_5262_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5231_, v___x_5261_, v_a_5233_, v_a_5234_, v_a_5235_);
if (lean_obj_tag(v___x_5262_) == 0)
{
lean_object* v_a_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v_a_5268_; 
v_a_5263_ = lean_ctor_get(v___x_5262_, 0);
lean_inc(v_a_5263_);
lean_dec_ref_known(v___x_5262_, 1);
v___x_5264_ = l_Lean_ConstantInfo_levelParams(v_a_5263_);
v___x_5265_ = lean_box(0);
lean_inc(v___x_5264_);
v___x_5266_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v___x_5264_, v___x_5265_);
lean_inc(v_matchDeclName_5231_);
v___x_5267_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_5231_, v_a_5235_);
v_a_5268_ = lean_ctor_get(v___x_5267_, 0);
lean_inc(v_a_5268_);
lean_dec_ref(v___x_5267_);
if (lean_obj_tag(v_a_5268_) == 1)
{
lean_object* v_val_5269_; lean_object* v___x_5270_; lean_object* v___f_5271_; lean_object* v___x_5272_; uint8_t v___x_5273_; lean_object* v___x_5274_; 
v_val_5269_ = lean_ctor_get(v_a_5268_, 0);
lean_inc(v_val_5269_);
lean_dec_ref_known(v_a_5268_, 1);
v___x_5270_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5269_);
lean_inc(v_a_5263_);
v___f_5271_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5271_, 0, v_val_5269_);
lean_closure_set(v___f_5271_, 1, v___x_5253_);
lean_closure_set(v___f_5271_, 2, v_matchDeclName_5231_);
lean_closure_set(v___f_5271_, 3, v___x_5270_);
lean_closure_set(v___f_5271_, 4, v_a_5263_);
lean_closure_set(v___f_5271_, 5, v___x_5266_);
lean_closure_set(v___f_5271_, 6, v___x_5264_);
v___x_5272_ = l_Lean_ConstantInfo_type(v_a_5263_);
lean_dec(v_a_5263_);
v___x_5273_ = 0;
v___x_5274_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5272_, v___f_5271_, v___x_5273_, v___x_5273_, v___x_5261_, v_a_5233_, v_a_5234_, v_a_5235_);
lean_dec_ref_known(v___x_5261_, 7);
return v___x_5274_;
}
else
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
lean_dec(v_a_5268_);
lean_dec(v___x_5266_);
lean_dec(v___x_5264_);
lean_dec(v_a_5263_);
v___x_5275_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5276_ = l_Lean_MessageData_ofName(v_matchDeclName_5231_);
v___x_5277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5275_);
lean_ctor_set(v___x_5277_, 1, v___x_5276_);
v___x_5278_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5277_);
lean_ctor_set(v___x_5279_, 1, v___x_5278_);
v___x_5280_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5279_, v___x_5261_, v_a_5233_, v_a_5234_, v_a_5235_);
lean_dec_ref_known(v___x_5261_, 7);
return v___x_5280_;
}
}
else
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5288_; 
lean_dec_ref_known(v___x_5261_, 7);
lean_dec(v_matchDeclName_5231_);
v_a_5281_ = lean_ctor_get(v___x_5262_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5262_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5283_ = v___x_5262_;
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5262_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5286_; 
if (v_isShared_5284_ == 0)
{
v___x_5286_ = v___x_5283_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_a_5281_);
v___x_5286_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
return v___x_5286_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_5231_ = stack[0].m_obj;
lean_object* v_a_5232_ = stack[1].m_obj;
lean_object* v_a_5233_ = stack[2].m_obj;
lean_object* v_a_5234_ = stack[3].m_obj;
lean_object* v_a_5235_ = stack[4].m_obj;
lean_object* v_res_5298_;
v_res_5298_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5231_, v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_);
stack->m_obj
 = v_res_5298_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5299_, lean_object* v_a_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_){
_start:
{
lean_object* v_res_5305_; 
v_res_5305_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
lean_dec(v_a_5303_);
lean_dec_ref(v_a_5302_);
lean_dec(v_a_5301_);
return v_res_5305_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v_inst_5306_, lean_object* v_R_5307_, lean_object* v_a_5308_, lean_object* v_b_5309_, lean_object* v_c_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v___x_5316_; 
v___x_5316_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_5308_, v_b_5309_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_);
return v___x_5316_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5308_ = stack[2].m_obj;
lean_object* v_b_5309_ = stack[3].m_obj;
lean_object* v___y_5311_ = stack[5].m_obj;
lean_object* v___y_5312_ = stack[6].m_obj;
lean_object* v___y_5313_ = stack[7].m_obj;
lean_object* v___y_5314_ = stack[8].m_obj;
lean_object* v_res_5317_;
v_res_5317_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_box(0), lean_box(0), v_a_5308_, v_b_5309_, lean_box(0), v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_);
stack->m_obj
 = v_res_5317_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v_inst_5318_, lean_object* v_R_5319_, lean_object* v_a_5320_, lean_object* v_b_5321_, lean_object* v_c_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_){
_start:
{
lean_object* v_res_5328_; 
v_res_5328_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_inst_5318_, v_R_5319_, v_a_5320_, v_b_5321_, v_c_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
return v_res_5328_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5329_, lean_object* v_val_5330_, lean_object* v_matchDeclName_5331_, lean_object* v___x_5332_, lean_object* v___x_5333_, lean_object* v_a_5334_, lean_object* v___x_5335_, lean_object* v___x_5336_, lean_object* v___x_5337_, lean_object* v___x_5338_, lean_object* v___x_5339_, lean_object* v___x_5340_, lean_object* v_inst_5341_, lean_object* v_R_5342_, lean_object* v_a_5343_, lean_object* v_b_5344_, lean_object* v_c_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v___x_5351_; 
v___x_5351_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5329_, v_val_5330_, v_matchDeclName_5331_, v___x_5332_, v___x_5333_, v_a_5334_, v___x_5335_, v___x_5336_, v___x_5337_, v___x_5338_, v___x_5339_, v___x_5340_, v_a_5343_, v_b_5344_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
return v___x_5351_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5329_ = stack[0].m_obj;
lean_object* v_val_5330_ = stack[1].m_obj;
lean_object* v_matchDeclName_5331_ = stack[2].m_obj;
lean_object* v___x_5332_ = stack[3].m_obj;
lean_object* v___x_5333_ = stack[4].m_obj;
lean_object* v_a_5334_ = stack[5].m_obj;
lean_object* v___x_5335_ = stack[6].m_obj;
lean_object* v___x_5336_ = stack[7].m_obj;
lean_object* v___x_5337_ = stack[8].m_obj;
lean_object* v___x_5338_ = stack[9].m_obj;
lean_object* v___x_5339_ = stack[10].m_obj;
lean_object* v___x_5340_ = stack[11].m_obj;
lean_object* v_a_5343_ = stack[14].m_obj;
lean_object* v_b_5344_ = stack[15].m_obj;
lean_object* v___y_5346_ = stack[17].m_obj;
lean_object* v___y_5347_ = stack[18].m_obj;
lean_object* v___y_5348_ = stack[19].m_obj;
lean_object* v___y_5349_ = stack[20].m_obj;
lean_object* v_res_5352_;
v_res_5352_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5329_, v_val_5330_, v_matchDeclName_5331_, v___x_5332_, v___x_5333_, v_a_5334_, v___x_5335_, v___x_5336_, v___x_5337_, v___x_5338_, v___x_5339_, v___x_5340_, lean_box(0), lean_box(0), v_a_5343_, v_b_5344_, lean_box(0), v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
stack->m_obj
 = v_res_5352_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5353_ = _args[0];
lean_object* v_val_5354_ = _args[1];
lean_object* v_matchDeclName_5355_ = _args[2];
lean_object* v___x_5356_ = _args[3];
lean_object* v___x_5357_ = _args[4];
lean_object* v_a_5358_ = _args[5];
lean_object* v___x_5359_ = _args[6];
lean_object* v___x_5360_ = _args[7];
lean_object* v___x_5361_ = _args[8];
lean_object* v___x_5362_ = _args[9];
lean_object* v___x_5363_ = _args[10];
lean_object* v___x_5364_ = _args[11];
lean_object* v_inst_5365_ = _args[12];
lean_object* v_R_5366_ = _args[13];
lean_object* v_a_5367_ = _args[14];
lean_object* v_b_5368_ = _args[15];
lean_object* v_c_5369_ = _args[16];
lean_object* v___y_5370_ = _args[17];
lean_object* v___y_5371_ = _args[18];
lean_object* v___y_5372_ = _args[19];
lean_object* v___y_5373_ = _args[20];
lean_object* v___y_5374_ = _args[21];
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5353_, v_val_5354_, v_matchDeclName_5355_, v___x_5356_, v___x_5357_, v_a_5358_, v___x_5359_, v___x_5360_, v___x_5361_, v___x_5362_, v___x_5363_, v___x_5364_, v_inst_5365_, v_R_5366_, v_a_5367_, v_b_5368_, v_c_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
lean_dec(v_upperBound_5353_);
return v_res_5375_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5376_, lean_object* v_matchDeclName_5377_, lean_object* v_a_5378_, lean_object* v_b_5379_){
_start:
{
uint8_t v___x_5381_; 
v___x_5381_ = lean_nat_dec_lt(v_a_5378_, v_upperBound_5376_);
if (v___x_5381_ == 0)
{
lean_object* v___x_5382_; 
lean_dec(v_a_5378_);
lean_dec(v_matchDeclName_5377_);
v___x_5382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5382_, 0, v_b_5379_);
return v___x_5382_;
}
else
{
lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5383_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5377_);
v___x_5384_ = l_Lean_Name_str___override(v_matchDeclName_5377_, v___x_5383_);
v___x_5385_ = lean_unsigned_to_nat(1u);
v___x_5386_ = lean_nat_add(v_a_5378_, v___x_5385_);
lean_dec(v_a_5378_);
lean_inc(v___x_5386_);
v___x_5387_ = lean_name_append_index_after(v___x_5384_, v___x_5386_);
v___x_5388_ = lean_array_push(v_b_5379_, v___x_5387_);
v_a_5378_ = v___x_5386_;
v_b_5379_ = v___x_5388_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5376_ = stack[0].m_obj;
lean_object* v_matchDeclName_5377_ = stack[1].m_obj;
lean_object* v_a_5378_ = stack[2].m_obj;
lean_object* v_b_5379_ = stack[3].m_obj;
lean_object* v_res_5390_;
v_res_5390_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5376_, v_matchDeclName_5377_, v_a_5378_, v_b_5379_);
stack->m_obj
 = v_res_5390_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5391_, lean_object* v_matchDeclName_5392_, lean_object* v_a_5393_, lean_object* v_b_5394_, lean_object* v___y_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5391_, v_matchDeclName_5392_, v_a_5393_, v_b_5394_);
lean_dec(v_upperBound_5391_);
return v_res_5396_;
}
}
lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_){
_start:
{
lean_object* v___x_5403_; lean_object* v_firstEqnName_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; 
v___x_5403_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5397_, 3);
v_firstEqnName_5404_ = l_Lean_Name_str___override(v_matchDeclName_5397_, v___x_5403_);
v___x_5405_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5405_, 0, v_matchDeclName_5397_);
v___x_5406_ = l_Lean_Meta_realizeConst(v_matchDeclName_5397_, v_firstEqnName_5404_, v___x_5405_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_);
if (lean_obj_tag(v___x_5406_) == 0)
{
lean_object* v___x_5407_; lean_object* v_a_5408_; 
lean_dec_ref_known(v___x_5406_, 1);
lean_inc(v_matchDeclName_5397_);
v___x_5407_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_5397_, v_a_5401_);
v_a_5408_ = lean_ctor_get(v___x_5407_, 0);
lean_inc(v_a_5408_);
lean_dec_ref(v___x_5407_);
if (lean_obj_tag(v_a_5408_) == 1)
{
lean_object* v_val_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; 
lean_dec(v_a_5401_);
lean_dec_ref(v_a_5400_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
v_val_5409_ = lean_ctor_get(v_a_5408_, 0);
lean_inc(v_val_5409_);
lean_dec_ref_known(v_a_5408_, 1);
v___x_5410_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5409_);
lean_dec(v_val_5409_);
v___x_5411_ = lean_unsigned_to_nat(0u);
v___x_5412_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5413_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5410_, v_matchDeclName_5397_, v___x_5411_, v___x_5412_);
lean_dec(v___x_5410_);
return v___x_5413_;
}
else
{
lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
lean_dec(v_a_5408_);
v___x_5414_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5415_ = l_Lean_MessageData_ofName(v_matchDeclName_5397_);
v___x_5416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5416_, 0, v___x_5414_);
lean_ctor_set(v___x_5416_, 1, v___x_5415_);
v___x_5417_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5418_, 0, v___x_5416_);
lean_ctor_set(v___x_5418_, 1, v___x_5417_);
v___x_5419_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5418_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_);
lean_dec(v_a_5401_);
lean_dec_ref(v_a_5400_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
return v___x_5419_;
}
}
else
{
lean_object* v_a_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5427_; 
lean_dec(v_a_5401_);
lean_dec_ref(v_a_5400_);
lean_dec(v_a_5399_);
lean_dec_ref(v_a_5398_);
lean_dec(v_matchDeclName_5397_);
v_a_5420_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5422_ = v___x_5406_;
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_a_5420_);
lean_dec(v___x_5406_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5425_; 
if (v_isShared_5423_ == 0)
{
v___x_5425_ = v___x_5422_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_a_5420_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
return v___x_5425_;
}
}
}
}
}
LEAN_EXPORT void lean_get_congr_match_equations_for_0interp(lean_interpreter_value* stack)
{
lean_object* v_matchDeclName_5397_ = stack[0].m_obj;
lean_object* v_a_5398_ = stack[1].m_obj;
lean_object* v_a_5399_ = stack[2].m_obj;
lean_object* v_a_5400_ = stack[3].m_obj;
lean_object* v_a_5401_ = stack[4].m_obj;
lean_object* v_res_5428_;
v_res_5428_ = lean_get_congr_match_equations_for(v_matchDeclName_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_);
stack->m_obj
 = v_res_5428_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_){
_start:
{
lean_object* v_res_5435_; 
v_res_5435_ = lean_get_congr_match_equations_for(v_matchDeclName_5429_, v_a_5430_, v_a_5431_, v_a_5432_, v_a_5433_);
return v_res_5435_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5436_, lean_object* v_matchDeclName_5437_, lean_object* v_inst_5438_, lean_object* v_R_5439_, lean_object* v_a_5440_, lean_object* v_b_5441_, lean_object* v_c_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_){
_start:
{
lean_object* v___x_5448_; 
v___x_5448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5436_, v_matchDeclName_5437_, v_a_5440_, v_b_5441_);
return v___x_5448_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5436_ = stack[0].m_obj;
lean_object* v_matchDeclName_5437_ = stack[1].m_obj;
lean_object* v_a_5440_ = stack[4].m_obj;
lean_object* v_b_5441_ = stack[5].m_obj;
lean_object* v___y_5443_ = stack[7].m_obj;
lean_object* v___y_5444_ = stack[8].m_obj;
lean_object* v___y_5445_ = stack[9].m_obj;
lean_object* v___y_5446_ = stack[10].m_obj;
lean_object* v_res_5449_;
v_res_5449_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5436_, v_matchDeclName_5437_, lean_box(0), lean_box(0), v_a_5440_, v_b_5441_, lean_box(0), v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_);
stack->m_obj
 = v_res_5449_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5450_, lean_object* v_matchDeclName_5451_, lean_object* v_inst_5452_, lean_object* v_R_5453_, lean_object* v_a_5454_, lean_object* v_b_5455_, lean_object* v_c_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5450_, v_matchDeclName_5451_, v_inst_5452_, v_R_5453_, v_a_5454_, v_b_5455_, v_c_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
lean_dec(v_upperBound_5450_);
return v_res_5462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5513_ = lean_unsigned_to_nat(3248161880u);
v___x_5514_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5515_ = l_Lean_Name_num___override(v___x_5514_, v___x_5513_);
return v___x_5515_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; 
v___x_5517_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5518_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5519_ = l_Lean_Name_str___override(v___x_5518_, v___x_5517_);
return v___x_5519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; 
v___x_5521_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5522_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5523_ = l_Lean_Name_str___override(v___x_5522_, v___x_5521_);
return v___x_5523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; 
v___x_5524_ = lean_unsigned_to_nat(2u);
v___x_5525_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5526_ = l_Lean_Name_num___override(v___x_5525_, v___x_5524_);
return v___x_5526_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5528_; uint8_t v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
v___x_5528_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5529_ = 0;
v___x_5530_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5531_ = l_Lean_registerTraceClass(v___x_5528_, v___x_5529_, v___x_5530_);
return v___x_5531_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5532_;
v_res_5532_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5532_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5533_){
_start:
{
lean_object* v_res_5534_; 
v_res_5534_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5535_, lean_object* v_n_5536_){
_start:
{
if (lean_obj_tag(v_n_5536_) == 1)
{
lean_object* v_pre_5537_; lean_object* v_str_5538_; uint8_t v___y_5540_; uint8_t v___x_5546_; 
v_pre_5537_ = lean_ctor_get(v_n_5536_, 0);
lean_inc(v_pre_5537_);
v_str_5538_ = lean_ctor_get(v_n_5536_, 1);
lean_inc_ref_n(v_str_5538_, 2);
lean_dec_ref_known(v_n_5536_, 2);
v___x_5546_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5538_);
if (v___x_5546_ == 0)
{
lean_object* v___x_5547_; uint8_t v___x_5548_; 
v___x_5547_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5548_ = lean_string_dec_eq(v_str_5538_, v___x_5547_);
lean_dec_ref(v_str_5538_);
v___y_5540_ = v___x_5548_;
goto v___jp_5539_;
}
else
{
lean_dec_ref(v_str_5538_);
v___y_5540_ = v___x_5546_;
goto v___jp_5539_;
}
v___jp_5539_:
{
if (v___y_5540_ == 0)
{
lean_object* v___x_5541_; 
lean_dec(v_pre_5537_);
lean_dec_ref(v_env_5535_);
v___x_5541_ = lean_box(0);
return v___x_5541_;
}
else
{
lean_object* v___x_5542_; 
v___x_5542_ = l_Lean_privateToUserName_x3f(v_pre_5537_);
if (lean_obj_tag(v___x_5542_) == 0)
{
lean_dec_ref(v_env_5535_);
return v___x_5542_;
}
else
{
lean_object* v_val_5543_; uint8_t v___x_5544_; 
v_val_5543_ = lean_ctor_get(v___x_5542_, 0);
lean_inc(v_val_5543_);
v___x_5544_ = l_Lean_Meta_isMatcherCore(v_env_5535_, v_val_5543_);
if (v___x_5544_ == 0)
{
lean_object* v___x_5545_; 
lean_dec_ref_known(v___x_5542_, 1);
v___x_5545_ = lean_box(0);
return v___x_5545_;
}
else
{
return v___x_5542_;
}
}
}
}
}
else
{
lean_object* v___x_5549_; 
lean_dec(v_n_5536_);
lean_dec_ref(v_env_5535_);
v___x_5549_ = lean_box(0);
return v___x_5549_;
}
}
}
uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5550_, lean_object* v_x2_5551_){
_start:
{
lean_object* v___x_5552_; 
v___x_5552_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5550_, v_x2_5551_);
if (lean_obj_tag(v___x_5552_) == 0)
{
uint8_t v___x_5553_; 
v___x_5553_ = 0;
return v___x_5553_;
}
else
{
uint8_t v___x_5554_; 
lean_dec_ref_known(v___x_5552_, 1);
v___x_5554_ = 1;
return v___x_5554_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_5550_ = stack[0].m_obj;
lean_object* v_x2_5551_ = stack[1].m_obj;
uint8_t v_res_5555_;
v_res_5555_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5550_, v_x2_5551_);
stack->m_num = v_res_5555_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5556_, lean_object* v_x2_5557_){
_start:
{
uint8_t v_res_5558_; lean_object* v_r_5559_; 
v_res_5558_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5556_, v_x2_5557_);
v_r_5559_ = lean_box(v_res_5558_);
return v_r_5559_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5562_; lean_object* v___x_5563_; 
v___f_5562_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5563_ = l_Lean_registerReservedNamePredicate(v___f_5562_);
return v___x_5563_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5564_;
v_res_5564_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5564_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5565_){
_start:
{
lean_object* v_res_5566_; 
v_res_5566_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5566_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5573_; uint64_t v___x_5574_; 
v___x_5573_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5574_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5573_);
return v___x_5574_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; 
v___x_5575_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5576_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5577_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5577_, 0, v___x_5576_);
lean_ctor_set_uint64(v___x_5577_, sizeof(void*)*1, v___x_5575_);
return v___x_5577_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; 
v___x_5580_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5581_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5582_ = lean_unsigned_to_nat(0u);
v___x_5583_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_5583_, 0, v___x_5582_);
lean_ctor_set(v___x_5583_, 1, v___x_5582_);
lean_ctor_set(v___x_5583_, 2, v___x_5582_);
lean_ctor_set(v___x_5583_, 3, v___x_5582_);
lean_ctor_set(v___x_5583_, 4, v___x_5581_);
lean_ctor_set(v___x_5583_, 5, v___x_5581_);
lean_ctor_set(v___x_5583_, 6, v___x_5581_);
lean_ctor_set(v___x_5583_, 7, v___x_5581_);
lean_ctor_set(v___x_5583_, 8, v___x_5581_);
lean_ctor_set(v___x_5583_, 9, v___x_5581_);
lean_ctor_set(v___x_5583_, 10, v___x_5581_);
lean_ctor_set(v___x_5583_, 11, v___x_5580_);
return v___x_5583_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5584_; lean_object* v___x_5585_; 
v___x_5584_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5585_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5585_, 0, v___x_5584_);
lean_ctor_set(v___x_5585_, 1, v___x_5584_);
lean_ctor_set(v___x_5585_, 2, v___x_5584_);
lean_ctor_set(v___x_5585_, 3, v___x_5584_);
lean_ctor_set(v___x_5585_, 4, v___x_5584_);
lean_ctor_set(v___x_5585_, 5, v___x_5584_);
return v___x_5585_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5586_; lean_object* v___x_5587_; 
v___x_5586_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5587_, 0, v___x_5586_);
lean_ctor_set(v___x_5587_, 1, v___x_5586_);
lean_ctor_set(v___x_5587_, 2, v___x_5586_);
lean_ctor_set(v___x_5587_, 3, v___x_5586_);
lean_ctor_set(v___x_5587_, 4, v___x_5586_);
return v___x_5587_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5588_, lean_object* v_name_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_){
_start:
{
lean_object* v___x_5593_; lean_object* v_env_5594_; lean_object* v___x_5595_; 
v___x_5593_ = lean_st_ref_get(v___y_5591_);
v_env_5594_ = lean_ctor_get(v___x_5593_, 0);
lean_inc_ref(v_env_5594_);
lean_dec(v___x_5593_);
v___x_5595_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5594_, v_name_5589_);
if (lean_obj_tag(v___x_5595_) == 1)
{
lean_object* v_val_5596_; uint8_t v___x_5597_; uint8_t v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; 
v_val_5596_ = lean_ctor_get(v___x_5595_, 0);
lean_inc(v_val_5596_);
lean_dec_ref_known(v___x_5595_, 1);
v___x_5597_ = 0;
v___x_5598_ = 1;
v___x_5599_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5600_ = lean_unsigned_to_nat(0u);
v___x_5601_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5602_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5603_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5604_ = lean_box(0);
lean_inc(v___x_5588_);
v___x_5605_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5605_, 0, v___x_5599_);
lean_ctor_set(v___x_5605_, 1, v___x_5588_);
lean_ctor_set(v___x_5605_, 2, v___x_5602_);
lean_ctor_set(v___x_5605_, 3, v___x_5603_);
lean_ctor_set(v___x_5605_, 4, v___x_5604_);
lean_ctor_set(v___x_5605_, 5, v___x_5600_);
lean_ctor_set(v___x_5605_, 6, v___x_5604_);
lean_ctor_set_uint8(v___x_5605_, sizeof(void*)*7, v___x_5597_);
lean_ctor_set_uint8(v___x_5605_, sizeof(void*)*7 + 1, v___x_5597_);
lean_ctor_set_uint8(v___x_5605_, sizeof(void*)*7 + 2, v___x_5597_);
lean_ctor_set_uint8(v___x_5605_, sizeof(void*)*7 + 3, v___x_5598_);
v___x_5606_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5607_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5608_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5609_, 0, v___x_5606_);
lean_ctor_set(v___x_5609_, 1, v___x_5607_);
lean_ctor_set(v___x_5609_, 2, v___x_5588_);
lean_ctor_set(v___x_5609_, 3, v___x_5601_);
lean_ctor_set(v___x_5609_, 4, v___x_5608_);
v___x_5610_ = lean_st_mk_ref(v___x_5609_);
lean_inc(v___y_5591_);
lean_inc_ref(v___y_5590_);
lean_inc(v___x_5610_);
v___x_5611_ = lean_get_match_equations_for(v_val_5596_, v___x_5605_, v___x_5610_, v___y_5590_, v___y_5591_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5620_; 
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5620_ == 0)
{
lean_object* v_unused_5621_; 
v_unused_5621_ = lean_ctor_get(v___x_5611_, 0);
lean_dec(v_unused_5621_);
v___x_5613_ = v___x_5611_;
v_isShared_5614_ = v_isSharedCheck_5620_;
goto v_resetjp_5612_;
}
else
{
lean_dec(v___x_5611_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5620_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5618_; 
v___x_5615_ = lean_st_ref_get(v___x_5610_);
lean_dec(v___x_5610_);
lean_dec(v___x_5615_);
v___x_5616_ = lean_box(v___x_5598_);
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 0, v___x_5616_);
v___x_5618_ = v___x_5613_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v___x_5616_);
v___x_5618_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
return v___x_5618_;
}
}
}
else
{
lean_dec(v___x_5610_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5629_; 
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5629_ == 0)
{
lean_object* v_unused_5630_; 
v_unused_5630_ = lean_ctor_get(v___x_5611_, 0);
lean_dec(v_unused_5630_);
v___x_5623_ = v___x_5611_;
v_isShared_5624_ = v_isSharedCheck_5629_;
goto v_resetjp_5622_;
}
else
{
lean_dec(v___x_5611_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5629_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5625_; lean_object* v___x_5627_; 
v___x_5625_ = lean_box(v___x_5598_);
if (v_isShared_5624_ == 0)
{
lean_ctor_set_tag(v___x_5623_, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5625_);
v___x_5627_ = v___x_5623_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v___x_5625_);
v___x_5627_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
return v___x_5627_;
}
}
}
else
{
lean_object* v_a_5631_; lean_object* v___x_5633_; uint8_t v_isShared_5634_; uint8_t v_isSharedCheck_5638_; 
v_a_5631_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5638_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5638_ == 0)
{
v___x_5633_ = v___x_5611_;
v_isShared_5634_ = v_isSharedCheck_5638_;
goto v_resetjp_5632_;
}
else
{
lean_inc(v_a_5631_);
lean_dec(v___x_5611_);
v___x_5633_ = lean_box(0);
v_isShared_5634_ = v_isSharedCheck_5638_;
goto v_resetjp_5632_;
}
v_resetjp_5632_:
{
lean_object* v___x_5636_; 
if (v_isShared_5634_ == 0)
{
v___x_5636_ = v___x_5633_;
goto v_reusejp_5635_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_a_5631_);
v___x_5636_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5635_;
}
v_reusejp_5635_:
{
return v___x_5636_;
}
}
}
}
}
else
{
uint8_t v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; 
lean_dec(v___x_5595_);
lean_dec(v___x_5588_);
v___x_5639_ = 0;
v___x_5640_ = lean_box(v___x_5639_);
v___x_5641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5640_);
return v___x_5641_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5588_ = stack[0].m_obj;
lean_object* v_name_5589_ = stack[1].m_obj;
lean_object* v___y_5590_ = stack[2].m_obj;
lean_object* v___y_5591_ = stack[3].m_obj;
lean_object* v_res_5642_;
v_res_5642_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5588_, v_name_5589_, v___y_5590_, v___y_5591_);
stack->m_obj
 = v_res_5642_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5643_, lean_object* v_name_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_){
_start:
{
lean_object* v_res_5648_; 
v_res_5648_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5643_, v_name_5644_, v___y_5645_, v___y_5646_);
lean_dec(v___y_5646_);
lean_dec_ref(v___y_5645_);
return v_res_5648_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5652_; lean_object* v___x_5653_; 
v___f_5652_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5653_ = l_Lean_registerReservedNameAction(v___f_5652_);
return v___x_5653_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5654_;
v_res_5654_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5654_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5655_){
_start:
{
lean_object* v_res_5656_; 
v_res_5656_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5657_, lean_object* v_n_5658_){
_start:
{
if (lean_obj_tag(v_n_5658_) == 1)
{
lean_object* v_pre_5659_; lean_object* v_str_5660_; uint8_t v___x_5661_; 
v_pre_5659_ = lean_ctor_get(v_n_5658_, 0);
lean_inc(v_pre_5659_);
v_str_5660_ = lean_ctor_get(v_n_5658_, 1);
lean_inc_ref(v_str_5660_);
lean_dec_ref_known(v_n_5658_, 2);
v___x_5661_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5660_);
if (v___x_5661_ == 0)
{
lean_object* v___x_5662_; 
lean_dec(v_pre_5659_);
lean_dec_ref(v_env_5657_);
v___x_5662_ = lean_box(0);
return v___x_5662_;
}
else
{
uint8_t v___x_5663_; 
lean_inc(v_pre_5659_);
v___x_5663_ = l_Lean_Meta_isMatcherCore(v_env_5657_, v_pre_5659_);
if (v___x_5663_ == 0)
{
lean_object* v___x_5664_; 
lean_dec(v_pre_5659_);
v___x_5664_ = lean_box(0);
return v___x_5664_;
}
else
{
lean_object* v___x_5665_; 
v___x_5665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5665_, 0, v_pre_5659_);
return v___x_5665_;
}
}
}
else
{
lean_object* v___x_5666_; 
lean_dec(v_n_5658_);
lean_dec_ref(v_env_5657_);
v___x_5666_ = lean_box(0);
return v___x_5666_;
}
}
}
uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5667_, lean_object* v_x2_5668_){
_start:
{
lean_object* v___x_5669_; 
v___x_5669_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5667_, v_x2_5668_);
if (lean_obj_tag(v___x_5669_) == 0)
{
uint8_t v___x_5670_; 
v___x_5670_ = 0;
return v___x_5670_;
}
else
{
uint8_t v___x_5671_; 
lean_dec_ref_known(v___x_5669_, 1);
v___x_5671_ = 1;
return v___x_5671_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_5667_ = stack[0].m_obj;
lean_object* v_x2_5668_ = stack[1].m_obj;
uint8_t v_res_5672_;
v_res_5672_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5667_, v_x2_5668_);
stack->m_num = v_res_5672_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5673_, lean_object* v_x2_5674_){
_start:
{
uint8_t v_res_5675_; lean_object* v_r_5676_; 
v_res_5675_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5673_, v_x2_5674_);
v_r_5676_ = lean_box(v_res_5675_);
return v_r_5676_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5679_; lean_object* v___x_5680_; 
v___f_5679_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5680_ = l_Lean_registerReservedNamePredicate(v___f_5679_);
return v___x_5680_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5681_;
v_res_5681_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5681_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5682_){
_start:
{
lean_object* v_res_5683_; 
v_res_5683_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5683_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5684_, lean_object* v_name_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_){
_start:
{
lean_object* v___x_5689_; lean_object* v_env_5690_; lean_object* v___x_5691_; 
v___x_5689_ = lean_st_ref_get(v___y_5687_);
v_env_5690_ = lean_ctor_get(v___x_5689_, 0);
lean_inc_ref(v_env_5690_);
lean_dec(v___x_5689_);
v___x_5691_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5690_, v_name_5685_);
if (lean_obj_tag(v___x_5691_) == 1)
{
lean_object* v_val_5692_; uint8_t v___x_5693_; uint8_t v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; 
v_val_5692_ = lean_ctor_get(v___x_5691_, 0);
lean_inc(v_val_5692_);
lean_dec_ref_known(v___x_5691_, 1);
v___x_5693_ = 0;
v___x_5694_ = 1;
v___x_5695_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5696_ = lean_unsigned_to_nat(32u);
v___x_5697_ = lean_mk_empty_array_with_capacity(v___x_5696_);
lean_dec_ref(v___x_5697_);
v___x_5698_ = lean_unsigned_to_nat(0u);
v___x_5699_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5700_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5701_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5702_ = lean_box(0);
lean_inc(v___x_5684_);
v___x_5703_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5703_, 0, v___x_5695_);
lean_ctor_set(v___x_5703_, 1, v___x_5684_);
lean_ctor_set(v___x_5703_, 2, v___x_5700_);
lean_ctor_set(v___x_5703_, 3, v___x_5701_);
lean_ctor_set(v___x_5703_, 4, v___x_5702_);
lean_ctor_set(v___x_5703_, 5, v___x_5698_);
lean_ctor_set(v___x_5703_, 6, v___x_5702_);
lean_ctor_set_uint8(v___x_5703_, sizeof(void*)*7, v___x_5693_);
lean_ctor_set_uint8(v___x_5703_, sizeof(void*)*7 + 1, v___x_5693_);
lean_ctor_set_uint8(v___x_5703_, sizeof(void*)*7 + 2, v___x_5693_);
lean_ctor_set_uint8(v___x_5703_, sizeof(void*)*7 + 3, v___x_5694_);
v___x_5704_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5705_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5706_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5704_);
lean_ctor_set(v___x_5707_, 1, v___x_5705_);
lean_ctor_set(v___x_5707_, 2, v___x_5684_);
lean_ctor_set(v___x_5707_, 3, v___x_5699_);
lean_ctor_set(v___x_5707_, 4, v___x_5706_);
v___x_5708_ = lean_st_mk_ref(v___x_5707_);
lean_inc(v___y_5687_);
lean_inc_ref(v___y_5686_);
lean_inc(v___x_5708_);
v___x_5709_ = lean_get_congr_match_equations_for(v_val_5692_, v___x_5703_, v___x_5708_, v___y_5686_, v___y_5687_);
if (lean_obj_tag(v___x_5709_) == 0)
{
lean_object* v___x_5711_; uint8_t v_isShared_5712_; uint8_t v_isSharedCheck_5718_; 
v_isSharedCheck_5718_ = !lean_is_exclusive(v___x_5709_);
if (v_isSharedCheck_5718_ == 0)
{
lean_object* v_unused_5719_; 
v_unused_5719_ = lean_ctor_get(v___x_5709_, 0);
lean_dec(v_unused_5719_);
v___x_5711_ = v___x_5709_;
v_isShared_5712_ = v_isSharedCheck_5718_;
goto v_resetjp_5710_;
}
else
{
lean_dec(v___x_5709_);
v___x_5711_ = lean_box(0);
v_isShared_5712_ = v_isSharedCheck_5718_;
goto v_resetjp_5710_;
}
v_resetjp_5710_:
{
lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5716_; 
v___x_5713_ = lean_st_ref_get(v___x_5708_);
lean_dec(v___x_5708_);
lean_dec(v___x_5713_);
v___x_5714_ = lean_box(v___x_5694_);
if (v_isShared_5712_ == 0)
{
lean_ctor_set(v___x_5711_, 0, v___x_5714_);
v___x_5716_ = v___x_5711_;
goto v_reusejp_5715_;
}
else
{
lean_object* v_reuseFailAlloc_5717_; 
v_reuseFailAlloc_5717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5717_, 0, v___x_5714_);
v___x_5716_ = v_reuseFailAlloc_5717_;
goto v_reusejp_5715_;
}
v_reusejp_5715_:
{
return v___x_5716_;
}
}
}
else
{
lean_dec(v___x_5708_);
if (lean_obj_tag(v___x_5709_) == 0)
{
lean_object* v___x_5721_; uint8_t v_isShared_5722_; uint8_t v_isSharedCheck_5727_; 
v_isSharedCheck_5727_ = !lean_is_exclusive(v___x_5709_);
if (v_isSharedCheck_5727_ == 0)
{
lean_object* v_unused_5728_; 
v_unused_5728_ = lean_ctor_get(v___x_5709_, 0);
lean_dec(v_unused_5728_);
v___x_5721_ = v___x_5709_;
v_isShared_5722_ = v_isSharedCheck_5727_;
goto v_resetjp_5720_;
}
else
{
lean_dec(v___x_5709_);
v___x_5721_ = lean_box(0);
v_isShared_5722_ = v_isSharedCheck_5727_;
goto v_resetjp_5720_;
}
v_resetjp_5720_:
{
lean_object* v___x_5723_; lean_object* v___x_5725_; 
v___x_5723_ = lean_box(v___x_5694_);
if (v_isShared_5722_ == 0)
{
lean_ctor_set_tag(v___x_5721_, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5723_);
v___x_5725_ = v___x_5721_;
goto v_reusejp_5724_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v___x_5723_);
v___x_5725_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5724_;
}
v_reusejp_5724_:
{
return v___x_5725_;
}
}
}
else
{
lean_object* v_a_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5736_; 
v_a_5729_ = lean_ctor_get(v___x_5709_, 0);
v_isSharedCheck_5736_ = !lean_is_exclusive(v___x_5709_);
if (v_isSharedCheck_5736_ == 0)
{
v___x_5731_ = v___x_5709_;
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_a_5729_);
lean_dec(v___x_5709_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v___x_5734_; 
if (v_isShared_5732_ == 0)
{
v___x_5734_ = v___x_5731_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_a_5729_);
v___x_5734_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
return v___x_5734_;
}
}
}
}
}
else
{
uint8_t v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; 
lean_dec(v___x_5691_);
lean_dec(v___x_5684_);
v___x_5737_ = 0;
v___x_5738_ = lean_box(v___x_5737_);
v___x_5739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5738_);
return v___x_5739_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5684_ = stack[0].m_obj;
lean_object* v_name_5685_ = stack[1].m_obj;
lean_object* v___y_5686_ = stack[2].m_obj;
lean_object* v___y_5687_ = stack[3].m_obj;
lean_object* v_res_5740_;
v_res_5740_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5684_, v_name_5685_, v___y_5686_, v___y_5687_);
stack->m_obj
 = v_res_5740_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5741_, lean_object* v_name_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_){
_start:
{
lean_object* v_res_5746_; 
v_res_5746_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5741_, v_name_5742_, v___y_5743_, v___y_5744_);
lean_dec(v___y_5744_);
lean_dec_ref(v___y_5743_);
return v_res_5746_;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5750_; lean_object* v___x_5751_; 
v___f_5750_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5751_ = l_Lean_registerReservedNameAction(v___f_5750_);
return v___x_5751_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5752_;
v_res_5752_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
stack->m_obj
 = v_res_5752_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5753_){
_start:
{
lean_object* v_res_5754_; 
v_res_5754_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5754_;
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
