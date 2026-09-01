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
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
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
v_options_12_ = lean_ctor_get(v___y_4_, 1);
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
v_ref_29_ = lean_ctor_get(v___y_26_, 4);
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
lean_inc_ref_n(v_mctx_334_, 2);
lean_dec(v___x_308_);
v___f_335_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0));
v___f_336_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_336_, 0, v_fvarId_305_);
v___x_337_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2);
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
lean_dec_ref_known(v___x_338_, 2);
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
v___x_322_ = lean_st_ref_put(v___y_306_, v___x_321_);
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
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
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
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
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
v___x_448_ = l_Lean_Meta_matchEq_x3f(v___x_447_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
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
lean_dec_ref_known(v___x_467_, 1);
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
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
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
v___x_577_ = l_Lean_Meta_matchEq_x3f(v___x_576_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_577_, 1);
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
lean_dec_ref_known(v___x_596_, 1);
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
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_as_663_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(lean_object* v_init_675_, lean_object* v_mvarId_676_, lean_object* v_n_677_, lean_object* v_b_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
if (lean_obj_tag(v_n_677_) == 0)
{
lean_object* v_cs_684_; lean_object* v___x_685_; lean_object* v___x_686_; size_t v_sz_687_; size_t v___x_688_; lean_object* v___x_689_; 
v_cs_684_ = lean_ctor_get(v_n_677_, 0);
v___x_685_ = lean_box(0);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v_b_678_);
v_sz_687_ = lean_array_size(v_cs_684_);
v___x_688_ = ((size_t)0ULL);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_675_, v_mvarId_676_, v_cs_684_, v_sz_687_, v___x_688_, v___x_686_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_704_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_704_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_704_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_704_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_fst_694_; 
v_fst_694_ = lean_ctor_get(v_a_690_, 0);
if (lean_obj_tag(v_fst_694_) == 0)
{
lean_object* v_snd_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v_snd_695_ = lean_ctor_get(v_a_690_, 1);
lean_inc(v_snd_695_);
lean_dec(v_a_690_);
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_snd_695_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_696_);
v___x_698_ = v___x_692_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_object* v_val_700_; lean_object* v___x_702_; 
lean_inc_ref(v_fst_694_);
lean_dec(v_a_690_);
v_val_700_ = lean_ctor_get(v_fst_694_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v_fst_694_, 1);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_val_700_);
v___x_702_ = v___x_692_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_val_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
v_a_705_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_689_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_689_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_object* v_vs_713_; lean_object* v___x_714_; lean_object* v___x_715_; size_t v_sz_716_; size_t v___x_717_; lean_object* v___x_718_; 
v_vs_713_ = lean_ctor_get(v_n_677_, 0);
v___x_714_ = lean_box(0);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v_b_678_);
v_sz_716_ = lean_array_size(v_vs_713_);
v___x_717_ = ((size_t)0ULL);
v___x_718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_676_, v_vs_713_, v_sz_716_, v___x_717_, v___x_715_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_733_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_733_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_733_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_733_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v_fst_723_; 
v_fst_723_ = lean_ctor_get(v_a_719_, 0);
if (lean_obj_tag(v_fst_723_) == 0)
{
lean_object* v_snd_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v_snd_724_ = lean_ctor_get(v_a_719_, 1);
lean_inc(v_snd_724_);
lean_dec(v_a_719_);
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v_snd_724_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_725_);
v___x_727_ = v___x_721_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v_val_729_; lean_object* v___x_731_; 
lean_inc_ref(v_fst_723_);
lean_dec(v_a_719_);
v_val_729_ = lean_ctor_get(v_fst_723_, 0);
lean_inc(v_val_729_);
lean_dec_ref_known(v_fst_723_, 1);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_val_729_);
v___x_731_ = v___x_721_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_val_729_);
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
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
v_a_734_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_718_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_718_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(lean_object* v_init_742_, lean_object* v_mvarId_743_, lean_object* v_as_744_, size_t v_sz_745_, size_t v_i_746_, lean_object* v_b_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
uint8_t v___x_753_; 
v___x_753_ = lean_usize_dec_lt(v_i_746_, v_sz_745_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
lean_dec(v_mvarId_743_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v_b_747_);
return v___x_754_;
}
else
{
lean_object* v_snd_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_789_; 
v_snd_755_ = lean_ctor_get(v_b_747_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_b_747_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_b_747_, 0);
lean_dec(v_unused_790_);
v___x_757_ = v_b_747_;
v_isShared_758_ = v_isSharedCheck_789_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snd_755_);
lean_dec(v_b_747_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_789_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_a_759_; lean_object* v___x_760_; 
v_a_759_ = lean_array_uget_borrowed(v_as_744_, v_i_746_);
lean_inc(v_snd_755_);
lean_inc(v_mvarId_743_);
v___x_760_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_742_, v_mvarId_743_, v_a_759_, v_snd_755_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_780_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_780_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_780_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_780_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
if (lean_obj_tag(v_a_761_) == 0)
{
lean_object* v___x_765_; lean_object* v___x_767_; 
lean_dec(v_mvarId_743_);
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v_a_761_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_765_);
v___x_767_ = v___x_757_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_snd_755_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_767_);
v___x_769_ = v___x_763_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_del_object(v___x_763_);
lean_dec(v_snd_755_);
v_a_772_ = lean_ctor_get(v_a_761_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v_a_761_, 1);
v___x_773_ = lean_box(0);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v_a_772_);
lean_ctor_set(v___x_757_, 0, v___x_773_);
v___x_775_ = v___x_757_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_a_772_);
v___x_775_ = v_reuseFailAlloc_779_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
size_t v___x_776_; size_t v___x_777_; 
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_add(v_i_746_, v___x_776_);
v_i_746_ = v___x_777_;
v_b_747_ = v___x_775_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_del_object(v___x_757_);
lean_dec(v_snd_755_);
lean_dec(v_mvarId_743_);
v_a_781_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_760_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_760_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3___boxed(lean_object* v_init_791_, lean_object* v_mvarId_792_, lean_object* v_as_793_, lean_object* v_sz_794_, lean_object* v_i_795_, lean_object* v_b_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
size_t v_sz_boxed_802_; size_t v_i_boxed_803_; lean_object* v_res_804_; 
v_sz_boxed_802_ = lean_unbox_usize(v_sz_794_);
lean_dec(v_sz_794_);
v_i_boxed_803_ = lean_unbox_usize(v_i_795_);
lean_dec(v_i_795_);
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_791_, v_mvarId_792_, v_as_793_, v_sz_boxed_802_, v_i_boxed_803_, v_b_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec_ref(v_as_793_);
lean_dec_ref(v_init_791_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1___boxed(lean_object* v_init_805_, lean_object* v_mvarId_806_, lean_object* v_n_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_805_, v_mvarId_806_, v_n_807_, v_b_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v_n_807_);
lean_dec_ref(v_init_805_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(lean_object* v_mvarId_818_, lean_object* v_as_819_, size_t v_sz_820_, size_t v_i_821_, lean_object* v_b_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = lean_usize_dec_lt(v_i_821_, v_sz_820_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v_mvarId_818_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v_b_822_);
return v___x_829_;
}
else
{
lean_object* v_snd_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_925_; 
v_snd_830_ = lean_ctor_get(v_b_822_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v_b_822_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v_b_822_, 0);
lean_dec(v_unused_926_);
v___x_832_ = v_b_822_;
v_isShared_833_ = v_isSharedCheck_925_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_snd_830_);
lean_dec(v_b_822_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_925_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v_a_836_; lean_object* v_a_843_; 
v___x_834_ = lean_box(0);
v_a_843_ = lean_array_uget_borrowed(v_as_819_, v_i_821_);
if (lean_obj_tag(v_a_843_) == 0)
{
v_a_836_ = v_snd_830_;
goto v___jp_835_;
}
else
{
lean_object* v_val_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_val_844_ = lean_ctor_get(v_a_843_, 0);
v___x_845_ = l_Lean_LocalDecl_type(v_val_844_);
v___x_846_ = l_Lean_Meta_matchEq_x3f(v___x_845_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = lean_box(0);
v___x_849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_847_) == 1)
{
lean_object* v_val_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_916_; 
v_val_850_ = lean_ctor_get(v_a_847_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v_a_847_);
if (v_isSharedCheck_916_ == 0)
{
v___x_852_ = v_a_847_;
v_isShared_853_ = v_isSharedCheck_916_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_val_850_);
lean_dec(v_a_847_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_916_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_snd_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_914_; 
v_snd_854_ = lean_ctor_get(v_val_850_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_val_850_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v_val_850_, 0);
lean_dec(v_unused_915_);
v___x_856_ = v_val_850_;
v_isShared_857_ = v_isSharedCheck_914_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snd_854_);
lean_dec(v_val_850_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_914_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_fst_858_; lean_object* v_snd_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_913_; 
v_fst_858_ = lean_ctor_get(v_snd_854_, 0);
v_snd_859_ = lean_ctor_get(v_snd_854_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_snd_854_);
if (v_isSharedCheck_913_ == 0)
{
v___x_861_ = v_snd_854_;
v_isShared_862_ = v_isSharedCheck_913_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_snd_859_);
lean_inc(v_fst_858_);
lean_dec(v_snd_854_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_913_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
uint8_t v___x_863_; 
v___x_863_ = l_Lean_Expr_isFVar(v_fst_858_);
if (v___x_863_ == 0)
{
lean_del_object(v___x_861_);
lean_dec(v_snd_859_);
lean_dec(v_fst_858_);
lean_del_object(v___x_856_);
lean_del_object(v___x_852_);
lean_dec(v_snd_830_);
v_a_836_ = v___x_849_;
goto v___jp_835_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = l_Lean_Expr_fvarId_x21(v_fst_858_);
lean_dec(v_fst_858_);
lean_inc(v___x_864_);
v___x_865_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_859_, v___x_864_, v___y_824_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; uint8_t v___x_867_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v___x_867_ = lean_unbox(v_a_866_);
lean_dec(v_a_866_);
if (v___x_867_ == 0)
{
if (v___x_863_ == 0)
{
lean_dec(v___x_864_);
lean_del_object(v___x_861_);
lean_del_object(v___x_856_);
lean_del_object(v___x_852_);
lean_dec(v_snd_830_);
v_a_836_ = v___x_849_;
goto v___jp_835_;
}
else
{
lean_object* v___x_868_; 
lean_inc(v_mvarId_818_);
v___x_868_ = l_Lean_Meta_subst_x3f(v_mvarId_818_, v___x_864_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_896_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_896_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_896_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_896_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
if (lean_obj_tag(v_a_869_) == 0)
{
lean_del_object(v___x_871_);
lean_del_object(v___x_861_);
lean_del_object(v___x_856_);
lean_del_object(v___x_852_);
lean_dec(v_snd_830_);
v_a_836_ = v___x_849_;
goto v___jp_835_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_895_; 
lean_del_object(v___x_832_);
lean_dec(v_mvarId_818_);
v_val_873_ = lean_ctor_get(v_a_869_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_869_);
if (v_isSharedCheck_895_ == 0)
{
v___x_875_ = v_a_869_;
v_isShared_876_ = v_isSharedCheck_895_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_val_873_);
lean_dec(v_a_869_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_895_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_mk_empty_array_with_capacity(v___x_877_);
v___x_879_ = lean_array_push(v___x_878_, v_val_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_879_);
v___x_881_ = v___x_875_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_894_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v___x_848_);
lean_ctor_set(v___x_861_, 0, v___x_881_);
v___x_883_ = v___x_861_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_848_);
v___x_883_ = v_reuseFailAlloc_893_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_883_);
v___x_885_ = v___x_852_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_892_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v_snd_830_);
lean_ctor_set(v___x_856_, 0, v___x_885_);
v___x_887_ = v___x_856_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_snd_830_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_887_);
v___x_889_ = v___x_871_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
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
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_del_object(v___x_861_);
lean_del_object(v___x_856_);
lean_del_object(v___x_852_);
lean_del_object(v___x_832_);
lean_dec(v_snd_830_);
lean_dec(v_mvarId_818_);
v_a_897_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_868_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_868_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
else
{
lean_dec(v___x_864_);
lean_del_object(v___x_861_);
lean_del_object(v___x_856_);
lean_del_object(v___x_852_);
lean_dec(v_snd_830_);
v_a_836_ = v___x_849_;
goto v___jp_835_;
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec(v___x_864_);
lean_del_object(v___x_861_);
lean_del_object(v___x_856_);
lean_del_object(v___x_852_);
lean_del_object(v___x_832_);
lean_dec(v_snd_830_);
lean_dec(v_mvarId_818_);
v_a_905_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_865_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_865_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
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
lean_dec(v_a_847_);
lean_dec(v_snd_830_);
v_a_836_ = v___x_849_;
goto v___jp_835_;
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_del_object(v___x_832_);
lean_dec(v_snd_830_);
lean_dec(v_mvarId_818_);
v_a_917_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_846_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_846_);
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
v___jp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_a_836_);
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_838_ = v___x_832_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_a_836_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
size_t v___x_839_; size_t v___x_840_; 
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_add(v_i_821_, v___x_839_);
v_i_821_ = v___x_840_;
v_b_822_ = v___x_838_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___boxed(lean_object* v_mvarId_927_, lean_object* v_as_928_, lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_b_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
size_t v_sz_boxed_937_; size_t v_i_boxed_938_; lean_object* v_res_939_; 
v_sz_boxed_937_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_938_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_927_, v_as_928_, v_sz_boxed_937_, v_i_boxed_938_, v_b_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_as_928_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(lean_object* v_mvarId_940_, lean_object* v_as_941_, size_t v_sz_942_, size_t v_i_943_, lean_object* v_b_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = lean_usize_dec_lt(v_i_943_, v_sz_942_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
lean_dec(v_mvarId_940_);
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v_b_944_);
return v___x_951_;
}
else
{
lean_object* v_snd_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_1047_; 
v_snd_952_ = lean_ctor_get(v_b_944_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_b_944_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v_b_944_, 0);
lean_dec(v_unused_1048_);
v___x_954_ = v_b_944_;
v_isShared_955_ = v_isSharedCheck_1047_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_snd_952_);
lean_dec(v_b_944_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_1047_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v_a_958_; lean_object* v_a_965_; 
v___x_956_ = lean_box(0);
v_a_965_ = lean_array_uget_borrowed(v_as_941_, v_i_943_);
if (lean_obj_tag(v_a_965_) == 0)
{
v_a_958_ = v_snd_952_;
goto v___jp_957_;
}
else
{
lean_object* v_val_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_val_966_ = lean_ctor_get(v_a_965_, 0);
v___x_967_ = l_Lean_LocalDecl_type(v_val_966_);
v___x_968_ = l_Lean_Meta_matchEq_x3f(v___x_967_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = lean_box(0);
v___x_971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_969_) == 1)
{
lean_object* v_val_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1038_; 
v_val_972_ = lean_ctor_get(v_a_969_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_a_969_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_974_ = v_a_969_;
v_isShared_975_ = v_isSharedCheck_1038_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_val_972_);
lean_dec(v_a_969_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1038_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_snd_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1036_; 
v_snd_976_ = lean_ctor_get(v_val_972_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_val_972_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v_val_972_, 0);
lean_dec(v_unused_1037_);
v___x_978_ = v_val_972_;
v_isShared_979_ = v_isSharedCheck_1036_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_snd_976_);
lean_dec(v_val_972_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1036_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_fst_980_; lean_object* v_snd_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1035_; 
v_fst_980_ = lean_ctor_get(v_snd_976_, 0);
v_snd_981_ = lean_ctor_get(v_snd_976_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_snd_976_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_983_ = v_snd_976_;
v_isShared_984_ = v_isSharedCheck_1035_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snd_981_);
lean_inc(v_fst_980_);
lean_dec(v_snd_976_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1035_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
uint8_t v___x_985_; 
v___x_985_ = l_Lean_Expr_isFVar(v_fst_980_);
if (v___x_985_ == 0)
{
lean_del_object(v___x_983_);
lean_dec(v_snd_981_);
lean_dec(v_fst_980_);
lean_del_object(v___x_978_);
lean_del_object(v___x_974_);
lean_dec(v_snd_952_);
v_a_958_ = v___x_971_;
goto v___jp_957_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = l_Lean_Expr_fvarId_x21(v_fst_980_);
lean_dec(v_fst_980_);
lean_inc(v___x_986_);
v___x_987_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_981_, v___x_986_, v___y_946_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; uint8_t v___x_989_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = lean_unbox(v_a_988_);
lean_dec(v_a_988_);
if (v___x_989_ == 0)
{
if (v___x_985_ == 0)
{
lean_dec(v___x_986_);
lean_del_object(v___x_983_);
lean_del_object(v___x_978_);
lean_del_object(v___x_974_);
lean_dec(v_snd_952_);
v_a_958_ = v___x_971_;
goto v___jp_957_;
}
else
{
lean_object* v___x_990_; 
lean_inc(v_mvarId_940_);
v___x_990_ = l_Lean_Meta_subst_x3f(v_mvarId_940_, v___x_986_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1018_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1018_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1018_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
if (lean_obj_tag(v_a_991_) == 0)
{
lean_del_object(v___x_993_);
lean_del_object(v___x_983_);
lean_del_object(v___x_978_);
lean_del_object(v___x_974_);
lean_dec(v_snd_952_);
v_a_958_ = v___x_971_;
goto v___jp_957_;
}
else
{
lean_object* v_val_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1017_; 
lean_del_object(v___x_954_);
lean_dec(v_mvarId_940_);
v_val_995_ = lean_ctor_get(v_a_991_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_a_991_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_997_ = v_a_991_;
v_isShared_998_ = v_isSharedCheck_1017_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_val_995_);
lean_dec(v_a_991_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1017_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_999_ = lean_unsigned_to_nat(1u);
v___x_1000_ = lean_mk_empty_array_with_capacity(v___x_999_);
v___x_1001_ = lean_array_push(v___x_1000_, v_val_995_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1001_);
v___x_1003_ = v___x_997_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v___x_970_);
lean_ctor_set(v___x_983_, 0, v___x_1003_);
v___x_1005_ = v___x_983_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v___x_970_);
v___x_1005_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_1005_);
v___x_1007_ = v___x_974_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v_snd_952_);
lean_ctor_set(v___x_978_, 0, v___x_1007_);
v___x_1009_ = v___x_978_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_snd_952_);
v___x_1009_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1009_);
v___x_1011_ = v___x_993_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
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
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_del_object(v___x_983_);
lean_del_object(v___x_978_);
lean_del_object(v___x_974_);
lean_del_object(v___x_954_);
lean_dec(v_snd_952_);
lean_dec(v_mvarId_940_);
v_a_1019_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_990_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_990_);
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
else
{
lean_dec(v___x_986_);
lean_del_object(v___x_983_);
lean_del_object(v___x_978_);
lean_del_object(v___x_974_);
lean_dec(v_snd_952_);
v_a_958_ = v___x_971_;
goto v___jp_957_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v___x_986_);
lean_del_object(v___x_983_);
lean_del_object(v___x_978_);
lean_del_object(v___x_974_);
lean_del_object(v___x_954_);
lean_dec(v_snd_952_);
lean_dec(v_mvarId_940_);
v_a_1027_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_987_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_987_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
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
lean_dec(v_a_969_);
lean_dec(v_snd_952_);
v_a_958_ = v___x_971_;
goto v___jp_957_;
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_del_object(v___x_954_);
lean_dec(v_snd_952_);
lean_dec(v_mvarId_940_);
v_a_1039_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_968_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_968_);
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
v___jp_957_:
{
lean_object* v___x_960_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_a_958_);
lean_ctor_set(v___x_954_, 0, v___x_956_);
v___x_960_ = v___x_954_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_a_958_);
v___x_960_ = v_reuseFailAlloc_964_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; 
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_add(v_i_943_, v___x_961_);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_940_, v_as_941_, v_sz_942_, v___x_962_, v___x_960_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
return v___x_963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2___boxed(lean_object* v_mvarId_1049_, lean_object* v_as_1050_, lean_object* v_sz_1051_, lean_object* v_i_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
size_t v_sz_boxed_1059_; size_t v_i_boxed_1060_; lean_object* v_res_1061_; 
v_sz_boxed_1059_ = lean_unbox_usize(v_sz_1051_);
lean_dec(v_sz_1051_);
v_i_boxed_1060_ = lean_unbox_usize(v_i_1052_);
lean_dec(v_i_1052_);
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1049_, v_as_1050_, v_sz_boxed_1059_, v_i_boxed_1060_, v_b_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec_ref(v_as_1050_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(lean_object* v_mvarId_1062_, lean_object* v_t_1063_, lean_object* v_init_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_root_1070_; lean_object* v_tail_1071_; lean_object* v___x_1072_; 
v_root_1070_ = lean_ctor_get(v_t_1063_, 0);
v_tail_1071_ = lean_ctor_get(v_t_1063_, 1);
lean_inc(v_mvarId_1062_);
lean_inc_ref(v_init_1064_);
v___x_1072_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_1064_, v_mvarId_1062_, v_root_1070_, v_init_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec_ref(v_init_1064_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1109_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1109_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1109_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
if (lean_obj_tag(v_a_1073_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; 
lean_dec(v_mvarId_1062_);
v_a_1077_ = lean_ctor_get(v_a_1073_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v_a_1073_, 1);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v_a_1077_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; size_t v_sz_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
lean_del_object(v___x_1075_);
v_a_1081_ = lean_ctor_get(v_a_1073_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v_a_1073_, 1);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_a_1081_);
v_sz_1084_ = lean_array_size(v_tail_1071_);
v___x_1085_ = ((size_t)0ULL);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1062_, v_tail_1071_, v_sz_1084_, v___x_1085_, v___x_1083_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1100_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1100_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1100_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_fst_1091_; 
v_fst_1091_ = lean_ctor_get(v_a_1087_, 0);
if (lean_obj_tag(v_fst_1091_) == 0)
{
lean_object* v_snd_1092_; lean_object* v___x_1094_; 
v_snd_1092_ = lean_ctor_get(v_a_1087_, 1);
lean_inc(v_snd_1092_);
lean_dec(v_a_1087_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v_snd_1092_);
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_snd_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
else
{
lean_object* v_val_1096_; lean_object* v___x_1098_; 
lean_inc_ref(v_fst_1091_);
lean_dec(v_a_1087_);
v_val_1096_ = lean_ctor_get(v_fst_1091_, 0);
lean_inc(v_val_1096_);
lean_dec_ref_known(v_fst_1091_, 1);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v_val_1096_);
v___x_1098_ = v___x_1089_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_val_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1086_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1086_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v_mvarId_1062_);
v_a_1110_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1072_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1072_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1___boxed(lean_object* v_mvarId_1118_, lean_object* v_t_1119_, lean_object* v_init_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1118_, v_t_1119_, v_init_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec_ref(v_t_1119_);
return v_res_1126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(lean_object* v_mvarId_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_lctx_1139_; lean_object* v_decls_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_lctx_1139_ = lean_ctor_get(v___y_1134_, 2);
v_decls_1140_ = lean_ctor_get(v_lctx_1139_, 1);
v___x_1141_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0));
v___x_1142_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1133_, v_decls_1140_, v___x_1141_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1154_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1154_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1154_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_fst_1147_; 
v_fst_1147_ = lean_ctor_get(v_a_1143_, 0);
lean_inc(v_fst_1147_);
lean_dec(v_a_1143_);
if (lean_obj_tag(v_fst_1147_) == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_del_object(v___x_1145_);
v___x_1148_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2);
v___x_1149_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1148_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
return v___x_1149_;
}
else
{
lean_object* v_val_1150_; lean_object* v___x_1152_; 
v_val_1150_ = lean_ctor_get(v_fst_1147_, 0);
lean_inc(v_val_1150_);
lean_dec_ref_known(v_fst_1147_, 1);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v_val_1150_);
v___x_1152_ = v___x_1145_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_val_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
v_a_1155_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1142_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1142_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed(lean_object* v_mvarId_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(v_mvarId_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(lean_object* v_mvarId_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___f_1176_; lean_object* v___x_1177_; 
lean_inc(v_mvarId_1170_);
v___f_1176_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1176_, 0, v_mvarId_1170_);
v___x_1177_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_1170_, v___f_1176_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___boxed(lean_object* v_mvarId_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v_mvarId_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object* v_x_1192_){
_start:
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1194_ = lean_name_eq(v_x_1192_, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object* v_x_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(v_x_1195_);
lean_dec(v_x_1195_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object* v_e_1198_){
_start:
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1200_ = l_Lean_Expr_isConstOf(v_e_1198_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object* v_e_1201_){
_start:
{
uint8_t v_res_1202_; lean_object* v_r_1203_; 
v_res_1202_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(v_e_1201_);
lean_dec_ref(v_e_1201_);
v_r_1203_ = lean_box(v_res_1202_);
return v_r_1203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2));
v___x_1208_ = l_Lean_stringToMessageData(v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object* v_mvarId_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; 
lean_inc(v_mvarId_1209_);
v___x_1215_ = l_Lean_MVarId_getType(v_mvarId_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___x_1219_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v___f_1217_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0));
v___f_1218_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1));
v___x_1219_ = lean_find_expr(v___f_1218_, v_a_1216_);
lean_dec(v_a_1216_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_mvarId_1209_);
v___x_1220_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3);
v___x_1221_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1220_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_object* v___x_1230_; 
lean_dec_ref_known(v___x_1219_, 1);
v___x_1230_ = l_Lean_MVarId_deltaTarget(v_mvarId_1209_, v___f_1217_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
return v___x_1230_;
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_mvarId_1209_);
v_a_1231_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1215_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1215_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object* v_mvarId_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_mvarId_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
return v_res_1245_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = l_Lean_maxRecDepthErrorMessage;
v___x_1252_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3);
v___x_1254_ = l_Lean_MessageData_ofFormat(v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4);
v___x_1256_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2));
v___x_1257_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v___x_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(lean_object* v_ref_1258_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v_ref_1258_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___boxed(lean_object* v_ref_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object* v_00_u03b1_1266_, lean_object* v_ref_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1267_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_ref_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v_00_u03b1_1274_, v_ref_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object* v_a_1282_, lean_object* v_____r_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_mk_empty_array_with_capacity(v___x_1289_);
v___x_1291_ = lean_array_push(v___x_1290_, v_a_1282_);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object* v_a_1293_, lean_object* v_____r_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1293_, v_____r_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1300_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1301_; double v___x_1302_; 
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_float_of_nat(v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object* v_cls_1306_, lean_object* v_msg_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_ref_1313_; lean_object* v___x_1314_; lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1359_; 
v_ref_1313_ = lean_ctor_get(v___y_1310_, 4);
v___x_1314_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1359_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1359_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v_traceState_1320_; lean_object* v_env_1321_; lean_object* v_nextMacroScope_1322_; lean_object* v_ngen_1323_; lean_object* v_auxDeclNGen_1324_; lean_object* v_cache_1325_; lean_object* v_messages_1326_; lean_object* v_infoState_1327_; lean_object* v_snapshotTasks_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1358_; 
v___x_1319_ = lean_st_ref_take(v___y_1311_);
v_traceState_1320_ = lean_ctor_get(v___x_1319_, 4);
v_env_1321_ = lean_ctor_get(v___x_1319_, 0);
v_nextMacroScope_1322_ = lean_ctor_get(v___x_1319_, 1);
v_ngen_1323_ = lean_ctor_get(v___x_1319_, 2);
v_auxDeclNGen_1324_ = lean_ctor_get(v___x_1319_, 3);
v_cache_1325_ = lean_ctor_get(v___x_1319_, 5);
v_messages_1326_ = lean_ctor_get(v___x_1319_, 6);
v_infoState_1327_ = lean_ctor_get(v___x_1319_, 7);
v_snapshotTasks_1328_ = lean_ctor_get(v___x_1319_, 8);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1330_ = v___x_1319_;
v_isShared_1331_ = v_isSharedCheck_1358_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_snapshotTasks_1328_);
lean_inc(v_infoState_1327_);
lean_inc(v_messages_1326_);
lean_inc(v_cache_1325_);
lean_inc(v_traceState_1320_);
lean_inc(v_auxDeclNGen_1324_);
lean_inc(v_ngen_1323_);
lean_inc(v_nextMacroScope_1322_);
lean_inc(v_env_1321_);
lean_dec(v___x_1319_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1358_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
uint64_t v_tid_1332_; lean_object* v_traces_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1357_; 
v_tid_1332_ = lean_ctor_get_uint64(v_traceState_1320_, sizeof(void*)*1);
v_traces_1333_ = lean_ctor_get(v_traceState_1320_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_traceState_1320_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1335_ = v_traceState_1320_;
v_isShared_1336_ = v_isSharedCheck_1357_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_traces_1333_);
lean_dec(v_traceState_1320_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1357_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; double v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0);
v___x_1339_ = 0;
v___x_1340_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1));
v___x_1341_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1341_, 0, v_cls_1306_);
lean_ctor_set(v___x_1341_, 1, v___x_1337_);
lean_ctor_set(v___x_1341_, 2, v___x_1340_);
lean_ctor_set_float(v___x_1341_, sizeof(void*)*3, v___x_1338_);
lean_ctor_set_float(v___x_1341_, sizeof(void*)*3 + 8, v___x_1338_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*3 + 16, v___x_1339_);
v___x_1342_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2));
v___x_1343_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v_a_1315_);
lean_ctor_set(v___x_1343_, 2, v___x_1342_);
lean_inc(v_ref_1313_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_ref_1313_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = l_Lean_PersistentArray_push___redArg(v_traces_1333_, v___x_1344_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1345_);
v___x_1347_ = v___x_1335_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1345_);
lean_ctor_set_uint64(v_reuseFailAlloc_1356_, sizeof(void*)*1, v_tid_1332_);
v___x_1347_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1349_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 4, v___x_1347_);
v___x_1349_ = v___x_1330_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_env_1321_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_nextMacroScope_1322_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_ngen_1323_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_auxDeclNGen_1324_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1355_, 5, v_cache_1325_);
lean_ctor_set(v_reuseFailAlloc_1355_, 6, v_messages_1326_);
lean_ctor_set(v_reuseFailAlloc_1355_, 7, v_infoState_1327_);
lean_ctor_set(v_reuseFailAlloc_1355_, 8, v_snapshotTasks_1328_);
v___x_1349_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = lean_st_ref_put(v___y_1311_, v___x_1349_);
v___x_1351_ = lean_box(0);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1351_);
v___x_1353_ = v___x_1317_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object* v_cls_1360_, lean_object* v_msg_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1360_, v_msg_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0));
v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2));
v___x_1373_ = l_Lean_stringToMessageData(v___x_1372_);
return v___x_1373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4));
v___x_1376_ = l_Lean_stringToMessageData(v___x_1375_);
return v___x_1376_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1379_ = l_Lean_stringToMessageData(v___x_1378_);
return v___x_1379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16(void){
_start:
{
lean_object* v_cls_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_cls_1393_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1394_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15));
v___x_1395_ = l_Lean_Name_append(v___x_1394_, v_cls_1393_);
return v___x_1395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17));
v___x_1398_ = l_Lean_stringToMessageData(v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1399_, lean_object* v_mvarId_1400_, lean_object* v_depth_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v_a_1412_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; uint8_t v___y_1449_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; uint8_t v___y_1474_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v_a_1498_; lean_object* v___y_1502_; lean_object* v___y_1503_; uint8_t v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; uint8_t v___y_1510_; lean_object* v___y_1545_; lean_object* v___y_1546_; uint8_t v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v_a_1552_; lean_object* v___y_1556_; lean_object* v___y_1557_; uint8_t v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; uint8_t v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; uint8_t v___y_1575_; lean_object* v___y_1599_; lean_object* v___y_1600_; uint8_t v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; uint8_t v___y_1607_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; uint8_t v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; uint8_t v___y_1632_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; uint8_t v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; uint8_t v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; uint8_t v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v_toCold_1763_; lean_object* v_options_1764_; lean_object* v_currRecDepth_1765_; lean_object* v_maxRecDepth_1766_; lean_object* v_ref_1767_; lean_object* v_currNamespace_1768_; lean_object* v_openDecls_1769_; lean_object* v_initHeartbeats_1770_; lean_object* v_maxHeartbeats_1771_; lean_object* v_currMacroScope_1772_; uint8_t v_diag_1773_; uint8_t v_suppressElabErrors_1774_; lean_object* v_cls_1775_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_toCold_1763_ = lean_ctor_get(v_a_1404_, 0);
v_options_1764_ = lean_ctor_get(v_a_1404_, 1);
v_currRecDepth_1765_ = lean_ctor_get(v_a_1404_, 2);
v_maxRecDepth_1766_ = lean_ctor_get(v_a_1404_, 3);
v_ref_1767_ = lean_ctor_get(v_a_1404_, 4);
v_currNamespace_1768_ = lean_ctor_get(v_a_1404_, 5);
v_openDecls_1769_ = lean_ctor_get(v_a_1404_, 6);
v_initHeartbeats_1770_ = lean_ctor_get(v_a_1404_, 7);
v_maxHeartbeats_1771_ = lean_ctor_get(v_a_1404_, 8);
v_currMacroScope_1772_ = lean_ctor_get(v_a_1404_, 9);
v_diag_1773_ = lean_ctor_get_uint8(v_a_1404_, sizeof(void*)*10);
v_suppressElabErrors_1774_ = lean_ctor_get_uint8(v_a_1404_, sizeof(void*)*10 + 1);
v_cls_1775_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_nat_dec_eq(v_maxRecDepth_1766_, v___x_1788_);
if (v___x_1789_ == 0)
{
uint8_t v___x_1790_; 
v___x_1790_ = lean_nat_dec_eq(v_currRecDepth_1765_, v_maxRecDepth_1766_);
if (v___x_1790_ == 0)
{
goto v___jp_1776_;
}
else
{
lean_object* v___x_1791_; 
lean_dec(v_mvarId_1400_);
lean_dec(v_matchDeclName_1399_);
lean_inc(v_ref_1767_);
v___x_1791_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1767_);
return v___x_1791_;
}
}
else
{
goto v___jp_1776_;
}
v___jp_1407_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = lean_array_get_size(v_a_1412_);
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_nat_dec_lt(v___x_1413_, v___x_1414_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
lean_dec_ref(v_a_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v_matchDeclName_1399_);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
return v___x_1417_;
}
else
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_nat_dec_le(v___x_1414_, v___x_1414_);
if (v___x_1418_ == 0)
{
if (v___x_1416_ == 0)
{
lean_object* v___x_1419_; 
lean_dec_ref(v_a_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v_matchDeclName_1399_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1415_);
return v___x_1419_;
}
else
{
size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = lean_usize_of_nat(v___x_1414_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1401_, v_matchDeclName_1399_, v_a_1412_, v___x_1420_, v___x_1421_, v___x_1415_, v___y_1409_, v___y_1408_, v___y_1411_, v___y_1410_);
lean_dec_ref(v___y_1411_);
lean_dec_ref(v_a_1412_);
return v___x_1422_;
}
}
else
{
size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = lean_usize_of_nat(v___x_1414_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1401_, v_matchDeclName_1399_, v_a_1412_, v___x_1423_, v___x_1424_, v___x_1415_, v___y_1409_, v___y_1408_, v___y_1411_, v___y_1410_);
lean_dec_ref(v___y_1411_);
lean_dec_ref(v_a_1412_);
return v___x_1425_;
}
}
}
v___jp_1426_:
{
if (lean_obj_tag(v___y_1431_) == 0)
{
lean_object* v_a_1432_; 
v_a_1432_ = lean_ctor_get(v___y_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___y_1431_, 1);
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
v___y_1410_ = v___y_1429_;
v___y_1411_ = v___y_1430_;
v_a_1412_ = v_a_1432_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v___y_1430_);
lean_dec(v_matchDeclName_1399_);
v_a_1433_ = lean_ctor_get(v___y_1431_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___y_1431_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___y_1431_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___y_1431_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
v___jp_1441_:
{
if (v___y_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_dec_ref(v___y_1442_);
v___x_1450_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1445_, v___y_1444_, v___y_1447_);
lean_dec_ref(v___y_1445_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1464_; 
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v___x_1450_, 0);
lean_dec(v_unused_1465_);
v___x_1452_ = v___x_1450_;
v_isShared_1453_ = v_isSharedCheck_1464_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v___x_1450_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1464_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1454_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1399_);
v___x_1455_ = l_Lean_MessageData_ofName(v_matchDeclName_1399_);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3);
v___x_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set_tag(v___x_1452_, 1);
lean_ctor_set(v___x_1452_, 0, v___y_1443_);
v___x_1460_ = v___x_1452_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___y_1443_);
v___x_1460_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1458_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1461_, v___y_1446_, v___y_1444_, v___y_1448_, v___y_1447_);
v___y_1427_ = v___y_1444_;
v___y_1428_ = v___y_1446_;
v___y_1429_ = v___y_1447_;
v___y_1430_ = v___y_1448_;
v___y_1431_ = v___x_1462_;
goto v___jp_1426_;
}
}
}
else
{
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1443_);
lean_dec(v_matchDeclName_1399_);
return v___x_1450_;
}
}
else
{
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1443_);
v___y_1427_ = v___y_1444_;
v___y_1428_ = v___y_1446_;
v___y_1429_ = v___y_1447_;
v___y_1430_ = v___y_1448_;
v___y_1431_ = v___y_1442_;
goto v___jp_1426_;
}
}
v___jp_1466_:
{
if (v___y_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_dec_ref(v___y_1469_);
v___x_1475_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1470_, v___y_1468_, v___y_1472_);
lean_dec_ref(v___y_1470_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v___x_1476_; 
lean_dec_ref_known(v___x_1475_, 1);
v___x_1476_ = l_Lean_Meta_saveState___redArg(v___y_1468_, v___y_1472_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
lean_inc(v___y_1467_);
v___x_1478_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1467_, v___y_1471_, v___y_1468_, v___y_1473_, v___y_1472_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_dec(v_a_1477_);
lean_dec(v___y_1467_);
v___y_1427_ = v___y_1468_;
v___y_1428_ = v___y_1471_;
v___y_1429_ = v___y_1472_;
v___y_1430_ = v___y_1473_;
v___y_1431_ = v___x_1478_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1479_; uint8_t v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
v___x_1480_ = l_Lean_Exception_isInterrupt(v_a_1479_);
if (v___x_1480_ == 0)
{
uint8_t v___x_1481_; 
v___x_1481_ = l_Lean_Exception_isRuntime(v_a_1479_);
v___y_1442_ = v___x_1478_;
v___y_1443_ = v___y_1467_;
v___y_1444_ = v___y_1468_;
v___y_1445_ = v_a_1477_;
v___y_1446_ = v___y_1471_;
v___y_1447_ = v___y_1472_;
v___y_1448_ = v___y_1473_;
v___y_1449_ = v___x_1481_;
goto v___jp_1441_;
}
else
{
lean_dec(v_a_1479_);
v___y_1442_ = v___x_1478_;
v___y_1443_ = v___y_1467_;
v___y_1444_ = v___y_1468_;
v___y_1445_ = v_a_1477_;
v___y_1446_ = v___y_1471_;
v___y_1447_ = v___y_1472_;
v___y_1448_ = v___y_1473_;
v___y_1449_ = v___x_1480_;
goto v___jp_1441_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1467_);
lean_dec(v_matchDeclName_1399_);
v_a_1482_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1476_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1476_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
else
{
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1467_);
lean_dec(v_matchDeclName_1399_);
return v___x_1475_;
}
}
else
{
lean_object* v___x_1490_; 
lean_dec_ref(v___y_1473_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1467_);
lean_dec(v_matchDeclName_1399_);
v___x_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1469_);
return v___x_1490_;
}
}
v___jp_1491_:
{
uint8_t v___x_1499_; 
v___x_1499_ = l_Lean_Exception_isInterrupt(v_a_1498_);
if (v___x_1499_ == 0)
{
uint8_t v___x_1500_; 
lean_inc_ref(v_a_1498_);
v___x_1500_ = l_Lean_Exception_isRuntime(v_a_1498_);
v___y_1467_ = v___y_1493_;
v___y_1468_ = v___y_1492_;
v___y_1469_ = v_a_1498_;
v___y_1470_ = v___y_1494_;
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___y_1496_;
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___x_1500_;
goto v___jp_1466_;
}
else
{
v___y_1467_ = v___y_1493_;
v___y_1468_ = v___y_1492_;
v___y_1469_ = v_a_1498_;
v___y_1470_ = v___y_1494_;
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___y_1496_;
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___x_1499_;
goto v___jp_1466_;
}
}
v___jp_1501_:
{
if (v___y_1510_ == 0)
{
lean_object* v___x_1511_; 
lean_dec_ref(v___y_1506_);
v___x_1511_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1509_, v___y_1503_, v___y_1507_);
lean_dec_ref(v___y_1509_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v___x_1512_; 
lean_dec_ref_known(v___x_1511_, 1);
v___x_1512_ = l_Lean_Meta_saveState___redArg(v___y_1503_, v___y_1507_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = lean_box(0);
lean_inc(v___y_1502_);
v___x_1515_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1502_, v___x_1514_, v___y_1504_, v___y_1505_, v___y_1503_, v___y_1508_, v___y_1507_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
if (lean_obj_tag(v_a_1516_) == 1)
{
lean_object* v_val_1517_; lean_object* v_fst_1518_; lean_object* v_snd_1519_; lean_object* v_mvarId_1520_; lean_object* v_fvarId_1521_; lean_object* v___x_1522_; 
v_val_1517_ = lean_ctor_get(v_a_1516_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v_a_1516_, 1);
v_fst_1518_ = lean_ctor_get(v_val_1517_, 0);
lean_inc(v_fst_1518_);
v_snd_1519_ = lean_ctor_get(v_val_1517_, 1);
lean_inc(v_snd_1519_);
lean_dec(v_val_1517_);
v_mvarId_1520_ = lean_ctor_get(v_fst_1518_, 0);
lean_inc(v_mvarId_1520_);
v_fvarId_1521_ = lean_ctor_get(v_fst_1518_, 1);
lean_inc(v_fvarId_1521_);
lean_dec(v_fst_1518_);
v___x_1522_ = l_Lean_Meta_trySubst(v_mvarId_1520_, v_fvarId_1521_, v___y_1505_, v___y_1503_, v___y_1508_, v___y_1507_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v_mvarId_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec(v_a_1513_);
lean_dec(v___y_1502_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v_mvarId_1524_ = lean_ctor_get(v_snd_1519_, 0);
lean_inc(v_mvarId_1524_);
lean_dec(v_snd_1519_);
v___x_1525_ = lean_unsigned_to_nat(2u);
v___x_1526_ = lean_mk_empty_array_with_capacity(v___x_1525_);
v___x_1527_ = lean_array_push(v___x_1526_, v_a_1523_);
v___x_1528_ = lean_array_push(v___x_1527_, v_mvarId_1524_);
v___y_1408_ = v___y_1503_;
v___y_1409_ = v___y_1505_;
v___y_1410_ = v___y_1507_;
v___y_1411_ = v___y_1508_;
v_a_1412_ = v___x_1528_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1529_; 
lean_dec(v_snd_1519_);
v_a_1529_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1522_, 1);
v___y_1492_ = v___y_1503_;
v___y_1493_ = v___y_1502_;
v___y_1494_ = v_a_1513_;
v___y_1495_ = v___y_1505_;
v___y_1496_ = v___y_1507_;
v___y_1497_ = v___y_1508_;
v_a_1498_ = v_a_1529_;
goto v___jp_1491_;
}
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_a_1516_);
v___x_1530_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1531_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1530_, v___y_1505_, v___y_1503_, v___y_1508_, v___y_1507_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; 
lean_dec(v_a_1513_);
lean_dec(v___y_1502_);
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___y_1408_ = v___y_1503_;
v___y_1409_ = v___y_1505_;
v___y_1410_ = v___y_1507_;
v___y_1411_ = v___y_1508_;
v_a_1412_ = v_a_1532_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1533_; 
v_a_1533_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1531_, 1);
v___y_1492_ = v___y_1503_;
v___y_1493_ = v___y_1502_;
v___y_1494_ = v_a_1513_;
v___y_1495_ = v___y_1505_;
v___y_1496_ = v___y_1507_;
v___y_1497_ = v___y_1508_;
v_a_1498_ = v_a_1533_;
goto v___jp_1491_;
}
}
}
else
{
lean_object* v_a_1534_; 
v_a_1534_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1515_, 1);
v___y_1492_ = v___y_1503_;
v___y_1493_ = v___y_1502_;
v___y_1494_ = v_a_1513_;
v___y_1495_ = v___y_1505_;
v___y_1496_ = v___y_1507_;
v___y_1497_ = v___y_1508_;
v_a_1498_ = v_a_1534_;
goto v___jp_1491_;
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1502_);
lean_dec(v_matchDeclName_1399_);
v_a_1535_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1512_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1512_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1502_);
lean_dec(v_matchDeclName_1399_);
return v___x_1511_;
}
}
else
{
lean_object* v___x_1543_; 
lean_dec_ref(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1502_);
lean_dec(v_matchDeclName_1399_);
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___y_1506_);
return v___x_1543_;
}
}
v___jp_1544_:
{
uint8_t v___x_1553_; 
v___x_1553_ = l_Lean_Exception_isInterrupt(v_a_1552_);
if (v___x_1553_ == 0)
{
uint8_t v___x_1554_; 
lean_inc_ref(v_a_1552_);
v___x_1554_ = l_Lean_Exception_isRuntime(v_a_1552_);
v___y_1502_ = v___y_1546_;
v___y_1503_ = v___y_1545_;
v___y_1504_ = v___y_1547_;
v___y_1505_ = v___y_1548_;
v___y_1506_ = v_a_1552_;
v___y_1507_ = v___y_1549_;
v___y_1508_ = v___y_1550_;
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___x_1554_;
goto v___jp_1501_;
}
else
{
v___y_1502_ = v___y_1546_;
v___y_1503_ = v___y_1545_;
v___y_1504_ = v___y_1547_;
v___y_1505_ = v___y_1548_;
v___y_1506_ = v_a_1552_;
v___y_1507_ = v___y_1549_;
v___y_1508_ = v___y_1550_;
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___x_1553_;
goto v___jp_1501_;
}
}
v___jp_1555_:
{
if (lean_obj_tag(v___y_1563_) == 0)
{
lean_object* v_a_1564_; 
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1556_);
v_a_1564_ = lean_ctor_get(v___y_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___y_1563_, 1);
v___y_1408_ = v___y_1557_;
v___y_1409_ = v___y_1559_;
v___y_1410_ = v___y_1560_;
v___y_1411_ = v___y_1561_;
v_a_1412_ = v_a_1564_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1565_; 
v_a_1565_ = lean_ctor_get(v___y_1563_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___y_1563_, 1);
v___y_1545_ = v___y_1557_;
v___y_1546_ = v___y_1556_;
v___y_1547_ = v___y_1558_;
v___y_1548_ = v___y_1559_;
v___y_1549_ = v___y_1560_;
v___y_1550_ = v___y_1561_;
v___y_1551_ = v___y_1562_;
v_a_1552_ = v_a_1565_;
goto v___jp_1544_;
}
}
v___jp_1566_:
{
if (v___y_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref(v___y_1567_);
v___x_1576_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1574_, v___y_1569_, v___y_1572_);
lean_dec_ref(v___y_1574_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref_known(v___x_1576_, 1);
v___x_1577_ = l_Lean_Meta_saveState___redArg(v___y_1569_, v___y_1572_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
lean_inc(v___y_1568_);
v___x_1579_ = l_Lean_Meta_simpIfTarget(v___y_1568_, v___y_1570_, v___y_1570_, v___y_1571_, v___y_1569_, v___y_1573_, v___y_1572_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; uint8_t v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = l_Lean_instBEqMVarId_beq(v_a_1580_, v___y_1568_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1580_, v___x_1582_, v___y_1571_, v___y_1569_, v___y_1573_, v___y_1572_);
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1569_;
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___y_1571_;
v___y_1560_ = v___y_1572_;
v___y_1561_ = v___y_1573_;
v___y_1562_ = v_a_1578_;
v___y_1563_ = v___x_1583_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1585_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1584_, v___y_1571_, v___y_1569_, v___y_1573_, v___y_1572_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1580_, v_a_1586_, v___y_1571_, v___y_1569_, v___y_1573_, v___y_1572_);
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1569_;
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___y_1571_;
v___y_1560_ = v___y_1572_;
v___y_1561_ = v___y_1573_;
v___y_1562_ = v_a_1578_;
v___y_1563_ = v___x_1587_;
goto v___jp_1555_;
}
else
{
lean_object* v_a_1588_; 
lean_dec(v_a_1580_);
v_a_1588_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1585_, 1);
v___y_1545_ = v___y_1569_;
v___y_1546_ = v___y_1568_;
v___y_1547_ = v___y_1570_;
v___y_1548_ = v___y_1571_;
v___y_1549_ = v___y_1572_;
v___y_1550_ = v___y_1573_;
v___y_1551_ = v_a_1578_;
v_a_1552_ = v_a_1588_;
goto v___jp_1544_;
}
}
}
else
{
lean_object* v_a_1589_; 
v_a_1589_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1579_, 1);
v___y_1545_ = v___y_1569_;
v___y_1546_ = v___y_1568_;
v___y_1547_ = v___y_1570_;
v___y_1548_ = v___y_1571_;
v___y_1549_ = v___y_1572_;
v___y_1550_ = v___y_1573_;
v___y_1551_ = v_a_1578_;
v_a_1552_ = v_a_1589_;
goto v___jp_1544_;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1568_);
lean_dec(v_matchDeclName_1399_);
v_a_1590_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1577_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1577_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1568_);
lean_dec(v_matchDeclName_1399_);
return v___x_1576_;
}
}
else
{
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1568_);
v___y_1427_ = v___y_1569_;
v___y_1428_ = v___y_1571_;
v___y_1429_ = v___y_1572_;
v___y_1430_ = v___y_1573_;
v___y_1431_ = v___y_1567_;
goto v___jp_1426_;
}
}
v___jp_1598_:
{
if (v___y_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref(v___y_1606_);
v___x_1608_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1604_, v___y_1600_, v___y_1603_);
lean_dec_ref(v___y_1604_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref_known(v___x_1608_, 1);
v___x_1609_ = l_Lean_Meta_saveState___redArg(v___y_1600_, v___y_1603_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
lean_inc(v___y_1599_);
v___x_1611_ = l_Lean_Meta_splitSparseCasesOn(v___y_1599_, v___y_1602_, v___y_1600_, v___y_1605_, v___y_1603_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_dec(v_a_1610_);
lean_dec(v___y_1599_);
v___y_1427_ = v___y_1600_;
v___y_1428_ = v___y_1602_;
v___y_1429_ = v___y_1603_;
v___y_1430_ = v___y_1605_;
v___y_1431_ = v___x_1611_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1612_; uint8_t v___x_1613_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
v___x_1613_ = l_Lean_Exception_isInterrupt(v_a_1612_);
if (v___x_1613_ == 0)
{
uint8_t v___x_1614_; 
v___x_1614_ = l_Lean_Exception_isRuntime(v_a_1612_);
v___y_1567_ = v___x_1611_;
v___y_1568_ = v___y_1599_;
v___y_1569_ = v___y_1600_;
v___y_1570_ = v___y_1601_;
v___y_1571_ = v___y_1602_;
v___y_1572_ = v___y_1603_;
v___y_1573_ = v___y_1605_;
v___y_1574_ = v_a_1610_;
v___y_1575_ = v___x_1614_;
goto v___jp_1566_;
}
else
{
lean_dec(v_a_1612_);
v___y_1567_ = v___x_1611_;
v___y_1568_ = v___y_1599_;
v___y_1569_ = v___y_1600_;
v___y_1570_ = v___y_1601_;
v___y_1571_ = v___y_1602_;
v___y_1572_ = v___y_1603_;
v___y_1573_ = v___y_1605_;
v___y_1574_ = v_a_1610_;
v___y_1575_ = v___x_1613_;
goto v___jp_1566_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1599_);
lean_dec(v_matchDeclName_1399_);
v_a_1615_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1609_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1609_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1599_);
lean_dec(v_matchDeclName_1399_);
return v___x_1608_;
}
}
else
{
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1599_);
v___y_1427_ = v___y_1600_;
v___y_1428_ = v___y_1602_;
v___y_1429_ = v___y_1603_;
v___y_1430_ = v___y_1605_;
v___y_1431_ = v___y_1606_;
goto v___jp_1426_;
}
}
v___jp_1623_:
{
if (v___y_1632_ == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref(v___y_1624_);
v___x_1633_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1630_, v___y_1626_, v___y_1629_);
lean_dec_ref(v___y_1630_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref_known(v___x_1633_, 1);
v___x_1634_ = l_Lean_Meta_saveState___redArg(v___y_1626_, v___y_1629_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1636_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
lean_inc(v___y_1625_);
v___x_1636_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1625_, v___y_1628_, v___y_1626_, v___y_1631_, v___y_1629_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_dec(v_a_1635_);
lean_dec(v___y_1625_);
v___y_1427_ = v___y_1626_;
v___y_1428_ = v___y_1628_;
v___y_1429_ = v___y_1629_;
v___y_1430_ = v___y_1631_;
v___y_1431_ = v___x_1636_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1637_; uint8_t v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
v___x_1638_ = l_Lean_Exception_isInterrupt(v_a_1637_);
if (v___x_1638_ == 0)
{
uint8_t v___x_1639_; 
v___x_1639_ = l_Lean_Exception_isRuntime(v_a_1637_);
v___y_1599_ = v___y_1625_;
v___y_1600_ = v___y_1626_;
v___y_1601_ = v___y_1627_;
v___y_1602_ = v___y_1628_;
v___y_1603_ = v___y_1629_;
v___y_1604_ = v_a_1635_;
v___y_1605_ = v___y_1631_;
v___y_1606_ = v___x_1636_;
v___y_1607_ = v___x_1639_;
goto v___jp_1598_;
}
else
{
lean_dec(v_a_1637_);
v___y_1599_ = v___y_1625_;
v___y_1600_ = v___y_1626_;
v___y_1601_ = v___y_1627_;
v___y_1602_ = v___y_1628_;
v___y_1603_ = v___y_1629_;
v___y_1604_ = v_a_1635_;
v___y_1605_ = v___y_1631_;
v___y_1606_ = v___x_1636_;
v___y_1607_ = v___x_1638_;
goto v___jp_1598_;
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1625_);
lean_dec(v_matchDeclName_1399_);
v_a_1640_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1634_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1634_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
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
else
{
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1625_);
lean_dec(v_matchDeclName_1399_);
return v___x_1633_;
}
}
else
{
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1625_);
v___y_1427_ = v___y_1626_;
v___y_1428_ = v___y_1628_;
v___y_1429_ = v___y_1629_;
v___y_1430_ = v___y_1631_;
v___y_1431_ = v___y_1624_;
goto v___jp_1426_;
}
}
v___jp_1648_:
{
if (v___y_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref(v___y_1652_);
v___x_1658_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1649_, v___y_1651_, v___y_1655_);
lean_dec_ref(v___y_1649_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v___x_1659_; 
lean_dec_ref_known(v___x_1658_, 1);
v___x_1659_ = l_Lean_Meta_saveState___redArg(v___y_1651_, v___y_1655_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1661_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
lean_inc(v___y_1650_);
v___x_1661_ = l_Lean_Meta_casesOnStuckLHS(v___y_1650_, v___y_1654_, v___y_1651_, v___y_1656_, v___y_1655_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_dec(v_a_1660_);
lean_dec(v___y_1650_);
v___y_1427_ = v___y_1651_;
v___y_1428_ = v___y_1654_;
v___y_1429_ = v___y_1655_;
v___y_1430_ = v___y_1656_;
v___y_1431_ = v___x_1661_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1662_; uint8_t v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
v___x_1663_ = l_Lean_Exception_isInterrupt(v_a_1662_);
if (v___x_1663_ == 0)
{
uint8_t v___x_1664_; 
v___x_1664_ = l_Lean_Exception_isRuntime(v_a_1662_);
v___y_1624_ = v___x_1661_;
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___y_1653_;
v___y_1628_ = v___y_1654_;
v___y_1629_ = v___y_1655_;
v___y_1630_ = v_a_1660_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___x_1664_;
goto v___jp_1623_;
}
else
{
lean_dec(v_a_1662_);
v___y_1624_ = v___x_1661_;
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___y_1653_;
v___y_1628_ = v___y_1654_;
v___y_1629_ = v___y_1655_;
v___y_1630_ = v_a_1660_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___x_1663_;
goto v___jp_1623_;
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1650_);
lean_dec(v_matchDeclName_1399_);
v_a_1665_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1659_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1659_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1650_);
lean_dec(v_matchDeclName_1399_);
return v___x_1658_;
}
}
else
{
lean_object* v___x_1673_; 
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v_matchDeclName_1399_);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___y_1652_);
return v___x_1673_;
}
}
v___jp_1674_:
{
if (v___y_1683_ == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref(v___y_1682_);
v___x_1684_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1675_, v___y_1677_, v___y_1680_);
lean_dec_ref(v___y_1675_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v___x_1685_; 
lean_dec_ref_known(v___x_1684_, 1);
v___x_1685_ = l_Lean_Meta_saveState___redArg(v___y_1677_, v___y_1680_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1685_, 1);
lean_inc(v___y_1676_);
v___x_1687_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1676_, v___y_1679_, v___y_1677_, v___y_1681_, v___y_1680_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_a_1686_);
lean_dec(v___y_1676_);
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_mk_empty_array_with_capacity(v___x_1689_);
v___x_1691_ = lean_array_push(v___x_1690_, v_a_1688_);
v___y_1408_ = v___y_1677_;
v___y_1409_ = v___y_1679_;
v___y_1410_ = v___y_1680_;
v___y_1411_ = v___y_1681_;
v_a_1412_ = v___x_1691_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1692_; uint8_t v___x_1693_; 
v_a_1692_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1693_ = l_Lean_Exception_isInterrupt(v_a_1692_);
if (v___x_1693_ == 0)
{
uint8_t v___x_1694_; 
lean_inc(v_a_1692_);
v___x_1694_ = l_Lean_Exception_isRuntime(v_a_1692_);
v___y_1649_ = v_a_1686_;
v___y_1650_ = v___y_1676_;
v___y_1651_ = v___y_1677_;
v___y_1652_ = v_a_1692_;
v___y_1653_ = v___y_1678_;
v___y_1654_ = v___y_1679_;
v___y_1655_ = v___y_1680_;
v___y_1656_ = v___y_1681_;
v___y_1657_ = v___x_1694_;
goto v___jp_1648_;
}
else
{
v___y_1649_ = v_a_1686_;
v___y_1650_ = v___y_1676_;
v___y_1651_ = v___y_1677_;
v___y_1652_ = v_a_1692_;
v___y_1653_ = v___y_1678_;
v___y_1654_ = v___y_1679_;
v___y_1655_ = v___y_1680_;
v___y_1656_ = v___y_1681_;
v___y_1657_ = v___x_1693_;
goto v___jp_1648_;
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1676_);
lean_dec(v_matchDeclName_1399_);
v_a_1695_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1685_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1685_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1676_);
lean_dec(v_matchDeclName_1399_);
return v___x_1684_;
}
}
else
{
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v_matchDeclName_1399_);
return v___y_1682_;
}
}
v___jp_1703_:
{
if (v___y_1712_ == 0)
{
lean_object* v___x_1713_; 
lean_dec_ref(v___y_1706_);
v___x_1713_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1711_, v___y_1705_, v___y_1709_);
lean_dec_ref(v___y_1711_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec_ref_known(v___x_1713_, 1);
v___x_1714_ = lean_unsigned_to_nat(16u);
v___x_1715_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*1, v___y_1707_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*1 + 1, v___y_1707_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*1 + 2, v___y_1707_);
v___x_1716_ = l_Lean_Meta_saveState___redArg(v___y_1705_, v___y_1709_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
lean_inc(v___y_1704_);
v___x_1718_ = l_Lean_MVarId_contradiction(v___y_1704_, v___x_1715_, v___y_1708_, v___y_1705_, v___y_1710_, v___y_1709_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v___x_1719_; 
lean_dec_ref_known(v___x_1718_, 1);
lean_dec(v_a_1717_);
lean_dec(v___y_1704_);
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1408_ = v___y_1705_;
v___y_1409_ = v___y_1708_;
v___y_1410_ = v___y_1709_;
v___y_1411_ = v___y_1710_;
v_a_1412_ = v___x_1719_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1720_; uint8_t v___x_1721_; 
v_a_1720_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1720_);
v___x_1721_ = l_Lean_Exception_isInterrupt(v_a_1720_);
if (v___x_1721_ == 0)
{
uint8_t v___x_1722_; 
v___x_1722_ = l_Lean_Exception_isRuntime(v_a_1720_);
v___y_1675_ = v_a_1717_;
v___y_1676_ = v___y_1704_;
v___y_1677_ = v___y_1705_;
v___y_1678_ = v___y_1707_;
v___y_1679_ = v___y_1708_;
v___y_1680_ = v___y_1709_;
v___y_1681_ = v___y_1710_;
v___y_1682_ = v___x_1718_;
v___y_1683_ = v___x_1722_;
goto v___jp_1674_;
}
else
{
lean_dec(v_a_1720_);
v___y_1675_ = v_a_1717_;
v___y_1676_ = v___y_1704_;
v___y_1677_ = v___y_1705_;
v___y_1678_ = v___y_1707_;
v___y_1679_ = v___y_1708_;
v___y_1680_ = v___y_1709_;
v___y_1681_ = v___y_1710_;
v___y_1682_ = v___x_1718_;
v___y_1683_ = v___x_1721_;
goto v___jp_1674_;
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref_known(v___x_1715_, 1);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1704_);
lean_dec(v_matchDeclName_1399_);
v_a_1723_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1716_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1716_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1704_);
lean_dec(v_matchDeclName_1399_);
return v___x_1713_;
}
}
else
{
lean_dec_ref(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1704_);
lean_dec(v_matchDeclName_1399_);
return v___y_1706_;
}
}
v___jp_1731_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1737_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1400_, v___x_1736_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1739_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v___x_1739_ = l_Lean_Meta_saveState___redArg(v___y_1733_, v___y_1735_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = 1;
lean_inc(v_a_1738_);
v___x_1742_ = l_Lean_MVarId_refl(v_a_1738_, v___x_1741_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v___x_1743_; 
lean_dec_ref_known(v___x_1742_, 1);
lean_dec(v_a_1740_);
lean_dec(v_a_1738_);
v___x_1743_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1408_ = v___y_1733_;
v___y_1409_ = v___y_1732_;
v___y_1410_ = v___y_1735_;
v___y_1411_ = v___y_1734_;
v_a_1412_ = v___x_1743_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1744_; uint8_t v___x_1745_; 
v_a_1744_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1744_);
v___x_1745_ = l_Lean_Exception_isInterrupt(v_a_1744_);
if (v___x_1745_ == 0)
{
uint8_t v___x_1746_; 
v___x_1746_ = l_Lean_Exception_isRuntime(v_a_1744_);
v___y_1704_ = v_a_1738_;
v___y_1705_ = v___y_1733_;
v___y_1706_ = v___x_1742_;
v___y_1707_ = v___x_1741_;
v___y_1708_ = v___y_1732_;
v___y_1709_ = v___y_1735_;
v___y_1710_ = v___y_1734_;
v___y_1711_ = v_a_1740_;
v___y_1712_ = v___x_1746_;
goto v___jp_1703_;
}
else
{
lean_dec(v_a_1744_);
v___y_1704_ = v_a_1738_;
v___y_1705_ = v___y_1733_;
v___y_1706_ = v___x_1742_;
v___y_1707_ = v___x_1741_;
v___y_1708_ = v___y_1732_;
v___y_1709_ = v___y_1735_;
v___y_1710_ = v___y_1734_;
v___y_1711_ = v_a_1740_;
v___y_1712_ = v___x_1745_;
goto v___jp_1703_;
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_a_1738_);
lean_dec_ref(v___y_1734_);
lean_dec(v_matchDeclName_1399_);
v_a_1747_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1739_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1739_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref(v___y_1734_);
lean_dec(v_matchDeclName_1399_);
v_a_1755_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1737_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1737_);
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
v___jp_1776_:
{
uint8_t v_hasTrace_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v_hasTrace_1777_ = lean_ctor_get_uint8(v_options_1764_, sizeof(void*)*1);
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_nat_add(v_currRecDepth_1765_, v___x_1778_);
lean_inc(v_currMacroScope_1772_);
lean_inc(v_maxHeartbeats_1771_);
lean_inc(v_initHeartbeats_1770_);
lean_inc(v_openDecls_1769_);
lean_inc(v_currNamespace_1768_);
lean_inc(v_ref_1767_);
lean_inc(v_maxRecDepth_1766_);
lean_inc_ref(v_options_1764_);
lean_inc_ref(v_toCold_1763_);
v___x_1780_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1780_, 0, v_toCold_1763_);
lean_ctor_set(v___x_1780_, 1, v_options_1764_);
lean_ctor_set(v___x_1780_, 2, v___x_1779_);
lean_ctor_set(v___x_1780_, 3, v_maxRecDepth_1766_);
lean_ctor_set(v___x_1780_, 4, v_ref_1767_);
lean_ctor_set(v___x_1780_, 5, v_currNamespace_1768_);
lean_ctor_set(v___x_1780_, 6, v_openDecls_1769_);
lean_ctor_set(v___x_1780_, 7, v_initHeartbeats_1770_);
lean_ctor_set(v___x_1780_, 8, v_maxHeartbeats_1771_);
lean_ctor_set(v___x_1780_, 9, v_currMacroScope_1772_);
lean_ctor_set_uint8(v___x_1780_, sizeof(void*)*10, v_diag_1773_);
lean_ctor_set_uint8(v___x_1780_, sizeof(void*)*10 + 1, v_suppressElabErrors_1774_);
if (v_hasTrace_1777_ == 0)
{
v___y_1732_ = v_a_1402_;
v___y_1733_ = v_a_1403_;
v___y_1734_ = v___x_1780_;
v___y_1735_ = v_a_1405_;
goto v___jp_1731_;
}
else
{
lean_object* v_inheritedTraceOptions_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v_inheritedTraceOptions_1781_ = lean_ctor_get(v_toCold_1763_, 4);
v___x_1782_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1783_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1781_, v_options_1764_, v___x_1782_);
if (v___x_1783_ == 0)
{
v___y_1732_ = v_a_1402_;
v___y_1733_ = v_a_1403_;
v___y_1734_ = v___x_1780_;
v___y_1735_ = v_a_1405_;
goto v___jp_1731_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1784_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1400_);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_mvarId_1400_);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1775_, v___x_1786_, v_a_1402_, v_a_1403_, v___x_1780_, v_a_1405_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_dec_ref_known(v___x_1787_, 1);
v___y_1732_ = v_a_1402_;
v___y_1733_ = v_a_1403_;
v___y_1734_ = v___x_1780_;
v___y_1735_ = v_a_1405_;
goto v___jp_1731_;
}
else
{
lean_dec_ref_known(v___x_1780_, 10);
lean_dec(v_mvarId_1400_);
lean_dec(v_matchDeclName_1399_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1980_, lean_object* v___f_1981_, lean_object* v_matchDeclName_1982_, lean_object* v___x_1983_, uint8_t v___x_1984_, lean_object* v_heqPos_1985_, lean_object* v_heqNum_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___x_1992_; lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2145_; 
v___x_1992_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1980_, v___y_1988_);
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2145_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2145_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1993_, v___x_1997_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2144_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2144_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2144_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; uint8_t v___y_2010_; lean_object* v_mvarId_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v_options_2067_; lean_object* v_toCold_2068_; uint8_t v_hasTrace_2069_; lean_object* v___x_2070_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; 
v_options_2067_ = lean_ctor_get(v___y_1989_, 1);
v_toCold_2068_ = lean_ctor_get(v___y_1989_, 0);
v_hasTrace_2069_ = lean_ctor_get_uint8(v_options_2067_, sizeof(void*)*1);
v___x_2070_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2069_ == 0)
{
v___y_2072_ = v___y_1987_;
v___y_2073_ = v___y_1988_;
v___y_2074_ = v___y_1989_;
v___y_2075_ = v___y_1990_;
goto v___jp_2071_;
}
else
{
lean_object* v_inheritedTraceOptions_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v_inheritedTraceOptions_2128_ = lean_ctor_get(v_toCold_2068_, 4);
v___x_2129_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2128_, v_options_2067_, v___x_2129_);
if (v___x_2130_ == 0)
{
v___y_2072_ = v___y_1987_;
v___y_2073_ = v___y_1988_;
v___y_2074_ = v___y_1989_;
v___y_2075_ = v___y_1990_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2131_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2132_ = l_Lean_Expr_mvarId_x21(v_a_1999_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2131_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2070_, v___x_2134_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_dec_ref_known(v___x_2135_, 1);
v___y_2072_ = v___y_1987_;
v___y_2073_ = v___y_1988_;
v___y_2074_ = v___y_1989_;
v___y_2075_ = v___y_1990_;
goto v___jp_2071_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_del_object(v___x_2001_);
lean_dec(v_a_1999_);
lean_del_object(v___x_1995_);
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
v___jp_2003_:
{
if (v___y_2010_ == 0)
{
lean_object* v___x_2011_; 
lean_dec_ref(v___y_2005_);
lean_del_object(v___x_2001_);
v___x_2011_ = l_Lean_MVarId_deltaTarget(v___y_2008_, v___f_1981_, v___y_2009_, v___y_2007_, v___y_2004_, v___y_2006_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = l_Lean_MVarId_heqOfEq(v_a_2012_, v___y_2009_, v___y_2007_, v___y_2004_, v___y_2006_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1982_, v_a_2014_, v___x_1983_, v___y_2009_, v___y_2007_, v___y_2004_, v___y_2006_);
lean_dec(v___x_1983_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2016_; 
lean_dec_ref_known(v___x_2015_, 1);
v___x_2016_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1999_, v___y_2007_);
return v___x_2016_;
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_a_1999_);
v_a_2017_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2015_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2015_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_a_1999_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
v_a_2025_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2013_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2013_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_a_1999_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
v_a_2033_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2011_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2011_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_object* v___x_2042_; 
lean_dec(v___y_2008_);
lean_dec(v_a_1999_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set_tag(v___x_2001_, 1);
lean_ctor_set(v___x_2001_, 0, v___y_2005_);
v___x_2042_ = v___x_2001_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___y_2005_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
v___jp_2044_:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_MVarId_intros(v_mvarId_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v_snd_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v_snd_2052_ = lean_ctor_get(v_a_2051_, 1);
lean_inc_n(v_snd_2052_, 2);
lean_dec(v_a_2051_);
v___x_2053_ = 1;
v___x_2054_ = l_Lean_MVarId_refl(v_snd_2052_, v___x_2053_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2055_; 
lean_dec_ref_known(v___x_2054_, 1);
lean_dec(v_snd_2052_);
lean_del_object(v___x_2001_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v___x_2055_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1999_, v___y_2047_);
return v___x_2055_;
}
else
{
lean_object* v_a_2056_; uint8_t v___x_2057_; 
v_a_2056_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2054_, 1);
v___x_2057_ = l_Lean_Exception_isInterrupt(v_a_2056_);
if (v___x_2057_ == 0)
{
uint8_t v___x_2058_; 
lean_inc(v_a_2056_);
v___x_2058_ = l_Lean_Exception_isRuntime(v_a_2056_);
v___y_2004_ = v___y_2048_;
v___y_2005_ = v_a_2056_;
v___y_2006_ = v___y_2049_;
v___y_2007_ = v___y_2047_;
v___y_2008_ = v_snd_2052_;
v___y_2009_ = v___y_2046_;
v___y_2010_ = v___x_2058_;
goto v___jp_2003_;
}
else
{
v___y_2004_ = v___y_2048_;
v___y_2005_ = v_a_2056_;
v___y_2006_ = v___y_2049_;
v___y_2007_ = v___y_2047_;
v___y_2008_ = v_snd_2052_;
v___y_2009_ = v___y_2046_;
v___y_2010_ = v___x_2057_;
goto v___jp_2003_;
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_del_object(v___x_2001_);
lean_dec(v_a_1999_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v_a_2059_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2050_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2050_);
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
v___jp_2071_:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_Expr_mvarId_x21(v_a_1999_);
if (v___x_1984_ == 0)
{
lean_del_object(v___x_1995_);
lean_dec(v_heqPos_1985_);
v_mvarId_2045_ = v___x_2076_;
v___y_2046_ = v___y_2072_;
v___y_2047_ = v___y_2073_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2077_; uint8_t v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = 0;
v___x_2079_ = l_Lean_Meta_introNCore(v___x_2076_, v_heqPos_1985_, v___x_2077_, v___x_2078_, v___x_2078_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v_snd_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2118_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___x_2079_, 1);
v_snd_2081_ = lean_ctor_get(v_a_2080_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_a_2080_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v_a_2080_, 0);
lean_dec(v_unused_2119_);
v___x_2083_ = v_a_2080_;
v_isShared_2084_ = v_isSharedCheck_2118_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_snd_2081_);
lean_dec(v_a_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2118_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; 
lean_inc(v___x_1983_);
v___x_2085_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1986_, v___x_1983_, v_snd_2081_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_options_2086_; uint8_t v_hasTrace_2087_; 
v_options_2086_ = lean_ctor_get(v___y_2074_, 1);
v_hasTrace_2087_ = lean_ctor_get_uint8(v_options_2086_, sizeof(void*)*1);
if (v_hasTrace_2087_ == 0)
{
lean_object* v_a_2088_; 
lean_del_object(v___x_2083_);
lean_del_object(v___x_1995_);
v_a_2088_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2085_, 1);
v_mvarId_2045_ = v_a_2088_;
v___y_2046_ = v___y_2072_;
v___y_2047_ = v___y_2073_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
goto v___jp_2044_;
}
else
{
lean_object* v_toCold_2089_; lean_object* v_a_2090_; lean_object* v_inheritedTraceOptions_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_toCold_2089_ = lean_ctor_get(v___y_2074_, 0);
v_a_2090_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2085_, 1);
v_inheritedTraceOptions_2091_ = lean_ctor_get(v_toCold_2089_, 4);
v___x_2092_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2093_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2091_, v_options_2086_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_del_object(v___x_2083_);
lean_del_object(v___x_1995_);
v_mvarId_2045_ = v_a_2090_;
v___y_2046_ = v___y_2072_;
v___y_2047_ = v___y_2073_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2090_);
if (v_isShared_1996_ == 0)
{
lean_ctor_set_tag(v___x_1995_, 1);
lean_ctor_set(v___x_1995_, 0, v_a_2090_);
v___x_2096_ = v___x_1995_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2090_);
v___x_2096_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2098_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set_tag(v___x_2083_, 7);
lean_ctor_set(v___x_2083_, 1, v___x_2096_);
lean_ctor_set(v___x_2083_, 0, v___x_2094_);
v___x_2098_ = v___x_2083_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2070_, v___x_2098_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_dec_ref_known(v___x_2099_, 1);
v_mvarId_2045_ = v_a_2090_;
v___y_2046_ = v___y_2072_;
v___y_2047_ = v___y_2073_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
goto v___jp_2044_;
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_a_2090_);
lean_del_object(v___x_2001_);
lean_dec(v_a_1999_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
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
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_del_object(v___x_2083_);
lean_del_object(v___x_2001_);
lean_dec(v_a_1999_);
lean_del_object(v___x_1995_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v_a_2110_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2085_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2085_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_del_object(v___x_2001_);
lean_dec(v_a_1999_);
lean_del_object(v___x_1995_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
v_a_2120_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2079_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2079_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1995_);
lean_dec(v_heqPos_1985_);
lean_dec(v___x_1983_);
lean_dec(v_matchDeclName_1982_);
lean_dec_ref(v___f_1981_);
return v___x_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2146_, lean_object* v___f_2147_, lean_object* v_matchDeclName_2148_, lean_object* v___x_2149_, lean_object* v___x_2150_, lean_object* v_heqPos_2151_, lean_object* v_heqNum_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
uint8_t v___x_5913__boxed_2158_; lean_object* v_res_2159_; 
v___x_5913__boxed_2158_ = lean_unbox(v___x_2150_);
v_res_2159_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2146_, v___f_2147_, v_matchDeclName_2148_, v___x_2149_, v___x_5913__boxed_2158_, v_heqPos_2151_, v_heqNum_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v_heqNum_2152_);
return v_res_2159_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_unsigned_to_nat(32u);
v___x_2164_ = lean_mk_empty_array_with_capacity(v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2166_ = ((size_t)5ULL);
v___x_2167_ = lean_unsigned_to_nat(0u);
v___x_2168_ = lean_unsigned_to_nat(32u);
v___x_2169_ = lean_mk_empty_array_with_capacity(v___x_2168_);
v___x_2170_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2171_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v___x_2169_);
lean_ctor_set(v___x_2171_, 2, v___x_2167_);
lean_ctor_set(v___x_2171_, 3, v___x_2167_);
lean_ctor_set_usize(v___x_2171_, 4, v___x_2166_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2172_ = lean_box(1);
v___x_2173_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2174_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
lean_ctor_set(v___x_2175_, 1, v___x_2173_);
lean_ctor_set(v___x_2175_, 2, v___x_2172_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2178_, lean_object* v_type_2179_, lean_object* v_heqPos_2180_, lean_object* v_heqNum_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v___f_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___f_2193_; lean_object* v___x_2194_; 
lean_inc(v_matchDeclName_2178_);
v___f_2187_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2187_, 0, v_matchDeclName_2178_);
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2190_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2191_ = lean_nat_dec_lt(v___x_2188_, v_heqNum_2181_);
v___x_2192_ = lean_box(v___x_2191_);
v___f_2193_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2193_, 0, v_type_2179_);
lean_closure_set(v___f_2193_, 1, v___f_2187_);
lean_closure_set(v___f_2193_, 2, v_matchDeclName_2178_);
lean_closure_set(v___f_2193_, 3, v___x_2188_);
lean_closure_set(v___f_2193_, 4, v___x_2192_);
lean_closure_set(v___f_2193_, 5, v_heqPos_2180_);
lean_closure_set(v___f_2193_, 6, v_heqNum_2181_);
v___x_2194_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2189_, v___x_2190_, v___f_2193_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2195_, lean_object* v_type_2196_, lean_object* v_heqPos_2197_, lean_object* v_heqNum_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2195_, v_type_2196_, v_heqPos_2197_, v_heqNum_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2205_, lean_object* v_inst_2206_, lean_object* v_R_2207_, lean_object* v_a_2208_, lean_object* v_b_2209_, lean_object* v_c_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2205_, v_a_2208_, v_b_2209_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2217_, lean_object* v_inst_2218_, lean_object* v_R_2219_, lean_object* v_a_2220_, lean_object* v_b_2221_, lean_object* v_c_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2217_, v_inst_2218_, v_R_2219_, v_a_2220_, v_b_2221_, v_c_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v_upperBound_2217_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2229_, lean_object* v_b_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
lean_inc(v___y_2234_);
lean_inc_ref(v___y_2233_);
lean_inc(v___y_2232_);
lean_inc_ref(v___y_2231_);
v___x_2236_ = lean_apply_6(v_k_2229_, v_b_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, lean_box(0));
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2237_, lean_object* v_b_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2237_, v_b_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2245_, uint8_t v_bi_2246_, lean_object* v_type_2247_, lean_object* v_k_2248_, uint8_t v_kind_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___f_2255_; lean_object* v___x_2256_; 
v___f_2255_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2255_, 0, v_k_2248_);
v___x_2256_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2245_, v_bi_2246_, v_type_2247_, v___f_2255_, v_kind_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
v_a_2265_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2256_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2256_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2273_, lean_object* v_bi_2274_, lean_object* v_type_2275_, lean_object* v_k_2276_, lean_object* v_kind_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
uint8_t v_bi_boxed_2283_; uint8_t v_kind_boxed_2284_; lean_object* v_res_2285_; 
v_bi_boxed_2283_ = lean_unbox(v_bi_2274_);
v_kind_boxed_2284_ = lean_unbox(v_kind_2277_);
v_res_2285_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2273_, v_bi_boxed_2283_, v_type_2275_, v_k_2276_, v_kind_boxed_2284_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2286_, lean_object* v_name_2287_, uint8_t v_bi_2288_, lean_object* v_type_2289_, lean_object* v_k_2290_, uint8_t v_kind_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2287_, v_bi_2288_, v_type_2289_, v_k_2290_, v_kind_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2298_, lean_object* v_name_2299_, lean_object* v_bi_2300_, lean_object* v_type_2301_, lean_object* v_k_2302_, lean_object* v_kind_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
uint8_t v_bi_boxed_2309_; uint8_t v_kind_boxed_2310_; lean_object* v_res_2311_; 
v_bi_boxed_2309_ = lean_unbox(v_bi_2300_);
v_kind_boxed_2310_ = lean_unbox(v_kind_2303_);
v_res_2311_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2298_, v_name_2299_, v_bi_boxed_2309_, v_type_2301_, v_k_2302_, v_kind_boxed_2310_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2312_, lean_object* v_altsNew_2313_, lean_object* v_discrs_2314_, lean_object* v_patterns_2315_, lean_object* v_alts_2316_, lean_object* v_k_2317_, lean_object* v_altNew_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2312_, v_altsNew_2313_, v_discrs_2314_, v_patterns_2315_, v_alts_2316_, v_k_2317_, v_altNew_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v_i_2312_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2325_, lean_object* v_patterns_2326_, lean_object* v_alts_2327_, lean_object* v_k_2328_, lean_object* v_i_2329_, lean_object* v_altsNew_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = lean_array_get_size(v_alts_2327_);
v___x_2337_ = lean_nat_dec_lt(v_i_2329_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; 
lean_dec(v_i_2329_);
lean_dec_ref(v_alts_2327_);
lean_dec_ref(v_patterns_2326_);
lean_dec_ref(v_discrs_2325_);
lean_inc(v_a_2334_);
lean_inc_ref(v_a_2333_);
lean_inc(v_a_2332_);
lean_inc_ref(v_a_2331_);
v___x_2338_ = lean_apply_6(v_k_2328_, v_altsNew_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, lean_box(0));
return v___x_2338_;
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_array_fget_borrowed(v_alts_2327_, v_i_2329_);
v___x_2340_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2339_, v_a_2331_, v_a_2333_, v_a_2334_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
lean_inc_ref(v_patterns_2326_);
lean_inc_ref(v_discrs_2325_);
v___f_2342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2342_, 0, v_i_2329_);
lean_closure_set(v___f_2342_, 1, v_altsNew_2330_);
lean_closure_set(v___f_2342_, 2, v_discrs_2325_);
lean_closure_set(v___f_2342_, 3, v_patterns_2326_);
lean_closure_set(v___f_2342_, 4, v_alts_2327_);
lean_closure_set(v___f_2342_, 5, v_k_2328_);
v___x_2343_ = l_Lean_LocalDecl_type(v_a_2341_);
v___x_2344_ = l_Lean_Expr_replaceFVars(v___x_2343_, v_discrs_2325_, v_patterns_2326_);
lean_dec_ref(v_patterns_2326_);
lean_dec_ref(v_discrs_2325_);
lean_dec_ref(v___x_2343_);
v___x_2345_ = l_Lean_LocalDecl_userName(v_a_2341_);
v___x_2346_ = l_Lean_LocalDecl_binderInfo(v_a_2341_);
lean_dec(v_a_2341_);
v___x_2347_ = 0;
v___x_2348_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2345_, v___x_2346_, v___x_2344_, v___f_2342_, v___x_2347_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
return v___x_2348_;
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec_ref(v_altsNew_2330_);
lean_dec(v_i_2329_);
lean_dec_ref(v_k_2328_);
lean_dec_ref(v_alts_2327_);
lean_dec_ref(v_patterns_2326_);
lean_dec_ref(v_discrs_2325_);
v_a_2349_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2340_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2340_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2357_, lean_object* v_altsNew_2358_, lean_object* v_discrs_2359_, lean_object* v_patterns_2360_, lean_object* v_alts_2361_, lean_object* v_k_2362_, lean_object* v_altNew_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_nat_add(v_i_2357_, v___x_2369_);
v___x_2371_ = lean_array_push(v_altsNew_2358_, v_altNew_2363_);
v___x_2372_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2359_, v_patterns_2360_, v_alts_2361_, v_k_2362_, v___x_2370_, v___x_2371_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2373_, lean_object* v_patterns_2374_, lean_object* v_alts_2375_, lean_object* v_k_2376_, lean_object* v_i_2377_, lean_object* v_altsNew_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2373_, v_patterns_2374_, v_alts_2375_, v_k_2376_, v_i_2377_, v_altsNew_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2385_, lean_object* v_discrs_2386_, lean_object* v_patterns_2387_, lean_object* v_alts_2388_, lean_object* v_k_2389_, lean_object* v_i_2390_, lean_object* v_altsNew_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2386_, v_patterns_2387_, v_alts_2388_, v_k_2389_, v_i_2390_, v_altsNew_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2398_, lean_object* v_discrs_2399_, lean_object* v_patterns_2400_, lean_object* v_alts_2401_, lean_object* v_k_2402_, lean_object* v_i_2403_, lean_object* v_altsNew_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2398_, v_discrs_2399_, v_patterns_2400_, v_alts_2401_, v_k_2402_, v_i_2403_, v_altsNew_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2413_, lean_object* v_discrs_2414_, lean_object* v_patterns_2415_, lean_object* v_alts_2416_, lean_object* v_k_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = lean_unsigned_to_nat(0u);
v___x_2424_ = lean_nat_dec_eq(v_numDiscrEqs_2413_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2426_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2414_, v_patterns_2415_, v_alts_2416_, v_k_2417_, v___x_2423_, v___x_2425_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; 
lean_dec_ref(v_patterns_2415_);
lean_dec_ref(v_discrs_2414_);
lean_inc(v_a_2421_);
lean_inc_ref(v_a_2420_);
lean_inc(v_a_2419_);
lean_inc_ref(v_a_2418_);
v___x_2427_ = lean_apply_6(v_k_2417_, v_alts_2416_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, lean_box(0));
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2428_, lean_object* v_discrs_2429_, lean_object* v_patterns_2430_, lean_object* v_alts_2431_, lean_object* v_k_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2428_, v_discrs_2429_, v_patterns_2430_, v_alts_2431_, v_k_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_numDiscrEqs_2428_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2439_, lean_object* v_numDiscrEqs_2440_, lean_object* v_discrs_2441_, lean_object* v_patterns_2442_, lean_object* v_alts_2443_, lean_object* v_k_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2440_, v_discrs_2441_, v_patterns_2442_, v_alts_2443_, v_k_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2451_, lean_object* v_numDiscrEqs_2452_, lean_object* v_discrs_2453_, lean_object* v_patterns_2454_, lean_object* v_alts_2455_, lean_object* v_k_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2451_, v_numDiscrEqs_2452_, v_discrs_2453_, v_patterns_2454_, v_alts_2455_, v_k_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_numDiscrEqs_2452_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(lean_object* v_declName_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; lean_object* v_env_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2466_ = lean_st_ref_get(v___y_2464_);
v_env_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc_ref(v_env_2467_);
lean_dec(v___x_2466_);
v___x_2468_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2467_, v_declName_2463_);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg___boxed(lean_object* v_declName_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2470_, v___y_2471_);
lean_dec(v___y_2471_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_declName_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2474_, v___y_2478_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___boxed(lean_object* v_declName_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v_declName_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___f_2495_; lean_object* v___x_14316__overap_2496_; lean_object* v___x_2497_; 
v___f_2495_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14316__overap_2496_ = lean_panic_fn_borrowed(v___f_2495_, v_msg_2489_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
v___x_2497_ = lean_apply_5(v___x_14316__overap_2496_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, lean_box(0));
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2505_, lean_object* v_b_2506_, lean_object* v_c_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; 
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
v___x_2513_ = lean_apply_7(v_k_2505_, v_b_2506_, v_c_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, lean_box(0));
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2514_, lean_object* v_b_2515_, lean_object* v_c_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2514_, v_b_2515_, v_c_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2523_, lean_object* v_k_2524_, uint8_t v_cleanupAnnotations_2525_, uint8_t v_whnfType_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___f_2532_; lean_object* v___x_2533_; 
v___f_2532_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2532_, 0, v_k_2524_);
v___x_2533_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2523_, v___f_2532_, v_cleanupAnnotations_2525_, v_whnfType_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2533_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2533_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v_a_2542_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2533_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2533_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2550_, lean_object* v_k_2551_, lean_object* v_cleanupAnnotations_2552_, lean_object* v_whnfType_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2559_; uint8_t v_whnfType_boxed_2560_; lean_object* v_res_2561_; 
v_cleanupAnnotations_boxed_2559_ = lean_unbox(v_cleanupAnnotations_2552_);
v_whnfType_boxed_2560_ = lean_unbox(v_whnfType_2553_);
v_res_2561_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2550_, v_k_2551_, v_cleanupAnnotations_boxed_2559_, v_whnfType_boxed_2560_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2562_, lean_object* v_type_2563_, lean_object* v_k_2564_, uint8_t v_cleanupAnnotations_2565_, uint8_t v_whnfType_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2563_, v_k_2564_, v_cleanupAnnotations_2565_, v_whnfType_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2573_, lean_object* v_type_2574_, lean_object* v_k_2575_, lean_object* v_cleanupAnnotations_2576_, lean_object* v_whnfType_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2583_; uint8_t v_whnfType_boxed_2584_; lean_object* v_res_2585_; 
v_cleanupAnnotations_boxed_2583_ = lean_unbox(v_cleanupAnnotations_2576_);
v_whnfType_boxed_2584_ = lean_unbox(v_whnfType_2577_);
v_res_2585_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2573_, v_type_2574_, v_k_2575_, v_cleanupAnnotations_boxed_2583_, v_whnfType_boxed_2584_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2586_, lean_object* v_splitterName_2587_, lean_object* v_matcherInput_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_matchType_2594_; lean_object* v_discrInfos_2595_; lean_object* v_lhss_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2616_; 
v_matchType_2594_ = lean_ctor_get(v_matcherInput_2588_, 1);
v_discrInfos_2595_ = lean_ctor_get(v_matcherInput_2588_, 2);
v_lhss_2596_ = lean_ctor_get(v_matcherInput_2588_, 3);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_matcherInput_2588_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; lean_object* v_unused_2618_; 
v_unused_2617_ = lean_ctor_get(v_matcherInput_2588_, 4);
lean_dec(v_unused_2617_);
v_unused_2618_ = lean_ctor_get(v_matcherInput_2588_, 0);
lean_dec(v_unused_2618_);
v___x_2598_ = v_matcherInput_2588_;
v_isShared_2599_ = v_isSharedCheck_2616_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_lhss_2596_);
lean_inc(v_discrInfos_2595_);
lean_inc(v_matchType_2594_);
lean_dec(v_matcherInput_2588_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2616_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2600_, 0, v_overlaps_2586_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 4, v___x_2600_);
lean_ctor_set(v___x_2598_, 0, v_splitterName_2587_);
v___x_2602_ = v___x_2598_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_splitterName_2587_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_matchType_2594_);
lean_ctor_set(v_reuseFailAlloc_2615_, 2, v_discrInfos_2595_);
lean_ctor_set(v_reuseFailAlloc_2615_, 3, v_lhss_2596_);
lean_ctor_set(v_reuseFailAlloc_2615_, 4, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Meta_Match_mkMatcher(v___x_2602_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v_addMatcher_2605_; lean_object* v___x_2606_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v_addMatcher_2605_ = lean_ctor_get(v_a_2604_, 3);
lean_inc_ref(v_addMatcher_2605_);
lean_dec(v_a_2604_);
lean_inc(v___y_2592_);
lean_inc_ref(v___y_2591_);
lean_inc(v___y_2590_);
lean_inc_ref(v___y_2589_);
v___x_2606_ = lean_apply_5(v_addMatcher_2605_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, lean_box(0));
return v___x_2606_;
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
v_a_2607_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2603_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2603_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2619_, lean_object* v_splitterName_2620_, lean_object* v_matcherInput_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2619_, v_splitterName_2620_, v_matcherInput_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
return v_res_2627_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2628_, lean_object* v_ys_2629_, lean_object* v_x_2630_){
_start:
{
lean_object* v_zero_2631_; uint8_t v_isZero_2632_; 
v_zero_2631_ = lean_unsigned_to_nat(0u);
v_isZero_2632_ = lean_nat_dec_eq(v_x_2630_, v_zero_2631_);
if (v_isZero_2632_ == 1)
{
lean_dec(v_x_2630_);
return v_isZero_2632_;
}
else
{
lean_object* v_one_2633_; lean_object* v_n_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v_one_2633_ = lean_unsigned_to_nat(1u);
v_n_2634_ = lean_nat_sub(v_x_2630_, v_one_2633_);
lean_dec(v_x_2630_);
v___x_2635_ = lean_array_fget_borrowed(v_xs_2628_, v_n_2634_);
v___x_2636_ = lean_array_fget_borrowed(v_ys_2629_, v_n_2634_);
v___x_2637_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2635_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_dec(v_n_2634_);
return v___x_2637_;
}
else
{
v_x_2630_ = v_n_2634_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2639_, lean_object* v_ys_2640_, lean_object* v_x_2641_){
_start:
{
uint8_t v_res_2642_; lean_object* v_r_2643_; 
v_res_2642_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2639_, v_ys_2640_, v_x_2641_);
lean_dec_ref(v_ys_2640_);
lean_dec_ref(v_xs_2639_);
v_r_2643_ = lean_box(v_res_2642_);
return v_r_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2644_, lean_object* v_b_2645_){
_start:
{
lean_object* v_array_2646_; lean_object* v_start_2647_; lean_object* v_stop_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2661_; 
v_array_2646_ = lean_ctor_get(v_a_2644_, 0);
v_start_2647_ = lean_ctor_get(v_a_2644_, 1);
v_stop_2648_ = lean_ctor_get(v_a_2644_, 2);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_a_2644_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2650_ = v_a_2644_;
v_isShared_2651_ = v_isSharedCheck_2661_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_stop_2648_);
lean_inc(v_start_2647_);
lean_inc(v_array_2646_);
lean_dec(v_a_2644_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2661_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
uint8_t v___x_2652_; 
v___x_2652_ = lean_nat_dec_lt(v_start_2647_, v_stop_2648_);
if (v___x_2652_ == 0)
{
lean_del_object(v___x_2650_);
lean_dec(v_stop_2648_);
lean_dec(v_start_2647_);
lean_dec_ref(v_array_2646_);
return v_b_2645_;
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2653_ = lean_unsigned_to_nat(1u);
v___x_2654_ = lean_nat_add(v_start_2647_, v___x_2653_);
lean_inc_ref(v_array_2646_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 1, v___x_2654_);
v___x_2656_ = v___x_2650_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_array_2646_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_stop_2648_);
v___x_2656_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_array_fget(v_array_2646_, v_start_2647_);
lean_dec(v_start_2647_);
lean_dec_ref(v_array_2646_);
v___x_2658_ = lean_array_push(v_b_2645_, v___x_2657_);
v_a_2644_ = v___x_2656_;
v_b_2645_ = v___x_2658_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2662_, size_t v_sz_2663_, size_t v_i_2664_, lean_object* v_b_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
uint8_t v___x_2671_; 
v___x_2671_ = lean_usize_dec_lt(v_i_2664_, v_sz_2663_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v_b_2665_);
return v___x_2672_;
}
else
{
lean_object* v_snd_2673_; lean_object* v_fst_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2726_; 
v_snd_2673_ = lean_ctor_get(v_b_2665_, 1);
v_fst_2674_ = lean_ctor_get(v_b_2665_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_b_2665_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2676_ = v_b_2665_;
v_isShared_2677_ = v_isSharedCheck_2726_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_snd_2673_);
lean_inc(v_fst_2674_);
lean_dec(v_b_2665_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2726_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v_array_2678_; lean_object* v_start_2679_; lean_object* v_stop_2680_; uint8_t v___x_2681_; 
v_array_2678_ = lean_ctor_get(v_snd_2673_, 0);
v_start_2679_ = lean_ctor_get(v_snd_2673_, 1);
v_stop_2680_ = lean_ctor_get(v_snd_2673_, 2);
v___x_2681_ = lean_nat_dec_lt(v_start_2679_, v_stop_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2683_; 
if (v_isShared_2677_ == 0)
{
v___x_2683_ = v___x_2676_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_fst_2674_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_snd_2673_);
v___x_2683_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
return v___x_2684_;
}
}
else
{
lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2722_; 
lean_inc(v_stop_2680_);
lean_inc(v_start_2679_);
lean_inc_ref(v_array_2678_);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_snd_2673_);
if (v_isSharedCheck_2722_ == 0)
{
lean_object* v_unused_2723_; lean_object* v_unused_2724_; lean_object* v_unused_2725_; 
v_unused_2723_ = lean_ctor_get(v_snd_2673_, 2);
lean_dec(v_unused_2723_);
v_unused_2724_ = lean_ctor_get(v_snd_2673_, 1);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_snd_2673_, 0);
lean_dec(v_unused_2725_);
v___x_2687_ = v_snd_2673_;
v_isShared_2688_ = v_isSharedCheck_2722_;
goto v_resetjp_2686_;
}
else
{
lean_dec(v_snd_2673_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2722_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_a_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_a_2689_ = lean_array_uget_borrowed(v_as_2662_, v_i_2664_);
v___x_2690_ = lean_array_fget_borrowed(v_array_2678_, v_start_2679_);
lean_inc(v___x_2690_);
lean_inc(v_a_2689_);
v___x_2691_ = l_Lean_Meta_mkEqHEq(v_a_2689_, v___x_2690_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
v___x_2693_ = l_Lean_mkArrow(v_a_2692_, v_fst_2674_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v___x_2695_ = lean_unsigned_to_nat(1u);
v___x_2696_ = lean_nat_add(v_start_2679_, v___x_2695_);
lean_dec(v_start_2679_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v___x_2696_);
v___x_2698_ = v___x_2687_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_array_2678_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v_stop_2680_);
v___x_2698_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 1, v___x_2698_);
lean_ctor_set(v___x_2676_, 0, v_a_2694_);
v___x_2700_ = v___x_2676_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2694_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
size_t v___x_2701_; size_t v___x_2702_; 
v___x_2701_ = ((size_t)1ULL);
v___x_2702_ = lean_usize_add(v_i_2664_, v___x_2701_);
v_i_2664_ = v___x_2702_;
v_b_2665_ = v___x_2700_;
goto _start;
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_del_object(v___x_2687_);
lean_dec(v_stop_2680_);
lean_dec(v_start_2679_);
lean_dec_ref(v_array_2678_);
lean_del_object(v___x_2676_);
v_a_2706_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2693_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2693_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_del_object(v___x_2687_);
lean_dec(v_stop_2680_);
lean_dec(v_start_2679_);
lean_dec_ref(v_array_2678_);
lean_del_object(v___x_2676_);
lean_dec(v_fst_2674_);
v_a_2714_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2691_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2691_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2727_, lean_object* v_sz_2728_, lean_object* v_i_2729_, lean_object* v_b_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_sz_boxed_2736_; size_t v_i_boxed_2737_; lean_object* v_res_2738_; 
v_sz_boxed_2736_ = lean_unbox_usize(v_sz_2728_);
lean_dec(v_sz_2728_);
v_i_boxed_2737_ = lean_unbox_usize(v_i_2729_);
lean_dec(v_i_2729_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2727_, v_sz_boxed_2736_, v_i_boxed_2737_, v_b_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec_ref(v_as_2727_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2739_, lean_object* v___x_2740_, lean_object* v_as_2741_, size_t v_sz_2742_, size_t v_i_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_usize_dec_lt(v_i_2743_, v_sz_2742_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v_b_2744_);
return v___x_2751_;
}
else
{
lean_object* v___x_2752_; lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2752_ = l_Lean_instInhabitedExpr;
v_a_2753_ = lean_array_uget_borrowed(v_as_2741_, v_i_2743_);
v___x_2754_ = lean_array_get_borrowed(v___x_2752_, v___x_2739_, v_a_2753_);
lean_inc(v___x_2754_);
v___x_2755_ = l_Lean_Meta_instantiateForall(v___x_2754_, v___x_2740_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2755_, 1);
v___x_2757_ = lean_array_get_size(v___x_2740_);
v___x_2758_ = l_Lean_Meta_Match_simpH_x3f(v_a_2756_, v___x_2757_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v_a_2761_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref_known(v___x_2758_, 1);
if (lean_obj_tag(v_a_2759_) == 1)
{
lean_object* v_val_2765_; lean_object* v___x_2766_; 
v_val_2765_ = lean_ctor_get(v_a_2759_, 0);
lean_inc(v_val_2765_);
lean_dec_ref_known(v_a_2759_, 1);
v___x_2766_ = lean_array_push(v_b_2744_, v_val_2765_);
v_a_2761_ = v___x_2766_;
goto v___jp_2760_;
}
else
{
lean_dec(v_a_2759_);
v_a_2761_ = v_b_2744_;
goto v___jp_2760_;
}
v___jp_2760_:
{
size_t v___x_2762_; size_t v___x_2763_; 
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = lean_usize_add(v_i_2743_, v___x_2762_);
v_i_2743_ = v___x_2763_;
v_b_2744_ = v_a_2761_;
goto _start;
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec_ref(v_b_2744_);
v_a_2767_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2758_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2758_);
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
lean_dec_ref(v_b_2744_);
v_a_2775_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2755_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2755_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2783_, lean_object* v___x_2784_, lean_object* v_as_2785_, lean_object* v_sz_2786_, lean_object* v_i_2787_, lean_object* v_b_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
size_t v_sz_boxed_2794_; size_t v_i_boxed_2795_; lean_object* v_res_2796_; 
v_sz_boxed_2794_ = lean_unbox_usize(v_sz_2786_);
lean_dec(v_sz_2786_);
v_i_boxed_2795_ = lean_unbox_usize(v_i_2787_);
lean_dec(v_i_2787_);
v_res_2796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2783_, v___x_2784_, v_as_2785_, v_sz_boxed_2794_, v_i_boxed_2795_, v_b_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec_ref(v_as_2785_);
lean_dec_ref(v___x_2784_);
lean_dec_ref(v___x_2783_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v___x_2800_, lean_object* v___x_2801_, lean_object* v___x_2802_, lean_object* v___x_2803_, lean_object* v___x_2804_, lean_object* v_rhsArgs_2805_, lean_object* v_a_2806_, lean_object* v_ys_2807_, uint8_t v___x_2808_, uint8_t v___x_2809_, uint8_t v___x_2810_, lean_object* v_matchDeclName_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v_argMask_2817_, lean_object* v_a_2818_, lean_object* v_alts_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2825_ = lean_array_get_borrowed(v___x_2797_, v_alts_2819_, v_a_2798_);
v___x_2826_ = l_Lean_ConstantInfo_name(v_a_2799_);
v___x_2827_ = l_Lean_mkConst(v___x_2826_, v___x_2800_);
v___x_2828_ = l_Subarray_copy___redArg(v___x_2801_);
v___x_2829_ = lean_mk_empty_array_with_capacity(v___x_2802_);
v___x_2830_ = lean_array_push(v___x_2829_, v___x_2803_);
v___x_2831_ = l_Array_append___redArg(v___x_2828_, v___x_2830_);
lean_dec_ref(v___x_2830_);
lean_inc_ref(v___x_2831_);
v___x_2832_ = l_Array_append___redArg(v___x_2831_, v___x_2804_);
v___x_2833_ = l_Array_append___redArg(v___x_2832_, v_alts_2819_);
v___x_2834_ = l_Lean_mkAppN(v___x_2827_, v___x_2833_);
lean_dec_ref(v___x_2833_);
lean_inc(v___x_2825_);
v___x_2835_ = l_Lean_mkAppN(v___x_2825_, v_rhsArgs_2805_);
v___x_2836_ = l_Lean_Meta_mkEq(v___x_2834_, v___x_2835_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2838_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2838_ = l_Lean_mkArrowN(v_a_2806_, v_a_2837_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = l_Array_append___redArg(v___x_2831_, v_ys_2807_);
v___x_2841_ = l_Array_append___redArg(v___x_2840_, v_alts_2819_);
v___x_2842_ = l_Lean_Meta_mkForallFVars(v___x_2841_, v_a_2839_, v___x_2808_, v___x_2809_, v___x_2809_, v___x_2810_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec_ref(v___x_2841_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2842_, 1);
v___x_2844_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2843_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc_n(v_a_2845_, 2);
lean_dec_ref_known(v___x_2844_, 1);
lean_inc(v___x_2812_);
v___x_2846_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2811_, v_a_2845_, v___x_2812_, v___x_2812_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
lean_inc(v___x_2813_);
v___x_2848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2813_);
lean_ctor_set(v___x_2848_, 1, v___x_2814_);
lean_ctor_set(v___x_2848_, 2, v_a_2845_);
v___x_2849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2813_);
lean_ctor_set(v___x_2849_, 1, v___x_2815_);
v___x_2850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set(v___x_2850_, 1, v_a_2847_);
lean_ctor_set(v___x_2850_, 2, v___x_2849_);
v___x_2851_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
v___x_2852_ = l_Lean_addDecl(v___x_2851_, v___x_2808_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2861_; 
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2861_ == 0)
{
lean_object* v_unused_2862_; 
v_unused_2862_ = lean_ctor_get(v___x_2852_, 0);
lean_dec(v_unused_2862_);
v___x_2854_ = v___x_2852_;
v_isShared_2855_ = v_isSharedCheck_2861_;
goto v_resetjp_2853_;
}
else
{
lean_dec(v___x_2852_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2861_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2816_);
lean_ctor_set(v___x_2856_, 1, v_argMask_2817_);
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v_a_2818_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v___x_2857_);
v___x_2859_ = v___x_2854_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec_ref(v_a_2818_);
lean_dec_ref(v_argMask_2817_);
lean_dec_ref(v___x_2816_);
v_a_2863_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2852_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2852_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2818_);
lean_dec_ref(v_argMask_2817_);
lean_dec_ref(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
v_a_2871_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2846_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2846_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec_ref(v_a_2818_);
lean_dec_ref(v_argMask_2817_);
lean_dec_ref(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v___x_2812_);
lean_dec(v_matchDeclName_2811_);
v_a_2879_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2844_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2844_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec_ref(v_a_2818_);
lean_dec_ref(v_argMask_2817_);
lean_dec_ref(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v___x_2812_);
lean_dec(v_matchDeclName_2811_);
v_a_2887_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2842_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2842_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec_ref(v___x_2831_);
lean_dec_ref(v_a_2818_);
lean_dec_ref(v_argMask_2817_);
lean_dec_ref(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v___x_2812_);
lean_dec(v_matchDeclName_2811_);
v_a_2895_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2838_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2838_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec_ref(v___x_2831_);
lean_dec_ref(v_a_2818_);
lean_dec_ref(v_argMask_2817_);
lean_dec_ref(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v___x_2812_);
lean_dec(v_matchDeclName_2811_);
v_a_2903_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2836_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2836_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2911_ = _args[0];
lean_object* v_a_2912_ = _args[1];
lean_object* v_a_2913_ = _args[2];
lean_object* v___x_2914_ = _args[3];
lean_object* v___x_2915_ = _args[4];
lean_object* v___x_2916_ = _args[5];
lean_object* v___x_2917_ = _args[6];
lean_object* v___x_2918_ = _args[7];
lean_object* v_rhsArgs_2919_ = _args[8];
lean_object* v_a_2920_ = _args[9];
lean_object* v_ys_2921_ = _args[10];
lean_object* v___x_2922_ = _args[11];
lean_object* v___x_2923_ = _args[12];
lean_object* v___x_2924_ = _args[13];
lean_object* v_matchDeclName_2925_ = _args[14];
lean_object* v___x_2926_ = _args[15];
lean_object* v___x_2927_ = _args[16];
lean_object* v___x_2928_ = _args[17];
lean_object* v___x_2929_ = _args[18];
lean_object* v___x_2930_ = _args[19];
lean_object* v_argMask_2931_ = _args[20];
lean_object* v_a_2932_ = _args[21];
lean_object* v_alts_2933_ = _args[22];
lean_object* v___y_2934_ = _args[23];
lean_object* v___y_2935_ = _args[24];
lean_object* v___y_2936_ = _args[25];
lean_object* v___y_2937_ = _args[26];
lean_object* v___y_2938_ = _args[27];
_start:
{
uint8_t v___x_18496__boxed_2939_; uint8_t v___x_18497__boxed_2940_; uint8_t v___x_18498__boxed_2941_; lean_object* v_res_2942_; 
v___x_18496__boxed_2939_ = lean_unbox(v___x_2922_);
v___x_18497__boxed_2940_ = lean_unbox(v___x_2923_);
v___x_18498__boxed_2941_ = lean_unbox(v___x_2924_);
v_res_2942_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2911_, v_a_2912_, v_a_2913_, v___x_2914_, v___x_2915_, v___x_2916_, v___x_2917_, v___x_2918_, v_rhsArgs_2919_, v_a_2920_, v_ys_2921_, v___x_18496__boxed_2939_, v___x_18497__boxed_2940_, v___x_18498__boxed_2941_, v_matchDeclName_2925_, v___x_2926_, v___x_2927_, v___x_2928_, v___x_2929_, v___x_2930_, v_argMask_2931_, v_a_2932_, v_alts_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec_ref(v_alts_2933_);
lean_dec_ref(v_ys_2921_);
lean_dec_ref(v_a_2920_);
lean_dec_ref(v_rhsArgs_2919_);
lean_dec_ref(v___x_2918_);
lean_dec(v___x_2916_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v___x_2911_);
return v_res_2942_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2943_; lean_object* v_dummy_2944_; 
v___x_2943_ = lean_box(0);
v_dummy_2944_ = l_Lean_Expr_sort___override(v___x_2943_);
return v_dummy_2944_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2948_ = lean_box(0);
v___x_2949_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_2950_ = l_Lean_mkConst(v___x_2949_, v___x_2948_);
return v___x_2950_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_2954_, lean_object* v_overlaps_2955_, lean_object* v_a_2956_, lean_object* v_fst_2957_, lean_object* v___x_2958_, lean_object* v___x_2959_, lean_object* v___x_2960_, uint8_t v___x_2961_, lean_object* v___x_2962_, lean_object* v_a_2963_, lean_object* v___x_2964_, lean_object* v___x_2965_, lean_object* v___x_2966_, lean_object* v_matchDeclName_2967_, lean_object* v___x_2968_, lean_object* v___x_2969_, lean_object* v___x_2970_, lean_object* v___x_2971_, lean_object* v___x_2972_, lean_object* v_ys_2973_, lean_object* v___eqs_2974_, lean_object* v_rhsArgs_2975_, lean_object* v_argMask_2976_, lean_object* v_altResultType_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_dummy_2983_; lean_object* v_nargs_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; size_t v_sz_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v_dummy_2983_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_2984_ = l_Lean_Expr_getAppNumArgs(v_altResultType_2977_);
lean_inc(v_nargs_2984_);
v___x_2985_ = lean_mk_array(v_nargs_2984_, v_dummy_2983_);
v___x_2986_ = lean_nat_sub(v_nargs_2984_, v___x_2954_);
lean_dec(v_nargs_2984_);
v___x_2987_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_2977_, v___x_2985_, v___x_2986_);
v___x_2988_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_2955_, v_a_2956_);
v_sz_2989_ = lean_array_size(v___x_2988_);
v___x_2990_ = ((size_t)0ULL);
lean_inc_ref(v___x_2958_);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_2957_, v___x_2987_, v___x_2988_, v_sz_2989_, v___x_2990_, v___x_2958_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
lean_dec_ref(v___x_2988_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; uint8_t v___y_2998_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v_options_3051_; uint8_t v_hasTrace_3052_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v_options_3051_ = lean_ctor_get(v___y_2980_, 1);
v_hasTrace_3052_ = lean_ctor_get_uint8(v_options_3051_, sizeof(void*)*1);
if (v_hasTrace_3052_ == 0)
{
v___y_3042_ = v___y_2978_;
v___y_3043_ = v___y_2979_;
v___y_3044_ = v___y_2980_;
v___y_3045_ = v___y_2981_;
goto v___jp_3041_;
}
else
{
lean_object* v_toCold_3053_; lean_object* v_inheritedTraceOptions_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; uint8_t v___x_3057_; 
v_toCold_3053_ = lean_ctor_get(v___y_2980_, 0);
v_inheritedTraceOptions_3054_ = lean_ctor_get(v_toCold_3053_, 4);
v___x_3055_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3056_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_3057_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3054_, v_options_3051_, v___x_3056_);
if (v___x_3057_ == 0)
{
v___y_3042_ = v___y_2978_;
v___y_3043_ = v___y_2979_;
v___y_3044_ = v___y_2980_;
v___y_3045_ = v___y_2981_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3058_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_2992_);
v___x_3059_ = lean_array_to_list(v_a_2992_);
v___x_3060_ = lean_box(0);
v___x_3061_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3059_, v___x_3060_);
v___x_3062_ = l_Lean_MessageData_ofList(v___x_3061_);
v___x_3063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3058_);
lean_ctor_set(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3055_, v___x_3063_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_dec_ref_known(v___x_3064_, 1);
v___y_3042_ = v___y_2978_;
v___y_3043_ = v___y_2979_;
v___y_3044_ = v___y_2980_;
v___y_3045_ = v___y_2981_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec(v_a_2992_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_argMask_2976_);
lean_dec_ref(v_rhsArgs_2975_);
lean_dec_ref(v_ys_2973_);
lean_dec_ref(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v___x_2968_);
lean_dec(v_matchDeclName_2967_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v_a_2963_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v_a_2956_);
lean_dec(v___x_2954_);
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3064_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3064_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
}
v___jp_2993_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; size_t v_sz_3006_; lean_object* v___x_3007_; 
v___x_2999_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2987_);
v___x_3000_ = l_Array_reverse___redArg(v___x_2987_);
v___x_3001_ = lean_array_get_size(v___x_3000_);
lean_inc(v___x_2959_);
v___x_3002_ = l_Array_toSubarray___redArg(v___x_3000_, v___x_2959_, v___x_3001_);
lean_inc_ref(v___x_2960_);
v___x_3003_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2960_, v___x_2958_);
v___x_3004_ = l_Array_reverse___redArg(v___x_3003_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_2999_);
lean_ctor_set(v___x_3005_, 1, v___x_3002_);
v_sz_3006_ = lean_array_size(v___x_3004_);
v___x_3007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3004_, v_sz_3006_, v___x_2990_, v___x_3005_, v___y_2994_, v___y_2995_, v___y_2997_, v___y_2996_);
lean_dec_ref(v___x_3004_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v_fst_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; uint8_t v___x_3013_; lean_object* v___x_3014_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref_known(v___x_3007_, 1);
v_fst_3009_ = lean_ctor_get(v_a_3008_, 0);
lean_inc(v_fst_3009_);
lean_dec(v_a_3008_);
v___x_3010_ = l_Subarray_copy___redArg(v___x_2960_);
lean_inc_ref(v___x_3010_);
v___x_3011_ = l_Array_append___redArg(v___x_3010_, v_ys_2973_);
v___x_3012_ = 0;
v___x_3013_ = 1;
v___x_3014_ = l_Lean_Meta_mkForallFVars(v___x_3011_, v_fst_3009_, v___x_3012_, v___x_2961_, v___x_2961_, v___x_3013_, v___y_2994_, v___y_2995_, v___y_2997_, v___y_2996_);
lean_dec_ref(v___x_3011_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___f_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = lean_array_get_size(v_ys_2973_);
v___x_3017_ = lean_array_get_size(v_a_2992_);
v___x_3018_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3018_, 0, v___x_3016_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
lean_ctor_set_uint8(v___x_3018_, sizeof(void*)*2, v___y_2998_);
v___x_3019_ = lean_box(v___x_3012_);
v___x_3020_ = lean_box(v___x_2961_);
v___x_3021_ = lean_box(v___x_3013_);
lean_inc_ref(v___x_2987_);
v___f_3022_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_3022_, 0, v___x_2962_);
lean_closure_set(v___f_3022_, 1, v_a_2956_);
lean_closure_set(v___f_3022_, 2, v_a_2963_);
lean_closure_set(v___f_3022_, 3, v___x_2964_);
lean_closure_set(v___f_3022_, 4, v___x_2965_);
lean_closure_set(v___f_3022_, 5, v___x_2954_);
lean_closure_set(v___f_3022_, 6, v___x_2966_);
lean_closure_set(v___f_3022_, 7, v___x_2987_);
lean_closure_set(v___f_3022_, 8, v_rhsArgs_2975_);
lean_closure_set(v___f_3022_, 9, v_a_2992_);
lean_closure_set(v___f_3022_, 10, v_ys_2973_);
lean_closure_set(v___f_3022_, 11, v___x_3019_);
lean_closure_set(v___f_3022_, 12, v___x_3020_);
lean_closure_set(v___f_3022_, 13, v___x_3021_);
lean_closure_set(v___f_3022_, 14, v_matchDeclName_2967_);
lean_closure_set(v___f_3022_, 15, v___x_2959_);
lean_closure_set(v___f_3022_, 16, v___x_2968_);
lean_closure_set(v___f_3022_, 17, v___x_2969_);
lean_closure_set(v___f_3022_, 18, v___x_2970_);
lean_closure_set(v___f_3022_, 19, v___x_3018_);
lean_closure_set(v___f_3022_, 20, v_argMask_2976_);
lean_closure_set(v___f_3022_, 21, v_a_3015_);
v___x_3023_ = l_Subarray_copy___redArg(v___x_2971_);
v___x_3024_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2972_, v___x_3010_, v___x_2987_, v___x_3023_, v___f_3022_, v___y_2994_, v___y_2995_, v___y_2997_, v___y_2996_);
return v___x_3024_;
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v___x_3010_);
lean_dec(v_a_2992_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_argMask_2976_);
lean_dec_ref(v_rhsArgs_2975_);
lean_dec_ref(v_ys_2973_);
lean_dec_ref(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v___x_2968_);
lean_dec(v_matchDeclName_2967_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v_a_2963_);
lean_dec_ref(v___x_2962_);
lean_dec(v___x_2959_);
lean_dec(v_a_2956_);
lean_dec(v___x_2954_);
v_a_3025_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3014_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3014_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec(v_a_2992_);
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_argMask_2976_);
lean_dec_ref(v_rhsArgs_2975_);
lean_dec_ref(v_ys_2973_);
lean_dec_ref(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v___x_2968_);
lean_dec(v_matchDeclName_2967_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v_a_2963_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec(v___x_2959_);
lean_dec(v_a_2956_);
lean_dec(v___x_2954_);
v_a_3033_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3007_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3007_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
v___jp_3041_:
{
lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = lean_array_get_size(v_ys_2973_);
v___x_3047_ = lean_nat_dec_eq(v___x_3046_, v___x_2959_);
if (v___x_3047_ == 0)
{
v___y_2994_ = v___y_3042_;
v___y_2995_ = v___y_3043_;
v___y_2996_ = v___y_3045_;
v___y_2997_ = v___y_3044_;
v___y_2998_ = v___x_3047_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_3048_ = lean_array_get_size(v_a_2992_);
v___x_3049_ = lean_nat_dec_eq(v___x_3048_, v___x_2959_);
if (v___x_3049_ == 0)
{
v___y_2994_ = v___y_3042_;
v___y_2995_ = v___y_3043_;
v___y_2996_ = v___y_3045_;
v___y_2997_ = v___y_3044_;
v___y_2998_ = v___x_3049_;
goto v___jp_2993_;
}
else
{
uint8_t v___x_3050_; 
v___x_3050_ = lean_nat_dec_eq(v___x_2972_, v___x_2959_);
v___y_2994_ = v___y_3042_;
v___y_2995_ = v___y_3043_;
v___y_2996_ = v___y_3045_;
v___y_2997_ = v___y_3044_;
v___y_2998_ = v___x_3050_;
goto v___jp_2993_;
}
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec_ref(v___x_2987_);
lean_dec_ref(v_argMask_2976_);
lean_dec_ref(v_rhsArgs_2975_);
lean_dec_ref(v_ys_2973_);
lean_dec_ref(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v___x_2968_);
lean_dec(v_matchDeclName_2967_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v_a_2963_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v_a_2956_);
lean_dec(v___x_2954_);
v_a_3073_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_2991_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_2991_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3081_ = _args[0];
lean_object* v_overlaps_3082_ = _args[1];
lean_object* v_a_3083_ = _args[2];
lean_object* v_fst_3084_ = _args[3];
lean_object* v___x_3085_ = _args[4];
lean_object* v___x_3086_ = _args[5];
lean_object* v___x_3087_ = _args[6];
lean_object* v___x_3088_ = _args[7];
lean_object* v___x_3089_ = _args[8];
lean_object* v_a_3090_ = _args[9];
lean_object* v___x_3091_ = _args[10];
lean_object* v___x_3092_ = _args[11];
lean_object* v___x_3093_ = _args[12];
lean_object* v_matchDeclName_3094_ = _args[13];
lean_object* v___x_3095_ = _args[14];
lean_object* v___x_3096_ = _args[15];
lean_object* v___x_3097_ = _args[16];
lean_object* v___x_3098_ = _args[17];
lean_object* v___x_3099_ = _args[18];
lean_object* v_ys_3100_ = _args[19];
lean_object* v___eqs_3101_ = _args[20];
lean_object* v_rhsArgs_3102_ = _args[21];
lean_object* v_argMask_3103_ = _args[22];
lean_object* v_altResultType_3104_ = _args[23];
lean_object* v___y_3105_ = _args[24];
lean_object* v___y_3106_ = _args[25];
lean_object* v___y_3107_ = _args[26];
lean_object* v___y_3108_ = _args[27];
lean_object* v___y_3109_ = _args[28];
_start:
{
uint8_t v___x_18764__boxed_3110_; lean_object* v_res_3111_; 
v___x_18764__boxed_3110_ = lean_unbox(v___x_3088_);
v_res_3111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3081_, v_overlaps_3082_, v_a_3083_, v_fst_3084_, v___x_3085_, v___x_3086_, v___x_3087_, v___x_18764__boxed_3110_, v___x_3089_, v_a_3090_, v___x_3091_, v___x_3092_, v___x_3093_, v_matchDeclName_3094_, v___x_3095_, v___x_3096_, v___x_3097_, v___x_3098_, v___x_3099_, v_ys_3100_, v___eqs_3101_, v_rhsArgs_3102_, v_argMask_3103_, v_altResultType_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec_ref(v___eqs_3101_);
lean_dec(v___x_3099_);
lean_dec(v_fst_3084_);
lean_dec_ref(v_overlaps_3082_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3112_, lean_object* v_val_3113_, lean_object* v_baseName_3114_, lean_object* v___x_3115_, lean_object* v_a_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v___x_3119_, lean_object* v_matchDeclName_3120_, lean_object* v___x_3121_, lean_object* v___x_3122_, lean_object* v___x_3123_, lean_object* v_a_3124_, lean_object* v_b_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
uint8_t v___x_3131_; 
v___x_3131_ = lean_nat_dec_lt(v_a_3124_, v_upperBound_3112_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; 
lean_dec(v_a_3124_);
lean_dec(v___x_3123_);
lean_dec_ref(v___x_3122_);
lean_dec(v___x_3121_);
lean_dec(v_matchDeclName_3120_);
lean_dec_ref(v___x_3119_);
lean_dec_ref(v___x_3118_);
lean_dec(v___x_3117_);
lean_dec_ref(v_a_3116_);
lean_dec_ref(v___x_3115_);
lean_dec(v_baseName_3114_);
lean_dec_ref(v_val_3113_);
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v_b_3125_);
return v___x_3132_;
}
else
{
lean_object* v_snd_3133_; lean_object* v_snd_3134_; lean_object* v_snd_3135_; lean_object* v_fst_3136_; lean_object* v_fst_3137_; lean_object* v_fst_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3221_; 
v_snd_3133_ = lean_ctor_get(v_b_3125_, 1);
lean_inc(v_snd_3133_);
v_snd_3134_ = lean_ctor_get(v_snd_3133_, 1);
lean_inc(v_snd_3134_);
v_snd_3135_ = lean_ctor_get(v_snd_3134_, 1);
lean_inc(v_snd_3135_);
v_fst_3136_ = lean_ctor_get(v_b_3125_, 0);
lean_inc(v_fst_3136_);
lean_dec_ref(v_b_3125_);
v_fst_3137_ = lean_ctor_get(v_snd_3133_, 0);
lean_inc(v_fst_3137_);
lean_dec(v_snd_3133_);
v_fst_3138_ = lean_ctor_get(v_snd_3134_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_snd_3134_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_snd_3134_, 1);
lean_dec(v_unused_3222_);
v___x_3140_ = v_snd_3134_;
v_isShared_3141_ = v_isSharedCheck_3221_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_fst_3138_);
lean_dec(v_snd_3134_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3221_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v_fst_3142_; lean_object* v_snd_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3220_; 
v_fst_3142_ = lean_ctor_get(v_snd_3135_, 0);
v_snd_3143_ = lean_ctor_get(v_snd_3135_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_snd_3135_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3145_ = v_snd_3135_;
v_isShared_3146_ = v_isSharedCheck_3220_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_snd_3143_);
lean_inc(v_fst_3142_);
lean_dec(v_snd_3135_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3220_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v_altInfos_3147_; lean_object* v_overlaps_3148_; lean_object* v_start_3149_; lean_object* v_stop_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___f_3162_; lean_object* v___x_3163_; lean_object* v___y_3165_; lean_object* v___x_3216_; uint8_t v___x_3217_; 
v_altInfos_3147_ = lean_ctor_get(v_val_3113_, 2);
v_overlaps_3148_ = lean_ctor_get(v_val_3113_, 5);
v_start_3149_ = lean_ctor_get(v___x_3122_, 1);
v_stop_3150_ = lean_ctor_get(v___x_3122_, 2);
v___x_3151_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3152_ = l_Lean_instInhabitedExpr;
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3155_ = lean_box(0);
v___x_3156_ = lean_unsigned_to_nat(1u);
v___x_3157_ = lean_array_get_borrowed(v___x_3151_, v_altInfos_3147_, v_a_3124_);
v___x_3158_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3114_);
v___x_3159_ = l_Lean_Name_str___override(v_baseName_3114_, v___x_3158_);
lean_inc(v_fst_3138_);
v___x_3160_ = lean_name_append_index_after(v___x_3159_, v_fst_3138_);
v___x_3161_ = lean_box(v___x_3131_);
lean_inc(v___x_3123_);
lean_inc_ref(v___x_3122_);
lean_inc(v___x_3121_);
lean_inc(v___x_3160_);
lean_inc(v_matchDeclName_3120_);
lean_inc_ref(v___x_3119_);
lean_inc_ref(v___x_3118_);
lean_inc(v___x_3117_);
lean_inc_ref(v_a_3116_);
lean_inc_ref(v___x_3115_);
lean_inc(v_fst_3137_);
lean_inc(v_a_3124_);
lean_inc_ref(v_overlaps_3148_);
v___f_3162_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3162_, 0, v___x_3156_);
lean_closure_set(v___f_3162_, 1, v_overlaps_3148_);
lean_closure_set(v___f_3162_, 2, v_a_3124_);
lean_closure_set(v___f_3162_, 3, v_fst_3137_);
lean_closure_set(v___f_3162_, 4, v___x_3154_);
lean_closure_set(v___f_3162_, 5, v___x_3153_);
lean_closure_set(v___f_3162_, 6, v___x_3115_);
lean_closure_set(v___f_3162_, 7, v___x_3161_);
lean_closure_set(v___f_3162_, 8, v___x_3152_);
lean_closure_set(v___f_3162_, 9, v_a_3116_);
lean_closure_set(v___f_3162_, 10, v___x_3117_);
lean_closure_set(v___f_3162_, 11, v___x_3118_);
lean_closure_set(v___f_3162_, 12, v___x_3119_);
lean_closure_set(v___f_3162_, 13, v_matchDeclName_3120_);
lean_closure_set(v___f_3162_, 14, v___x_3160_);
lean_closure_set(v___f_3162_, 15, v___x_3121_);
lean_closure_set(v___f_3162_, 16, v___x_3155_);
lean_closure_set(v___f_3162_, 17, v___x_3122_);
lean_closure_set(v___f_3162_, 18, v___x_3123_);
v___x_3163_ = lean_array_push(v_fst_3136_, v___x_3160_);
v___x_3216_ = lean_nat_sub(v_stop_3150_, v_start_3149_);
v___x_3217_ = lean_nat_dec_lt(v_a_3124_, v___x_3216_);
lean_dec(v___x_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
v___x_3218_ = l_outOfBounds___redArg(v___x_3152_);
v___y_3165_ = v___x_3218_;
goto v___jp_3164_;
}
else
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Subarray_get___redArg(v___x_3122_, v_a_3124_);
v___y_3165_ = v___x_3219_;
goto v___jp_3164_;
}
v___jp_3164_:
{
lean_object* v___x_3166_; 
lean_inc(v___y_3129_);
lean_inc_ref(v___y_3128_);
lean_inc(v___y_3127_);
lean_inc_ref(v___y_3126_);
v___x_3166_ = lean_infer_type(v___y_3165_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3168_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3167_);
lean_dec_ref_known(v___x_3166_, 1);
lean_inc(v___x_3123_);
lean_inc(v___x_3157_);
v___x_3168_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3167_, v___x_3157_, v___x_3123_, v___f_3162_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v_snd_3170_; lean_object* v_fst_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3199_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3168_, 1);
v_snd_3170_ = lean_ctor_get(v_a_3169_, 1);
v_fst_3171_ = lean_ctor_get(v_a_3169_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_a_3169_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3173_ = v_a_3169_;
v_isShared_3174_ = v_isSharedCheck_3199_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_snd_3170_);
lean_inc(v_fst_3171_);
lean_dec(v_a_3169_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3199_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v_fst_3175_; lean_object* v_snd_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3198_; 
v_fst_3175_ = lean_ctor_get(v_snd_3170_, 0);
v_snd_3176_ = lean_ctor_get(v_snd_3170_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_snd_3170_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3178_ = v_snd_3170_;
v_isShared_3179_ = v_isSharedCheck_3198_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_snd_3176_);
lean_inc(v_fst_3175_);
lean_dec(v_snd_3170_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3198_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3185_; 
v___x_3180_ = lean_array_push(v_fst_3137_, v_fst_3171_);
v___x_3181_ = lean_array_push(v_fst_3142_, v_fst_3175_);
v___x_3182_ = lean_array_push(v_snd_3143_, v_snd_3176_);
v___x_3183_ = lean_nat_add(v_fst_3138_, v___x_3156_);
lean_dec(v_fst_3138_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 1, v___x_3182_);
lean_ctor_set(v___x_3178_, 0, v___x_3181_);
v___x_3185_ = v___x_3178_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3182_);
v___x_3185_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3187_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 1, v___x_3185_);
lean_ctor_set(v___x_3173_, 0, v___x_3183_);
v___x_3187_ = v___x_3173_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3183_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3189_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 1, v___x_3187_);
lean_ctor_set(v___x_3145_, 0, v___x_3180_);
v___x_3189_ = v___x_3145_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3191_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 1, v___x_3189_);
lean_ctor_set(v___x_3140_, 0, v___x_3163_);
v___x_3191_ = v___x_3140_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_nat_add(v_a_3124_, v___x_3156_);
lean_dec(v_a_3124_);
v_a_3124_ = v___x_3192_;
v_b_3125_ = v___x_3191_;
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
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec_ref(v___x_3163_);
lean_del_object(v___x_3145_);
lean_dec(v_snd_3143_);
lean_dec(v_fst_3142_);
lean_del_object(v___x_3140_);
lean_dec(v_fst_3138_);
lean_dec(v_fst_3137_);
lean_dec(v_a_3124_);
lean_dec(v___x_3123_);
lean_dec_ref(v___x_3122_);
lean_dec(v___x_3121_);
lean_dec(v_matchDeclName_3120_);
lean_dec_ref(v___x_3119_);
lean_dec_ref(v___x_3118_);
lean_dec(v___x_3117_);
lean_dec_ref(v_a_3116_);
lean_dec_ref(v___x_3115_);
lean_dec(v_baseName_3114_);
lean_dec_ref(v_val_3113_);
v_a_3200_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3168_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3168_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec_ref(v___x_3163_);
lean_dec_ref(v___f_3162_);
lean_del_object(v___x_3145_);
lean_dec(v_snd_3143_);
lean_dec(v_fst_3142_);
lean_del_object(v___x_3140_);
lean_dec(v_fst_3138_);
lean_dec(v_fst_3137_);
lean_dec(v_a_3124_);
lean_dec(v___x_3123_);
lean_dec_ref(v___x_3122_);
lean_dec(v___x_3121_);
lean_dec(v_matchDeclName_3120_);
lean_dec_ref(v___x_3119_);
lean_dec_ref(v___x_3118_);
lean_dec(v___x_3117_);
lean_dec_ref(v_a_3116_);
lean_dec_ref(v___x_3115_);
lean_dec(v_baseName_3114_);
lean_dec_ref(v_val_3113_);
v_a_3208_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3166_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3166_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_3223_ = _args[0];
lean_object* v_val_3224_ = _args[1];
lean_object* v_baseName_3225_ = _args[2];
lean_object* v___x_3226_ = _args[3];
lean_object* v_a_3227_ = _args[4];
lean_object* v___x_3228_ = _args[5];
lean_object* v___x_3229_ = _args[6];
lean_object* v___x_3230_ = _args[7];
lean_object* v_matchDeclName_3231_ = _args[8];
lean_object* v___x_3232_ = _args[9];
lean_object* v___x_3233_ = _args[10];
lean_object* v___x_3234_ = _args[11];
lean_object* v_a_3235_ = _args[12];
lean_object* v_b_3236_ = _args[13];
lean_object* v___y_3237_ = _args[14];
lean_object* v___y_3238_ = _args[15];
lean_object* v___y_3239_ = _args[16];
lean_object* v___y_3240_ = _args[17];
lean_object* v___y_3241_ = _args[18];
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3223_, v_val_3224_, v_baseName_3225_, v___x_3226_, v_a_3227_, v___x_3228_, v___x_3229_, v___x_3230_, v_matchDeclName_3231_, v___x_3232_, v___x_3233_, v___x_3234_, v_a_3235_, v_b_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v_upperBound_3223_);
return v_res_3242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3246_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3247_ = lean_unsigned_to_nat(6u);
v___x_3248_ = lean_unsigned_to_nat(233u);
v___x_3249_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3250_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3251_ = l_mkPanicMessageWithDecl(v___x_3250_, v___x_3249_, v___x_3248_, v___x_3247_, v___x_3246_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3264_, lean_object* v_matchDeclName_3265_, lean_object* v_numParams_3266_, lean_object* v_val_3267_, lean_object* v___x_3268_, lean_object* v_numDiscrs_3269_, lean_object* v_baseName_3270_, lean_object* v_a_3271_, lean_object* v___x_3272_, lean_object* v___x_3273_, lean_object* v___x_3274_, lean_object* v_uElimPos_x3f_3275_, lean_object* v_discrInfos_3276_, lean_object* v_overlaps_3277_, lean_object* v___f_3278_, lean_object* v___x_3279_, lean_object* v_altInfos_3280_, lean_object* v_xs_3281_, lean_object* v___matchResultType_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; uint8_t v___y_3300_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v_lower_3308_; lean_object* v_upper_3309_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_3302_ = lean_box(0);
v___x_3303_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3266_);
lean_inc_ref(v_xs_3281_);
v___x_3304_ = l_Array_toSubarray___redArg(v_xs_3281_, v___x_3303_, v_numParams_3266_);
v___x_3305_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3267_);
v___x_3306_ = lean_array_get(v___x_3268_, v_xs_3281_, v___x_3305_);
lean_dec(v___x_3305_);
v___x_3362_ = lean_array_get_size(v_xs_3281_);
v___x_3363_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3267_);
v___x_3364_ = lean_nat_sub(v___x_3362_, v___x_3363_);
lean_dec(v___x_3363_);
v___x_3365_ = lean_nat_dec_le(v___x_3364_, v___x_3303_);
if (v___x_3365_ == 0)
{
v_lower_3308_ = v___x_3364_;
v_upper_3309_ = v___x_3362_;
goto v___jp_3307_;
}
else
{
lean_dec(v___x_3364_);
v_lower_3308_ = v___x_3303_;
v_upper_3309_ = v___x_3362_;
goto v___jp_3307_;
}
v___jp_3288_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3290_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3289_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
return v___x_3290_;
}
v___jp_3291_:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3294_, 0, v___y_3292_);
lean_ctor_set(v___x_3294_, 1, v_splitterName_3264_);
lean_ctor_set(v___x_3294_, 2, v___y_3293_);
v___x_3295_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3265_, v___x_3294_, v___y_3286_);
return v___x_3295_;
}
v___jp_3296_:
{
lean_object* v___x_3301_; 
lean_inc(v_matchDeclName_3265_);
v___x_3301_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3265_, v___y_3300_, v___y_3299_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_dec_ref_known(v___x_3301_, 1);
v___y_3292_ = v___y_3297_;
v___y_3293_ = v___y_3298_;
goto v___jp_3291_;
}
else
{
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v_matchDeclName_3265_);
lean_dec(v_splitterName_3264_);
return v___x_3301_;
}
}
v___jp_3307_:
{
lean_object* v___x_3310_; lean_object* v_start_3311_; lean_object* v_stop_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_inc_ref(v_xs_3281_);
v___x_3310_ = l_Array_toSubarray___redArg(v_xs_3281_, v_lower_3308_, v_upper_3309_);
v_start_3311_ = lean_ctor_get(v___x_3310_, 1);
lean_inc(v_start_3311_);
v_stop_3312_ = lean_ctor_get(v___x_3310_, 2);
lean_inc(v_stop_3312_);
v___x_3313_ = lean_unsigned_to_nat(1u);
v___x_3314_ = lean_nat_add(v_numParams_3266_, v___x_3313_);
v___x_3315_ = lean_nat_add(v___x_3314_, v_numDiscrs_3269_);
v___x_3316_ = lean_nat_sub(v_stop_3312_, v_start_3311_);
lean_dec(v_start_3311_);
lean_dec(v_stop_3312_);
v___x_3317_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3318_ = l_Array_toSubarray___redArg(v_xs_3281_, v___x_3314_, v___x_3315_);
lean_inc(v___x_3273_);
lean_inc(v_matchDeclName_3265_);
lean_inc(v___x_3272_);
v___x_3319_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3316_, v_val_3267_, v_baseName_3270_, v___x_3318_, v_a_3271_, v___x_3272_, v___x_3304_, v___x_3306_, v_matchDeclName_3265_, v___x_3273_, v___x_3310_, v___x_3274_, v___x_3303_, v___x_3317_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___x_3316_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v_snd_3321_; lean_object* v_snd_3322_; lean_object* v_snd_3323_; lean_object* v_fst_3324_; lean_object* v_fst_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3352_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v_snd_3321_ = lean_ctor_get(v_a_3320_, 1);
v_snd_3322_ = lean_ctor_get(v_snd_3321_, 1);
v_snd_3323_ = lean_ctor_get(v_snd_3322_, 1);
lean_inc(v_snd_3323_);
v_fst_3324_ = lean_ctor_get(v_a_3320_, 0);
lean_inc(v_fst_3324_);
lean_dec(v_a_3320_);
v_fst_3325_ = lean_ctor_get(v_snd_3323_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_snd_3323_);
if (v_isSharedCheck_3352_ == 0)
{
lean_object* v_unused_3353_; 
v_unused_3353_ = lean_ctor_get(v_snd_3323_, 1);
lean_dec(v_unused_3353_);
v___x_3327_ = v_snd_3323_;
v_isShared_3328_ = v_isSharedCheck_3352_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_fst_3325_);
lean_dec(v_snd_3323_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3352_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; uint8_t v___x_3330_; 
lean_inc_ref(v_overlaps_3277_);
lean_inc(v_fst_3325_);
v___x_3329_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3329_, 0, v_numParams_3266_);
lean_ctor_set(v___x_3329_, 1, v_numDiscrs_3269_);
lean_ctor_set(v___x_3329_, 2, v_fst_3325_);
lean_ctor_set(v___x_3329_, 3, v_uElimPos_x3f_3275_);
lean_ctor_set(v___x_3329_, 4, v_discrInfos_3276_);
lean_ctor_set(v___x_3329_, 5, v_overlaps_3277_);
v___x_3330_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3277_);
lean_dec_ref(v_overlaps_3277_);
if (v___x_3330_ == 0)
{
uint8_t v___x_3331_; 
lean_del_object(v___x_3327_);
lean_dec(v_fst_3325_);
lean_dec_ref(v___x_3279_);
lean_dec(v___x_3273_);
lean_dec(v___x_3272_);
v___x_3331_ = 1;
v___y_3297_ = v_fst_3324_;
v___y_3298_ = v___x_3329_;
v___y_3299_ = v___f_3278_;
v___y_3300_ = v___x_3331_;
goto v___jp_3296_;
}
else
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3333_ = lean_find_expr(v___x_3332_, v___x_3279_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; 
lean_dec_ref(v___f_3278_);
v___x_3334_ = lean_array_get_size(v_altInfos_3280_);
v___x_3335_ = lean_array_get_size(v_fst_3325_);
v___x_3336_ = lean_nat_dec_eq(v___x_3334_, v___x_3335_);
if (v___x_3336_ == 0)
{
lean_dec_ref_known(v___x_3329_, 6);
lean_del_object(v___x_3327_);
lean_dec(v_fst_3325_);
lean_dec(v_fst_3324_);
lean_dec_ref(v___x_3279_);
lean_dec(v___x_3273_);
lean_dec(v___x_3272_);
lean_dec(v_matchDeclName_3265_);
lean_dec(v_splitterName_3264_);
goto v___jp_3288_;
}
else
{
uint8_t v___x_3337_; 
v___x_3337_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3280_, v_fst_3325_, v___x_3334_);
lean_dec(v_fst_3325_);
if (v___x_3337_ == 0)
{
lean_dec_ref_known(v___x_3329_, 6);
lean_del_object(v___x_3327_);
lean_dec(v_fst_3324_);
lean_dec_ref(v___x_3279_);
lean_dec(v___x_3273_);
lean_dec(v___x_3272_);
lean_dec(v_matchDeclName_3265_);
lean_dec(v_splitterName_3264_);
goto v___jp_3288_;
}
else
{
uint8_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; lean_object* v___x_3344_; 
v___x_3338_ = 0;
lean_inc_n(v_splitterName_3264_, 2);
v___x_3339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3339_, 0, v_splitterName_3264_);
lean_ctor_set(v___x_3339_, 1, v___x_3273_);
lean_ctor_set(v___x_3339_, 2, v___x_3279_);
lean_inc(v_matchDeclName_3265_);
v___x_3340_ = l_Lean_mkConst(v_matchDeclName_3265_, v___x_3272_);
v___x_3341_ = lean_box(1);
v___x_3342_ = 1;
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 1);
lean_ctor_set(v___x_3327_, 1, v___x_3302_);
lean_ctor_set(v___x_3327_, 0, v_splitterName_3264_);
v___x_3344_ = v___x_3327_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_splitterName_3264_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v___x_3302_);
v___x_3344_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3345_, 0, v___x_3339_);
lean_ctor_set(v___x_3345_, 1, v___x_3340_);
lean_ctor_set(v___x_3345_, 2, v___x_3341_);
lean_ctor_set(v___x_3345_, 3, v___x_3344_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*4, v___x_3342_);
v___x_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
lean_inc_ref(v___x_3346_);
v___x_3347_ = l_Lean_addDecl(v___x_3346_, v___x_3338_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3347_) == 0)
{
uint8_t v___x_3348_; lean_object* v___x_3349_; 
lean_dec_ref_known(v___x_3347_, 1);
v___x_3348_ = 0;
lean_inc(v_splitterName_3264_);
v___x_3349_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3264_, v___x_3348_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v___x_3350_; 
lean_dec_ref_known(v___x_3349_, 1);
v___x_3350_ = l_Lean_compileDecl(v___x_3346_, v___x_3338_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_dec_ref_known(v___x_3350_, 1);
v___y_3292_ = v_fst_3324_;
v___y_3293_ = v___x_3329_;
goto v___jp_3291_;
}
else
{
lean_dec_ref_known(v___x_3329_, 6);
lean_dec(v_fst_3324_);
lean_dec(v_matchDeclName_3265_);
lean_dec(v_splitterName_3264_);
return v___x_3350_;
}
}
else
{
lean_dec_ref_known(v___x_3346_, 1);
lean_dec_ref_known(v___x_3329_, 6);
lean_dec(v_fst_3324_);
lean_dec(v_matchDeclName_3265_);
lean_dec(v_splitterName_3264_);
return v___x_3349_;
}
}
else
{
lean_dec_ref_known(v___x_3346_, 1);
lean_dec_ref_known(v___x_3329_, 6);
lean_dec(v_fst_3324_);
lean_dec(v_matchDeclName_3265_);
lean_dec(v_splitterName_3264_);
return v___x_3347_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3333_, 1);
lean_del_object(v___x_3327_);
lean_dec(v_fst_3325_);
lean_dec_ref(v___x_3279_);
lean_dec(v___x_3273_);
lean_dec(v___x_3272_);
v___y_3297_ = v_fst_3324_;
v___y_3298_ = v___x_3329_;
v___y_3299_ = v___f_3278_;
v___y_3300_ = v___x_3330_;
goto v___jp_3296_;
}
}
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec_ref(v___x_3279_);
lean_dec_ref(v___f_3278_);
lean_dec_ref(v_overlaps_3277_);
lean_dec_ref(v_discrInfos_3276_);
lean_dec(v_uElimPos_x3f_3275_);
lean_dec(v___x_3273_);
lean_dec(v___x_3272_);
lean_dec(v_numDiscrs_3269_);
lean_dec(v_numParams_3266_);
lean_dec(v_matchDeclName_3265_);
lean_dec(v_splitterName_3264_);
v_a_3354_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3319_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3319_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3366_ = _args[0];
lean_object* v_matchDeclName_3367_ = _args[1];
lean_object* v_numParams_3368_ = _args[2];
lean_object* v_val_3369_ = _args[3];
lean_object* v___x_3370_ = _args[4];
lean_object* v_numDiscrs_3371_ = _args[5];
lean_object* v_baseName_3372_ = _args[6];
lean_object* v_a_3373_ = _args[7];
lean_object* v___x_3374_ = _args[8];
lean_object* v___x_3375_ = _args[9];
lean_object* v___x_3376_ = _args[10];
lean_object* v_uElimPos_x3f_3377_ = _args[11];
lean_object* v_discrInfos_3378_ = _args[12];
lean_object* v_overlaps_3379_ = _args[13];
lean_object* v___f_3380_ = _args[14];
lean_object* v___x_3381_ = _args[15];
lean_object* v_altInfos_3382_ = _args[16];
lean_object* v_xs_3383_ = _args[17];
lean_object* v___matchResultType_3384_ = _args[18];
lean_object* v___y_3385_ = _args[19];
lean_object* v___y_3386_ = _args[20];
lean_object* v___y_3387_ = _args[21];
lean_object* v___y_3388_ = _args[22];
lean_object* v___y_3389_ = _args[23];
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3366_, v_matchDeclName_3367_, v_numParams_3368_, v_val_3369_, v___x_3370_, v_numDiscrs_3371_, v_baseName_3372_, v_a_3373_, v___x_3374_, v___x_3375_, v___x_3376_, v_uElimPos_x3f_3377_, v_discrInfos_3378_, v_overlaps_3379_, v___f_3380_, v___x_3381_, v_altInfos_3382_, v_xs_3383_, v___matchResultType_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec_ref(v___matchResultType_3384_);
lean_dec_ref(v_altInfos_3382_);
lean_dec_ref(v___x_3370_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
if (lean_obj_tag(v_a_3391_) == 0)
{
lean_object* v___x_3393_; 
v___x_3393_ = l_List_reverse___redArg(v_a_3392_);
return v___x_3393_;
}
else
{
lean_object* v_head_3394_; lean_object* v_tail_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3404_; 
v_head_3394_ = lean_ctor_get(v_a_3391_, 0);
v_tail_3395_ = lean_ctor_get(v_a_3391_, 1);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_a_3391_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3397_ = v_a_3391_;
v_isShared_3398_ = v_isSharedCheck_3404_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_tail_3395_);
lean_inc(v_head_3394_);
lean_dec(v_a_3391_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3404_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = l_Lean_mkLevelParam(v_head_3394_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 1, v_a_3392_);
lean_ctor_set(v___x_3397_, 0, v___x_3399_);
v___x_3401_ = v___x_3397_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v_a_3392_);
v___x_3401_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
v_a_3391_ = v_tail_3395_;
v_a_3392_ = v___x_3401_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3405_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
return v___x_3407_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3409_ = lean_unsigned_to_nat(0u);
v___x_3410_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
lean_ctor_set(v___x_3410_, 2, v___x_3409_);
lean_ctor_set(v___x_3410_, 3, v___x_3409_);
lean_ctor_set(v___x_3410_, 4, v___x_3408_);
lean_ctor_set(v___x_3410_, 5, v___x_3408_);
lean_ctor_set(v___x_3410_, 6, v___x_3408_);
lean_ctor_set(v___x_3410_, 7, v___x_3408_);
lean_ctor_set(v___x_3410_, 8, v___x_3408_);
lean_ctor_set(v___x_3410_, 9, v___x_3408_);
lean_ctor_set(v___x_3410_, 10, v___x_3408_);
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3411_ = lean_box(1);
v___x_3412_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3413_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set(v___x_3414_, 1, v___x_3412_);
lean_ctor_set(v___x_3414_, 2, v___x_3411_);
return v___x_3414_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_3417_ = l_Lean_stringToMessageData(v___x_3416_);
return v___x_3417_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_3420_ = l_Lean_stringToMessageData(v___x_3419_);
return v___x_3420_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_3423_ = l_Lean_stringToMessageData(v___x_3422_);
return v___x_3423_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
return v___x_3426_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_3429_ = l_Lean_stringToMessageData(v___x_3428_);
return v___x_3429_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_3432_ = l_Lean_stringToMessageData(v___x_3431_);
return v___x_3432_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_3435_ = l_Lean_stringToMessageData(v___x_3434_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3436_, lean_object* v_declHint_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v___x_3440_; lean_object* v_env_3441_; uint8_t v___x_3442_; 
v___x_3440_ = lean_st_ref_get(v___y_3438_);
v_env_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc_ref(v_env_3441_);
lean_dec(v___x_3440_);
v___x_3442_ = l_Lean_Name_isAnonymous(v_declHint_3437_);
if (v___x_3442_ == 0)
{
uint8_t v_isExporting_3443_; 
v_isExporting_3443_ = lean_ctor_get_uint8(v_env_3441_, sizeof(void*)*8);
if (v_isExporting_3443_ == 0)
{
lean_object* v___x_3444_; 
lean_dec_ref(v_env_3441_);
lean_dec(v_declHint_3437_);
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v_msg_3436_);
return v___x_3444_;
}
else
{
lean_object* v___x_3445_; uint8_t v___x_3446_; 
lean_inc_ref(v_env_3441_);
v___x_3445_ = l_Lean_Environment_setExporting(v_env_3441_, v___x_3442_);
lean_inc(v_declHint_3437_);
lean_inc_ref(v___x_3445_);
v___x_3446_ = l_Lean_Environment_contains(v___x_3445_, v_declHint_3437_, v_isExporting_3443_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
lean_dec_ref(v___x_3445_);
lean_dec_ref(v_env_3441_);
lean_dec(v_declHint_3437_);
v___x_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3447_, 0, v_msg_3436_);
return v___x_3447_;
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v_c_3453_; lean_object* v___x_3454_; 
v___x_3448_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3449_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3450_ = l_Lean_Options_empty;
v___x_3451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3445_);
lean_ctor_set(v___x_3451_, 1, v___x_3448_);
lean_ctor_set(v___x_3451_, 2, v___x_3449_);
lean_ctor_set(v___x_3451_, 3, v___x_3450_);
lean_inc(v_declHint_3437_);
v___x_3452_ = l_Lean_MessageData_ofConstName(v_declHint_3437_, v___x_3442_);
v_c_3453_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3453_, 0, v___x_3451_);
lean_ctor_set(v_c_3453_, 1, v___x_3452_);
v___x_3454_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3441_, v_declHint_3437_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_dec_ref(v_env_3441_);
lean_dec(v_declHint_3437_);
v___x_3455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
lean_ctor_set(v___x_3456_, 1, v_c_3453_);
v___x_3457_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = l_Lean_MessageData_note(v___x_3458_);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v_msg_3436_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
return v___x_3461_;
}
else
{
lean_object* v_val_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3497_; 
v_val_3462_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3464_ = v___x_3454_;
v_isShared_3465_ = v_isSharedCheck_3497_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_val_3462_);
lean_dec(v___x_3454_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3497_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v_mod_3469_; uint8_t v___x_3470_; 
v___x_3466_ = lean_box(0);
v___x_3467_ = l_Lean_Environment_header(v_env_3441_);
lean_dec_ref(v_env_3441_);
v___x_3468_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3467_);
v_mod_3469_ = lean_array_get(v___x_3466_, v___x_3468_, v_val_3462_);
lean_dec(v_val_3462_);
lean_dec_ref(v___x_3468_);
v___x_3470_ = l_Lean_isPrivateName(v_declHint_3437_);
lean_dec(v_declHint_3437_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3471_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
lean_ctor_set(v___x_3472_, 1, v_c_3453_);
v___x_3473_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3472_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = l_Lean_MessageData_ofName(v_mod_3469_);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3474_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3476_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = l_Lean_MessageData_note(v___x_3478_);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v_msg_3436_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set_tag(v___x_3464_, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3480_);
v___x_3482_ = v___x_3464_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3495_; 
v___x_3484_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
lean_ctor_set(v___x_3485_, 1, v_c_3453_);
v___x_3486_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = l_Lean_MessageData_ofName(v_mod_3469_);
v___x_3489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3487_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = l_Lean_MessageData_note(v___x_3491_);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v_msg_3436_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set_tag(v___x_3464_, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3493_);
v___x_3495_ = v___x_3464_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3498_; 
lean_dec_ref(v_env_3441_);
lean_dec(v_declHint_3437_);
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_msg_3436_);
return v___x_3498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3499_, lean_object* v_declHint_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3499_, v_declHint_3500_, v___y_3501_);
lean_dec(v___y_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3504_, lean_object* v_declHint_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3521_; 
v___x_3511_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3504_, v_declHint_3505_, v___y_3509_);
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3521_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3521_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; 
v___x_3516_ = l_Lean_unknownIdentifierMessageTag;
v___x_3517_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v_a_3512_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v___x_3517_);
v___x_3519_ = v___x_3514_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3522_, lean_object* v_declHint_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3522_, v_declHint_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3530_, lean_object* v_msg_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_toCold_3537_; lean_object* v_options_3538_; lean_object* v_currRecDepth_3539_; lean_object* v_maxRecDepth_3540_; lean_object* v_ref_3541_; lean_object* v_currNamespace_3542_; lean_object* v_openDecls_3543_; lean_object* v_initHeartbeats_3544_; lean_object* v_maxHeartbeats_3545_; lean_object* v_currMacroScope_3546_; uint8_t v_diag_3547_; uint8_t v_suppressElabErrors_3548_; lean_object* v_ref_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v_toCold_3537_ = lean_ctor_get(v___y_3534_, 0);
v_options_3538_ = lean_ctor_get(v___y_3534_, 1);
v_currRecDepth_3539_ = lean_ctor_get(v___y_3534_, 2);
v_maxRecDepth_3540_ = lean_ctor_get(v___y_3534_, 3);
v_ref_3541_ = lean_ctor_get(v___y_3534_, 4);
v_currNamespace_3542_ = lean_ctor_get(v___y_3534_, 5);
v_openDecls_3543_ = lean_ctor_get(v___y_3534_, 6);
v_initHeartbeats_3544_ = lean_ctor_get(v___y_3534_, 7);
v_maxHeartbeats_3545_ = lean_ctor_get(v___y_3534_, 8);
v_currMacroScope_3546_ = lean_ctor_get(v___y_3534_, 9);
v_diag_3547_ = lean_ctor_get_uint8(v___y_3534_, sizeof(void*)*10);
v_suppressElabErrors_3548_ = lean_ctor_get_uint8(v___y_3534_, sizeof(void*)*10 + 1);
v_ref_3549_ = l_Lean_replaceRef(v_ref_3530_, v_ref_3541_);
lean_inc(v_currMacroScope_3546_);
lean_inc(v_maxHeartbeats_3545_);
lean_inc(v_initHeartbeats_3544_);
lean_inc(v_openDecls_3543_);
lean_inc(v_currNamespace_3542_);
lean_inc(v_maxRecDepth_3540_);
lean_inc(v_currRecDepth_3539_);
lean_inc_ref(v_options_3538_);
lean_inc_ref(v_toCold_3537_);
v___x_3550_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3550_, 0, v_toCold_3537_);
lean_ctor_set(v___x_3550_, 1, v_options_3538_);
lean_ctor_set(v___x_3550_, 2, v_currRecDepth_3539_);
lean_ctor_set(v___x_3550_, 3, v_maxRecDepth_3540_);
lean_ctor_set(v___x_3550_, 4, v_ref_3549_);
lean_ctor_set(v___x_3550_, 5, v_currNamespace_3542_);
lean_ctor_set(v___x_3550_, 6, v_openDecls_3543_);
lean_ctor_set(v___x_3550_, 7, v_initHeartbeats_3544_);
lean_ctor_set(v___x_3550_, 8, v_maxHeartbeats_3545_);
lean_ctor_set(v___x_3550_, 9, v_currMacroScope_3546_);
lean_ctor_set_uint8(v___x_3550_, sizeof(void*)*10, v_diag_3547_);
lean_ctor_set_uint8(v___x_3550_, sizeof(void*)*10 + 1, v_suppressElabErrors_3548_);
v___x_3551_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3531_, v___y_3532_, v___y_3533_, v___x_3550_, v___y_3535_);
lean_dec_ref_known(v___x_3550_, 10);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3552_, lean_object* v_msg_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3552_, v_msg_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v_ref_3552_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3560_, lean_object* v_msg_3561_, lean_object* v_declHint_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v___x_3568_; lean_object* v_a_3569_; lean_object* v___x_3570_; 
v___x_3568_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3561_, v_declHint_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref(v___x_3568_);
v___x_3570_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3560_, v_a_3569_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3571_, lean_object* v_msg_3572_, lean_object* v_declHint_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3571_, v_msg_3572_, v_declHint_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v_ref_3571_);
return v_res_3579_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3581_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3582_ = l_Lean_stringToMessageData(v___x_3581_);
return v___x_3582_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3585_ = l_Lean_stringToMessageData(v___x_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3586_, lean_object* v_constName_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v___x_3593_; uint8_t v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3593_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3594_ = 0;
lean_inc(v_constName_3587_);
v___x_3595_ = l_Lean_MessageData_ofConstName(v_constName_3587_, v___x_3594_);
v___x_3596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3593_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3586_, v___x_3598_, v_constName_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3600_, lean_object* v_constName_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3600_, v_constName_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v_ref_3600_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_ref_3614_; lean_object* v___x_3615_; 
v_ref_3614_ = lean_ctor_get(v___y_3611_, 4);
v___x_3615_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3614_, v_constName_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___x_3629_; lean_object* v_env_3630_; uint8_t v___x_3631_; lean_object* v___x_3632_; 
v___x_3629_ = lean_st_ref_get(v___y_3627_);
v_env_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc_ref(v_env_3630_);
lean_dec(v___x_3629_);
v___x_3631_ = 0;
lean_inc(v_constName_3623_);
v___x_3632_ = l_Lean_Environment_find_x3f(v_env_3630_, v_constName_3623_, v___x_3631_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
return v___x_3633_;
}
else
{
lean_object* v_val_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_constName_3623_);
v_val_3634_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3632_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_val_3634_);
lean_dec(v___x_3632_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 0);
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_val_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
return v_res_3648_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3651_ = l_Lean_stringToMessageData(v___x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3652_, lean_object* v_baseName_3653_, lean_object* v_splitterName_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v___x_3660_; uint8_t v_foApprox_3661_; uint8_t v_ctxApprox_3662_; uint8_t v_quasiPatternApprox_3663_; uint8_t v_constApprox_3664_; uint8_t v_isDefEqStuckEx_3665_; uint8_t v_unificationHints_3666_; uint8_t v_proofIrrelevance_3667_; uint8_t v_assignSyntheticOpaque_3668_; uint8_t v_offsetCnstrs_3669_; uint8_t v_transparency_3670_; uint8_t v_univApprox_3671_; uint8_t v_iota_3672_; uint8_t v_beta_3673_; uint8_t v_proj_3674_; uint8_t v_zeta_3675_; uint8_t v_zetaDelta_3676_; uint8_t v_zetaUnused_3677_; uint8_t v_zetaHave_3678_; uint8_t v_canUnfoldPredicateConfig_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3742_; 
v___x_3660_ = l_Lean_Meta_Context_config(v_a_3655_);
v_foApprox_3661_ = lean_ctor_get_uint8(v___x_3660_, 0);
v_ctxApprox_3662_ = lean_ctor_get_uint8(v___x_3660_, 1);
v_quasiPatternApprox_3663_ = lean_ctor_get_uint8(v___x_3660_, 2);
v_constApprox_3664_ = lean_ctor_get_uint8(v___x_3660_, 3);
v_isDefEqStuckEx_3665_ = lean_ctor_get_uint8(v___x_3660_, 4);
v_unificationHints_3666_ = lean_ctor_get_uint8(v___x_3660_, 5);
v_proofIrrelevance_3667_ = lean_ctor_get_uint8(v___x_3660_, 6);
v_assignSyntheticOpaque_3668_ = lean_ctor_get_uint8(v___x_3660_, 7);
v_offsetCnstrs_3669_ = lean_ctor_get_uint8(v___x_3660_, 8);
v_transparency_3670_ = lean_ctor_get_uint8(v___x_3660_, 9);
v_univApprox_3671_ = lean_ctor_get_uint8(v___x_3660_, 11);
v_iota_3672_ = lean_ctor_get_uint8(v___x_3660_, 12);
v_beta_3673_ = lean_ctor_get_uint8(v___x_3660_, 13);
v_proj_3674_ = lean_ctor_get_uint8(v___x_3660_, 14);
v_zeta_3675_ = lean_ctor_get_uint8(v___x_3660_, 15);
v_zetaDelta_3676_ = lean_ctor_get_uint8(v___x_3660_, 16);
v_zetaUnused_3677_ = lean_ctor_get_uint8(v___x_3660_, 17);
v_zetaHave_3678_ = lean_ctor_get_uint8(v___x_3660_, 18);
v_canUnfoldPredicateConfig_3679_ = lean_ctor_get_uint8(v___x_3660_, 19);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3681_ = v___x_3660_;
v_isShared_3682_ = v_isSharedCheck_3742_;
goto v_resetjp_3680_;
}
else
{
lean_dec(v___x_3660_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3742_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
uint8_t v_trackZetaDelta_3683_; lean_object* v_zetaDeltaSet_3684_; lean_object* v_lctx_3685_; lean_object* v_localInstances_3686_; lean_object* v_defEqCtx_x3f_3687_; lean_object* v_synthPendingDepth_3688_; lean_object* v_customCanUnfoldPredicate_x3f_3689_; uint8_t v_univApprox_3690_; uint8_t v_inTypeClassResolution_3691_; uint8_t v_cacheInferType_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3740_; 
v_trackZetaDelta_3683_ = lean_ctor_get_uint8(v_a_3655_, sizeof(void*)*7);
v_zetaDeltaSet_3684_ = lean_ctor_get(v_a_3655_, 1);
v_lctx_3685_ = lean_ctor_get(v_a_3655_, 2);
v_localInstances_3686_ = lean_ctor_get(v_a_3655_, 3);
v_defEqCtx_x3f_3687_ = lean_ctor_get(v_a_3655_, 4);
v_synthPendingDepth_3688_ = lean_ctor_get(v_a_3655_, 5);
v_customCanUnfoldPredicate_x3f_3689_ = lean_ctor_get(v_a_3655_, 6);
v_univApprox_3690_ = lean_ctor_get_uint8(v_a_3655_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3691_ = lean_ctor_get_uint8(v_a_3655_, sizeof(void*)*7 + 2);
v_cacheInferType_3692_ = lean_ctor_get_uint8(v_a_3655_, sizeof(void*)*7 + 3);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_a_3655_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; 
v_unused_3741_ = lean_ctor_get(v_a_3655_, 0);
lean_dec(v_unused_3741_);
v___x_3694_ = v_a_3655_;
v_isShared_3695_ = v_isSharedCheck_3740_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3689_);
lean_inc(v_synthPendingDepth_3688_);
lean_inc(v_defEqCtx_x3f_3687_);
lean_inc(v_localInstances_3686_);
lean_inc(v_lctx_3685_);
lean_inc(v_zetaDeltaSet_3684_);
lean_dec(v_a_3655_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3740_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
uint8_t v___x_3696_; lean_object* v___x_3698_; 
v___x_3696_ = 2;
if (v_isShared_3682_ == 0)
{
v___x_3698_ = v___x_3681_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 0, v_foApprox_3661_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 1, v_ctxApprox_3662_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 2, v_quasiPatternApprox_3663_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 3, v_constApprox_3664_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 4, v_isDefEqStuckEx_3665_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 5, v_unificationHints_3666_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 6, v_proofIrrelevance_3667_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 7, v_assignSyntheticOpaque_3668_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 8, v_offsetCnstrs_3669_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 9, v_transparency_3670_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 11, v_univApprox_3671_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 12, v_iota_3672_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 13, v_beta_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 14, v_proj_3674_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 15, v_zeta_3675_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 16, v_zetaDelta_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 17, v_zetaUnused_3677_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 18, v_zetaHave_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3739_, 19, v_canUnfoldPredicateConfig_3679_);
v___x_3698_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
uint64_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
lean_ctor_set_uint8(v___x_3698_, 10, v___x_3696_);
v___x_3699_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3698_);
v___x_3700_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3700_, 0, v___x_3698_);
lean_ctor_set_uint64(v___x_3700_, sizeof(void*)*1, v___x_3699_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3700_);
v___x_3702_ = v___x_3694_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_zetaDeltaSet_3684_);
lean_ctor_set(v_reuseFailAlloc_3738_, 2, v_lctx_3685_);
lean_ctor_set(v_reuseFailAlloc_3738_, 3, v_localInstances_3686_);
lean_ctor_set(v_reuseFailAlloc_3738_, 4, v_defEqCtx_x3f_3687_);
lean_ctor_set(v_reuseFailAlloc_3738_, 5, v_synthPendingDepth_3688_);
lean_ctor_set(v_reuseFailAlloc_3738_, 6, v_customCanUnfoldPredicate_x3f_3689_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*7, v_trackZetaDelta_3683_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*7 + 1, v_univApprox_3690_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3691_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*7 + 3, v_cacheInferType_3692_);
v___x_3702_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3703_; 
lean_inc(v_matchDeclName_3652_);
v___x_3703_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3652_, v___x_3702_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3705_; lean_object* v_a_3706_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_a_3704_);
lean_dec_ref_known(v___x_3703_, 1);
lean_inc(v_matchDeclName_3652_);
v___x_3705_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_3652_, v_a_3658_);
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref(v___x_3705_);
if (lean_obj_tag(v_a_3706_) == 1)
{
lean_object* v_val_3707_; lean_object* v_numParams_3708_; lean_object* v_numDiscrs_3709_; lean_object* v_altInfos_3710_; lean_object* v_uElimPos_x3f_3711_; lean_object* v_discrInfos_3712_; lean_object* v_overlaps_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___f_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___f_3721_; uint8_t v___x_3722_; lean_object* v___x_3723_; 
v_val_3707_ = lean_ctor_get(v_a_3706_, 0);
lean_inc(v_val_3707_);
lean_dec_ref_known(v_a_3706_, 1);
v_numParams_3708_ = lean_ctor_get(v_val_3707_, 0);
lean_inc(v_numParams_3708_);
v_numDiscrs_3709_ = lean_ctor_get(v_val_3707_, 1);
lean_inc(v_numDiscrs_3709_);
v_altInfos_3710_ = lean_ctor_get(v_val_3707_, 2);
lean_inc_ref(v_altInfos_3710_);
v_uElimPos_x3f_3711_ = lean_ctor_get(v_val_3707_, 3);
lean_inc(v_uElimPos_x3f_3711_);
v_discrInfos_3712_ = lean_ctor_get(v_val_3707_, 4);
lean_inc_ref(v_discrInfos_3712_);
v_overlaps_3713_ = lean_ctor_get(v_val_3707_, 5);
lean_inc_ref_n(v_overlaps_3713_, 2);
v___x_3714_ = l_Lean_instInhabitedExpr;
v___x_3715_ = l_Lean_ConstantInfo_levelParams(v_a_3704_);
v___x_3716_ = lean_box(0);
lean_inc(v___x_3715_);
v___x_3717_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_3715_, v___x_3716_);
lean_inc(v_splitterName_3654_);
v___f_3718_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3718_, 0, v_overlaps_3713_);
lean_closure_set(v___f_3718_, 1, v_splitterName_3654_);
v___x_3719_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3712_);
v___x_3720_ = l_Lean_ConstantInfo_type(v_a_3704_);
lean_inc_ref(v___x_3720_);
v___f_3721_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3721_, 0, v_splitterName_3654_);
lean_closure_set(v___f_3721_, 1, v_matchDeclName_3652_);
lean_closure_set(v___f_3721_, 2, v_numParams_3708_);
lean_closure_set(v___f_3721_, 3, v_val_3707_);
lean_closure_set(v___f_3721_, 4, v___x_3714_);
lean_closure_set(v___f_3721_, 5, v_numDiscrs_3709_);
lean_closure_set(v___f_3721_, 6, v_baseName_3653_);
lean_closure_set(v___f_3721_, 7, v_a_3704_);
lean_closure_set(v___f_3721_, 8, v___x_3717_);
lean_closure_set(v___f_3721_, 9, v___x_3715_);
lean_closure_set(v___f_3721_, 10, v___x_3719_);
lean_closure_set(v___f_3721_, 11, v_uElimPos_x3f_3711_);
lean_closure_set(v___f_3721_, 12, v_discrInfos_3712_);
lean_closure_set(v___f_3721_, 13, v_overlaps_3713_);
lean_closure_set(v___f_3721_, 14, v___f_3718_);
lean_closure_set(v___f_3721_, 15, v___x_3720_);
lean_closure_set(v___f_3721_, 16, v_altInfos_3710_);
v___x_3722_ = 0;
v___x_3723_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3720_, v___f_3721_, v___x_3722_, v___x_3722_, v___x_3702_, v_a_3656_, v_a_3657_, v_a_3658_);
lean_dec_ref(v___x_3702_);
return v___x_3723_;
}
else
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
lean_dec(v_a_3706_);
lean_dec(v_a_3704_);
lean_dec(v_splitterName_3654_);
lean_dec(v_baseName_3653_);
v___x_3724_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3725_ = l_Lean_MessageData_ofName(v_matchDeclName_3652_);
v___x_3726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3724_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3728_, v___x_3702_, v_a_3656_, v_a_3657_, v_a_3658_);
lean_dec_ref(v___x_3702_);
return v___x_3729_;
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v___x_3702_);
lean_dec(v_splitterName_3654_);
lean_dec(v_baseName_3653_);
lean_dec(v_matchDeclName_3652_);
v_a_3730_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3703_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3703_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3743_, lean_object* v_baseName_3744_, lean_object* v_splitterName_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3743_, v_baseName_3744_, v_splitterName_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
return v_res_3751_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3752_, lean_object* v_ys_3753_, lean_object* v_hsz_3754_, lean_object* v_x_3755_, lean_object* v_x_3756_){
_start:
{
uint8_t v___x_3757_; 
v___x_3757_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3752_, v_ys_3753_, v_x_3755_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3758_, lean_object* v_ys_3759_, lean_object* v_hsz_3760_, lean_object* v_x_3761_, lean_object* v_x_3762_){
_start:
{
uint8_t v_res_3763_; lean_object* v_r_3764_; 
v_res_3763_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3758_, v_ys_3759_, v_hsz_3760_, v_x_3761_, v_x_3762_);
lean_dec_ref(v_ys_3759_);
lean_dec_ref(v_xs_3758_);
v_r_3764_ = lean_box(v_res_3763_);
return v_r_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3765_, lean_object* v_R_3766_, lean_object* v_a_3767_, lean_object* v_b_3768_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3767_, v_b_3768_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3770_, lean_object* v_val_3771_, lean_object* v_baseName_3772_, lean_object* v___x_3773_, lean_object* v_a_3774_, lean_object* v___x_3775_, lean_object* v___x_3776_, lean_object* v___x_3777_, lean_object* v_matchDeclName_3778_, lean_object* v___x_3779_, lean_object* v___x_3780_, lean_object* v___x_3781_, lean_object* v_inst_3782_, lean_object* v_R_3783_, lean_object* v_a_3784_, lean_object* v_b_3785_, lean_object* v_c_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3770_, v_val_3771_, v_baseName_3772_, v___x_3773_, v_a_3774_, v___x_3775_, v___x_3776_, v___x_3777_, v_matchDeclName_3778_, v___x_3779_, v___x_3780_, v___x_3781_, v_a_3784_, v_b_3785_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3793_ = _args[0];
lean_object* v_val_3794_ = _args[1];
lean_object* v_baseName_3795_ = _args[2];
lean_object* v___x_3796_ = _args[3];
lean_object* v_a_3797_ = _args[4];
lean_object* v___x_3798_ = _args[5];
lean_object* v___x_3799_ = _args[6];
lean_object* v___x_3800_ = _args[7];
lean_object* v_matchDeclName_3801_ = _args[8];
lean_object* v___x_3802_ = _args[9];
lean_object* v___x_3803_ = _args[10];
lean_object* v___x_3804_ = _args[11];
lean_object* v_inst_3805_ = _args[12];
lean_object* v_R_3806_ = _args[13];
lean_object* v_a_3807_ = _args[14];
lean_object* v_b_3808_ = _args[15];
lean_object* v_c_3809_ = _args[16];
lean_object* v___y_3810_ = _args[17];
lean_object* v___y_3811_ = _args[18];
lean_object* v___y_3812_ = _args[19];
lean_object* v___y_3813_ = _args[20];
lean_object* v___y_3814_ = _args[21];
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3793_, v_val_3794_, v_baseName_3795_, v___x_3796_, v_a_3797_, v___x_3798_, v___x_3799_, v___x_3800_, v_matchDeclName_3801_, v___x_3802_, v___x_3803_, v___x_3804_, v_inst_3805_, v_R_3806_, v_a_3807_, v_b_3808_, v_c_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v_upperBound_3793_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3816_, lean_object* v_constName_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3824_, lean_object* v_constName_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3824_, v_constName_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3832_, lean_object* v_ref_3833_, lean_object* v_constName_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3833_, v_constName_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3841_, lean_object* v_ref_3842_, lean_object* v_constName_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3841_, v_ref_3842_, v_constName_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v_ref_3842_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3850_, lean_object* v_ref_3851_, lean_object* v_msg_3852_, lean_object* v_declHint_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3851_, v_msg_3852_, v_declHint_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3860_, lean_object* v_ref_3861_, lean_object* v_msg_3862_, lean_object* v_declHint_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3860_, v_ref_3861_, v_msg_3862_, v_declHint_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v_ref_3861_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3870_, lean_object* v_declHint_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3870_, v_declHint_3871_, v___y_3875_);
return v___x_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3878_, lean_object* v_declHint_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3878_, v_declHint_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3886_, lean_object* v_ref_3887_, lean_object* v_msg_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3887_, v_msg_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3895_, lean_object* v_ref_3896_, lean_object* v_msg_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3895_, v_ref_3896_, v_msg_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v_ref_3896_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3904_, lean_object* v_vals_3905_, lean_object* v_i_3906_, lean_object* v_k_3907_){
_start:
{
lean_object* v___x_3908_; uint8_t v___x_3909_; 
v___x_3908_ = lean_array_get_size(v_keys_3904_);
v___x_3909_ = lean_nat_dec_lt(v_i_3906_, v___x_3908_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; 
lean_dec(v_i_3906_);
v___x_3910_ = lean_box(0);
return v___x_3910_;
}
else
{
lean_object* v_k_x27_3911_; uint8_t v___x_3912_; 
v_k_x27_3911_ = lean_array_fget_borrowed(v_keys_3904_, v_i_3906_);
v___x_3912_ = lean_name_eq(v_k_3907_, v_k_x27_3911_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = lean_unsigned_to_nat(1u);
v___x_3914_ = lean_nat_add(v_i_3906_, v___x_3913_);
lean_dec(v_i_3906_);
v_i_3906_ = v___x_3914_;
goto _start;
}
else
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3916_ = lean_array_fget_borrowed(v_vals_3905_, v_i_3906_);
lean_dec(v_i_3906_);
lean_inc(v___x_3916_);
v___x_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
return v___x_3917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3918_, lean_object* v_vals_3919_, lean_object* v_i_3920_, lean_object* v_k_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3918_, v_vals_3919_, v_i_3920_, v_k_3921_);
lean_dec(v_k_3921_);
lean_dec_ref(v_vals_3919_);
lean_dec_ref(v_keys_3918_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3923_, size_t v_x_3924_, lean_object* v_x_3925_){
_start:
{
if (lean_obj_tag(v_x_3923_) == 0)
{
lean_object* v_es_3926_; lean_object* v___x_3927_; size_t v___x_3928_; size_t v___x_3929_; lean_object* v_j_3930_; lean_object* v___x_3931_; 
v_es_3926_ = lean_ctor_get(v_x_3923_, 0);
v___x_3927_ = lean_box(2);
v___x_3928_ = ((size_t)31ULL);
v___x_3929_ = lean_usize_land(v_x_3924_, v___x_3928_);
v_j_3930_ = lean_usize_to_nat(v___x_3929_);
v___x_3931_ = lean_array_get_borrowed(v___x_3927_, v_es_3926_, v_j_3930_);
lean_dec(v_j_3930_);
switch(lean_obj_tag(v___x_3931_))
{
case 0:
{
lean_object* v_key_3932_; lean_object* v_val_3933_; uint8_t v___x_3934_; 
v_key_3932_ = lean_ctor_get(v___x_3931_, 0);
v_val_3933_ = lean_ctor_get(v___x_3931_, 1);
v___x_3934_ = lean_name_eq(v_x_3925_, v_key_3932_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; 
v___x_3935_ = lean_box(0);
return v___x_3935_;
}
else
{
lean_object* v___x_3936_; 
lean_inc(v_val_3933_);
v___x_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3936_, 0, v_val_3933_);
return v___x_3936_;
}
}
case 1:
{
lean_object* v_node_3937_; size_t v___x_3938_; size_t v___x_3939_; 
v_node_3937_ = lean_ctor_get(v___x_3931_, 0);
v___x_3938_ = ((size_t)5ULL);
v___x_3939_ = lean_usize_shift_right(v_x_3924_, v___x_3938_);
v_x_3923_ = v_node_3937_;
v_x_3924_ = v___x_3939_;
goto _start;
}
default: 
{
lean_object* v___x_3941_; 
v___x_3941_ = lean_box(0);
return v___x_3941_;
}
}
}
else
{
lean_object* v_ks_3942_; lean_object* v_vs_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v_ks_3942_ = lean_ctor_get(v_x_3923_, 0);
v_vs_3943_ = lean_ctor_get(v_x_3923_, 1);
v___x_3944_ = lean_unsigned_to_nat(0u);
v___x_3945_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3942_, v_vs_3943_, v___x_3944_, v_x_3925_);
return v___x_3945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3946_, lean_object* v_x_3947_, lean_object* v_x_3948_){
_start:
{
size_t v_x_700__boxed_3949_; lean_object* v_res_3950_; 
v_x_700__boxed_3949_ = lean_unbox_usize(v_x_3947_);
lean_dec(v_x_3947_);
v_res_3950_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3946_, v_x_700__boxed_3949_, v_x_3948_);
lean_dec(v_x_3948_);
lean_dec_ref(v_x_3946_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3951_, lean_object* v_x_3952_){
_start:
{
uint64_t v___y_3954_; 
if (lean_obj_tag(v_x_3952_) == 0)
{
uint64_t v___x_3957_; 
v___x_3957_ = 1723ULL;
v___y_3954_ = v___x_3957_;
goto v___jp_3953_;
}
else
{
uint64_t v_hash_3958_; 
v_hash_3958_ = lean_ctor_get_uint64(v_x_3952_, sizeof(void*)*2);
v___y_3954_ = v_hash_3958_;
goto v___jp_3953_;
}
v___jp_3953_:
{
size_t v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = lean_uint64_to_usize(v___y_3954_);
v___x_3956_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3951_, v___x_3955_, v_x_3952_);
return v___x_3956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3959_, lean_object* v_x_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3959_, v_x_3960_);
lean_dec(v_x_3960_);
lean_dec_ref(v_x_3959_);
return v_res_3961_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3968_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3969_ = l_Lean_stringToMessageData(v___x_3968_);
return v___x_3969_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3972_ = l_Lean_stringToMessageData(v___x_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_){
_start:
{
lean_object* v___x_3979_; lean_object* v_env_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3979_ = lean_st_ref_get(v_a_3977_);
v_env_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc_ref(v_env_3980_);
lean_dec(v___x_3979_);
lean_inc_n(v_matchDeclName_3973_, 3);
v___x_3981_ = l_Lean_mkPrivateName(v_env_3980_, v_matchDeclName_3973_);
lean_dec_ref(v_env_3980_);
v___x_3982_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_3981_);
v___x_3983_ = l_Lean_Name_append(v___x_3981_, v___x_3982_);
lean_inc_n(v___x_3983_, 2);
v___x_3984_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_3984_, 0, v_matchDeclName_3973_);
lean_closure_set(v___x_3984_, 1, v___x_3981_);
lean_closure_set(v___x_3984_, 2, v___x_3983_);
v___x_3985_ = l_Lean_Meta_realizeConst(v_matchDeclName_3973_, v___x_3983_, v___x_3984_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4014_; 
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4014_ == 0)
{
lean_object* v_unused_4015_; 
v_unused_4015_ = lean_ctor_get(v___x_3985_, 0);
lean_dec(v_unused_4015_);
v___x_3987_ = v___x_3985_;
v_isShared_3988_ = v_isSharedCheck_4014_;
goto v_resetjp_3986_;
}
else
{
lean_dec(v___x_3985_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4014_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v_env_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v_map_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4012_; 
v___x_3989_ = lean_st_ref_get(v_a_3977_);
v_env_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc_ref(v_env_3990_);
lean_dec(v___x_3989_);
v___x_3991_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_3992_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_3993_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_3994_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3991_, v___x_3992_, v_env_3990_, v___x_3993_, v___x_3983_);
v_map_3995_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4012_ == 0)
{
lean_object* v_unused_4013_; 
v_unused_4013_ = lean_ctor_get(v___x_3994_, 1);
lean_dec(v_unused_4013_);
v___x_3997_ = v___x_3994_;
v_isShared_3998_ = v_isSharedCheck_4012_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_map_3995_);
lean_dec(v___x_3994_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4012_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_3999_; 
v___x_3999_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_3995_, v_matchDeclName_3973_);
lean_dec_ref(v_map_3995_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4003_; 
lean_del_object(v___x_3987_);
v___x_4000_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_4001_ = l_Lean_MessageData_ofName(v_matchDeclName_3973_);
if (v_isShared_3998_ == 0)
{
lean_ctor_set_tag(v___x_3997_, 7);
lean_ctor_set(v___x_3997_, 1, v___x_4001_);
lean_ctor_set(v___x_3997_, 0, v___x_4000_);
v___x_4003_ = v___x_3997_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4000_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v___x_4001_);
v___x_4003_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4003_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
v___x_4006_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_4005_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
return v___x_4006_;
}
}
else
{
lean_object* v_val_4008_; lean_object* v___x_4010_; 
lean_del_object(v___x_3997_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
lean_dec(v_matchDeclName_3973_);
v_val_4008_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_val_4008_);
lean_dec_ref_known(v___x_3999_, 1);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v_val_4008_);
v___x_4010_ = v___x_3987_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_val_4008_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v___x_3983_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
lean_dec(v_matchDeclName_3973_);
v_a_4016_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_3985_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_3985_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = lean_get_match_equations_for(v_matchDeclName_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4031_, lean_object* v_x_4032_, lean_object* v_x_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4032_, v_x_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4035_, lean_object* v_x_4036_, lean_object* v_x_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4035_, v_x_4036_, v_x_4037_);
lean_dec(v_x_4037_);
lean_dec_ref(v_x_4036_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4039_, lean_object* v_x_4040_, size_t v_x_4041_, lean_object* v_x_4042_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4040_, v_x_4041_, v_x_4042_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4044_, lean_object* v_x_4045_, lean_object* v_x_4046_, lean_object* v_x_4047_){
_start:
{
size_t v_x_892__boxed_4048_; lean_object* v_res_4049_; 
v_x_892__boxed_4048_ = lean_unbox_usize(v_x_4046_);
lean_dec(v_x_4046_);
v_res_4049_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4044_, v_x_4045_, v_x_892__boxed_4048_, v_x_4047_);
lean_dec(v_x_4047_);
lean_dec_ref(v_x_4045_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4050_, lean_object* v_keys_4051_, lean_object* v_vals_4052_, lean_object* v_heq_4053_, lean_object* v_i_4054_, lean_object* v_k_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4051_, v_vals_4052_, v_i_4054_, v_k_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4057_, lean_object* v_keys_4058_, lean_object* v_vals_4059_, lean_object* v_heq_4060_, lean_object* v_i_4061_, lean_object* v_k_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4057_, v_keys_4058_, v_vals_4059_, v_heq_4060_, v_i_4061_, v_k_4062_);
lean_dec(v_k_4062_);
lean_dec_ref(v_vals_4059_);
lean_dec_ref(v_keys_4058_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4064_, lean_object* v_k_4065_, uint8_t v_cleanupAnnotations_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v___f_4072_; uint8_t v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___f_4072_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4072_, 0, v_k_4065_);
v___x_4073_ = 0;
v___x_4074_ = lean_box(0);
v___x_4075_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4073_, v___x_4074_, v_type_4064_, v___f_4072_, v_cleanupAnnotations_4066_, v___x_4073_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4075_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4075_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
v_a_4084_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4075_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4075_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4092_, lean_object* v_k_4093_, lean_object* v_cleanupAnnotations_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4100_; lean_object* v_res_4101_; 
v_cleanupAnnotations_boxed_4100_ = lean_unbox(v_cleanupAnnotations_4094_);
v_res_4101_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4092_, v_k_4093_, v_cleanupAnnotations_boxed_4100_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4102_, lean_object* v_type_4103_, lean_object* v_k_4104_, uint8_t v_cleanupAnnotations_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4103_, v_k_4104_, v_cleanupAnnotations_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4112_, lean_object* v_type_4113_, lean_object* v_k_4114_, lean_object* v_cleanupAnnotations_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4121_; lean_object* v_res_4122_; 
v_cleanupAnnotations_boxed_4121_ = lean_unbox(v_cleanupAnnotations_4115_);
v_res_4122_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4112_, v_type_4113_, v_k_4114_, v_cleanupAnnotations_boxed_4121_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_msg_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v___f_4129_; lean_object* v___x_18786__overap_4130_; lean_object* v___x_4131_; 
v___f_4129_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_18786__overap_4130_ = lean_panic_fn_borrowed(v___f_4129_, v_msg_4123_);
lean_inc(v___y_4127_);
lean_inc_ref(v___y_4126_);
lean_inc(v___y_4125_);
lean_inc_ref(v___y_4124_);
v___x_4131_ = lean_apply_5(v___x_18786__overap_4130_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, lean_box(0));
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_msg_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_msg_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4139_){
_start:
{
uint8_t v_foApprox_4140_; uint8_t v_ctxApprox_4141_; uint8_t v_quasiPatternApprox_4142_; uint8_t v_constApprox_4143_; uint8_t v_isDefEqStuckEx_4144_; uint8_t v_unificationHints_4145_; uint8_t v_proofIrrelevance_4146_; uint8_t v_assignSyntheticOpaque_4147_; uint8_t v_offsetCnstrs_4148_; uint8_t v_transparency_4149_; uint8_t v_univApprox_4150_; uint8_t v_iota_4151_; uint8_t v_beta_4152_; uint8_t v_proj_4153_; uint8_t v_zeta_4154_; uint8_t v_zetaDelta_4155_; uint8_t v_zetaUnused_4156_; uint8_t v_zetaHave_4157_; uint8_t v_canUnfoldPredicateConfig_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4166_; 
v_foApprox_4140_ = lean_ctor_get_uint8(v_c_4139_, 0);
v_ctxApprox_4141_ = lean_ctor_get_uint8(v_c_4139_, 1);
v_quasiPatternApprox_4142_ = lean_ctor_get_uint8(v_c_4139_, 2);
v_constApprox_4143_ = lean_ctor_get_uint8(v_c_4139_, 3);
v_isDefEqStuckEx_4144_ = lean_ctor_get_uint8(v_c_4139_, 4);
v_unificationHints_4145_ = lean_ctor_get_uint8(v_c_4139_, 5);
v_proofIrrelevance_4146_ = lean_ctor_get_uint8(v_c_4139_, 6);
v_assignSyntheticOpaque_4147_ = lean_ctor_get_uint8(v_c_4139_, 7);
v_offsetCnstrs_4148_ = lean_ctor_get_uint8(v_c_4139_, 8);
v_transparency_4149_ = lean_ctor_get_uint8(v_c_4139_, 9);
v_univApprox_4150_ = lean_ctor_get_uint8(v_c_4139_, 11);
v_iota_4151_ = lean_ctor_get_uint8(v_c_4139_, 12);
v_beta_4152_ = lean_ctor_get_uint8(v_c_4139_, 13);
v_proj_4153_ = lean_ctor_get_uint8(v_c_4139_, 14);
v_zeta_4154_ = lean_ctor_get_uint8(v_c_4139_, 15);
v_zetaDelta_4155_ = lean_ctor_get_uint8(v_c_4139_, 16);
v_zetaUnused_4156_ = lean_ctor_get_uint8(v_c_4139_, 17);
v_zetaHave_4157_ = lean_ctor_get_uint8(v_c_4139_, 18);
v_canUnfoldPredicateConfig_4158_ = lean_ctor_get_uint8(v_c_4139_, 19);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_c_4139_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4160_ = v_c_4139_;
v_isShared_4161_ = v_isSharedCheck_4166_;
goto v_resetjp_4159_;
}
else
{
lean_dec(v_c_4139_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4166_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
uint8_t v___x_4162_; lean_object* v___x_4164_; 
v___x_4162_ = 2;
if (v_isShared_4161_ == 0)
{
v___x_4164_ = v___x_4160_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 0, v_foApprox_4140_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 1, v_ctxApprox_4141_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 2, v_quasiPatternApprox_4142_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 3, v_constApprox_4143_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 4, v_isDefEqStuckEx_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 5, v_unificationHints_4145_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 6, v_proofIrrelevance_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 7, v_assignSyntheticOpaque_4147_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 8, v_offsetCnstrs_4148_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 9, v_transparency_4149_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 11, v_univApprox_4150_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 12, v_iota_4151_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 13, v_beta_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 14, v_proj_4153_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 15, v_zeta_4154_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 16, v_zetaDelta_4155_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 17, v_zetaUnused_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 18, v_zetaHave_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4165_, 19, v_canUnfoldPredicateConfig_4158_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_ctor_set_uint8(v___x_4164_, 10, v___x_4162_);
return v___x_4164_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4167_, lean_object* v_t_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v_dummy_4174_; lean_object* v_nargs_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v_dummy_4174_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4175_ = l_Lean_Expr_getAppNumArgs(v_t_4168_);
lean_inc(v_nargs_4175_);
v___x_4176_ = lean_mk_array(v_nargs_4175_, v_dummy_4174_);
v___x_4177_ = lean_unsigned_to_nat(1u);
v___x_4178_ = lean_nat_sub(v_nargs_4175_, v___x_4177_);
lean_dec(v_nargs_4175_);
v___x_4179_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4168_, v___x_4176_, v___x_4178_);
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4181_, lean_object* v_t_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4181_, v_t_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec_ref(v_x_4181_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4189_, lean_object* v_x_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4196_, 0, v_snd_4189_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4197_, lean_object* v_x_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4197_, v_x_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec_ref(v_x_4198_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4205_, size_t v_i_4206_, lean_object* v_bs_4207_){
_start:
{
uint8_t v___x_4208_; 
v___x_4208_ = lean_usize_dec_lt(v_i_4206_, v_sz_4205_);
if (v___x_4208_ == 0)
{
return v_bs_4207_;
}
else
{
lean_object* v_v_4209_; lean_object* v_fst_4210_; lean_object* v_snd_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4225_; 
v_v_4209_ = lean_array_uget(v_bs_4207_, v_i_4206_);
v_fst_4210_ = lean_ctor_get(v_v_4209_, 0);
v_snd_4211_ = lean_ctor_get(v_v_4209_, 1);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_v_4209_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4213_ = v_v_4209_;
v_isShared_4214_ = v_isSharedCheck_4225_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_snd_4211_);
lean_inc(v_fst_4210_);
lean_dec(v_v_4209_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4225_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; lean_object* v_bs_x27_4216_; lean_object* v___f_4217_; lean_object* v___x_4219_; 
v___x_4215_ = lean_unsigned_to_nat(0u);
v_bs_x27_4216_ = lean_array_uset(v_bs_4207_, v_i_4206_, v___x_4215_);
v___f_4217_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4217_, 0, v_snd_4211_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 1, v___f_4217_);
v___x_4219_ = v___x_4213_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_fst_4210_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v___f_4217_);
v___x_4219_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
size_t v___x_4220_; size_t v___x_4221_; lean_object* v___x_4222_; 
v___x_4220_ = ((size_t)1ULL);
v___x_4221_ = lean_usize_add(v_i_4206_, v___x_4220_);
v___x_4222_ = lean_array_uset(v_bs_x27_4216_, v_i_4206_, v___x_4219_);
v_i_4206_ = v___x_4221_;
v_bs_4207_ = v___x_4222_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4226_, lean_object* v_i_4227_, lean_object* v_bs_4228_){
_start:
{
size_t v_sz_boxed_4229_; size_t v_i_boxed_4230_; lean_object* v_res_4231_; 
v_sz_boxed_4229_ = lean_unbox_usize(v_sz_4226_);
lean_dec(v_sz_4226_);
v_i_boxed_4230_ = lean_unbox_usize(v_i_4227_);
lean_dec(v_i_4227_);
v_res_4231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4229_, v_i_boxed_4230_, v_bs_4228_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4232_, size_t v_i_4233_, lean_object* v_bs_4234_){
_start:
{
uint8_t v___x_4235_; 
v___x_4235_ = lean_usize_dec_lt(v_i_4233_, v_sz_4232_);
if (v___x_4235_ == 0)
{
return v_bs_4234_;
}
else
{
lean_object* v_v_4236_; lean_object* v_fst_4237_; lean_object* v_snd_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4254_; 
v_v_4236_ = lean_array_uget(v_bs_4234_, v_i_4233_);
v_fst_4237_ = lean_ctor_get(v_v_4236_, 0);
v_snd_4238_ = lean_ctor_get(v_v_4236_, 1);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_v_4236_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4240_ = v_v_4236_;
v_isShared_4241_ = v_isSharedCheck_4254_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_snd_4238_);
lean_inc(v_fst_4237_);
lean_dec(v_v_4236_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4254_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4242_; lean_object* v_bs_x27_4243_; uint8_t v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4247_; 
v___x_4242_ = lean_unsigned_to_nat(0u);
v_bs_x27_4243_ = lean_array_uset(v_bs_4234_, v_i_4233_, v___x_4242_);
v___x_4244_ = 0;
v___x_4245_ = lean_box(v___x_4244_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4245_);
v___x_4247_ = v___x_4240_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4245_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_snd_4238_);
v___x_4247_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
lean_object* v___x_4248_; size_t v___x_4249_; size_t v___x_4250_; lean_object* v___x_4251_; 
v___x_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4248_, 0, v_fst_4237_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = ((size_t)1ULL);
v___x_4250_ = lean_usize_add(v_i_4233_, v___x_4249_);
v___x_4251_ = lean_array_uset(v_bs_x27_4243_, v_i_4233_, v___x_4248_);
v_i_4233_ = v___x_4250_;
v_bs_4234_ = v___x_4251_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4255_, lean_object* v_i_4256_, lean_object* v_bs_4257_){
_start:
{
size_t v_sz_boxed_4258_; size_t v_i_boxed_4259_; lean_object* v_res_4260_; 
v_sz_boxed_4258_ = lean_unbox_usize(v_sz_4255_);
lean_dec(v_sz_4255_);
v_i_boxed_4259_ = lean_unbox_usize(v_i_4256_);
lean_dec(v_i_4256_);
v_res_4260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4258_, v_i_boxed_4259_, v_bs_4257_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4261_, lean_object* v___x_4262_, lean_object* v_a_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v___x_20465__overap_4269_; lean_object* v___x_4270_; 
v___x_20465__overap_4269_ = l_instInhabitedOfMonad___redArg(v___x_4261_, v___x_4262_);
lean_inc(v___y_4267_);
lean_inc_ref(v___y_4266_);
lean_inc(v___y_4265_);
lean_inc_ref(v___y_4264_);
v___x_4270_ = lean_apply_5(v___x_20465__overap_4269_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, lean_box(0));
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4271_, lean_object* v___x_4272_, lean_object* v_a_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4271_, v___x_4272_, v_a_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec_ref(v_a_4273_);
return v_res_4279_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_instMonadEIO(lean_box(0));
return v___x_4280_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4282_ = l_StateRefT_x27_instMonad___redArg(v___x_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4287_, lean_object* v_declInfos_4288_, lean_object* v_k_4289_, lean_object* v_kind_4290_, lean_object* v_x_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
uint8_t v_kind_boxed_4297_; lean_object* v_res_4298_; 
v_kind_boxed_4297_ = lean_unbox(v_kind_4290_);
v_res_4298_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4287_, v_declInfos_4288_, v_k_4289_, v_kind_boxed_4297_, v_x_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4299_, lean_object* v_k_4300_, uint8_t v_kind_4301_, lean_object* v_acc_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v___x_4308_; lean_object* v_toApplicative_4309_; lean_object* v_toFunctor_4310_; lean_object* v_toSeq_4311_; lean_object* v_toSeqLeft_4312_; lean_object* v_toSeqRight_4313_; lean_object* v___f_4314_; lean_object* v___f_4315_; lean_object* v___f_4316_; lean_object* v___f_4317_; lean_object* v___x_4318_; lean_object* v___f_4319_; lean_object* v___f_4320_; lean_object* v___f_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v_toApplicative_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4375_; 
v___x_4308_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4309_ = lean_ctor_get(v___x_4308_, 0);
v_toFunctor_4310_ = lean_ctor_get(v_toApplicative_4309_, 0);
v_toSeq_4311_ = lean_ctor_get(v_toApplicative_4309_, 2);
v_toSeqLeft_4312_ = lean_ctor_get(v_toApplicative_4309_, 3);
v_toSeqRight_4313_ = lean_ctor_get(v_toApplicative_4309_, 4);
v___f_4314_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4315_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4310_, 2);
v___f_4316_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4316_, 0, v_toFunctor_4310_);
v___f_4317_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4317_, 0, v_toFunctor_4310_);
v___x_4318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4318_, 0, v___f_4316_);
lean_ctor_set(v___x_4318_, 1, v___f_4317_);
lean_inc(v_toSeqRight_4313_);
v___f_4319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4319_, 0, v_toSeqRight_4313_);
lean_inc(v_toSeqLeft_4312_);
v___f_4320_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4320_, 0, v_toSeqLeft_4312_);
lean_inc(v_toSeq_4311_);
v___f_4321_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4321_, 0, v_toSeq_4311_);
v___x_4322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4318_);
lean_ctor_set(v___x_4322_, 1, v___f_4314_);
lean_ctor_set(v___x_4322_, 2, v___f_4321_);
lean_ctor_set(v___x_4322_, 3, v___f_4320_);
lean_ctor_set(v___x_4322_, 4, v___f_4319_);
v___x_4323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
lean_ctor_set(v___x_4323_, 1, v___f_4315_);
v___x_4324_ = l_StateRefT_x27_instMonad___redArg(v___x_4323_);
v_toApplicative_4325_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4375_ == 0)
{
lean_object* v_unused_4376_; 
v_unused_4376_ = lean_ctor_get(v___x_4324_, 1);
lean_dec(v_unused_4376_);
v___x_4327_ = v___x_4324_;
v_isShared_4328_ = v_isSharedCheck_4375_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_toApplicative_4325_);
lean_dec(v___x_4324_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4375_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v_toFunctor_4329_; lean_object* v_toSeq_4330_; lean_object* v_toSeqLeft_4331_; lean_object* v_toSeqRight_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4373_; 
v_toFunctor_4329_ = lean_ctor_get(v_toApplicative_4325_, 0);
v_toSeq_4330_ = lean_ctor_get(v_toApplicative_4325_, 2);
v_toSeqLeft_4331_ = lean_ctor_get(v_toApplicative_4325_, 3);
v_toSeqRight_4332_ = lean_ctor_get(v_toApplicative_4325_, 4);
v_isSharedCheck_4373_ = !lean_is_exclusive(v_toApplicative_4325_);
if (v_isSharedCheck_4373_ == 0)
{
lean_object* v_unused_4374_; 
v_unused_4374_ = lean_ctor_get(v_toApplicative_4325_, 1);
lean_dec(v_unused_4374_);
v___x_4334_ = v_toApplicative_4325_;
v_isShared_4335_ = v_isSharedCheck_4373_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_toSeqRight_4332_);
lean_inc(v_toSeqLeft_4331_);
lean_inc(v_toSeq_4330_);
lean_inc(v_toFunctor_4329_);
lean_dec(v_toApplicative_4325_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4373_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___f_4336_; lean_object* v___f_4337_; lean_object* v___f_4338_; lean_object* v___f_4339_; lean_object* v___x_4340_; lean_object* v___f_4341_; lean_object* v___f_4342_; lean_object* v___f_4343_; lean_object* v___x_4345_; 
v___f_4336_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4337_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4329_);
v___f_4338_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4338_, 0, v_toFunctor_4329_);
v___f_4339_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4339_, 0, v_toFunctor_4329_);
v___x_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___f_4338_);
lean_ctor_set(v___x_4340_, 1, v___f_4339_);
v___f_4341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4341_, 0, v_toSeqRight_4332_);
v___f_4342_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4342_, 0, v_toSeqLeft_4331_);
v___f_4343_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4343_, 0, v_toSeq_4330_);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 4, v___f_4341_);
lean_ctor_set(v___x_4334_, 3, v___f_4342_);
lean_ctor_set(v___x_4334_, 2, v___f_4343_);
lean_ctor_set(v___x_4334_, 1, v___f_4336_);
lean_ctor_set(v___x_4334_, 0, v___x_4340_);
v___x_4345_ = v___x_4334_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4340_);
lean_ctor_set(v_reuseFailAlloc_4372_, 1, v___f_4336_);
lean_ctor_set(v_reuseFailAlloc_4372_, 2, v___f_4343_);
lean_ctor_set(v_reuseFailAlloc_4372_, 3, v___f_4342_);
lean_ctor_set(v_reuseFailAlloc_4372_, 4, v___f_4341_);
v___x_4345_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4347_; 
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 1, v___f_4337_);
lean_ctor_set(v___x_4327_, 0, v___x_4345_);
v___x_4347_ = v___x_4327_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4345_);
lean_ctor_set(v_reuseFailAlloc_4371_, 1, v___f_4337_);
v___x_4347_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; uint8_t v___x_4350_; 
v___x_4348_ = lean_array_get_size(v_acc_4302_);
v___x_4349_ = lean_array_get_size(v_declInfos_4299_);
v___x_4350_ = lean_nat_dec_lt(v___x_4348_, v___x_4349_);
if (v___x_4350_ == 0)
{
lean_object* v___x_4351_; 
lean_dec_ref(v___x_4347_);
lean_dec_ref(v_declInfos_4299_);
lean_inc(v___y_4306_);
lean_inc_ref(v___y_4305_);
lean_inc(v___y_4304_);
lean_inc_ref(v___y_4303_);
v___x_4351_ = lean_apply_6(v_k_4300_, v_acc_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, lean_box(0));
return v___x_4351_;
}
else
{
lean_object* v___x_4352_; uint8_t v___x_4353_; lean_object* v___x_4354_; lean_object* v___f_4355_; lean_object* v___f_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v_snd_4361_; lean_object* v_fst_4362_; lean_object* v_fst_4363_; lean_object* v_snd_4364_; lean_object* v___x_4365_; 
v___x_4352_ = lean_box(0);
v___x_4353_ = 0;
v___x_4354_ = l_Lean_instInhabitedExpr;
v___f_4355_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4355_, 0, v___x_4347_);
lean_closure_set(v___f_4355_, 1, v___x_4354_);
v___f_4356_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4356_, 0, v___f_4355_);
v___x_4357_ = lean_box(v___x_4353_);
v___x_4358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
lean_ctor_set(v___x_4358_, 1, v___f_4356_);
v___x_4359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4352_);
lean_ctor_set(v___x_4359_, 1, v___x_4358_);
v___x_4360_ = lean_array_get(v___x_4359_, v_declInfos_4299_, v___x_4348_);
lean_dec_ref_known(v___x_4359_, 2);
v_snd_4361_ = lean_ctor_get(v___x_4360_, 1);
lean_inc(v_snd_4361_);
v_fst_4362_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_fst_4362_);
lean_dec(v___x_4360_);
v_fst_4363_ = lean_ctor_get(v_snd_4361_, 0);
lean_inc(v_fst_4363_);
v_snd_4364_ = lean_ctor_get(v_snd_4361_, 1);
lean_inc(v_snd_4364_);
lean_dec(v_snd_4361_);
lean_inc(v___y_4306_);
lean_inc_ref(v___y_4305_);
lean_inc(v___y_4304_);
lean_inc_ref(v___y_4303_);
lean_inc_ref(v_acc_4302_);
v___x_4365_ = lean_apply_6(v_snd_4364_, v_acc_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, lean_box(0));
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4367_; lean_object* v___f_4368_; uint8_t v___x_4369_; lean_object* v___x_4370_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_a_4366_);
lean_dec_ref_known(v___x_4365_, 1);
v___x_4367_ = lean_box(v_kind_4301_);
v___f_4368_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4368_, 0, v_acc_4302_);
lean_closure_set(v___f_4368_, 1, v_declInfos_4299_);
lean_closure_set(v___f_4368_, 2, v_k_4300_);
lean_closure_set(v___f_4368_, 3, v___x_4367_);
v___x_4369_ = lean_unbox(v_fst_4363_);
lean_dec(v_fst_4363_);
v___x_4370_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4362_, v___x_4369_, v_a_4366_, v___f_4368_, v_kind_4301_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
return v___x_4370_;
}
else
{
lean_dec(v_fst_4363_);
lean_dec(v_fst_4362_);
lean_dec_ref(v_acc_4302_);
lean_dec_ref(v_k_4300_);
lean_dec_ref(v_declInfos_4299_);
return v___x_4365_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4377_, lean_object* v_declInfos_4378_, lean_object* v_k_4379_, uint8_t v_kind_4380_, lean_object* v_x_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = lean_array_push(v_acc_4377_, v_x_4381_);
v___x_4388_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4378_, v_k_4379_, v_kind_4380_, v___x_4387_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4389_, lean_object* v_k_4390_, lean_object* v_kind_4391_, lean_object* v_acc_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
uint8_t v_kind_boxed_4398_; lean_object* v_res_4399_; 
v_kind_boxed_4398_ = lean_unbox(v_kind_4391_);
v_res_4399_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4389_, v_k_4390_, v_kind_boxed_4398_, v_acc_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4400_, lean_object* v_k_4401_, uint8_t v_kind_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4409_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4400_, v_k_4401_, v_kind_4402_, v___x_4408_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4410_, lean_object* v_k_4411_, lean_object* v_kind_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
uint8_t v_kind_boxed_4418_; lean_object* v_res_4419_; 
v_kind_boxed_4418_ = lean_unbox(v_kind_4412_);
v_res_4419_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4410_, v_k_4411_, v_kind_boxed_4418_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4420_, lean_object* v_k_4421_, uint8_t v_kind_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
size_t v_sz_4428_; size_t v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v_sz_4428_ = lean_array_size(v_declInfos_4420_);
v___x_4429_ = ((size_t)0ULL);
v___x_4430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4428_, v___x_4429_, v_declInfos_4420_);
v___x_4431_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4430_, v_k_4421_, v_kind_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4432_, lean_object* v_k_4433_, lean_object* v_kind_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
uint8_t v_kind_boxed_4440_; lean_object* v_res_4441_; 
v_kind_boxed_4440_ = lean_unbox(v_kind_4434_);
v_res_4441_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4432_, v_k_4433_, v_kind_boxed_4440_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4442_, lean_object* v_k_4443_, uint8_t v_kind_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
size_t v_sz_4450_; size_t v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v_sz_4450_ = lean_array_size(v_declInfos_4442_);
v___x_4451_ = ((size_t)0ULL);
v___x_4452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4450_, v___x_4451_, v_declInfos_4442_);
v___x_4453_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4452_, v_k_4443_, v_kind_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4454_, lean_object* v_k_4455_, lean_object* v_kind_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
uint8_t v_kind_boxed_4462_; lean_object* v_res_4463_; 
v_kind_boxed_4462_ = lean_unbox(v_kind_4456_);
v_res_4463_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4454_, v_k_4455_, v_kind_boxed_4462_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(lean_object* v_a_4467_, lean_object* v_b_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_array_4474_; lean_object* v_start_4475_; lean_object* v_stop_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4534_; 
v_array_4474_ = lean_ctor_get(v_a_4467_, 0);
v_start_4475_ = lean_ctor_get(v_a_4467_, 1);
v_stop_4476_ = lean_ctor_get(v_a_4467_, 2);
v_isSharedCheck_4534_ = !lean_is_exclusive(v_a_4467_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4478_ = v_a_4467_;
v_isShared_4479_ = v_isSharedCheck_4534_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_stop_4476_);
lean_inc(v_start_4475_);
lean_inc(v_array_4474_);
lean_dec(v_a_4467_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4534_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
uint8_t v___x_4480_; 
v___x_4480_ = lean_nat_dec_lt(v_start_4475_, v_stop_4476_);
if (v___x_4480_ == 0)
{
lean_object* v___x_4481_; 
lean_del_object(v___x_4478_);
lean_dec(v_stop_4476_);
lean_dec(v_start_4475_);
lean_dec_ref(v_array_4474_);
v___x_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4481_, 0, v_b_4468_);
return v___x_4481_;
}
else
{
lean_object* v_snd_4482_; lean_object* v_fst_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4533_; 
v_snd_4482_ = lean_ctor_get(v_b_4468_, 1);
v_fst_4483_ = lean_ctor_get(v_b_4468_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_b_4468_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4485_ = v_b_4468_;
v_isShared_4486_ = v_isSharedCheck_4533_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_snd_4482_);
lean_inc(v_fst_4483_);
lean_dec(v_b_4468_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4533_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v_array_4487_; lean_object* v_start_4488_; lean_object* v_stop_4489_; uint8_t v___x_4490_; 
v_array_4487_ = lean_ctor_get(v_snd_4482_, 0);
v_start_4488_ = lean_ctor_get(v_snd_4482_, 1);
v_stop_4489_ = lean_ctor_get(v_snd_4482_, 2);
v___x_4490_ = lean_nat_dec_lt(v_start_4488_, v_stop_4489_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4492_; 
lean_del_object(v___x_4478_);
lean_dec(v_stop_4476_);
lean_dec(v_start_4475_);
lean_dec_ref(v_array_4474_);
if (v_isShared_4486_ == 0)
{
v___x_4492_ = v___x_4485_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_fst_4483_);
lean_ctor_set(v_reuseFailAlloc_4494_, 1, v_snd_4482_);
v___x_4492_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_object* v___x_4493_; 
v___x_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
return v___x_4493_;
}
}
else
{
lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4529_; 
lean_inc(v_stop_4489_);
lean_inc(v_start_4488_);
lean_inc_ref(v_array_4487_);
v_isSharedCheck_4529_ = !lean_is_exclusive(v_snd_4482_);
if (v_isSharedCheck_4529_ == 0)
{
lean_object* v_unused_4530_; lean_object* v_unused_4531_; lean_object* v_unused_4532_; 
v_unused_4530_ = lean_ctor_get(v_snd_4482_, 2);
lean_dec(v_unused_4530_);
v_unused_4531_ = lean_ctor_get(v_snd_4482_, 1);
lean_dec(v_unused_4531_);
v_unused_4532_ = lean_ctor_get(v_snd_4482_, 0);
lean_dec(v_unused_4532_);
v___x_4496_ = v_snd_4482_;
v_isShared_4497_ = v_isSharedCheck_4529_;
goto v_resetjp_4495_;
}
else
{
lean_dec(v_snd_4482_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4529_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4498_ = lean_array_fget_borrowed(v_array_4474_, v_start_4475_);
v___x_4499_ = lean_array_fget_borrowed(v_array_4487_, v_start_4488_);
lean_inc(v___x_4499_);
lean_inc(v___x_4498_);
v___x_4500_ = l_Lean_Meta_mkEqHEq(v___x_4498_, v___x_4499_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4505_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref_known(v___x_4500_, 1);
v___x_4502_ = lean_unsigned_to_nat(1u);
v___x_4503_ = lean_nat_add(v_start_4475_, v___x_4502_);
lean_dec(v_start_4475_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 2, v_stop_4476_);
lean_ctor_set(v___x_4496_, 1, v___x_4503_);
lean_ctor_set(v___x_4496_, 0, v_array_4474_);
v___x_4505_ = v___x_4496_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_array_4474_);
lean_ctor_set(v_reuseFailAlloc_4520_, 1, v___x_4503_);
lean_ctor_set(v_reuseFailAlloc_4520_, 2, v_stop_4476_);
v___x_4505_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4506_ = lean_nat_add(v_start_4488_, v___x_4502_);
lean_dec(v_start_4488_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 2, v_stop_4489_);
lean_ctor_set(v___x_4478_, 1, v___x_4506_);
lean_ctor_set(v___x_4478_, 0, v_array_4487_);
v___x_4508_ = v___x_4478_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_array_4487_);
lean_ctor_set(v_reuseFailAlloc_4519_, 1, v___x_4506_);
lean_ctor_set(v_reuseFailAlloc_4519_, 2, v_stop_4489_);
v___x_4508_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4514_; 
v___x_4509_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__1));
v___x_4510_ = lean_array_get_size(v_fst_4483_);
v___x_4511_ = lean_nat_add(v___x_4510_, v___x_4502_);
v___x_4512_ = lean_name_append_index_after(v___x_4509_, v___x_4511_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 1, v_a_4501_);
lean_ctor_set(v___x_4485_, 0, v___x_4512_);
v___x_4514_ = v___x_4485_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4512_);
lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_a_4501_);
v___x_4514_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4515_ = lean_array_push(v_fst_4483_, v___x_4514_);
v___x_4516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
lean_ctor_set(v___x_4516_, 1, v___x_4508_);
v_a_4467_ = v___x_4505_;
v_b_4468_ = v___x_4516_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_del_object(v___x_4496_);
lean_dec(v_stop_4489_);
lean_dec(v_start_4488_);
lean_dec_ref(v_array_4487_);
lean_del_object(v___x_4485_);
lean_dec(v_fst_4483_);
lean_del_object(v___x_4478_);
lean_dec(v_stop_4476_);
lean_dec(v_start_4475_);
lean_dec_ref(v_array_4474_);
v_a_4521_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4500_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4500_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___boxed(lean_object* v_a_4535_, lean_object* v_b_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_4535_, v_b_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v___x_4543_, lean_object* v_a_4544_, lean_object* v___x_4545_, lean_object* v_as_4546_, size_t v_sz_4547_, size_t v_i_4548_, lean_object* v_b_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
uint8_t v___x_4555_; 
v___x_4555_ = lean_usize_dec_lt(v_i_4548_, v_sz_4547_);
if (v___x_4555_ == 0)
{
lean_object* v___x_4556_; 
lean_dec(v___x_4545_);
v___x_4556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4556_, 0, v_b_4549_);
return v___x_4556_;
}
else
{
lean_object* v___x_4557_; lean_object* v_a_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4557_ = l_Lean_instInhabitedExpr;
v_a_4558_ = lean_array_uget_borrowed(v_as_4546_, v_i_4548_);
v___x_4559_ = lean_array_get_borrowed(v___x_4557_, v___x_4543_, v_a_4558_);
lean_inc(v___x_4559_);
v___x_4560_ = l_Lean_Meta_instantiateForall(v___x_4559_, v_a_4544_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4562_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_a_4561_);
lean_dec_ref_known(v___x_4560_, 1);
lean_inc(v___x_4545_);
v___x_4562_ = l_Lean_Meta_Match_simpH_x3f(v_a_4561_, v___x_4545_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; lean_object* v_a_4565_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_a_4563_);
lean_dec_ref_known(v___x_4562_, 1);
if (lean_obj_tag(v_a_4563_) == 1)
{
lean_object* v_val_4569_; lean_object* v___x_4570_; 
v_val_4569_ = lean_ctor_get(v_a_4563_, 0);
lean_inc(v_val_4569_);
lean_dec_ref_known(v_a_4563_, 1);
v___x_4570_ = lean_array_push(v_b_4549_, v_val_4569_);
v_a_4565_ = v___x_4570_;
goto v___jp_4564_;
}
else
{
lean_dec(v_a_4563_);
v_a_4565_ = v_b_4549_;
goto v___jp_4564_;
}
v___jp_4564_:
{
size_t v___x_4566_; size_t v___x_4567_; 
v___x_4566_ = ((size_t)1ULL);
v___x_4567_ = lean_usize_add(v_i_4548_, v___x_4566_);
v_i_4548_ = v___x_4567_;
v_b_4549_ = v_a_4565_;
goto _start;
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v_b_4549_);
lean_dec(v___x_4545_);
v_a_4571_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4562_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4562_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec_ref(v_b_4549_);
lean_dec(v___x_4545_);
v_a_4579_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4560_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4560_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v___x_4587_, lean_object* v_a_4588_, lean_object* v___x_4589_, lean_object* v_as_4590_, lean_object* v_sz_4591_, lean_object* v_i_4592_, lean_object* v_b_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
size_t v_sz_boxed_4599_; size_t v_i_boxed_4600_; lean_object* v_res_4601_; 
v_sz_boxed_4599_ = lean_unbox_usize(v_sz_4591_);
lean_dec(v_sz_4591_);
v_i_boxed_4600_ = lean_unbox_usize(v_i_4592_);
lean_dec(v_i_4592_);
v_res_4601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4587_, v_a_4588_, v___x_4589_, v_as_4590_, v_sz_boxed_4599_, v_i_boxed_4600_, v_b_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec_ref(v_as_4590_);
lean_dec_ref(v_a_4588_);
lean_dec_ref(v___x_4587_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4602_, lean_object* v_args_4603_, lean_object* v___x_4604_, lean_object* v_overlaps_4605_, lean_object* v_a_4606_, lean_object* v_fst_4607_, lean_object* v_a_4608_, lean_object* v___x_4609_, lean_object* v___x_4610_, lean_object* v___x_4611_, lean_object* v___x_4612_, lean_object* v_altVars_4613_, uint8_t v___x_4614_, uint8_t v___x_4615_, lean_object* v_a_4616_, lean_object* v___x_4617_, lean_object* v___x_4618_, lean_object* v___x_4619_, lean_object* v___x_4620_, lean_object* v___x_4621_, lean_object* v___x_4622_, lean_object* v___x_4623_, lean_object* v_matchDeclName_4624_, lean_object* v___x_4625_, lean_object* v___x_4626_, lean_object* v___x_4627_, lean_object* v_heqs_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4634_ = l_Lean_mkAppN(v___y_4602_, v_args_4603_);
lean_inc_ref(v_heqs_4628_);
v___x_4635_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4634_, v_heqs_4628_, v___x_4604_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v_a_4636_; lean_object* v___x_4637_; size_t v_sz_4638_; size_t v___x_4639_; lean_object* v___x_4640_; 
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_a_4636_);
lean_dec_ref_known(v___x_4635_, 1);
v___x_4637_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4605_, v_a_4606_);
v_sz_4638_ = lean_array_size(v___x_4637_);
v___x_4639_ = ((size_t)0ULL);
lean_inc_ref(v___x_4610_);
v___x_4640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_fst_4607_, v_a_4608_, v___x_4609_, v___x_4637_, v_sz_4638_, v___x_4639_, v___x_4610_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
lean_dec_ref(v___x_4637_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v_options_4753_; uint8_t v_hasTrace_4754_; 
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
lean_inc(v_a_4641_);
lean_dec_ref_known(v___x_4640_, 1);
v_options_4753_ = lean_ctor_get(v___y_4631_, 1);
v_hasTrace_4754_ = lean_ctor_get_uint8(v_options_4753_, sizeof(void*)*1);
if (v_hasTrace_4754_ == 0)
{
v___y_4643_ = v___y_4629_;
v___y_4644_ = v___y_4630_;
v___y_4645_ = v___y_4631_;
v___y_4646_ = v___y_4632_;
goto v___jp_4642_;
}
else
{
lean_object* v_toCold_4755_; lean_object* v_inheritedTraceOptions_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; uint8_t v___x_4759_; 
v_toCold_4755_ = lean_ctor_get(v___y_4631_, 0);
v_inheritedTraceOptions_4756_ = lean_ctor_get(v_toCold_4755_, 4);
v___x_4757_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4758_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4759_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4756_, v_options_4753_, v___x_4758_);
if (v___x_4759_ == 0)
{
v___y_4643_ = v___y_4629_;
v___y_4644_ = v___y_4630_;
v___y_4645_ = v___y_4631_;
v___y_4646_ = v___y_4632_;
goto v___jp_4642_;
}
else
{
lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4760_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4641_);
v___x_4761_ = lean_array_to_list(v_a_4641_);
v___x_4762_ = lean_box(0);
v___x_4763_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4761_, v___x_4762_);
v___x_4764_ = l_Lean_MessageData_ofList(v___x_4763_);
v___x_4765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4760_);
lean_ctor_set(v___x_4765_, 1, v___x_4764_);
v___x_4766_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4757_, v___x_4765_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_dec_ref_known(v___x_4766_, 1);
v___y_4643_ = v___y_4629_;
v___y_4644_ = v___y_4630_;
v___y_4645_ = v___y_4631_;
v___y_4646_ = v___y_4632_;
goto v___jp_4642_;
}
else
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
lean_dec(v_a_4641_);
lean_dec(v_a_4636_);
lean_dec_ref(v_heqs_4628_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec(v_matchDeclName_4624_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec_ref(v___x_4612_);
lean_dec(v___x_4611_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v_a_4608_);
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___x_4766_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4766_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4772_; 
if (v_isShared_4770_ == 0)
{
v___x_4772_ = v___x_4769_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
}
v___jp_4642_:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; size_t v_sz_4654_; lean_object* v___x_4655_; 
v___x_4647_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4648_ = l_Array_reverse___redArg(v_a_4608_);
v___x_4649_ = lean_array_get_size(v___x_4648_);
v___x_4650_ = l_Array_toSubarray___redArg(v___x_4648_, v___x_4611_, v___x_4649_);
lean_inc_ref(v___x_4612_);
v___x_4651_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4612_, v___x_4610_);
v___x_4652_ = l_Array_reverse___redArg(v___x_4651_);
v___x_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4647_);
lean_ctor_set(v___x_4653_, 1, v___x_4650_);
v_sz_4654_ = lean_array_size(v___x_4652_);
v___x_4655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4652_, v_sz_4654_, v___x_4639_, v___x_4653_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
lean_dec_ref(v___x_4652_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v_fst_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4743_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_a_4656_);
lean_dec_ref_known(v___x_4655_, 1);
v_fst_4657_ = lean_ctor_get(v_a_4656_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v_a_4656_);
if (v_isSharedCheck_4743_ == 0)
{
lean_object* v_unused_4744_; 
v_unused_4744_ = lean_ctor_get(v_a_4656_, 1);
lean_dec(v_unused_4744_);
v___x_4659_ = v_a_4656_;
v_isShared_4660_ = v_isSharedCheck_4743_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_fst_4657_);
lean_dec(v_a_4656_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4743_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; lean_object* v___x_4664_; 
v___x_4661_ = l_Subarray_copy___redArg(v___x_4612_);
lean_inc_ref(v___x_4661_);
v___x_4662_ = l_Array_append___redArg(v___x_4661_, v_altVars_4613_);
v___x_4663_ = 1;
v___x_4664_ = l_Lean_Meta_mkForallFVars(v___x_4662_, v_fst_4657_, v___x_4614_, v___x_4615_, v___x_4615_, v___x_4663_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
lean_dec_ref(v___x_4662_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v___x_4664_, 1);
v___x_4666_ = l_Lean_ConstantInfo_name(v_a_4616_);
v___x_4667_ = l_Lean_mkConst(v___x_4666_, v___x_4617_);
lean_inc_ref(v___x_4618_);
v___x_4668_ = l_Subarray_copy___redArg(v___x_4618_);
v___x_4669_ = lean_mk_empty_array_with_capacity(v___x_4619_);
v___x_4670_ = lean_array_push(v___x_4669_, v___x_4620_);
v___x_4671_ = l_Array_append___redArg(v___x_4668_, v___x_4670_);
lean_dec_ref(v___x_4670_);
v___x_4672_ = l_Array_append___redArg(v___x_4671_, v___x_4661_);
lean_dec_ref(v___x_4661_);
v___x_4673_ = l_Subarray_copy___redArg(v___x_4621_);
v___x_4674_ = l_Array_append___redArg(v___x_4672_, v___x_4673_);
lean_dec_ref(v___x_4673_);
v___x_4675_ = l_Lean_mkAppN(v___x_4667_, v___x_4674_);
v___x_4676_ = l_Lean_Meta_mkHEq(v___x_4675_, v_a_4636_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4678_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v___x_4676_, 1);
v___x_4678_ = l_Lean_mkArrowN(v_a_4641_, v_a_4677_, v___y_4645_, v___y_4646_);
lean_dec(v_a_4641_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4679_);
lean_dec_ref_known(v___x_4678_, 1);
v___x_4680_ = l_Array_append___redArg(v___x_4674_, v_altVars_4613_);
v___x_4681_ = l_Array_append___redArg(v___x_4680_, v_heqs_4628_);
v___x_4682_ = l_Lean_Meta_mkForallFVars(v___x_4681_, v_a_4679_, v___x_4614_, v___x_4615_, v___x_4615_, v___x_4663_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
lean_dec_ref(v___x_4681_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4684_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_a_4683_);
lean_dec_ref_known(v___x_4682_, 1);
v___x_4684_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4683_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v___x_4687_; uint8_t v_isShared_4688_; uint8_t v_isSharedCheck_4742_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4684_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4687_ = v___x_4684_;
v_isShared_4688_ = v_isSharedCheck_4742_;
goto v_resetjp_4686_;
}
else
{
lean_inc(v_a_4685_);
lean_dec(v___x_4684_);
v___x_4687_ = lean_box(0);
v_isShared_4688_ = v_isSharedCheck_4742_;
goto v_resetjp_4686_;
}
v_resetjp_4686_:
{
lean_object* v_start_4689_; lean_object* v_stop_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4740_; 
v_start_4689_ = lean_ctor_get(v___x_4618_, 1);
v_stop_4690_ = lean_ctor_get(v___x_4618_, 2);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4740_ == 0)
{
lean_object* v_unused_4741_; 
v_unused_4741_ = lean_ctor_get(v___x_4618_, 0);
lean_dec(v_unused_4741_);
v___x_4692_ = v___x_4618_;
v_isShared_4693_ = v_isSharedCheck_4740_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_stop_4690_);
lean_inc(v_start_4689_);
lean_dec(v___x_4618_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4740_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4694_ = lean_nat_sub(v_stop_4690_, v_start_4689_);
lean_dec(v_start_4689_);
lean_dec(v_stop_4690_);
v___x_4695_ = lean_nat_add(v___x_4694_, v___x_4619_);
lean_dec(v___x_4694_);
v___x_4696_ = lean_nat_add(v___x_4695_, v___x_4622_);
lean_dec(v___x_4695_);
v___x_4697_ = lean_nat_add(v___x_4696_, v___x_4623_);
lean_dec(v___x_4696_);
v___x_4698_ = lean_array_get_size(v_altVars_4613_);
v___x_4699_ = lean_nat_add(v___x_4697_, v___x_4698_);
lean_dec(v___x_4697_);
v___x_4700_ = lean_array_get_size(v_heqs_4628_);
lean_dec_ref(v_heqs_4628_);
lean_inc(v_a_4685_);
v___x_4701_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4624_, v_a_4685_, v___x_4699_, v___x_4700_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4739_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4704_ = v___x_4701_;
v_isShared_4705_ = v_isSharedCheck_4739_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4701_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4739_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; lean_object* v_env_4707_; uint8_t v___x_4708_; 
v___x_4706_ = lean_st_ref_get(v___y_4646_);
v_env_4707_ = lean_ctor_get(v___x_4706_, 0);
lean_inc_ref(v_env_4707_);
lean_dec(v___x_4706_);
lean_inc(v___x_4625_);
v___x_4708_ = l_Lean_Environment_contains(v_env_4707_, v___x_4625_, v___x_4615_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4710_; 
lean_del_object(v___x_4704_);
lean_inc(v___x_4625_);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 2, v_a_4685_);
lean_ctor_set(v___x_4692_, 1, v___x_4626_);
lean_ctor_set(v___x_4692_, 0, v___x_4625_);
v___x_4710_ = v___x_4692_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v___x_4625_);
lean_ctor_set(v_reuseFailAlloc_4735_, 1, v___x_4626_);
lean_ctor_set(v_reuseFailAlloc_4735_, 2, v_a_4685_);
v___x_4710_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4712_; 
if (v_isShared_4660_ == 0)
{
lean_ctor_set_tag(v___x_4659_, 1);
lean_ctor_set(v___x_4659_, 1, v___x_4627_);
lean_ctor_set(v___x_4659_, 0, v___x_4625_);
v___x_4712_ = v___x_4659_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4625_);
lean_ctor_set(v_reuseFailAlloc_4734_, 1, v___x_4627_);
v___x_4712_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
lean_object* v___x_4713_; lean_object* v___x_4715_; 
v___x_4713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4710_);
lean_ctor_set(v___x_4713_, 1, v_a_4702_);
lean_ctor_set(v___x_4713_, 2, v___x_4712_);
if (v_isShared_4688_ == 0)
{
lean_ctor_set_tag(v___x_4687_, 2);
lean_ctor_set(v___x_4687_, 0, v___x_4713_);
v___x_4715_ = v___x_4687_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4713_);
v___x_4715_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
lean_object* v___x_4716_; 
v___x_4716_ = l_Lean_addDecl(v___x_4715_, v___x_4614_, v___y_4645_, v___y_4646_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4723_; 
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4723_ == 0)
{
lean_object* v_unused_4724_; 
v_unused_4724_ = lean_ctor_get(v___x_4716_, 0);
lean_dec(v_unused_4724_);
v___x_4718_ = v___x_4716_;
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
else
{
lean_dec(v___x_4716_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4721_; 
if (v_isShared_4719_ == 0)
{
lean_ctor_set(v___x_4718_, 0, v_a_4665_);
v___x_4721_ = v___x_4718_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4665_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
else
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4732_; 
lean_dec(v_a_4665_);
v_a_4725_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4727_ = v___x_4716_;
v_isShared_4728_ = v_isSharedCheck_4732_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4716_);
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
}
}
}
else
{
lean_object* v___x_4737_; 
lean_dec(v_a_4702_);
lean_del_object(v___x_4692_);
lean_del_object(v___x_4687_);
lean_dec(v_a_4685_);
lean_del_object(v___x_4659_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 0, v_a_4665_);
v___x_4737_ = v___x_4704_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4665_);
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
else
{
lean_del_object(v___x_4692_);
lean_del_object(v___x_4687_);
lean_dec(v_a_4685_);
lean_dec(v_a_4665_);
lean_del_object(v___x_4659_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
return v___x_4701_;
}
}
}
}
else
{
lean_dec(v_a_4665_);
lean_del_object(v___x_4659_);
lean_dec_ref(v_heqs_4628_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec(v_matchDeclName_4624_);
lean_dec_ref(v___x_4618_);
return v___x_4684_;
}
}
else
{
lean_dec(v_a_4665_);
lean_del_object(v___x_4659_);
lean_dec_ref(v_heqs_4628_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec(v_matchDeclName_4624_);
lean_dec_ref(v___x_4618_);
return v___x_4682_;
}
}
else
{
lean_dec_ref(v___x_4674_);
lean_dec(v_a_4665_);
lean_del_object(v___x_4659_);
lean_dec_ref(v_heqs_4628_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec(v_matchDeclName_4624_);
lean_dec_ref(v___x_4618_);
return v___x_4678_;
}
}
else
{
lean_dec_ref(v___x_4674_);
lean_dec(v_a_4665_);
lean_del_object(v___x_4659_);
lean_dec(v_a_4641_);
lean_dec_ref(v_heqs_4628_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec(v_matchDeclName_4624_);
lean_dec_ref(v___x_4618_);
return v___x_4676_;
}
}
else
{
lean_dec_ref(v___x_4661_);
lean_del_object(v___x_4659_);
lean_dec(v_a_4641_);
lean_dec(v_a_4636_);
lean_dec_ref(v_heqs_4628_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec(v_matchDeclName_4624_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4618_);
lean_dec(v___x_4617_);
return v___x_4664_;
}
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4752_; 
lean_dec(v_a_4641_);
lean_dec(v_a_4636_);
lean_dec_ref(v_heqs_4628_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec(v_matchDeclName_4624_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec_ref(v___x_4612_);
v_a_4745_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4747_ = v___x_4655_;
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4655_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4752_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4750_; 
if (v_isShared_4748_ == 0)
{
v___x_4750_ = v___x_4747_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
}
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4782_; 
lean_dec(v_a_4636_);
lean_dec_ref(v_heqs_4628_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec(v_matchDeclName_4624_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec_ref(v___x_4612_);
lean_dec(v___x_4611_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v_a_4608_);
v_a_4775_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4777_ = v___x_4640_;
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v___x_4640_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4780_; 
if (v_isShared_4778_ == 0)
{
v___x_4780_ = v___x_4777_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4775_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4628_);
lean_dec(v___x_4627_);
lean_dec(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec(v_matchDeclName_4624_);
lean_dec_ref(v___x_4621_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec_ref(v___x_4612_);
lean_dec(v___x_4611_);
lean_dec_ref(v___x_4610_);
lean_dec(v___x_4609_);
lean_dec_ref(v_a_4608_);
return v___x_4635_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4783_ = _args[0];
lean_object* v_args_4784_ = _args[1];
lean_object* v___x_4785_ = _args[2];
lean_object* v_overlaps_4786_ = _args[3];
lean_object* v_a_4787_ = _args[4];
lean_object* v_fst_4788_ = _args[5];
lean_object* v_a_4789_ = _args[6];
lean_object* v___x_4790_ = _args[7];
lean_object* v___x_4791_ = _args[8];
lean_object* v___x_4792_ = _args[9];
lean_object* v___x_4793_ = _args[10];
lean_object* v_altVars_4794_ = _args[11];
lean_object* v___x_4795_ = _args[12];
lean_object* v___x_4796_ = _args[13];
lean_object* v_a_4797_ = _args[14];
lean_object* v___x_4798_ = _args[15];
lean_object* v___x_4799_ = _args[16];
lean_object* v___x_4800_ = _args[17];
lean_object* v___x_4801_ = _args[18];
lean_object* v___x_4802_ = _args[19];
lean_object* v___x_4803_ = _args[20];
lean_object* v___x_4804_ = _args[21];
lean_object* v_matchDeclName_4805_ = _args[22];
lean_object* v___x_4806_ = _args[23];
lean_object* v___x_4807_ = _args[24];
lean_object* v___x_4808_ = _args[25];
lean_object* v_heqs_4809_ = _args[26];
lean_object* v___y_4810_ = _args[27];
lean_object* v___y_4811_ = _args[28];
lean_object* v___y_4812_ = _args[29];
lean_object* v___y_4813_ = _args[30];
lean_object* v___y_4814_ = _args[31];
_start:
{
uint8_t v___x_21208__boxed_4815_; uint8_t v___x_21209__boxed_4816_; lean_object* v_res_4817_; 
v___x_21208__boxed_4815_ = lean_unbox(v___x_4795_);
v___x_21209__boxed_4816_ = lean_unbox(v___x_4796_);
v_res_4817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4783_, v_args_4784_, v___x_4785_, v_overlaps_4786_, v_a_4787_, v_fst_4788_, v_a_4789_, v___x_4790_, v___x_4791_, v___x_4792_, v___x_4793_, v_altVars_4794_, v___x_21208__boxed_4815_, v___x_21209__boxed_4816_, v_a_4797_, v___x_4798_, v___x_4799_, v___x_4800_, v___x_4801_, v___x_4802_, v___x_4803_, v___x_4804_, v_matchDeclName_4805_, v___x_4806_, v___x_4807_, v___x_4808_, v_heqs_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec(v___y_4811_);
lean_dec_ref(v___y_4810_);
lean_dec(v___x_4804_);
lean_dec(v___x_4803_);
lean_dec(v___x_4800_);
lean_dec_ref(v_a_4797_);
lean_dec_ref(v_altVars_4794_);
lean_dec(v_fst_4788_);
lean_dec(v_a_4787_);
lean_dec_ref(v_overlaps_4786_);
lean_dec_ref(v_args_4784_);
return v_res_4817_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4820_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4821_ = lean_unsigned_to_nat(8u);
v___x_4822_ = lean_unsigned_to_nat(295u);
v___x_4823_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4824_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4825_ = l_mkPanicMessageWithDecl(v___x_4824_, v___x_4823_, v___x_4822_, v___x_4821_, v___x_4820_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4826_, lean_object* v___x_4827_, lean_object* v___x_4828_, lean_object* v___y_4829_, lean_object* v___x_4830_, lean_object* v_overlaps_4831_, lean_object* v_a_4832_, lean_object* v_fst_4833_, lean_object* v___x_4834_, uint8_t v___x_4835_, lean_object* v_a_4836_, lean_object* v___x_4837_, lean_object* v___x_4838_, lean_object* v___x_4839_, lean_object* v___x_4840_, lean_object* v___x_4841_, lean_object* v___x_4842_, lean_object* v_matchDeclName_4843_, lean_object* v___x_4844_, lean_object* v___x_4845_, lean_object* v___x_4846_, lean_object* v_altVars_4847_, lean_object* v_args_4848_, lean_object* v___mask_4849_, lean_object* v_altResultType_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_){
_start:
{
uint8_t v___x_4856_; lean_object* v___x_4857_; 
v___x_4856_ = 0;
v___x_4857_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4850_, v___f_4826_, v___x_4856_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; lean_object* v_start_4859_; lean_object* v_stop_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4858_);
lean_dec_ref_known(v___x_4857_, 1);
v_start_4859_ = lean_ctor_get(v___x_4827_, 1);
v_stop_4860_ = lean_ctor_get(v___x_4827_, 2);
v___x_4861_ = lean_array_get_size(v_a_4858_);
v___x_4862_ = lean_nat_sub(v_stop_4860_, v_start_4859_);
v___x_4863_ = lean_nat_dec_eq(v___x_4861_, v___x_4862_);
if (v___x_4863_ == 0)
{
lean_object* v___x_4864_; lean_object* v___x_4865_; 
lean_dec(v___x_4862_);
lean_dec(v_a_4858_);
lean_dec_ref(v_args_4848_);
lean_dec_ref(v_altVars_4847_);
lean_dec(v___x_4846_);
lean_dec(v___x_4845_);
lean_dec(v___x_4844_);
lean_dec(v_matchDeclName_4843_);
lean_dec(v___x_4842_);
lean_dec_ref(v___x_4841_);
lean_dec_ref(v___x_4840_);
lean_dec(v___x_4839_);
lean_dec_ref(v___x_4838_);
lean_dec(v___x_4837_);
lean_dec_ref(v_a_4836_);
lean_dec_ref(v___x_4834_);
lean_dec(v_fst_4833_);
lean_dec(v_a_4832_);
lean_dec_ref(v_overlaps_4831_);
lean_dec(v___x_4830_);
lean_dec_ref(v___y_4829_);
lean_dec(v___x_4828_);
lean_dec_ref(v___x_4827_);
v___x_4864_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4865_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v___x_4864_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
return v___x_4865_;
}
else
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4866_ = lean_mk_empty_array_with_capacity(v___x_4828_);
lean_inc(v___x_4828_);
lean_inc(v_a_4858_);
v___x_4867_ = l_Array_toSubarray___redArg(v_a_4858_, v___x_4828_, v___x_4861_);
v___x_4868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4866_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
lean_inc_ref(v___x_4827_);
v___x_4869_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v___x_4827_, v___x_4868_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v_fst_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___f_4874_; uint8_t v___x_4875_; lean_object* v___x_4876_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
lean_inc(v_a_4870_);
lean_dec_ref_known(v___x_4869_, 1);
v_fst_4871_ = lean_ctor_get(v_a_4870_, 0);
lean_inc(v_fst_4871_);
lean_dec(v_a_4870_);
v___x_4872_ = lean_box(v___x_4856_);
v___x_4873_ = lean_box(v___x_4835_);
v___f_4874_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4874_, 0, v___y_4829_);
lean_closure_set(v___f_4874_, 1, v_args_4848_);
lean_closure_set(v___f_4874_, 2, v___x_4830_);
lean_closure_set(v___f_4874_, 3, v_overlaps_4831_);
lean_closure_set(v___f_4874_, 4, v_a_4832_);
lean_closure_set(v___f_4874_, 5, v_fst_4833_);
lean_closure_set(v___f_4874_, 6, v_a_4858_);
lean_closure_set(v___f_4874_, 7, v___x_4861_);
lean_closure_set(v___f_4874_, 8, v___x_4834_);
lean_closure_set(v___f_4874_, 9, v___x_4828_);
lean_closure_set(v___f_4874_, 10, v___x_4827_);
lean_closure_set(v___f_4874_, 11, v_altVars_4847_);
lean_closure_set(v___f_4874_, 12, v___x_4872_);
lean_closure_set(v___f_4874_, 13, v___x_4873_);
lean_closure_set(v___f_4874_, 14, v_a_4836_);
lean_closure_set(v___f_4874_, 15, v___x_4837_);
lean_closure_set(v___f_4874_, 16, v___x_4838_);
lean_closure_set(v___f_4874_, 17, v___x_4839_);
lean_closure_set(v___f_4874_, 18, v___x_4840_);
lean_closure_set(v___f_4874_, 19, v___x_4841_);
lean_closure_set(v___f_4874_, 20, v___x_4862_);
lean_closure_set(v___f_4874_, 21, v___x_4842_);
lean_closure_set(v___f_4874_, 22, v_matchDeclName_4843_);
lean_closure_set(v___f_4874_, 23, v___x_4844_);
lean_closure_set(v___f_4874_, 24, v___x_4845_);
lean_closure_set(v___f_4874_, 25, v___x_4846_);
v___x_4875_ = 0;
v___x_4876_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4871_, v___f_4874_, v___x_4875_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
return v___x_4876_;
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_dec(v___x_4862_);
lean_dec(v_a_4858_);
lean_dec_ref(v_args_4848_);
lean_dec_ref(v_altVars_4847_);
lean_dec(v___x_4846_);
lean_dec(v___x_4845_);
lean_dec(v___x_4844_);
lean_dec(v_matchDeclName_4843_);
lean_dec(v___x_4842_);
lean_dec_ref(v___x_4841_);
lean_dec_ref(v___x_4840_);
lean_dec(v___x_4839_);
lean_dec_ref(v___x_4838_);
lean_dec(v___x_4837_);
lean_dec_ref(v_a_4836_);
lean_dec_ref(v___x_4834_);
lean_dec(v_fst_4833_);
lean_dec(v_a_4832_);
lean_dec_ref(v_overlaps_4831_);
lean_dec(v___x_4830_);
lean_dec_ref(v___y_4829_);
lean_dec(v___x_4828_);
lean_dec_ref(v___x_4827_);
v_a_4877_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4869_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4869_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
lean_dec_ref(v_args_4848_);
lean_dec_ref(v_altVars_4847_);
lean_dec(v___x_4846_);
lean_dec(v___x_4845_);
lean_dec(v___x_4844_);
lean_dec(v_matchDeclName_4843_);
lean_dec(v___x_4842_);
lean_dec_ref(v___x_4841_);
lean_dec_ref(v___x_4840_);
lean_dec(v___x_4839_);
lean_dec_ref(v___x_4838_);
lean_dec(v___x_4837_);
lean_dec_ref(v_a_4836_);
lean_dec_ref(v___x_4834_);
lean_dec(v_fst_4833_);
lean_dec(v_a_4832_);
lean_dec_ref(v_overlaps_4831_);
lean_dec(v___x_4830_);
lean_dec_ref(v___y_4829_);
lean_dec(v___x_4828_);
lean_dec_ref(v___x_4827_);
v_a_4885_ = lean_ctor_get(v___x_4857_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4857_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4857_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4893_ = _args[0];
lean_object* v___x_4894_ = _args[1];
lean_object* v___x_4895_ = _args[2];
lean_object* v___y_4896_ = _args[3];
lean_object* v___x_4897_ = _args[4];
lean_object* v_overlaps_4898_ = _args[5];
lean_object* v_a_4899_ = _args[6];
lean_object* v_fst_4900_ = _args[7];
lean_object* v___x_4901_ = _args[8];
lean_object* v___x_4902_ = _args[9];
lean_object* v_a_4903_ = _args[10];
lean_object* v___x_4904_ = _args[11];
lean_object* v___x_4905_ = _args[12];
lean_object* v___x_4906_ = _args[13];
lean_object* v___x_4907_ = _args[14];
lean_object* v___x_4908_ = _args[15];
lean_object* v___x_4909_ = _args[16];
lean_object* v_matchDeclName_4910_ = _args[17];
lean_object* v___x_4911_ = _args[18];
lean_object* v___x_4912_ = _args[19];
lean_object* v___x_4913_ = _args[20];
lean_object* v_altVars_4914_ = _args[21];
lean_object* v_args_4915_ = _args[22];
lean_object* v___mask_4916_ = _args[23];
lean_object* v_altResultType_4917_ = _args[24];
lean_object* v___y_4918_ = _args[25];
lean_object* v___y_4919_ = _args[26];
lean_object* v___y_4920_ = _args[27];
lean_object* v___y_4921_ = _args[28];
lean_object* v___y_4922_ = _args[29];
_start:
{
uint8_t v___x_21595__boxed_4923_; lean_object* v_res_4924_; 
v___x_21595__boxed_4923_ = lean_unbox(v___x_4902_);
v_res_4924_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4893_, v___x_4894_, v___x_4895_, v___y_4896_, v___x_4897_, v_overlaps_4898_, v_a_4899_, v_fst_4900_, v___x_4901_, v___x_21595__boxed_4923_, v_a_4903_, v___x_4904_, v___x_4905_, v___x_4906_, v___x_4907_, v___x_4908_, v___x_4909_, v_matchDeclName_4910_, v___x_4911_, v___x_4912_, v___x_4913_, v_altVars_4914_, v_args_4915_, v___mask_4916_, v_altResultType_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_);
lean_dec(v___y_4921_);
lean_dec_ref(v___y_4920_);
lean_dec(v___y_4919_);
lean_dec_ref(v___y_4918_);
lean_dec_ref(v___mask_4916_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4926_, lean_object* v_val_4927_, lean_object* v_matchDeclName_4928_, lean_object* v___x_4929_, lean_object* v___x_4930_, lean_object* v_a_4931_, lean_object* v___x_4932_, lean_object* v___x_4933_, lean_object* v___x_4934_, lean_object* v___x_4935_, lean_object* v___x_4936_, lean_object* v___x_4937_, lean_object* v_a_4938_, lean_object* v_b_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_){
_start:
{
uint8_t v___x_4945_; 
v___x_4945_ = lean_nat_dec_lt(v_a_4938_, v_upperBound_4926_);
if (v___x_4945_ == 0)
{
lean_object* v___x_4946_; 
lean_dec(v_a_4938_);
lean_dec(v___x_4937_);
lean_dec(v___x_4936_);
lean_dec_ref(v___x_4935_);
lean_dec_ref(v___x_4934_);
lean_dec_ref(v___x_4933_);
lean_dec(v___x_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v___x_4930_);
lean_dec_ref(v___x_4929_);
lean_dec(v_matchDeclName_4928_);
lean_dec_ref(v_val_4927_);
v___x_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4946_, 0, v_b_4939_);
return v___x_4946_;
}
else
{
lean_object* v_snd_4947_; lean_object* v_fst_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_5012_; 
v_snd_4947_ = lean_ctor_get(v_b_4939_, 1);
v_fst_4948_ = lean_ctor_get(v_b_4939_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v_b_4939_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_4950_ = v_b_4939_;
v_isShared_4951_ = v_isSharedCheck_5012_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_snd_4947_);
lean_inc(v_fst_4948_);
lean_dec(v_b_4939_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_5012_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v_fst_4952_; lean_object* v_snd_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_5011_; 
v_fst_4952_ = lean_ctor_get(v_snd_4947_, 0);
v_snd_4953_ = lean_ctor_get(v_snd_4947_, 1);
v_isSharedCheck_5011_ = !lean_is_exclusive(v_snd_4947_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_4955_ = v_snd_4947_;
v_isShared_4956_ = v_isSharedCheck_5011_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_snd_4953_);
lean_inc(v_fst_4952_);
lean_dec(v_snd_4947_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_5011_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v_altInfos_4957_; lean_object* v_overlaps_4958_; lean_object* v_start_4959_; lean_object* v_stop_4960_; lean_object* v___f_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___y_4973_; lean_object* v___x_5006_; uint8_t v___x_5007_; 
v_altInfos_4957_ = lean_ctor_get(v_val_4927_, 2);
v_overlaps_4958_ = lean_ctor_get(v_val_4927_, 5);
v_start_4959_ = lean_ctor_get(v___x_4935_, 1);
v_stop_4960_ = lean_ctor_get(v___x_4935_, 2);
v___f_4961_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4962_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4963_ = lean_unsigned_to_nat(0u);
v___x_4964_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4965_ = lean_unsigned_to_nat(1u);
v___x_4966_ = lean_box(0);
v___x_4967_ = lean_array_get_borrowed(v___x_4962_, v_altInfos_4957_, v_a_4938_);
v___x_4968_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4928_);
v___x_4969_ = l_Lean_Name_str___override(v_matchDeclName_4928_, v___x_4968_);
lean_inc(v_snd_4953_);
v___x_4970_ = lean_name_append_index_after(v___x_4969_, v_snd_4953_);
lean_inc(v___x_4970_);
v___x_4971_ = lean_array_push(v_fst_4948_, v___x_4970_);
v___x_5006_ = lean_nat_sub(v_stop_4960_, v_start_4959_);
v___x_5007_ = lean_nat_dec_lt(v_a_4938_, v___x_5006_);
lean_dec(v___x_5006_);
if (v___x_5007_ == 0)
{
lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5008_ = l_Lean_instInhabitedExpr;
v___x_5009_ = l_outOfBounds___redArg(v___x_5008_);
v___y_4973_ = v___x_5009_;
goto v___jp_4972_;
}
else
{
lean_object* v___x_5010_; 
v___x_5010_ = l_Subarray_get___redArg(v___x_4935_, v_a_4938_);
v___y_4973_ = v___x_5010_;
goto v___jp_4972_;
}
v___jp_4972_:
{
lean_object* v___x_4974_; 
lean_inc(v___y_4943_);
lean_inc_ref(v___y_4942_);
lean_inc(v___y_4941_);
lean_inc_ref(v___y_4940_);
lean_inc_ref(v___y_4973_);
v___x_4974_ = lean_infer_type(v___y_4973_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4976_; lean_object* v___f_4977_; lean_object* v___x_4978_; 
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_a_4975_);
lean_dec_ref_known(v___x_4974_, 1);
v___x_4976_ = lean_box(v___x_4945_);
lean_inc(v___x_4937_);
lean_inc(v_matchDeclName_4928_);
lean_inc(v___x_4936_);
lean_inc_ref(v___x_4935_);
lean_inc_ref(v___x_4934_);
lean_inc_ref(v___x_4933_);
lean_inc(v___x_4932_);
lean_inc_ref(v_a_4931_);
lean_inc(v_fst_4952_);
lean_inc(v_a_4938_);
lean_inc_ref(v_overlaps_4958_);
lean_inc(v___x_4930_);
lean_inc_ref(v___x_4929_);
v___f_4977_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 30, 21);
lean_closure_set(v___f_4977_, 0, v___f_4961_);
lean_closure_set(v___f_4977_, 1, v___x_4929_);
lean_closure_set(v___f_4977_, 2, v___x_4963_);
lean_closure_set(v___f_4977_, 3, v___y_4973_);
lean_closure_set(v___f_4977_, 4, v___x_4930_);
lean_closure_set(v___f_4977_, 5, v_overlaps_4958_);
lean_closure_set(v___f_4977_, 6, v_a_4938_);
lean_closure_set(v___f_4977_, 7, v_fst_4952_);
lean_closure_set(v___f_4977_, 8, v___x_4964_);
lean_closure_set(v___f_4977_, 9, v___x_4976_);
lean_closure_set(v___f_4977_, 10, v_a_4931_);
lean_closure_set(v___f_4977_, 11, v___x_4932_);
lean_closure_set(v___f_4977_, 12, v___x_4933_);
lean_closure_set(v___f_4977_, 13, v___x_4965_);
lean_closure_set(v___f_4977_, 14, v___x_4934_);
lean_closure_set(v___f_4977_, 15, v___x_4935_);
lean_closure_set(v___f_4977_, 16, v___x_4936_);
lean_closure_set(v___f_4977_, 17, v_matchDeclName_4928_);
lean_closure_set(v___f_4977_, 18, v___x_4970_);
lean_closure_set(v___f_4977_, 19, v___x_4937_);
lean_closure_set(v___f_4977_, 20, v___x_4966_);
lean_inc(v___x_4967_);
v___x_4978_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4975_, v___x_4967_, v___f_4977_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_object* v_a_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4983_; 
v_a_4979_ = lean_ctor_get(v___x_4978_, 0);
lean_inc(v_a_4979_);
lean_dec_ref_known(v___x_4978_, 1);
v___x_4980_ = lean_array_push(v_fst_4952_, v_a_4979_);
v___x_4981_ = lean_nat_add(v_snd_4953_, v___x_4965_);
lean_dec(v_snd_4953_);
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 1, v___x_4981_);
lean_ctor_set(v___x_4955_, 0, v___x_4980_);
v___x_4983_ = v___x_4955_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4980_);
lean_ctor_set(v_reuseFailAlloc_4989_, 1, v___x_4981_);
v___x_4983_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
lean_object* v___x_4985_; 
if (v_isShared_4951_ == 0)
{
lean_ctor_set(v___x_4950_, 1, v___x_4983_);
lean_ctor_set(v___x_4950_, 0, v___x_4971_);
v___x_4985_ = v___x_4950_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4971_);
lean_ctor_set(v_reuseFailAlloc_4988_, 1, v___x_4983_);
v___x_4985_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
lean_object* v___x_4986_; 
v___x_4986_ = lean_nat_add(v_a_4938_, v___x_4965_);
lean_dec(v_a_4938_);
v_a_4938_ = v___x_4986_;
v_b_4939_ = v___x_4985_;
goto _start;
}
}
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_4997_; 
lean_dec_ref(v___x_4971_);
lean_del_object(v___x_4955_);
lean_dec(v_snd_4953_);
lean_dec(v_fst_4952_);
lean_del_object(v___x_4950_);
lean_dec(v_a_4938_);
lean_dec(v___x_4937_);
lean_dec(v___x_4936_);
lean_dec_ref(v___x_4935_);
lean_dec_ref(v___x_4934_);
lean_dec_ref(v___x_4933_);
lean_dec(v___x_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v___x_4930_);
lean_dec_ref(v___x_4929_);
lean_dec(v_matchDeclName_4928_);
lean_dec_ref(v_val_4927_);
v_a_4990_ = lean_ctor_get(v___x_4978_, 0);
v_isSharedCheck_4997_ = !lean_is_exclusive(v___x_4978_);
if (v_isSharedCheck_4997_ == 0)
{
v___x_4992_ = v___x_4978_;
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4978_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_4997_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___x_4995_; 
if (v_isShared_4993_ == 0)
{
v___x_4995_ = v___x_4992_;
goto v_reusejp_4994_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
v___x_4995_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4994_;
}
v_reusejp_4994_:
{
return v___x_4995_;
}
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
lean_dec_ref(v___y_4973_);
lean_dec_ref(v___x_4971_);
lean_dec(v___x_4970_);
lean_del_object(v___x_4955_);
lean_dec(v_snd_4953_);
lean_dec(v_fst_4952_);
lean_del_object(v___x_4950_);
lean_dec(v_a_4938_);
lean_dec(v___x_4937_);
lean_dec(v___x_4936_);
lean_dec_ref(v___x_4935_);
lean_dec_ref(v___x_4934_);
lean_dec_ref(v___x_4933_);
lean_dec(v___x_4932_);
lean_dec_ref(v_a_4931_);
lean_dec(v___x_4930_);
lean_dec_ref(v___x_4929_);
lean_dec(v_matchDeclName_4928_);
lean_dec_ref(v_val_4927_);
v_a_4998_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4974_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4974_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
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
lean_object* v_upperBound_5013_ = _args[0];
lean_object* v_val_5014_ = _args[1];
lean_object* v_matchDeclName_5015_ = _args[2];
lean_object* v___x_5016_ = _args[3];
lean_object* v___x_5017_ = _args[4];
lean_object* v_a_5018_ = _args[5];
lean_object* v___x_5019_ = _args[6];
lean_object* v___x_5020_ = _args[7];
lean_object* v___x_5021_ = _args[8];
lean_object* v___x_5022_ = _args[9];
lean_object* v___x_5023_ = _args[10];
lean_object* v___x_5024_ = _args[11];
lean_object* v_a_5025_ = _args[12];
lean_object* v_b_5026_ = _args[13];
lean_object* v___y_5027_ = _args[14];
lean_object* v___y_5028_ = _args[15];
lean_object* v___y_5029_ = _args[16];
lean_object* v___y_5030_ = _args[17];
lean_object* v___y_5031_ = _args[18];
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5013_, v_val_5014_, v_matchDeclName_5015_, v___x_5016_, v___x_5017_, v_a_5018_, v___x_5019_, v___x_5020_, v___x_5021_, v___x_5022_, v___x_5023_, v___x_5024_, v_a_5025_, v_b_5026_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
lean_dec(v_upperBound_5013_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5039_, lean_object* v___x_5040_, lean_object* v_matchDeclName_5041_, lean_object* v___x_5042_, lean_object* v_a_5043_, lean_object* v___x_5044_, lean_object* v___x_5045_, lean_object* v_xs_5046_, lean_object* v___matchResultType_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_){
_start:
{
lean_object* v_numParams_5053_; lean_object* v_numDiscrs_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v_lower_5060_; lean_object* v_upper_5061_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; uint8_t v___x_5092_; 
v_numParams_5053_ = lean_ctor_get(v_val_5039_, 0);
v_numDiscrs_5054_ = lean_ctor_get(v_val_5039_, 1);
v___x_5055_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5053_);
lean_inc_ref(v_xs_5046_);
v___x_5056_ = l_Array_toSubarray___redArg(v_xs_5046_, v___x_5055_, v_numParams_5053_);
v___x_5057_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5039_);
v___x_5058_ = lean_array_get(v___x_5040_, v_xs_5046_, v___x_5057_);
lean_dec(v___x_5057_);
v___x_5089_ = lean_array_get_size(v_xs_5046_);
v___x_5090_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5039_);
v___x_5091_ = lean_nat_sub(v___x_5089_, v___x_5090_);
lean_dec(v___x_5090_);
v___x_5092_ = lean_nat_dec_le(v___x_5091_, v___x_5055_);
if (v___x_5092_ == 0)
{
v_lower_5060_ = v___x_5091_;
v_upper_5061_ = v___x_5089_;
goto v___jp_5059_;
}
else
{
lean_dec(v___x_5091_);
v_lower_5060_ = v___x_5055_;
v_upper_5061_ = v___x_5089_;
goto v___jp_5059_;
}
v___jp_5059_:
{
lean_object* v___x_5062_; lean_object* v_start_5063_; lean_object* v_stop_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
lean_inc_ref(v_xs_5046_);
v___x_5062_ = l_Array_toSubarray___redArg(v_xs_5046_, v_lower_5060_, v_upper_5061_);
v_start_5063_ = lean_ctor_get(v___x_5062_, 1);
lean_inc(v_start_5063_);
v_stop_5064_ = lean_ctor_get(v___x_5062_, 2);
lean_inc(v_stop_5064_);
v___x_5065_ = lean_unsigned_to_nat(1u);
v___x_5066_ = lean_nat_add(v_numParams_5053_, v___x_5065_);
v___x_5067_ = lean_nat_add(v___x_5066_, v_numDiscrs_5054_);
v___x_5068_ = lean_nat_sub(v_stop_5064_, v_start_5063_);
lean_dec(v_start_5063_);
lean_dec(v_stop_5064_);
v___x_5069_ = l_Array_toSubarray___redArg(v_xs_5046_, v___x_5066_, v___x_5067_);
v___x_5070_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5068_);
v___x_5071_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5068_, v_val_5039_, v_matchDeclName_5041_, v___x_5069_, v___x_5042_, v_a_5043_, v___x_5044_, v___x_5056_, v___x_5058_, v___x_5062_, v___x_5068_, v___x_5045_, v___x_5055_, v___x_5070_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_);
lean_dec(v___x_5068_);
if (lean_obj_tag(v___x_5071_) == 0)
{
lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5079_; 
v_isSharedCheck_5079_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5079_ == 0)
{
lean_object* v_unused_5080_; 
v_unused_5080_ = lean_ctor_get(v___x_5071_, 0);
lean_dec(v_unused_5080_);
v___x_5073_ = v___x_5071_;
v_isShared_5074_ = v_isSharedCheck_5079_;
goto v_resetjp_5072_;
}
else
{
lean_dec(v___x_5071_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5079_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5075_; lean_object* v___x_5077_; 
v___x_5075_ = lean_box(0);
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v___x_5075_);
v___x_5077_ = v___x_5073_;
goto v_reusejp_5076_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v___x_5075_);
v___x_5077_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5076_;
}
v_reusejp_5076_:
{
return v___x_5077_;
}
}
}
else
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
v_a_5081_ = lean_ctor_get(v___x_5071_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5071_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5071_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5071_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5093_, lean_object* v___x_5094_, lean_object* v_matchDeclName_5095_, lean_object* v___x_5096_, lean_object* v_a_5097_, lean_object* v___x_5098_, lean_object* v___x_5099_, lean_object* v_xs_5100_, lean_object* v___matchResultType_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_){
_start:
{
lean_object* v_res_5107_; 
v_res_5107_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5093_, v___x_5094_, v_matchDeclName_5095_, v___x_5096_, v_a_5097_, v___x_5098_, v___x_5099_, v_xs_5100_, v___matchResultType_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_);
lean_dec(v___y_5105_);
lean_dec_ref(v___y_5104_);
lean_dec(v___y_5103_);
lean_dec_ref(v___y_5102_);
lean_dec_ref(v___matchResultType_5101_);
lean_dec_ref(v___x_5094_);
return v_res_5107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_){
_start:
{
uint8_t v_trackZetaDelta_5114_; lean_object* v_zetaDeltaSet_5115_; lean_object* v_lctx_5116_; lean_object* v_localInstances_5117_; lean_object* v_defEqCtx_x3f_5118_; lean_object* v_synthPendingDepth_5119_; lean_object* v_customCanUnfoldPredicate_x3f_5120_; uint8_t v_univApprox_5121_; uint8_t v_inTypeClassResolution_5122_; uint8_t v_cacheInferType_5123_; lean_object* v___x_5124_; lean_object* v___x_5126_; uint8_t v_isShared_5127_; uint8_t v_isSharedCheck_5167_; 
v_trackZetaDelta_5114_ = lean_ctor_get_uint8(v_a_5109_, sizeof(void*)*7);
v_zetaDeltaSet_5115_ = lean_ctor_get(v_a_5109_, 1);
lean_inc(v_zetaDeltaSet_5115_);
v_lctx_5116_ = lean_ctor_get(v_a_5109_, 2);
lean_inc_ref(v_lctx_5116_);
v_localInstances_5117_ = lean_ctor_get(v_a_5109_, 3);
lean_inc_ref(v_localInstances_5117_);
v_defEqCtx_x3f_5118_ = lean_ctor_get(v_a_5109_, 4);
lean_inc(v_defEqCtx_x3f_5118_);
v_synthPendingDepth_5119_ = lean_ctor_get(v_a_5109_, 5);
lean_inc(v_synthPendingDepth_5119_);
v_customCanUnfoldPredicate_x3f_5120_ = lean_ctor_get(v_a_5109_, 6);
lean_inc(v_customCanUnfoldPredicate_x3f_5120_);
v_univApprox_5121_ = lean_ctor_get_uint8(v_a_5109_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5122_ = lean_ctor_get_uint8(v_a_5109_, sizeof(void*)*7 + 2);
v_cacheInferType_5123_ = lean_ctor_get_uint8(v_a_5109_, sizeof(void*)*7 + 3);
v___x_5124_ = l_Lean_Meta_Context_config(v_a_5109_);
v_isSharedCheck_5167_ = !lean_is_exclusive(v_a_5109_);
if (v_isSharedCheck_5167_ == 0)
{
lean_object* v_unused_5168_; lean_object* v_unused_5169_; lean_object* v_unused_5170_; lean_object* v_unused_5171_; lean_object* v_unused_5172_; lean_object* v_unused_5173_; lean_object* v_unused_5174_; 
v_unused_5168_ = lean_ctor_get(v_a_5109_, 6);
lean_dec(v_unused_5168_);
v_unused_5169_ = lean_ctor_get(v_a_5109_, 5);
lean_dec(v_unused_5169_);
v_unused_5170_ = lean_ctor_get(v_a_5109_, 4);
lean_dec(v_unused_5170_);
v_unused_5171_ = lean_ctor_get(v_a_5109_, 3);
lean_dec(v_unused_5171_);
v_unused_5172_ = lean_ctor_get(v_a_5109_, 2);
lean_dec(v_unused_5172_);
v_unused_5173_ = lean_ctor_get(v_a_5109_, 1);
lean_dec(v_unused_5173_);
v_unused_5174_ = lean_ctor_get(v_a_5109_, 0);
lean_dec(v_unused_5174_);
v___x_5126_ = v_a_5109_;
v_isShared_5127_ = v_isSharedCheck_5167_;
goto v_resetjp_5125_;
}
else
{
lean_dec(v_a_5109_);
v___x_5126_ = lean_box(0);
v_isShared_5127_ = v_isSharedCheck_5167_;
goto v_resetjp_5125_;
}
v_resetjp_5125_:
{
lean_object* v___x_5128_; uint64_t v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5132_; 
v___x_5128_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5124_);
v___x_5129_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5128_);
v___x_5130_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5130_, 0, v___x_5128_);
lean_ctor_set_uint64(v___x_5130_, sizeof(void*)*1, v___x_5129_);
lean_inc(v_customCanUnfoldPredicate_x3f_5120_);
lean_inc(v_synthPendingDepth_5119_);
lean_inc(v_defEqCtx_x3f_5118_);
lean_inc_ref(v_localInstances_5117_);
lean_inc_ref(v_lctx_5116_);
lean_inc(v_zetaDeltaSet_5115_);
if (v_isShared_5127_ == 0)
{
lean_ctor_set(v___x_5126_, 0, v___x_5130_);
v___x_5132_ = v___x_5126_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v___x_5130_);
lean_ctor_set(v_reuseFailAlloc_5166_, 1, v_zetaDeltaSet_5115_);
lean_ctor_set(v_reuseFailAlloc_5166_, 2, v_lctx_5116_);
lean_ctor_set(v_reuseFailAlloc_5166_, 3, v_localInstances_5117_);
lean_ctor_set(v_reuseFailAlloc_5166_, 4, v_defEqCtx_x3f_5118_);
lean_ctor_set(v_reuseFailAlloc_5166_, 5, v_synthPendingDepth_5119_);
lean_ctor_set(v_reuseFailAlloc_5166_, 6, v_customCanUnfoldPredicate_x3f_5120_);
lean_ctor_set_uint8(v_reuseFailAlloc_5166_, sizeof(void*)*7, v_trackZetaDelta_5114_);
lean_ctor_set_uint8(v_reuseFailAlloc_5166_, sizeof(void*)*7 + 1, v_univApprox_5121_);
lean_ctor_set_uint8(v_reuseFailAlloc_5166_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5122_);
lean_ctor_set_uint8(v_reuseFailAlloc_5166_, sizeof(void*)*7 + 3, v_cacheInferType_5123_);
v___x_5132_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
lean_object* v___x_5133_; lean_object* v___x_5134_; uint64_t v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5133_ = l_Lean_Meta_Context_config(v___x_5132_);
lean_dec_ref(v___x_5132_);
v___x_5134_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5133_);
v___x_5135_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5134_);
v___x_5136_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5136_, 0, v___x_5134_);
lean_ctor_set_uint64(v___x_5136_, sizeof(void*)*1, v___x_5135_);
v___x_5137_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5137_, 0, v___x_5136_);
lean_ctor_set(v___x_5137_, 1, v_zetaDeltaSet_5115_);
lean_ctor_set(v___x_5137_, 2, v_lctx_5116_);
lean_ctor_set(v___x_5137_, 3, v_localInstances_5117_);
lean_ctor_set(v___x_5137_, 4, v_defEqCtx_x3f_5118_);
lean_ctor_set(v___x_5137_, 5, v_synthPendingDepth_5119_);
lean_ctor_set(v___x_5137_, 6, v_customCanUnfoldPredicate_x3f_5120_);
lean_ctor_set_uint8(v___x_5137_, sizeof(void*)*7, v_trackZetaDelta_5114_);
lean_ctor_set_uint8(v___x_5137_, sizeof(void*)*7 + 1, v_univApprox_5121_);
lean_ctor_set_uint8(v___x_5137_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5122_);
lean_ctor_set_uint8(v___x_5137_, sizeof(void*)*7 + 3, v_cacheInferType_5123_);
lean_inc(v_matchDeclName_5108_);
v___x_5138_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5108_, v___x_5137_, v_a_5110_, v_a_5111_, v_a_5112_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v_a_5139_; lean_object* v___x_5140_; lean_object* v_a_5141_; 
v_a_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc(v_a_5139_);
lean_dec_ref_known(v___x_5138_, 1);
lean_inc(v_matchDeclName_5108_);
v___x_5140_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5108_, v_a_5112_);
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
lean_inc(v_a_5141_);
lean_dec_ref(v___x_5140_);
if (lean_obj_tag(v_a_5141_) == 1)
{
lean_object* v_val_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___f_5148_; lean_object* v___x_5149_; uint8_t v___x_5150_; lean_object* v___x_5151_; 
v_val_5142_ = lean_ctor_get(v_a_5141_, 0);
lean_inc(v_val_5142_);
lean_dec_ref_known(v_a_5141_, 1);
v___x_5143_ = l_Lean_instInhabitedExpr;
v___x_5144_ = l_Lean_ConstantInfo_levelParams(v_a_5139_);
v___x_5145_ = lean_box(0);
lean_inc(v___x_5144_);
v___x_5146_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_5144_, v___x_5145_);
v___x_5147_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5142_);
lean_inc(v_a_5139_);
v___f_5148_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5148_, 0, v_val_5142_);
lean_closure_set(v___f_5148_, 1, v___x_5143_);
lean_closure_set(v___f_5148_, 2, v_matchDeclName_5108_);
lean_closure_set(v___f_5148_, 3, v___x_5147_);
lean_closure_set(v___f_5148_, 4, v_a_5139_);
lean_closure_set(v___f_5148_, 5, v___x_5146_);
lean_closure_set(v___f_5148_, 6, v___x_5144_);
v___x_5149_ = l_Lean_ConstantInfo_type(v_a_5139_);
lean_dec(v_a_5139_);
v___x_5150_ = 0;
v___x_5151_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5149_, v___f_5148_, v___x_5150_, v___x_5150_, v___x_5137_, v_a_5110_, v_a_5111_, v_a_5112_);
lean_dec_ref_known(v___x_5137_, 7);
return v___x_5151_;
}
else
{
lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; 
lean_dec(v_a_5141_);
lean_dec(v_a_5139_);
v___x_5152_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5153_ = l_Lean_MessageData_ofName(v_matchDeclName_5108_);
v___x_5154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5154_, 0, v___x_5152_);
lean_ctor_set(v___x_5154_, 1, v___x_5153_);
v___x_5155_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5156_, 0, v___x_5154_);
lean_ctor_set(v___x_5156_, 1, v___x_5155_);
v___x_5157_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5156_, v___x_5137_, v_a_5110_, v_a_5111_, v_a_5112_);
lean_dec_ref_known(v___x_5137_, 7);
return v___x_5157_;
}
}
else
{
lean_object* v_a_5158_; lean_object* v___x_5160_; uint8_t v_isShared_5161_; uint8_t v_isSharedCheck_5165_; 
lean_dec_ref_known(v___x_5137_, 7);
lean_dec(v_matchDeclName_5108_);
v_a_5158_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5165_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5165_ == 0)
{
v___x_5160_ = v___x_5138_;
v_isShared_5161_ = v_isSharedCheck_5165_;
goto v_resetjp_5159_;
}
else
{
lean_inc(v_a_5158_);
lean_dec(v___x_5138_);
v___x_5160_ = lean_box(0);
v_isShared_5161_ = v_isSharedCheck_5165_;
goto v_resetjp_5159_;
}
v_resetjp_5159_:
{
lean_object* v___x_5163_; 
if (v_isShared_5161_ == 0)
{
v___x_5163_ = v___x_5160_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5164_; 
v_reuseFailAlloc_5164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5164_, 0, v_a_5158_);
v___x_5163_ = v_reuseFailAlloc_5164_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
return v___x_5163_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
lean_dec(v_a_5179_);
lean_dec_ref(v_a_5178_);
lean_dec(v_a_5177_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v_inst_5182_, lean_object* v_R_5183_, lean_object* v_a_5184_, lean_object* v_b_5185_, lean_object* v_c_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
lean_object* v___x_5192_; 
v___x_5192_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_5184_, v_b_5185_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
return v___x_5192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v_inst_5193_, lean_object* v_R_5194_, lean_object* v_a_5195_, lean_object* v_b_5196_, lean_object* v_c_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_inst_5193_, v_R_5194_, v_a_5195_, v_b_5196_, v_c_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_);
lean_dec(v___y_5201_);
lean_dec_ref(v___y_5200_);
lean_dec(v___y_5199_);
lean_dec_ref(v___y_5198_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5204_, lean_object* v_val_5205_, lean_object* v_matchDeclName_5206_, lean_object* v___x_5207_, lean_object* v___x_5208_, lean_object* v_a_5209_, lean_object* v___x_5210_, lean_object* v___x_5211_, lean_object* v___x_5212_, lean_object* v___x_5213_, lean_object* v___x_5214_, lean_object* v___x_5215_, lean_object* v_inst_5216_, lean_object* v_R_5217_, lean_object* v_a_5218_, lean_object* v_b_5219_, lean_object* v_c_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_){
_start:
{
lean_object* v___x_5226_; 
v___x_5226_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5204_, v_val_5205_, v_matchDeclName_5206_, v___x_5207_, v___x_5208_, v_a_5209_, v___x_5210_, v___x_5211_, v___x_5212_, v___x_5213_, v___x_5214_, v___x_5215_, v_a_5218_, v_b_5219_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5227_ = _args[0];
lean_object* v_val_5228_ = _args[1];
lean_object* v_matchDeclName_5229_ = _args[2];
lean_object* v___x_5230_ = _args[3];
lean_object* v___x_5231_ = _args[4];
lean_object* v_a_5232_ = _args[5];
lean_object* v___x_5233_ = _args[6];
lean_object* v___x_5234_ = _args[7];
lean_object* v___x_5235_ = _args[8];
lean_object* v___x_5236_ = _args[9];
lean_object* v___x_5237_ = _args[10];
lean_object* v___x_5238_ = _args[11];
lean_object* v_inst_5239_ = _args[12];
lean_object* v_R_5240_ = _args[13];
lean_object* v_a_5241_ = _args[14];
lean_object* v_b_5242_ = _args[15];
lean_object* v_c_5243_ = _args[16];
lean_object* v___y_5244_ = _args[17];
lean_object* v___y_5245_ = _args[18];
lean_object* v___y_5246_ = _args[19];
lean_object* v___y_5247_ = _args[20];
lean_object* v___y_5248_ = _args[21];
_start:
{
lean_object* v_res_5249_; 
v_res_5249_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5227_, v_val_5228_, v_matchDeclName_5229_, v___x_5230_, v___x_5231_, v_a_5232_, v___x_5233_, v___x_5234_, v___x_5235_, v___x_5236_, v___x_5237_, v___x_5238_, v_inst_5239_, v_R_5240_, v_a_5241_, v_b_5242_, v_c_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec(v___y_5245_);
lean_dec_ref(v___y_5244_);
lean_dec(v_upperBound_5227_);
return v_res_5249_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5250_, lean_object* v_matchDeclName_5251_, lean_object* v_a_5252_, lean_object* v_b_5253_){
_start:
{
uint8_t v___x_5255_; 
v___x_5255_ = lean_nat_dec_lt(v_a_5252_, v_upperBound_5250_);
if (v___x_5255_ == 0)
{
lean_object* v___x_5256_; 
lean_dec(v_a_5252_);
lean_dec(v_matchDeclName_5251_);
v___x_5256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5256_, 0, v_b_5253_);
return v___x_5256_;
}
else
{
lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5257_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5251_);
v___x_5258_ = l_Lean_Name_str___override(v_matchDeclName_5251_, v___x_5257_);
v___x_5259_ = lean_unsigned_to_nat(1u);
v___x_5260_ = lean_nat_add(v_a_5252_, v___x_5259_);
lean_dec(v_a_5252_);
lean_inc(v___x_5260_);
v___x_5261_ = lean_name_append_index_after(v___x_5258_, v___x_5260_);
v___x_5262_ = lean_array_push(v_b_5253_, v___x_5261_);
v_a_5252_ = v___x_5260_;
v_b_5253_ = v___x_5262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5264_, lean_object* v_matchDeclName_5265_, lean_object* v_a_5266_, lean_object* v_b_5267_, lean_object* v___y_5268_){
_start:
{
lean_object* v_res_5269_; 
v_res_5269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5264_, v_matchDeclName_5265_, v_a_5266_, v_b_5267_);
lean_dec(v_upperBound_5264_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_){
_start:
{
lean_object* v___x_5276_; lean_object* v_firstEqnName_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
v___x_5276_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5270_, 3);
v_firstEqnName_5277_ = l_Lean_Name_str___override(v_matchDeclName_5270_, v___x_5276_);
v___x_5278_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5278_, 0, v_matchDeclName_5270_);
v___x_5279_ = l_Lean_Meta_realizeConst(v_matchDeclName_5270_, v_firstEqnName_5277_, v___x_5278_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
if (lean_obj_tag(v___x_5279_) == 0)
{
lean_object* v___x_5280_; lean_object* v_a_5281_; 
lean_dec_ref_known(v___x_5279_, 1);
lean_inc(v_matchDeclName_5270_);
v___x_5280_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5270_, v_a_5274_);
v_a_5281_ = lean_ctor_get(v___x_5280_, 0);
lean_inc(v_a_5281_);
lean_dec_ref(v___x_5280_);
if (lean_obj_tag(v_a_5281_) == 1)
{
lean_object* v_val_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
lean_dec(v_a_5274_);
lean_dec_ref(v_a_5273_);
lean_dec(v_a_5272_);
lean_dec_ref(v_a_5271_);
v_val_5282_ = lean_ctor_get(v_a_5281_, 0);
lean_inc(v_val_5282_);
lean_dec_ref_known(v_a_5281_, 1);
v___x_5283_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5282_);
lean_dec(v_val_5282_);
v___x_5284_ = lean_unsigned_to_nat(0u);
v___x_5285_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5286_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5283_, v_matchDeclName_5270_, v___x_5284_, v___x_5285_);
lean_dec(v___x_5283_);
return v___x_5286_;
}
else
{
lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; 
lean_dec(v_a_5281_);
v___x_5287_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5288_ = l_Lean_MessageData_ofName(v_matchDeclName_5270_);
v___x_5289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5289_, 0, v___x_5287_);
lean_ctor_set(v___x_5289_, 1, v___x_5288_);
v___x_5290_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5289_);
lean_ctor_set(v___x_5291_, 1, v___x_5290_);
v___x_5292_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5291_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
lean_dec(v_a_5274_);
lean_dec_ref(v_a_5273_);
lean_dec(v_a_5272_);
lean_dec_ref(v_a_5271_);
return v___x_5292_;
}
}
else
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5300_; 
lean_dec(v_a_5274_);
lean_dec_ref(v_a_5273_);
lean_dec(v_a_5272_);
lean_dec_ref(v_a_5271_);
lean_dec(v_matchDeclName_5270_);
v_a_5293_ = lean_ctor_get(v___x_5279_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v___x_5279_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5295_ = v___x_5279_;
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5279_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5298_; 
if (v_isShared_5296_ == 0)
{
v___x_5298_ = v___x_5295_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_a_5293_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
return v___x_5298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_){
_start:
{
lean_object* v_res_5307_; 
v_res_5307_ = lean_get_congr_match_equations_for(v_matchDeclName_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5308_, lean_object* v_matchDeclName_5309_, lean_object* v_inst_5310_, lean_object* v_R_5311_, lean_object* v_a_5312_, lean_object* v_b_5313_, lean_object* v_c_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_){
_start:
{
lean_object* v___x_5320_; 
v___x_5320_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5308_, v_matchDeclName_5309_, v_a_5312_, v_b_5313_);
return v___x_5320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5321_, lean_object* v_matchDeclName_5322_, lean_object* v_inst_5323_, lean_object* v_R_5324_, lean_object* v_a_5325_, lean_object* v_b_5326_, lean_object* v_c_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v_res_5333_; 
v_res_5333_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5321_, v_matchDeclName_5322_, v_inst_5323_, v_R_5324_, v_a_5325_, v_b_5326_, v_c_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
lean_dec(v_upperBound_5321_);
return v_res_5333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5384_ = lean_unsigned_to_nat(3248161880u);
v___x_5385_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5386_ = l_Lean_Name_num___override(v___x_5385_, v___x_5384_);
return v___x_5386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; 
v___x_5388_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5389_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5390_ = l_Lean_Name_str___override(v___x_5389_, v___x_5388_);
return v___x_5390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; 
v___x_5392_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5393_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5394_ = l_Lean_Name_str___override(v___x_5393_, v___x_5392_);
return v___x_5394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5395_ = lean_unsigned_to_nat(2u);
v___x_5396_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5397_ = l_Lean_Name_num___override(v___x_5396_, v___x_5395_);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5399_; uint8_t v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5399_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5400_ = 0;
v___x_5401_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5402_ = l_Lean_registerTraceClass(v___x_5399_, v___x_5400_, v___x_5401_);
return v___x_5402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5405_, lean_object* v_n_5406_){
_start:
{
if (lean_obj_tag(v_n_5406_) == 1)
{
lean_object* v_pre_5407_; lean_object* v_str_5408_; uint8_t v___y_5410_; uint8_t v___x_5416_; 
v_pre_5407_ = lean_ctor_get(v_n_5406_, 0);
lean_inc(v_pre_5407_);
v_str_5408_ = lean_ctor_get(v_n_5406_, 1);
lean_inc_ref_n(v_str_5408_, 2);
lean_dec_ref_known(v_n_5406_, 2);
v___x_5416_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5408_);
if (v___x_5416_ == 0)
{
lean_object* v___x_5417_; uint8_t v___x_5418_; 
v___x_5417_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5418_ = lean_string_dec_eq(v_str_5408_, v___x_5417_);
lean_dec_ref(v_str_5408_);
v___y_5410_ = v___x_5418_;
goto v___jp_5409_;
}
else
{
lean_dec_ref(v_str_5408_);
v___y_5410_ = v___x_5416_;
goto v___jp_5409_;
}
v___jp_5409_:
{
if (v___y_5410_ == 0)
{
lean_object* v___x_5411_; 
lean_dec(v_pre_5407_);
lean_dec_ref(v_env_5405_);
v___x_5411_ = lean_box(0);
return v___x_5411_;
}
else
{
lean_object* v___x_5412_; 
v___x_5412_ = l_Lean_privateToUserName_x3f(v_pre_5407_);
if (lean_obj_tag(v___x_5412_) == 0)
{
lean_dec_ref(v_env_5405_);
return v___x_5412_;
}
else
{
lean_object* v_val_5413_; uint8_t v___x_5414_; 
v_val_5413_ = lean_ctor_get(v___x_5412_, 0);
lean_inc(v_val_5413_);
v___x_5414_ = l_Lean_Meta_isMatcherCore(v_env_5405_, v_val_5413_);
if (v___x_5414_ == 0)
{
lean_object* v___x_5415_; 
lean_dec_ref_known(v___x_5412_, 1);
v___x_5415_ = lean_box(0);
return v___x_5415_;
}
else
{
return v___x_5412_;
}
}
}
}
}
else
{
lean_object* v___x_5419_; 
lean_dec(v_n_5406_);
lean_dec_ref(v_env_5405_);
v___x_5419_ = lean_box(0);
return v___x_5419_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5420_, lean_object* v_x2_5421_){
_start:
{
lean_object* v___x_5422_; 
v___x_5422_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5420_, v_x2_5421_);
if (lean_obj_tag(v___x_5422_) == 0)
{
uint8_t v___x_5423_; 
v___x_5423_ = 0;
return v___x_5423_;
}
else
{
uint8_t v___x_5424_; 
lean_dec_ref_known(v___x_5422_, 1);
v___x_5424_ = 1;
return v___x_5424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5425_, lean_object* v_x2_5426_){
_start:
{
uint8_t v_res_5427_; lean_object* v_r_5428_; 
v_res_5427_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5425_, v_x2_5426_);
v_r_5428_ = lean_box(v_res_5427_);
return v_r_5428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5431_; lean_object* v___x_5432_; 
v___f_5431_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5432_ = l_Lean_registerReservedNamePredicate(v___f_5431_);
return v___x_5432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5434_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5441_; uint64_t v___x_5442_; 
v___x_5441_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5442_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5441_);
return v___x_5442_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
v___x_5443_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5444_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5445_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5445_, 0, v___x_5444_);
lean_ctor_set_uint64(v___x_5445_, sizeof(void*)*1, v___x_5443_);
return v___x_5445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; 
v___x_5448_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5449_ = lean_unsigned_to_nat(0u);
v___x_5450_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5450_, 0, v___x_5449_);
lean_ctor_set(v___x_5450_, 1, v___x_5449_);
lean_ctor_set(v___x_5450_, 2, v___x_5449_);
lean_ctor_set(v___x_5450_, 3, v___x_5449_);
lean_ctor_set(v___x_5450_, 4, v___x_5448_);
lean_ctor_set(v___x_5450_, 5, v___x_5448_);
lean_ctor_set(v___x_5450_, 6, v___x_5448_);
lean_ctor_set(v___x_5450_, 7, v___x_5448_);
lean_ctor_set(v___x_5450_, 8, v___x_5448_);
lean_ctor_set(v___x_5450_, 9, v___x_5448_);
lean_ctor_set(v___x_5450_, 10, v___x_5448_);
return v___x_5450_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5451_; lean_object* v___x_5452_; 
v___x_5451_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5452_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5452_, 0, v___x_5451_);
lean_ctor_set(v___x_5452_, 1, v___x_5451_);
lean_ctor_set(v___x_5452_, 2, v___x_5451_);
lean_ctor_set(v___x_5452_, 3, v___x_5451_);
lean_ctor_set(v___x_5452_, 4, v___x_5451_);
lean_ctor_set(v___x_5452_, 5, v___x_5451_);
return v___x_5452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5453_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5454_, 0, v___x_5453_);
lean_ctor_set(v___x_5454_, 1, v___x_5453_);
lean_ctor_set(v___x_5454_, 2, v___x_5453_);
lean_ctor_set(v___x_5454_, 3, v___x_5453_);
lean_ctor_set(v___x_5454_, 4, v___x_5453_);
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5455_, lean_object* v_name_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_){
_start:
{
lean_object* v___x_5460_; lean_object* v_env_5461_; lean_object* v___x_5462_; 
v___x_5460_ = lean_st_ref_get(v___y_5458_);
v_env_5461_ = lean_ctor_get(v___x_5460_, 0);
lean_inc_ref(v_env_5461_);
lean_dec(v___x_5460_);
v___x_5462_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5461_, v_name_5456_);
if (lean_obj_tag(v___x_5462_) == 1)
{
lean_object* v_val_5463_; uint8_t v___x_5464_; uint8_t v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; 
v_val_5463_ = lean_ctor_get(v___x_5462_, 0);
lean_inc(v_val_5463_);
lean_dec_ref_known(v___x_5462_, 1);
v___x_5464_ = 0;
v___x_5465_ = 1;
v___x_5466_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5467_ = lean_unsigned_to_nat(0u);
v___x_5468_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5469_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5470_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5471_ = lean_box(0);
lean_inc(v___x_5455_);
v___x_5472_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5472_, 0, v___x_5466_);
lean_ctor_set(v___x_5472_, 1, v___x_5455_);
lean_ctor_set(v___x_5472_, 2, v___x_5469_);
lean_ctor_set(v___x_5472_, 3, v___x_5470_);
lean_ctor_set(v___x_5472_, 4, v___x_5471_);
lean_ctor_set(v___x_5472_, 5, v___x_5467_);
lean_ctor_set(v___x_5472_, 6, v___x_5471_);
lean_ctor_set_uint8(v___x_5472_, sizeof(void*)*7, v___x_5464_);
lean_ctor_set_uint8(v___x_5472_, sizeof(void*)*7 + 1, v___x_5464_);
lean_ctor_set_uint8(v___x_5472_, sizeof(void*)*7 + 2, v___x_5464_);
lean_ctor_set_uint8(v___x_5472_, sizeof(void*)*7 + 3, v___x_5465_);
v___x_5473_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5474_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5475_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5476_, 0, v___x_5473_);
lean_ctor_set(v___x_5476_, 1, v___x_5474_);
lean_ctor_set(v___x_5476_, 2, v___x_5455_);
lean_ctor_set(v___x_5476_, 3, v___x_5468_);
lean_ctor_set(v___x_5476_, 4, v___x_5475_);
v___x_5477_ = lean_st_mk_ref(v___x_5476_);
lean_inc(v___y_5458_);
lean_inc_ref(v___y_5457_);
lean_inc(v___x_5477_);
v___x_5478_ = lean_get_match_equations_for(v_val_5463_, v___x_5472_, v___x_5477_, v___y_5457_, v___y_5458_);
if (lean_obj_tag(v___x_5478_) == 0)
{
lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5487_; 
v_isSharedCheck_5487_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5487_ == 0)
{
lean_object* v_unused_5488_; 
v_unused_5488_ = lean_ctor_get(v___x_5478_, 0);
lean_dec(v_unused_5488_);
v___x_5480_ = v___x_5478_;
v_isShared_5481_ = v_isSharedCheck_5487_;
goto v_resetjp_5479_;
}
else
{
lean_dec(v___x_5478_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5487_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5485_; 
v___x_5482_ = lean_st_ref_get(v___x_5477_);
lean_dec(v___x_5477_);
lean_dec(v___x_5482_);
v___x_5483_ = lean_box(v___x_5465_);
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 0, v___x_5483_);
v___x_5485_ = v___x_5480_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v___x_5483_);
v___x_5485_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
return v___x_5485_;
}
}
}
else
{
lean_dec(v___x_5477_);
if (lean_obj_tag(v___x_5478_) == 0)
{
lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5496_; 
v_isSharedCheck_5496_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5496_ == 0)
{
lean_object* v_unused_5497_; 
v_unused_5497_ = lean_ctor_get(v___x_5478_, 0);
lean_dec(v_unused_5497_);
v___x_5490_ = v___x_5478_;
v_isShared_5491_ = v_isSharedCheck_5496_;
goto v_resetjp_5489_;
}
else
{
lean_dec(v___x_5478_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5496_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
lean_object* v___x_5492_; lean_object* v___x_5494_; 
v___x_5492_ = lean_box(v___x_5465_);
if (v_isShared_5491_ == 0)
{
lean_ctor_set_tag(v___x_5490_, 0);
lean_ctor_set(v___x_5490_, 0, v___x_5492_);
v___x_5494_ = v___x_5490_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v___x_5492_);
v___x_5494_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
return v___x_5494_;
}
}
}
else
{
lean_object* v_a_5498_; lean_object* v___x_5500_; uint8_t v_isShared_5501_; uint8_t v_isSharedCheck_5505_; 
v_a_5498_ = lean_ctor_get(v___x_5478_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5500_ = v___x_5478_;
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
else
{
lean_inc(v_a_5498_);
lean_dec(v___x_5478_);
v___x_5500_ = lean_box(0);
v_isShared_5501_ = v_isSharedCheck_5505_;
goto v_resetjp_5499_;
}
v_resetjp_5499_:
{
lean_object* v___x_5503_; 
if (v_isShared_5501_ == 0)
{
v___x_5503_ = v___x_5500_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_a_5498_);
v___x_5503_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
return v___x_5503_;
}
}
}
}
}
else
{
uint8_t v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; 
lean_dec(v___x_5462_);
lean_dec(v___x_5455_);
v___x_5506_ = 0;
v___x_5507_ = lean_box(v___x_5506_);
v___x_5508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5508_, 0, v___x_5507_);
return v___x_5508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5509_, lean_object* v_name_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_){
_start:
{
lean_object* v_res_5514_; 
v_res_5514_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5509_, v_name_5510_, v___y_5511_, v___y_5512_);
lean_dec(v___y_5512_);
lean_dec_ref(v___y_5511_);
return v_res_5514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5518_; lean_object* v___x_5519_; 
v___f_5518_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5519_ = l_Lean_registerReservedNameAction(v___f_5518_);
return v___x_5519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5520_){
_start:
{
lean_object* v_res_5521_; 
v_res_5521_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5522_, lean_object* v_n_5523_){
_start:
{
if (lean_obj_tag(v_n_5523_) == 1)
{
lean_object* v_pre_5524_; lean_object* v_str_5525_; uint8_t v___x_5526_; 
v_pre_5524_ = lean_ctor_get(v_n_5523_, 0);
lean_inc(v_pre_5524_);
v_str_5525_ = lean_ctor_get(v_n_5523_, 1);
lean_inc_ref(v_str_5525_);
lean_dec_ref_known(v_n_5523_, 2);
v___x_5526_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5525_);
if (v___x_5526_ == 0)
{
lean_object* v___x_5527_; 
lean_dec(v_pre_5524_);
lean_dec_ref(v_env_5522_);
v___x_5527_ = lean_box(0);
return v___x_5527_;
}
else
{
uint8_t v___x_5528_; 
lean_inc(v_pre_5524_);
v___x_5528_ = l_Lean_Meta_isMatcherCore(v_env_5522_, v_pre_5524_);
if (v___x_5528_ == 0)
{
lean_object* v___x_5529_; 
lean_dec(v_pre_5524_);
v___x_5529_ = lean_box(0);
return v___x_5529_;
}
else
{
lean_object* v___x_5530_; 
v___x_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5530_, 0, v_pre_5524_);
return v___x_5530_;
}
}
}
else
{
lean_object* v___x_5531_; 
lean_dec(v_n_5523_);
lean_dec_ref(v_env_5522_);
v___x_5531_ = lean_box(0);
return v___x_5531_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5532_, lean_object* v_x2_5533_){
_start:
{
lean_object* v___x_5534_; 
v___x_5534_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5532_, v_x2_5533_);
if (lean_obj_tag(v___x_5534_) == 0)
{
uint8_t v___x_5535_; 
v___x_5535_ = 0;
return v___x_5535_;
}
else
{
uint8_t v___x_5536_; 
lean_dec_ref_known(v___x_5534_, 1);
v___x_5536_ = 1;
return v___x_5536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5537_, lean_object* v_x2_5538_){
_start:
{
uint8_t v_res_5539_; lean_object* v_r_5540_; 
v_res_5539_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5537_, v_x2_5538_);
v_r_5540_ = lean_box(v_res_5539_);
return v_r_5540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5543_; lean_object* v___x_5544_; 
v___f_5543_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5544_ = l_Lean_registerReservedNamePredicate(v___f_5543_);
return v___x_5544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5545_){
_start:
{
lean_object* v_res_5546_; 
v_res_5546_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5547_, lean_object* v_name_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_){
_start:
{
lean_object* v___x_5552_; lean_object* v_env_5553_; lean_object* v___x_5554_; 
v___x_5552_ = lean_st_ref_get(v___y_5550_);
v_env_5553_ = lean_ctor_get(v___x_5552_, 0);
lean_inc_ref(v_env_5553_);
lean_dec(v___x_5552_);
v___x_5554_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5553_, v_name_5548_);
if (lean_obj_tag(v___x_5554_) == 1)
{
lean_object* v_val_5555_; uint8_t v___x_5556_; uint8_t v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; 
v_val_5555_ = lean_ctor_get(v___x_5554_, 0);
lean_inc(v_val_5555_);
lean_dec_ref_known(v___x_5554_, 1);
v___x_5556_ = 0;
v___x_5557_ = 1;
v___x_5558_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5559_ = lean_unsigned_to_nat(32u);
v___x_5560_ = lean_mk_empty_array_with_capacity(v___x_5559_);
lean_dec_ref(v___x_5560_);
v___x_5561_ = lean_unsigned_to_nat(0u);
v___x_5562_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5563_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5564_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5565_ = lean_box(0);
lean_inc(v___x_5547_);
v___x_5566_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5566_, 0, v___x_5558_);
lean_ctor_set(v___x_5566_, 1, v___x_5547_);
lean_ctor_set(v___x_5566_, 2, v___x_5563_);
lean_ctor_set(v___x_5566_, 3, v___x_5564_);
lean_ctor_set(v___x_5566_, 4, v___x_5565_);
lean_ctor_set(v___x_5566_, 5, v___x_5561_);
lean_ctor_set(v___x_5566_, 6, v___x_5565_);
lean_ctor_set_uint8(v___x_5566_, sizeof(void*)*7, v___x_5556_);
lean_ctor_set_uint8(v___x_5566_, sizeof(void*)*7 + 1, v___x_5556_);
lean_ctor_set_uint8(v___x_5566_, sizeof(void*)*7 + 2, v___x_5556_);
lean_ctor_set_uint8(v___x_5566_, sizeof(void*)*7 + 3, v___x_5557_);
v___x_5567_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5568_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5569_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5570_, 0, v___x_5567_);
lean_ctor_set(v___x_5570_, 1, v___x_5568_);
lean_ctor_set(v___x_5570_, 2, v___x_5547_);
lean_ctor_set(v___x_5570_, 3, v___x_5562_);
lean_ctor_set(v___x_5570_, 4, v___x_5569_);
v___x_5571_ = lean_st_mk_ref(v___x_5570_);
lean_inc(v___y_5550_);
lean_inc_ref(v___y_5549_);
lean_inc(v___x_5571_);
v___x_5572_ = lean_get_congr_match_equations_for(v_val_5555_, v___x_5566_, v___x_5571_, v___y_5549_, v___y_5550_);
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v___x_5574_; uint8_t v_isShared_5575_; uint8_t v_isSharedCheck_5581_; 
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5581_ == 0)
{
lean_object* v_unused_5582_; 
v_unused_5582_ = lean_ctor_get(v___x_5572_, 0);
lean_dec(v_unused_5582_);
v___x_5574_ = v___x_5572_;
v_isShared_5575_ = v_isSharedCheck_5581_;
goto v_resetjp_5573_;
}
else
{
lean_dec(v___x_5572_);
v___x_5574_ = lean_box(0);
v_isShared_5575_ = v_isSharedCheck_5581_;
goto v_resetjp_5573_;
}
v_resetjp_5573_:
{
lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5579_; 
v___x_5576_ = lean_st_ref_get(v___x_5571_);
lean_dec(v___x_5571_);
lean_dec(v___x_5576_);
v___x_5577_ = lean_box(v___x_5557_);
if (v_isShared_5575_ == 0)
{
lean_ctor_set(v___x_5574_, 0, v___x_5577_);
v___x_5579_ = v___x_5574_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5577_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
else
{
lean_dec(v___x_5571_);
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5590_; 
v_isSharedCheck_5590_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5590_ == 0)
{
lean_object* v_unused_5591_; 
v_unused_5591_ = lean_ctor_get(v___x_5572_, 0);
lean_dec(v_unused_5591_);
v___x_5584_ = v___x_5572_;
v_isShared_5585_ = v_isSharedCheck_5590_;
goto v_resetjp_5583_;
}
else
{
lean_dec(v___x_5572_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5590_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v___x_5586_; lean_object* v___x_5588_; 
v___x_5586_ = lean_box(v___x_5557_);
if (v_isShared_5585_ == 0)
{
lean_ctor_set_tag(v___x_5584_, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5586_);
v___x_5588_ = v___x_5584_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v___x_5586_);
v___x_5588_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
return v___x_5588_;
}
}
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5599_; 
v_a_5592_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5594_ = v___x_5572_;
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v___x_5572_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5597_; 
if (v_isShared_5595_ == 0)
{
v___x_5597_ = v___x_5594_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5592_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
}
}
else
{
uint8_t v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; 
lean_dec(v___x_5554_);
lean_dec(v___x_5547_);
v___x_5600_ = 0;
v___x_5601_ = lean_box(v___x_5600_);
v___x_5602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5602_, 0, v___x_5601_);
return v___x_5602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5603_, lean_object* v_name_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_){
_start:
{
lean_object* v_res_5608_; 
v_res_5608_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5603_, v_name_5604_, v___y_5605_, v___y_5606_);
lean_dec(v___y_5606_);
lean_dec_ref(v___y_5605_);
return v_res_5608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5612_; lean_object* v___x_5613_; 
v___f_5612_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5613_ = l_Lean_registerReservedNameAction(v___f_5612_);
return v___x_5613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5614_){
_start:
{
lean_object* v_res_5615_; 
v_res_5615_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5615_;
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
