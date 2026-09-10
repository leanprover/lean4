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
lean_object* v_a_168_; lean_object* v___x_169_; 
lean_dec_ref(v_b_160_);
v_a_168_ = lean_array_uget_borrowed(v_as_157_, v_i_159_);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v___y_162_);
lean_inc_ref(v___y_161_);
lean_inc(v_a_168_);
v___x_169_ = lean_infer_type(v_a_168_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_171_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_170_);
lean_dec_ref_known(v___x_169_, 1);
lean_inc_ref(v_binderType_150_);
v___x_171_ = l_Lean_Meta_isExprDefEq(v_a_170_, v_binderType_150_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v___x_171_, 1);
v___x_173_ = lean_box(0);
v___x_174_ = lean_unbox(v_a_172_);
lean_dec(v_a_172_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; size_t v___x_176_; size_t v___x_177_; 
v___x_175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0));
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_add(v_i_159_, v___x_176_);
v_i_159_ = v___x_177_;
v_b_160_ = v___x_175_;
goto _start;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec_ref(v_binderType_150_);
lean_inc(v_a_168_);
v___x_179_ = l_Lean_Expr_app___override(v_e_151_, v_a_168_);
v___x_180_ = lean_expr_instantiate1(v_body_152_, v_a_168_);
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
lean_ctor_set(v___x_189_, 1, v___x_173_);
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
v_a_202_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_171_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_171_);
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
v_a_210_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_169_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_169_);
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
lean_object* v___x_309_; uint8_t v_fst_311_; lean_object* v_mctx_312_; lean_object* v___y_330_; lean_object* v_mctx_335_; lean_object* v___f_336_; lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_309_ = lean_st_ref_get(v___y_307_);
v_mctx_335_ = lean_ctor_get(v___x_309_, 0);
lean_inc_ref_n(v_mctx_335_, 2);
lean_dec(v___x_309_);
v___f_336_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0));
v___f_337_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_337_, 0, v_fvarId_306_);
v___x_338_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_mctx_335_);
v___x_340_ = l_Lean_Expr_hasFVar(v_e_305_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
v___x_341_ = l_Lean_Expr_hasMVar(v_e_305_);
if (v___x_341_ == 0)
{
lean_dec_ref_known(v___x_339_, 2);
lean_dec_ref(v___f_337_);
lean_dec_ref(v_e_305_);
v_fst_311_ = v___x_341_;
v_mctx_312_ = v_mctx_335_;
goto v___jp_310_;
}
else
{
lean_object* v___x_342_; 
lean_dec_ref(v_mctx_335_);
v___x_342_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_337_, v___f_336_, v_e_305_, v___x_339_);
v___y_330_ = v___x_342_;
goto v___jp_329_;
}
}
else
{
lean_object* v___x_343_; 
lean_dec_ref(v_mctx_335_);
v___x_343_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_337_, v___f_336_, v_e_305_, v___x_339_);
v___y_330_ = v___x_343_;
goto v___jp_329_;
}
v___jp_310_:
{
lean_object* v___x_313_; lean_object* v_cache_314_; lean_object* v_zetaDeltaFVarIds_315_; lean_object* v_postponed_316_; lean_object* v_diag_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_327_; 
v___x_313_ = lean_st_ref_take(v___y_307_);
v_cache_314_ = lean_ctor_get(v___x_313_, 1);
v_zetaDeltaFVarIds_315_ = lean_ctor_get(v___x_313_, 2);
v_postponed_316_ = lean_ctor_get(v___x_313_, 3);
v_diag_317_ = lean_ctor_get(v___x_313_, 4);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v___x_313_, 0);
lean_dec(v_unused_328_);
v___x_319_ = v___x_313_;
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_diag_317_);
lean_inc(v_postponed_316_);
lean_inc(v_zetaDeltaFVarIds_315_);
lean_inc(v_cache_314_);
lean_dec(v___x_313_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v_mctx_312_);
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_mctx_312_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_cache_314_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_zetaDeltaFVarIds_315_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_postponed_316_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v_diag_317_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_st_ref_put(v___y_307_, v___x_322_);
v___x_324_ = lean_box(v_fst_311_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
}
v___jp_329_:
{
lean_object* v_snd_331_; lean_object* v_fst_332_; lean_object* v_mctx_333_; uint8_t v___x_334_; 
v_snd_331_ = lean_ctor_get(v___y_330_, 1);
lean_inc(v_snd_331_);
v_fst_332_ = lean_ctor_get(v___y_330_, 0);
lean_inc(v_fst_332_);
lean_dec_ref(v___y_330_);
v_mctx_333_ = lean_ctor_get(v_snd_331_, 1);
lean_inc_ref(v_mctx_333_);
lean_dec(v_snd_331_);
v___x_334_ = lean_unbox(v_fst_332_);
lean_dec(v_fst_332_);
v_fst_311_ = v___x_334_;
v_mctx_312_ = v_mctx_333_;
goto v___jp_310_;
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
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = l_Lean_LocalDecl_type(v_val_444_);
lean_dec(v_val_444_);
v___x_449_ = l_Lean_Meta_matchEq_x3f(v___x_448_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = lean_box(0);
v___x_452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
if (lean_obj_tag(v_a_450_) == 1)
{
lean_object* v_val_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_522_; 
v_val_453_ = lean_ctor_get(v_a_450_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_522_ == 0)
{
v___x_455_ = v_a_450_;
v_isShared_456_ = v_isSharedCheck_522_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_val_453_);
lean_dec(v_a_450_);
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
v_a_436_ = v___x_452_;
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
v_a_436_ = v___x_452_;
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
v_a_436_ = v___x_452_;
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
lean_ctor_set(v___x_464_, 1, v___x_451_);
lean_ctor_set(v___x_464_, 0, v___x_484_);
v___x_486_ = v___x_464_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_451_);
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
v_a_436_ = v___x_452_;
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
lean_dec(v_a_450_);
lean_del_object(v___x_446_);
lean_dec(v_snd_430_);
v_a_436_ = v___x_452_;
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
v_a_523_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_449_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_449_);
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
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = l_Lean_LocalDecl_type(v_val_573_);
lean_dec(v_val_573_);
v___x_578_ = l_Lean_Meta_matchEq_x3f(v___x_577_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v___x_580_ = lean_box(0);
v___x_581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
if (lean_obj_tag(v_a_579_) == 1)
{
lean_object* v_val_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_651_; 
v_val_582_ = lean_ctor_get(v_a_579_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_579_);
if (v_isSharedCheck_651_ == 0)
{
v___x_584_ = v_a_579_;
v_isShared_585_ = v_isSharedCheck_651_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_val_582_);
lean_dec(v_a_579_);
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
v_a_565_ = v___x_581_;
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
v_a_565_ = v___x_581_;
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
v_a_565_ = v___x_581_;
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
lean_ctor_set(v___x_593_, 1, v___x_580_);
lean_ctor_set(v___x_593_, 0, v___x_613_);
v___x_615_ = v___x_593_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_580_);
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
v_a_565_ = v___x_581_;
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
lean_dec(v_a_579_);
lean_del_object(v___x_575_);
lean_dec(v_snd_559_);
v_a_565_ = v___x_581_;
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
v_a_652_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_578_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_578_);
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
lean_object* v_a_760_; lean_object* v___x_761_; 
v_a_760_ = lean_array_uget_borrowed(v_as_745_, v_i_747_);
lean_inc(v_snd_756_);
lean_inc(v_mvarId_744_);
v___x_761_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_743_, v_mvarId_744_, v_a_760_, v_snd_756_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_781_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_781_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_781_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_781_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
if (lean_obj_tag(v_a_762_) == 0)
{
lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec(v_mvarId_744_);
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v_a_762_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_766_);
v___x_768_ = v___x_758_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_snd_756_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_768_);
v___x_770_ = v___x_764_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
lean_del_object(v___x_764_);
lean_dec(v_snd_756_);
v_a_773_ = lean_ctor_get(v_a_762_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v_a_762_, 1);
v___x_774_ = lean_box(0);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v_a_773_);
lean_ctor_set(v___x_758_, 0, v___x_774_);
v___x_776_ = v___x_758_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_a_773_);
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
v_a_782_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_761_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_761_);
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
lean_object* v_val_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_val_845_ = lean_ctor_get(v_a_844_, 0);
v___x_846_ = l_Lean_LocalDecl_type(v_val_845_);
v___x_847_ = l_Lean_Meta_matchEq_x3f(v___x_846_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v___x_849_ = lean_box(0);
v___x_850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_848_) == 1)
{
lean_object* v_val_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_917_; 
v_val_851_ = lean_ctor_get(v_a_848_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_a_848_);
if (v_isSharedCheck_917_ == 0)
{
v___x_853_ = v_a_848_;
v_isShared_854_ = v_isSharedCheck_917_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_val_851_);
lean_dec(v_a_848_);
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
v_a_837_ = v___x_850_;
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
v_a_837_ = v___x_850_;
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
v_a_837_ = v___x_850_;
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
lean_ctor_set(v___x_862_, 1, v___x_849_);
lean_ctor_set(v___x_862_, 0, v___x_882_);
v___x_884_ = v___x_862_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_849_);
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
v_a_837_ = v___x_850_;
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
lean_dec(v_a_848_);
lean_dec(v_snd_831_);
v_a_837_ = v___x_850_;
goto v___jp_836_;
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_del_object(v___x_833_);
lean_dec(v_snd_831_);
lean_dec(v_mvarId_819_);
v_a_918_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_847_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_847_);
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
lean_object* v_val_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_val_967_ = lean_ctor_get(v_a_966_, 0);
v___x_968_ = l_Lean_LocalDecl_type(v_val_967_);
v___x_969_ = l_Lean_Meta_matchEq_x3f(v___x_968_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = lean_box(0);
v___x_972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_970_) == 1)
{
lean_object* v_val_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1039_; 
v_val_973_ = lean_ctor_get(v_a_970_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_a_970_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_975_ = v_a_970_;
v_isShared_976_ = v_isSharedCheck_1039_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_val_973_);
lean_dec(v_a_970_);
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
v_a_959_ = v___x_972_;
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
v_a_959_ = v___x_972_;
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
v_a_959_ = v___x_972_;
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
lean_ctor_set(v___x_984_, 1, v___x_971_);
lean_ctor_set(v___x_984_, 0, v___x_1004_);
v___x_1006_ = v___x_984_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_971_);
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
v_a_959_ = v___x_972_;
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
lean_dec(v_a_970_);
lean_dec(v_snd_953_);
v_a_959_ = v___x_972_;
goto v___jp_958_;
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_del_object(v___x_955_);
lean_dec(v_snd_953_);
lean_dec(v_mvarId_941_);
v_a_1040_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_969_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_969_);
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
lean_object* v___x_1216_; 
lean_inc(v_mvarId_1210_);
v___x_1216_ = l_Lean_MVarId_getType(v_mvarId_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v___f_1218_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0));
v___f_1219_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1));
v___x_1220_ = lean_find_expr(v___f_1219_, v_a_1217_);
lean_dec(v_a_1217_);
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
v___x_1231_ = l_Lean_MVarId_deltaTarget(v_mvarId_1210_, v___f_1218_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
return v___x_1231_;
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_mvarId_1210_);
v_a_1232_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1216_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1216_);
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
lean_object* v_ref_1314_; lean_object* v___x_1315_; lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1360_; 
v_ref_1314_ = lean_ctor_get(v___y_1311_, 2);
v___x_1315_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1360_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1360_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v_traceState_1321_; lean_object* v_env_1322_; lean_object* v_nextMacroScope_1323_; lean_object* v_ngen_1324_; lean_object* v_auxDeclNGen_1325_; lean_object* v_cache_1326_; lean_object* v_messages_1327_; lean_object* v_infoState_1328_; lean_object* v_snapshotTasks_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1359_; 
v___x_1320_ = lean_st_ref_take(v___y_1312_);
v_traceState_1321_ = lean_ctor_get(v___x_1320_, 4);
v_env_1322_ = lean_ctor_get(v___x_1320_, 0);
v_nextMacroScope_1323_ = lean_ctor_get(v___x_1320_, 1);
v_ngen_1324_ = lean_ctor_get(v___x_1320_, 2);
v_auxDeclNGen_1325_ = lean_ctor_get(v___x_1320_, 3);
v_cache_1326_ = lean_ctor_get(v___x_1320_, 5);
v_messages_1327_ = lean_ctor_get(v___x_1320_, 6);
v_infoState_1328_ = lean_ctor_get(v___x_1320_, 7);
v_snapshotTasks_1329_ = lean_ctor_get(v___x_1320_, 8);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1331_ = v___x_1320_;
v_isShared_1332_ = v_isSharedCheck_1359_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_snapshotTasks_1329_);
lean_inc(v_infoState_1328_);
lean_inc(v_messages_1327_);
lean_inc(v_cache_1326_);
lean_inc(v_traceState_1321_);
lean_inc(v_auxDeclNGen_1325_);
lean_inc(v_ngen_1324_);
lean_inc(v_nextMacroScope_1323_);
lean_inc(v_env_1322_);
lean_dec(v___x_1320_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1359_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
uint64_t v_tid_1333_; lean_object* v_traces_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1358_; 
v_tid_1333_ = lean_ctor_get_uint64(v_traceState_1321_, sizeof(void*)*1);
v_traces_1334_ = lean_ctor_get(v_traceState_1321_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_traceState_1321_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1336_ = v_traceState_1321_;
v_isShared_1337_ = v_isSharedCheck_1358_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_traces_1334_);
lean_dec(v_traceState_1321_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1358_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; double v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0);
v___x_1340_ = 0;
v___x_1341_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1));
v___x_1342_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1342_, 0, v_cls_1307_);
lean_ctor_set(v___x_1342_, 1, v___x_1338_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
lean_ctor_set_float(v___x_1342_, sizeof(void*)*3, v___x_1339_);
lean_ctor_set_float(v___x_1342_, sizeof(void*)*3 + 8, v___x_1339_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*3 + 16, v___x_1340_);
v___x_1343_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2));
v___x_1344_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v_a_1316_);
lean_ctor_set(v___x_1344_, 2, v___x_1343_);
lean_inc(v_ref_1314_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_ref_1314_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = l_Lean_PersistentArray_push___redArg(v_traces_1334_, v___x_1345_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1346_);
v___x_1348_ = v___x_1336_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1346_);
lean_ctor_set_uint64(v_reuseFailAlloc_1357_, sizeof(void*)*1, v_tid_1333_);
v___x_1348_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1350_; 
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 4, v___x_1348_);
v___x_1350_ = v___x_1331_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_env_1322_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_nextMacroScope_1323_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_ngen_1324_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_auxDeclNGen_1325_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1356_, 5, v_cache_1326_);
lean_ctor_set(v_reuseFailAlloc_1356_, 6, v_messages_1327_);
lean_ctor_set(v_reuseFailAlloc_1356_, 7, v_infoState_1328_);
lean_ctor_set(v_reuseFailAlloc_1356_, 8, v_snapshotTasks_1329_);
v___x_1350_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_st_ref_put(v___y_1312_, v___x_1350_);
v___x_1352_ = lean_box(0);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1352_);
v___x_1354_ = v___x_1318_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object* v_cls_1361_, lean_object* v_msg_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1361_, v_msg_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0));
v___x_1371_ = l_Lean_stringToMessageData(v___x_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2));
v___x_1374_ = l_Lean_stringToMessageData(v___x_1373_);
return v___x_1374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16(void){
_start:
{
lean_object* v_cls_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_cls_1394_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1395_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15));
v___x_1396_ = l_Lean_Name_append(v___x_1395_, v_cls_1394_);
return v___x_1396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1398_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17));
v___x_1399_ = l_Lean_stringToMessageData(v___x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1400_, lean_object* v_mvarId_1401_, lean_object* v_depth_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v_a_1413_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; uint8_t v___y_1450_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; uint8_t v___y_1475_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v_a_1499_; uint8_t v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; uint8_t v___y_1511_; lean_object* v___y_1546_; uint8_t v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v_a_1553_; uint8_t v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; uint8_t v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; uint8_t v___y_1576_; uint8_t v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; uint8_t v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; uint8_t v___y_1633_; uint8_t v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; uint8_t v___y_1658_; uint8_t v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; uint8_t v___y_1684_; lean_object* v___y_1705_; uint8_t v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; uint8_t v___y_1713_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v_toCold_1764_; lean_object* v_currRecDepth_1765_; lean_object* v_ref_1766_; uint8_t v_diag_1767_; uint8_t v_suppressElabErrors_1768_; lean_object* v_options_1769_; lean_object* v_maxRecDepth_1770_; lean_object* v_inheritedTraceOptions_1771_; lean_object* v_cls_1772_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_toCold_1764_ = lean_ctor_get(v_a_1405_, 0);
v_currRecDepth_1765_ = lean_ctor_get(v_a_1405_, 1);
v_ref_1766_ = lean_ctor_get(v_a_1405_, 2);
v_diag_1767_ = lean_ctor_get_uint8(v_a_1405_, sizeof(void*)*3);
v_suppressElabErrors_1768_ = lean_ctor_get_uint8(v_a_1405_, sizeof(void*)*3 + 1);
v_options_1769_ = lean_ctor_get(v_toCold_1764_, 2);
v_maxRecDepth_1770_ = lean_ctor_get(v_toCold_1764_, 3);
v_inheritedTraceOptions_1771_ = lean_ctor_get(v_toCold_1764_, 11);
v_cls_1772_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_nat_dec_eq(v_maxRecDepth_1770_, v___x_1784_);
if (v___x_1785_ == 0)
{
uint8_t v___x_1786_; 
v___x_1786_ = lean_nat_dec_eq(v_currRecDepth_1765_, v_maxRecDepth_1770_);
if (v___x_1786_ == 0)
{
goto v___jp_1773_;
}
else
{
lean_object* v___x_1787_; 
lean_dec(v_mvarId_1401_);
lean_dec(v_matchDeclName_1400_);
lean_inc(v_ref_1766_);
v___x_1787_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1766_);
return v___x_1787_;
}
}
else
{
goto v___jp_1773_;
}
v___jp_1408_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1414_ = lean_unsigned_to_nat(0u);
v___x_1415_ = lean_array_get_size(v_a_1413_);
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_nat_dec_lt(v___x_1414_, v___x_1415_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref(v_a_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v_matchDeclName_1400_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
return v___x_1418_;
}
else
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_nat_dec_le(v___x_1415_, v___x_1415_);
if (v___x_1419_ == 0)
{
if (v___x_1417_ == 0)
{
lean_object* v___x_1420_; 
lean_dec_ref(v_a_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v_matchDeclName_1400_);
v___x_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1416_);
return v___x_1420_;
}
else
{
size_t v___x_1421_; size_t v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = ((size_t)0ULL);
v___x_1422_ = lean_usize_of_nat(v___x_1415_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1402_, v_matchDeclName_1400_, v_a_1413_, v___x_1421_, v___x_1422_, v___x_1416_, v___y_1411_, v___y_1409_, v___y_1412_, v___y_1410_);
lean_dec_ref(v___y_1412_);
lean_dec_ref(v_a_1413_);
return v___x_1423_;
}
}
else
{
size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = lean_usize_of_nat(v___x_1415_);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1402_, v_matchDeclName_1400_, v_a_1413_, v___x_1424_, v___x_1425_, v___x_1416_, v___y_1411_, v___y_1409_, v___y_1412_, v___y_1410_);
lean_dec_ref(v___y_1412_);
lean_dec_ref(v_a_1413_);
return v___x_1426_;
}
}
}
v___jp_1427_:
{
if (lean_obj_tag(v___y_1432_) == 0)
{
lean_object* v_a_1433_; 
v_a_1433_ = lean_ctor_get(v___y_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___y_1432_, 1);
v___y_1409_ = v___y_1428_;
v___y_1410_ = v___y_1429_;
v___y_1411_ = v___y_1430_;
v___y_1412_ = v___y_1431_;
v_a_1413_ = v_a_1433_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec_ref(v___y_1431_);
lean_dec(v_matchDeclName_1400_);
v_a_1434_ = lean_ctor_get(v___y_1432_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___y_1432_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___y_1432_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___y_1432_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
v___jp_1442_:
{
if (v___y_1450_ == 0)
{
lean_object* v___x_1451_; 
lean_dec_ref(v___y_1445_);
v___x_1451_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1446_, v___y_1444_, v___y_1447_);
lean_dec_ref(v___y_1446_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1465_; 
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1451_, 0);
lean_dec(v_unused_1466_);
v___x_1453_ = v___x_1451_;
v_isShared_1454_ = v_isSharedCheck_1465_;
goto v_resetjp_1452_;
}
else
{
lean_dec(v___x_1451_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1465_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1455_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1400_);
v___x_1456_ = l_Lean_MessageData_ofName(v_matchDeclName_1400_);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3);
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set_tag(v___x_1453_, 1);
lean_ctor_set(v___x_1453_, 0, v___y_1443_);
v___x_1461_ = v___x_1453_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___y_1443_);
v___x_1461_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1459_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1462_, v___y_1448_, v___y_1444_, v___y_1449_, v___y_1447_);
v___y_1428_ = v___y_1444_;
v___y_1429_ = v___y_1447_;
v___y_1430_ = v___y_1448_;
v___y_1431_ = v___y_1449_;
v___y_1432_ = v___x_1463_;
goto v___jp_1427_;
}
}
}
else
{
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1443_);
lean_dec(v_matchDeclName_1400_);
return v___x_1451_;
}
}
else
{
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1443_);
v___y_1428_ = v___y_1444_;
v___y_1429_ = v___y_1447_;
v___y_1430_ = v___y_1448_;
v___y_1431_ = v___y_1449_;
v___y_1432_ = v___y_1445_;
goto v___jp_1427_;
}
}
v___jp_1467_:
{
if (v___y_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_dec_ref(v___y_1473_);
v___x_1476_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1470_, v___y_1469_, v___y_1471_);
lean_dec_ref(v___y_1470_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v___x_1477_; 
lean_dec_ref_known(v___x_1476_, 1);
v___x_1477_ = l_Lean_Meta_saveState___redArg(v___y_1469_, v___y_1471_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
lean_inc(v___y_1468_);
v___x_1479_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1468_, v___y_1472_, v___y_1469_, v___y_1474_, v___y_1471_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_dec(v_a_1478_);
lean_dec(v___y_1468_);
v___y_1428_ = v___y_1469_;
v___y_1429_ = v___y_1471_;
v___y_1430_ = v___y_1472_;
v___y_1431_ = v___y_1474_;
v___y_1432_ = v___x_1479_;
goto v___jp_1427_;
}
else
{
lean_object* v_a_1480_; uint8_t v___x_1481_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
v___x_1481_ = l_Lean_Exception_isInterrupt(v_a_1480_);
if (v___x_1481_ == 0)
{
uint8_t v___x_1482_; 
v___x_1482_ = l_Lean_Exception_isRuntime(v_a_1480_);
v___y_1443_ = v___y_1468_;
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___x_1479_;
v___y_1446_ = v_a_1478_;
v___y_1447_ = v___y_1471_;
v___y_1448_ = v___y_1472_;
v___y_1449_ = v___y_1474_;
v___y_1450_ = v___x_1482_;
goto v___jp_1442_;
}
else
{
lean_dec(v_a_1480_);
v___y_1443_ = v___y_1468_;
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___x_1479_;
v___y_1446_ = v_a_1478_;
v___y_1447_ = v___y_1471_;
v___y_1448_ = v___y_1472_;
v___y_1449_ = v___y_1474_;
v___y_1450_ = v___x_1481_;
goto v___jp_1442_;
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1468_);
lean_dec(v_matchDeclName_1400_);
v_a_1483_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1477_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1477_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1468_);
lean_dec(v_matchDeclName_1400_);
return v___x_1476_;
}
}
else
{
lean_object* v___x_1491_; 
lean_dec_ref(v___y_1474_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1468_);
lean_dec(v_matchDeclName_1400_);
v___x_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___y_1473_);
return v___x_1491_;
}
}
v___jp_1492_:
{
uint8_t v___x_1500_; 
v___x_1500_ = l_Lean_Exception_isInterrupt(v_a_1499_);
if (v___x_1500_ == 0)
{
uint8_t v___x_1501_; 
lean_inc_ref(v_a_1499_);
v___x_1501_ = l_Lean_Exception_isRuntime(v_a_1499_);
v___y_1468_ = v___y_1493_;
v___y_1469_ = v___y_1494_;
v___y_1470_ = v___y_1495_;
v___y_1471_ = v___y_1496_;
v___y_1472_ = v___y_1497_;
v___y_1473_ = v_a_1499_;
v___y_1474_ = v___y_1498_;
v___y_1475_ = v___x_1501_;
goto v___jp_1467_;
}
else
{
v___y_1468_ = v___y_1493_;
v___y_1469_ = v___y_1494_;
v___y_1470_ = v___y_1495_;
v___y_1471_ = v___y_1496_;
v___y_1472_ = v___y_1497_;
v___y_1473_ = v_a_1499_;
v___y_1474_ = v___y_1498_;
v___y_1475_ = v___x_1500_;
goto v___jp_1467_;
}
}
v___jp_1502_:
{
if (v___y_1511_ == 0)
{
lean_object* v___x_1512_; 
lean_dec_ref(v___y_1507_);
v___x_1512_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1509_, v___y_1505_, v___y_1506_);
lean_dec_ref(v___y_1509_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v___x_1513_; 
lean_dec_ref_known(v___x_1512_, 1);
v___x_1513_ = l_Lean_Meta_saveState___redArg(v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = lean_box(0);
lean_inc(v___y_1504_);
v___x_1516_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1504_, v___x_1515_, v___y_1503_, v___y_1508_, v___y_1505_, v___y_1510_, v___y_1506_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
if (lean_obj_tag(v_a_1517_) == 1)
{
lean_object* v_val_1518_; lean_object* v_fst_1519_; lean_object* v_snd_1520_; lean_object* v_mvarId_1521_; lean_object* v_fvarId_1522_; lean_object* v___x_1523_; 
v_val_1518_ = lean_ctor_get(v_a_1517_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v_a_1517_, 1);
v_fst_1519_ = lean_ctor_get(v_val_1518_, 0);
lean_inc(v_fst_1519_);
v_snd_1520_ = lean_ctor_get(v_val_1518_, 1);
lean_inc(v_snd_1520_);
lean_dec(v_val_1518_);
v_mvarId_1521_ = lean_ctor_get(v_fst_1519_, 0);
lean_inc(v_mvarId_1521_);
v_fvarId_1522_ = lean_ctor_get(v_fst_1519_, 1);
lean_inc(v_fvarId_1522_);
lean_dec(v_fst_1519_);
v___x_1523_ = l_Lean_Meta_trySubst(v_mvarId_1521_, v_fvarId_1522_, v___y_1508_, v___y_1505_, v___y_1510_, v___y_1506_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v_mvarId_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_a_1514_);
lean_dec(v___y_1504_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v_mvarId_1525_ = lean_ctor_get(v_snd_1520_, 0);
lean_inc(v_mvarId_1525_);
lean_dec(v_snd_1520_);
v___x_1526_ = lean_unsigned_to_nat(2u);
v___x_1527_ = lean_mk_empty_array_with_capacity(v___x_1526_);
v___x_1528_ = lean_array_push(v___x_1527_, v_a_1524_);
v___x_1529_ = lean_array_push(v___x_1528_, v_mvarId_1525_);
v___y_1409_ = v___y_1505_;
v___y_1410_ = v___y_1506_;
v___y_1411_ = v___y_1508_;
v___y_1412_ = v___y_1510_;
v_a_1413_ = v___x_1529_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1530_; 
lean_dec(v_snd_1520_);
v_a_1530_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1523_, 1);
v___y_1493_ = v___y_1504_;
v___y_1494_ = v___y_1505_;
v___y_1495_ = v_a_1514_;
v___y_1496_ = v___y_1506_;
v___y_1497_ = v___y_1508_;
v___y_1498_ = v___y_1510_;
v_a_1499_ = v_a_1530_;
goto v___jp_1492_;
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec(v_a_1517_);
v___x_1531_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1532_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1531_, v___y_1508_, v___y_1505_, v___y_1510_, v___y_1506_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; 
lean_dec(v_a_1514_);
lean_dec(v___y_1504_);
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___y_1409_ = v___y_1505_;
v___y_1410_ = v___y_1506_;
v___y_1411_ = v___y_1508_;
v___y_1412_ = v___y_1510_;
v_a_1413_ = v_a_1533_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1534_; 
v_a_1534_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1532_, 1);
v___y_1493_ = v___y_1504_;
v___y_1494_ = v___y_1505_;
v___y_1495_ = v_a_1514_;
v___y_1496_ = v___y_1506_;
v___y_1497_ = v___y_1508_;
v___y_1498_ = v___y_1510_;
v_a_1499_ = v_a_1534_;
goto v___jp_1492_;
}
}
}
else
{
lean_object* v_a_1535_; 
v_a_1535_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1516_, 1);
v___y_1493_ = v___y_1504_;
v___y_1494_ = v___y_1505_;
v___y_1495_ = v_a_1514_;
v___y_1496_ = v___y_1506_;
v___y_1497_ = v___y_1508_;
v___y_1498_ = v___y_1510_;
v_a_1499_ = v_a_1535_;
goto v___jp_1492_;
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1504_);
lean_dec(v_matchDeclName_1400_);
v_a_1536_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1513_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1513_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1504_);
lean_dec(v_matchDeclName_1400_);
return v___x_1512_;
}
}
else
{
lean_object* v___x_1544_; 
lean_dec_ref(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1504_);
lean_dec(v_matchDeclName_1400_);
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___y_1507_);
return v___x_1544_;
}
}
v___jp_1545_:
{
uint8_t v___x_1554_; 
v___x_1554_ = l_Lean_Exception_isInterrupt(v_a_1553_);
if (v___x_1554_ == 0)
{
uint8_t v___x_1555_; 
lean_inc_ref(v_a_1553_);
v___x_1555_ = l_Lean_Exception_isRuntime(v_a_1553_);
v___y_1503_ = v___y_1547_;
v___y_1504_ = v___y_1546_;
v___y_1505_ = v___y_1548_;
v___y_1506_ = v___y_1549_;
v___y_1507_ = v_a_1553_;
v___y_1508_ = v___y_1550_;
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___y_1552_;
v___y_1511_ = v___x_1555_;
goto v___jp_1502_;
}
else
{
v___y_1503_ = v___y_1547_;
v___y_1504_ = v___y_1546_;
v___y_1505_ = v___y_1548_;
v___y_1506_ = v___y_1549_;
v___y_1507_ = v_a_1553_;
v___y_1508_ = v___y_1550_;
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___y_1552_;
v___y_1511_ = v___x_1554_;
goto v___jp_1502_;
}
}
v___jp_1556_:
{
if (lean_obj_tag(v___y_1564_) == 0)
{
lean_object* v_a_1565_; 
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1558_);
v_a_1565_ = lean_ctor_get(v___y_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___y_1564_, 1);
v___y_1409_ = v___y_1559_;
v___y_1410_ = v___y_1560_;
v___y_1411_ = v___y_1561_;
v___y_1412_ = v___y_1563_;
v_a_1413_ = v_a_1565_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1566_; 
v_a_1566_ = lean_ctor_get(v___y_1564_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___y_1564_, 1);
v___y_1546_ = v___y_1558_;
v___y_1547_ = v___y_1557_;
v___y_1548_ = v___y_1559_;
v___y_1549_ = v___y_1560_;
v___y_1550_ = v___y_1561_;
v___y_1551_ = v___y_1562_;
v___y_1552_ = v___y_1563_;
v_a_1553_ = v_a_1566_;
goto v___jp_1545_;
}
}
v___jp_1567_:
{
if (v___y_1576_ == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref(v___y_1574_);
v___x_1577_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1575_, v___y_1570_, v___y_1571_);
lean_dec_ref(v___y_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref_known(v___x_1577_, 1);
v___x_1578_ = l_Lean_Meta_saveState___redArg(v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
lean_inc(v___y_1569_);
v___x_1580_ = l_Lean_Meta_simpIfTarget(v___y_1569_, v___y_1568_, v___y_1568_, v___y_1572_, v___y_1570_, v___y_1573_, v___y_1571_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; uint8_t v___x_1582_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1582_ = l_Lean_instBEqMVarId_beq(v_a_1581_, v___y_1569_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_box(0);
v___x_1584_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1581_, v___x_1583_, v___y_1572_, v___y_1570_, v___y_1573_, v___y_1571_);
v___y_1557_ = v___y_1568_;
v___y_1558_ = v___y_1569_;
v___y_1559_ = v___y_1570_;
v___y_1560_ = v___y_1571_;
v___y_1561_ = v___y_1572_;
v___y_1562_ = v_a_1579_;
v___y_1563_ = v___y_1573_;
v___y_1564_ = v___x_1584_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1586_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1585_, v___y_1572_, v___y_1570_, v___y_1573_, v___y_1571_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1581_, v_a_1587_, v___y_1572_, v___y_1570_, v___y_1573_, v___y_1571_);
v___y_1557_ = v___y_1568_;
v___y_1558_ = v___y_1569_;
v___y_1559_ = v___y_1570_;
v___y_1560_ = v___y_1571_;
v___y_1561_ = v___y_1572_;
v___y_1562_ = v_a_1579_;
v___y_1563_ = v___y_1573_;
v___y_1564_ = v___x_1588_;
goto v___jp_1556_;
}
else
{
lean_object* v_a_1589_; 
lean_dec(v_a_1581_);
v_a_1589_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1586_, 1);
v___y_1546_ = v___y_1569_;
v___y_1547_ = v___y_1568_;
v___y_1548_ = v___y_1570_;
v___y_1549_ = v___y_1571_;
v___y_1550_ = v___y_1572_;
v___y_1551_ = v_a_1579_;
v___y_1552_ = v___y_1573_;
v_a_1553_ = v_a_1589_;
goto v___jp_1545_;
}
}
}
else
{
lean_object* v_a_1590_; 
v_a_1590_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1580_, 1);
v___y_1546_ = v___y_1569_;
v___y_1547_ = v___y_1568_;
v___y_1548_ = v___y_1570_;
v___y_1549_ = v___y_1571_;
v___y_1550_ = v___y_1572_;
v___y_1551_ = v_a_1579_;
v___y_1552_ = v___y_1573_;
v_a_1553_ = v_a_1590_;
goto v___jp_1545_;
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1569_);
lean_dec(v_matchDeclName_1400_);
v_a_1591_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1578_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1578_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1569_);
lean_dec(v_matchDeclName_1400_);
return v___x_1577_;
}
}
else
{
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1569_);
v___y_1428_ = v___y_1570_;
v___y_1429_ = v___y_1571_;
v___y_1430_ = v___y_1572_;
v___y_1431_ = v___y_1573_;
v___y_1432_ = v___y_1574_;
goto v___jp_1427_;
}
}
v___jp_1599_:
{
if (v___y_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref(v___y_1607_);
v___x_1609_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1603_, v___y_1602_, v___y_1604_);
lean_dec_ref(v___y_1603_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v___x_1610_; 
lean_dec_ref_known(v___x_1609_, 1);
v___x_1610_ = l_Lean_Meta_saveState___redArg(v___y_1602_, v___y_1604_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
lean_inc(v___y_1601_);
v___x_1612_ = l_Lean_Meta_splitSparseCasesOn(v___y_1601_, v___y_1605_, v___y_1602_, v___y_1606_, v___y_1604_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_dec(v_a_1611_);
lean_dec(v___y_1601_);
v___y_1428_ = v___y_1602_;
v___y_1429_ = v___y_1604_;
v___y_1430_ = v___y_1605_;
v___y_1431_ = v___y_1606_;
v___y_1432_ = v___x_1612_;
goto v___jp_1427_;
}
else
{
lean_object* v_a_1613_; uint8_t v___x_1614_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
v___x_1614_ = l_Lean_Exception_isInterrupt(v_a_1613_);
if (v___x_1614_ == 0)
{
uint8_t v___x_1615_; 
v___x_1615_ = l_Lean_Exception_isRuntime(v_a_1613_);
v___y_1568_ = v___y_1600_;
v___y_1569_ = v___y_1601_;
v___y_1570_ = v___y_1602_;
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1606_;
v___y_1574_ = v___x_1612_;
v___y_1575_ = v_a_1611_;
v___y_1576_ = v___x_1615_;
goto v___jp_1567_;
}
else
{
lean_dec(v_a_1613_);
v___y_1568_ = v___y_1600_;
v___y_1569_ = v___y_1601_;
v___y_1570_ = v___y_1602_;
v___y_1571_ = v___y_1604_;
v___y_1572_ = v___y_1605_;
v___y_1573_ = v___y_1606_;
v___y_1574_ = v___x_1612_;
v___y_1575_ = v_a_1611_;
v___y_1576_ = v___x_1614_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1601_);
lean_dec(v_matchDeclName_1400_);
v_a_1616_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1610_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1610_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1601_);
lean_dec(v_matchDeclName_1400_);
return v___x_1609_;
}
}
else
{
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1601_);
v___y_1428_ = v___y_1602_;
v___y_1429_ = v___y_1604_;
v___y_1430_ = v___y_1605_;
v___y_1431_ = v___y_1606_;
v___y_1432_ = v___y_1607_;
goto v___jp_1427_;
}
}
v___jp_1624_:
{
if (v___y_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref(v___y_1629_);
v___x_1634_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1628_, v___y_1627_, v___y_1630_);
lean_dec_ref(v___y_1628_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v___x_1635_; 
lean_dec_ref_known(v___x_1634_, 1);
v___x_1635_ = l_Lean_Meta_saveState___redArg(v___y_1627_, v___y_1630_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v___x_1635_, 1);
lean_inc(v___y_1626_);
v___x_1637_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1626_, v___y_1631_, v___y_1627_, v___y_1632_, v___y_1630_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_dec(v_a_1636_);
lean_dec(v___y_1626_);
v___y_1428_ = v___y_1627_;
v___y_1429_ = v___y_1630_;
v___y_1430_ = v___y_1631_;
v___y_1431_ = v___y_1632_;
v___y_1432_ = v___x_1637_;
goto v___jp_1427_;
}
else
{
lean_object* v_a_1638_; uint8_t v___x_1639_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
v___x_1639_ = l_Lean_Exception_isInterrupt(v_a_1638_);
if (v___x_1639_ == 0)
{
uint8_t v___x_1640_; 
v___x_1640_ = l_Lean_Exception_isRuntime(v_a_1638_);
v___y_1600_ = v___y_1625_;
v___y_1601_ = v___y_1626_;
v___y_1602_ = v___y_1627_;
v___y_1603_ = v_a_1636_;
v___y_1604_ = v___y_1630_;
v___y_1605_ = v___y_1631_;
v___y_1606_ = v___y_1632_;
v___y_1607_ = v___x_1637_;
v___y_1608_ = v___x_1640_;
goto v___jp_1599_;
}
else
{
lean_dec(v_a_1638_);
v___y_1600_ = v___y_1625_;
v___y_1601_ = v___y_1626_;
v___y_1602_ = v___y_1627_;
v___y_1603_ = v_a_1636_;
v___y_1604_ = v___y_1630_;
v___y_1605_ = v___y_1631_;
v___y_1606_ = v___y_1632_;
v___y_1607_ = v___x_1637_;
v___y_1608_ = v___x_1639_;
goto v___jp_1599_;
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1626_);
lean_dec(v_matchDeclName_1400_);
v_a_1641_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1635_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1635_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1626_);
lean_dec(v_matchDeclName_1400_);
return v___x_1634_;
}
}
else
{
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1626_);
v___y_1428_ = v___y_1627_;
v___y_1429_ = v___y_1630_;
v___y_1430_ = v___y_1631_;
v___y_1431_ = v___y_1632_;
v___y_1432_ = v___y_1629_;
goto v___jp_1427_;
}
}
v___jp_1649_:
{
if (v___y_1658_ == 0)
{
lean_object* v___x_1659_; 
lean_dec_ref(v___y_1653_);
v___x_1659_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1654_, v___y_1652_, v___y_1655_);
lean_dec_ref(v___y_1654_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v___x_1660_; 
lean_dec_ref_known(v___x_1659_, 1);
v___x_1660_ = l_Lean_Meta_saveState___redArg(v___y_1652_, v___y_1655_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
lean_inc(v___y_1651_);
v___x_1662_ = l_Lean_Meta_casesOnStuckLHS(v___y_1651_, v___y_1656_, v___y_1652_, v___y_1657_, v___y_1655_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_dec(v_a_1661_);
lean_dec(v___y_1651_);
v___y_1428_ = v___y_1652_;
v___y_1429_ = v___y_1655_;
v___y_1430_ = v___y_1656_;
v___y_1431_ = v___y_1657_;
v___y_1432_ = v___x_1662_;
goto v___jp_1427_;
}
else
{
lean_object* v_a_1663_; uint8_t v___x_1664_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
v___x_1664_ = l_Lean_Exception_isInterrupt(v_a_1663_);
if (v___x_1664_ == 0)
{
uint8_t v___x_1665_; 
v___x_1665_ = l_Lean_Exception_isRuntime(v_a_1663_);
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v_a_1661_;
v___y_1629_ = v___x_1662_;
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___x_1665_;
goto v___jp_1624_;
}
else
{
lean_dec(v_a_1663_);
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v_a_1661_;
v___y_1629_ = v___x_1662_;
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___x_1664_;
goto v___jp_1624_;
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1651_);
lean_dec(v_matchDeclName_1400_);
v_a_1666_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1660_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1660_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1651_);
lean_dec(v_matchDeclName_1400_);
return v___x_1659_;
}
}
else
{
lean_object* v___x_1674_; 
lean_dec_ref(v___y_1657_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1651_);
lean_dec(v_matchDeclName_1400_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___y_1653_);
return v___x_1674_;
}
}
v___jp_1675_:
{
if (v___y_1684_ == 0)
{
lean_object* v___x_1685_; 
lean_dec_ref(v___y_1680_);
v___x_1685_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1679_, v___y_1678_, v___y_1681_);
lean_dec_ref(v___y_1679_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v___x_1686_; 
lean_dec_ref_known(v___x_1685_, 1);
v___x_1686_ = l_Lean_Meta_saveState___redArg(v___y_1678_, v___y_1681_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
lean_inc(v___y_1677_);
v___x_1688_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1677_, v___y_1682_, v___y_1678_, v___y_1683_, v___y_1681_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v_a_1687_);
lean_dec(v___y_1677_);
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = lean_unsigned_to_nat(1u);
v___x_1691_ = lean_mk_empty_array_with_capacity(v___x_1690_);
v___x_1692_ = lean_array_push(v___x_1691_, v_a_1689_);
v___y_1409_ = v___y_1678_;
v___y_1410_ = v___y_1681_;
v___y_1411_ = v___y_1682_;
v___y_1412_ = v___y_1683_;
v_a_1413_ = v___x_1692_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1693_; uint8_t v___x_1694_; 
v_a_1693_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1694_ = l_Lean_Exception_isInterrupt(v_a_1693_);
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; 
lean_inc(v_a_1693_);
v___x_1695_ = l_Lean_Exception_isRuntime(v_a_1693_);
v___y_1650_ = v___y_1676_;
v___y_1651_ = v___y_1677_;
v___y_1652_ = v___y_1678_;
v___y_1653_ = v_a_1693_;
v___y_1654_ = v_a_1687_;
v___y_1655_ = v___y_1681_;
v___y_1656_ = v___y_1682_;
v___y_1657_ = v___y_1683_;
v___y_1658_ = v___x_1695_;
goto v___jp_1649_;
}
else
{
v___y_1650_ = v___y_1676_;
v___y_1651_ = v___y_1677_;
v___y_1652_ = v___y_1678_;
v___y_1653_ = v_a_1693_;
v___y_1654_ = v_a_1687_;
v___y_1655_ = v___y_1681_;
v___y_1656_ = v___y_1682_;
v___y_1657_ = v___y_1683_;
v___y_1658_ = v___x_1694_;
goto v___jp_1649_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1677_);
lean_dec(v_matchDeclName_1400_);
v_a_1696_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1686_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1686_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1677_);
lean_dec(v_matchDeclName_1400_);
return v___x_1685_;
}
}
else
{
lean_dec_ref(v___y_1683_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1677_);
lean_dec(v_matchDeclName_1400_);
return v___y_1680_;
}
}
v___jp_1704_:
{
if (v___y_1713_ == 0)
{
lean_object* v___x_1714_; 
lean_dec_ref(v___y_1708_);
v___x_1714_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1709_, v___y_1707_, v___y_1710_);
lean_dec_ref(v___y_1709_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec_ref_known(v___x_1714_, 1);
v___x_1715_ = lean_unsigned_to_nat(16u);
v___x_1716_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*1, v___y_1706_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*1 + 1, v___y_1706_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*1 + 2, v___y_1706_);
v___x_1717_ = l_Lean_Meta_saveState___redArg(v___y_1707_, v___y_1710_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
lean_inc(v___y_1705_);
v___x_1719_ = l_Lean_MVarId_contradiction(v___y_1705_, v___x_1716_, v___y_1711_, v___y_1707_, v___y_1712_, v___y_1710_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v___x_1720_; 
lean_dec_ref_known(v___x_1719_, 1);
lean_dec(v_a_1718_);
lean_dec(v___y_1705_);
v___x_1720_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1409_ = v___y_1707_;
v___y_1410_ = v___y_1710_;
v___y_1411_ = v___y_1711_;
v___y_1412_ = v___y_1712_;
v_a_1413_ = v___x_1720_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1721_; uint8_t v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1721_);
v___x_1722_ = l_Lean_Exception_isInterrupt(v_a_1721_);
if (v___x_1722_ == 0)
{
uint8_t v___x_1723_; 
v___x_1723_ = l_Lean_Exception_isRuntime(v_a_1721_);
v___y_1676_ = v___y_1706_;
v___y_1677_ = v___y_1705_;
v___y_1678_ = v___y_1707_;
v___y_1679_ = v_a_1718_;
v___y_1680_ = v___x_1719_;
v___y_1681_ = v___y_1710_;
v___y_1682_ = v___y_1711_;
v___y_1683_ = v___y_1712_;
v___y_1684_ = v___x_1723_;
goto v___jp_1675_;
}
else
{
lean_dec(v_a_1721_);
v___y_1676_ = v___y_1706_;
v___y_1677_ = v___y_1705_;
v___y_1678_ = v___y_1707_;
v___y_1679_ = v_a_1718_;
v___y_1680_ = v___x_1719_;
v___y_1681_ = v___y_1710_;
v___y_1682_ = v___y_1711_;
v___y_1683_ = v___y_1712_;
v___y_1684_ = v___x_1722_;
goto v___jp_1675_;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref_known(v___x_1716_, 1);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1705_);
lean_dec(v_matchDeclName_1400_);
v_a_1724_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1717_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1717_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
else
{
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1705_);
lean_dec(v_matchDeclName_1400_);
return v___x_1714_;
}
}
else
{
lean_dec_ref(v___y_1712_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1705_);
lean_dec(v_matchDeclName_1400_);
return v___y_1708_;
}
}
v___jp_1732_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1738_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1401_, v___x_1737_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v___x_1740_ = l_Lean_Meta_saveState___redArg(v___y_1734_, v___y_1736_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v___x_1742_ = 1;
lean_inc(v_a_1739_);
v___x_1743_ = l_Lean_MVarId_refl(v_a_1739_, v___x_1742_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v___x_1744_; 
lean_dec_ref_known(v___x_1743_, 1);
lean_dec(v_a_1741_);
lean_dec(v_a_1739_);
v___x_1744_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1409_ = v___y_1734_;
v___y_1410_ = v___y_1736_;
v___y_1411_ = v___y_1733_;
v___y_1412_ = v___y_1735_;
v_a_1413_ = v___x_1744_;
goto v___jp_1408_;
}
else
{
lean_object* v_a_1745_; uint8_t v___x_1746_; 
v_a_1745_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1745_);
v___x_1746_ = l_Lean_Exception_isInterrupt(v_a_1745_);
if (v___x_1746_ == 0)
{
uint8_t v___x_1747_; 
v___x_1747_ = l_Lean_Exception_isRuntime(v_a_1745_);
v___y_1705_ = v_a_1739_;
v___y_1706_ = v___x_1742_;
v___y_1707_ = v___y_1734_;
v___y_1708_ = v___x_1743_;
v___y_1709_ = v_a_1741_;
v___y_1710_ = v___y_1736_;
v___y_1711_ = v___y_1733_;
v___y_1712_ = v___y_1735_;
v___y_1713_ = v___x_1747_;
goto v___jp_1704_;
}
else
{
lean_dec(v_a_1745_);
v___y_1705_ = v_a_1739_;
v___y_1706_ = v___x_1742_;
v___y_1707_ = v___y_1734_;
v___y_1708_ = v___x_1743_;
v___y_1709_ = v_a_1741_;
v___y_1710_ = v___y_1736_;
v___y_1711_ = v___y_1733_;
v___y_1712_ = v___y_1735_;
v___y_1713_ = v___x_1746_;
goto v___jp_1704_;
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_a_1739_);
lean_dec_ref(v___y_1735_);
lean_dec(v_matchDeclName_1400_);
v_a_1748_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1740_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1740_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref(v___y_1735_);
lean_dec(v_matchDeclName_1400_);
v_a_1756_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1738_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1738_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
v___jp_1773_:
{
uint8_t v_hasTrace_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_hasTrace_1774_ = lean_ctor_get_uint8(v_options_1769_, sizeof(void*)*1);
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = lean_nat_add(v_currRecDepth_1765_, v___x_1775_);
lean_inc(v_ref_1766_);
lean_inc_ref(v_toCold_1764_);
v___x_1777_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1777_, 0, v_toCold_1764_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
lean_ctor_set(v___x_1777_, 2, v_ref_1766_);
lean_ctor_set_uint8(v___x_1777_, sizeof(void*)*3, v_diag_1767_);
lean_ctor_set_uint8(v___x_1777_, sizeof(void*)*3 + 1, v_suppressElabErrors_1768_);
if (v_hasTrace_1774_ == 0)
{
v___y_1733_ = v_a_1403_;
v___y_1734_ = v_a_1404_;
v___y_1735_ = v___x_1777_;
v___y_1736_ = v_a_1406_;
goto v___jp_1732_;
}
else
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1779_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1771_, v_options_1769_, v___x_1778_);
if (v___x_1779_ == 0)
{
v___y_1733_ = v_a_1403_;
v___y_1734_ = v_a_1404_;
v___y_1735_ = v___x_1777_;
v___y_1736_ = v_a_1406_;
goto v___jp_1732_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1780_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1401_);
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_mvarId_1401_);
v___x_1782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1772_, v___x_1782_, v_a_1403_, v_a_1404_, v___x_1777_, v_a_1406_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_dec_ref_known(v___x_1783_, 1);
v___y_1733_ = v_a_1403_;
v___y_1734_ = v_a_1404_;
v___y_1735_ = v___x_1777_;
v___y_1736_ = v_a_1406_;
goto v___jp_1732_;
}
else
{
lean_dec_ref_known(v___x_1777_, 3);
lean_dec(v_mvarId_1401_);
lean_dec(v_matchDeclName_1400_);
return v___x_1783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1788_, lean_object* v_matchDeclName_1789_, lean_object* v_as_1790_, size_t v_i_1791_, size_t v_stop_1792_, lean_object* v_b_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
uint8_t v___x_1799_; 
v___x_1799_ = lean_usize_dec_eq(v_i_1791_, v_stop_1792_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1800_ = lean_array_uget_borrowed(v_as_1790_, v_i_1791_);
v___x_1801_ = lean_unsigned_to_nat(1u);
v___x_1802_ = lean_nat_add(v_depth_1788_, v___x_1801_);
lean_inc(v___x_1800_);
lean_inc(v_matchDeclName_1789_);
v___x_1803_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1789_, v___x_1800_, v___x_1802_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___x_1802_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; size_t v___x_1805_; size_t v___x_1806_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1805_ = ((size_t)1ULL);
v___x_1806_ = lean_usize_add(v_i_1791_, v___x_1805_);
v_i_1791_ = v___x_1806_;
v_b_1793_ = v_a_1804_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1789_);
return v___x_1803_;
}
}
else
{
lean_object* v___x_1808_; 
lean_dec(v_matchDeclName_1789_);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_b_1793_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1809_, lean_object* v_matchDeclName_1810_, lean_object* v_as_1811_, lean_object* v_i_1812_, lean_object* v_stop_1813_, lean_object* v_b_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
size_t v_i_boxed_1820_; size_t v_stop_boxed_1821_; lean_object* v_res_1822_; 
v_i_boxed_1820_ = lean_unbox_usize(v_i_1812_);
lean_dec(v_i_1812_);
v_stop_boxed_1821_ = lean_unbox_usize(v_stop_1813_);
lean_dec(v_stop_1813_);
v_res_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1809_, v_matchDeclName_1810_, v_as_1811_, v_i_boxed_1820_, v_stop_boxed_1821_, v_b_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v_as_1811_);
lean_dec(v_depth_1809_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1823_, lean_object* v_mvarId_1824_, lean_object* v_depth_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1823_, v_mvarId_1824_, v_depth_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_depth_1825_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1832_, lean_object* v___y_1833_){
_start:
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Lean_Expr_hasMVar(v_e_1832_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_e_1832_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; lean_object* v_mctx_1838_; lean_object* v___x_1839_; lean_object* v_fst_1840_; lean_object* v_snd_1841_; lean_object* v___x_1842_; lean_object* v_cache_1843_; lean_object* v_zetaDeltaFVarIds_1844_; lean_object* v_postponed_1845_; lean_object* v_diag_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1855_; 
v___x_1837_ = lean_st_ref_get(v___y_1833_);
v_mctx_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc_ref(v_mctx_1838_);
lean_dec(v___x_1837_);
v___x_1839_ = l_Lean_instantiateMVarsCore(v_mctx_1838_, v_e_1832_);
v_fst_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_fst_1840_);
v_snd_1841_ = lean_ctor_get(v___x_1839_, 1);
lean_inc(v_snd_1841_);
lean_dec_ref(v___x_1839_);
v___x_1842_ = lean_st_ref_take(v___y_1833_);
v_cache_1843_ = lean_ctor_get(v___x_1842_, 1);
v_zetaDeltaFVarIds_1844_ = lean_ctor_get(v___x_1842_, 2);
v_postponed_1845_ = lean_ctor_get(v___x_1842_, 3);
v_diag_1846_ = lean_ctor_get(v___x_1842_, 4);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; 
v_unused_1856_ = lean_ctor_get(v___x_1842_, 0);
lean_dec(v_unused_1856_);
v___x_1848_ = v___x_1842_;
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_diag_1846_);
lean_inc(v_postponed_1845_);
lean_inc(v_zetaDeltaFVarIds_1844_);
lean_inc(v_cache_1843_);
lean_dec(v___x_1842_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v_snd_1841_);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_snd_1841_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_cache_1843_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_zetaDeltaFVarIds_1844_);
lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_postponed_1845_);
lean_ctor_set(v_reuseFailAlloc_1854_, 4, v_diag_1846_);
v___x_1851_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_st_ref_put(v___y_1833_, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_fst_1840_);
return v___x_1853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1857_, v___y_1858_);
lean_dec(v___y_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1861_, v___y_1863_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1875_, lean_object* v_localInsts_1876_, lean_object* v_x_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1875_, v_localInsts_1876_, v_x_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
v_a_1892_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1883_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1883_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1900_, lean_object* v_localInsts_1901_, lean_object* v_x_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1900_, v_localInsts_1901_, v_x_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1909_, lean_object* v_lctx_1910_, lean_object* v_localInsts_1911_, lean_object* v_x_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1910_, v_localInsts_1911_, v_x_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1919_, lean_object* v_lctx_1920_, lean_object* v_localInsts_1921_, lean_object* v_x_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1919_, v_lctx_1920_, v_localInsts_1921_, v_x_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
return v_res_1928_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1929_, lean_object* v_x_1930_){
_start:
{
uint8_t v___x_1931_; 
v___x_1931_ = lean_name_eq(v_x_1930_, v_matchDeclName_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1932_, lean_object* v_x_1933_){
_start:
{
uint8_t v_res_1934_; lean_object* v_r_1935_; 
v_res_1934_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1932_, v_x_1933_);
lean_dec(v_x_1933_);
lean_dec(v_matchDeclName_1932_);
v_r_1935_ = lean_box(v_res_1934_);
return v_r_1935_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1936_, lean_object* v_a_1937_, lean_object* v_b_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_nat_dec_lt(v_a_1937_, v_upperBound_1936_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; 
lean_dec(v_a_1937_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v_b_1938_);
return v___x_1945_;
}
else
{
uint8_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = 0;
v___x_1947_ = l_Lean_Meta_introSubstEq(v_b_1938_, v___x_1946_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v_snd_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v_snd_1949_ = lean_ctor_get(v_a_1948_, 1);
lean_inc(v_snd_1949_);
lean_dec(v_a_1948_);
v___x_1950_ = lean_unsigned_to_nat(1u);
v___x_1951_ = lean_nat_add(v_a_1937_, v___x_1950_);
lean_dec(v_a_1937_);
v_a_1937_ = v___x_1951_;
v_b_1938_ = v_snd_1949_;
goto _start;
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_a_1937_);
v_a_1953_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1947_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1947_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1961_, lean_object* v_a_1962_, lean_object* v_b_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1961_, v_a_1962_, v_b_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v_upperBound_1961_);
return v_res_1969_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1972_ = l_Lean_stringToMessageData(v___x_1971_);
return v___x_1972_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1975_ = l_Lean_stringToMessageData(v___x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1976_, lean_object* v___f_1977_, lean_object* v_matchDeclName_1978_, lean_object* v___x_1979_, uint8_t v___x_1980_, lean_object* v_heqPos_1981_, lean_object* v_heqNum_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2141_; 
v___x_1988_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1976_, v___y_1984_);
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_2141_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2141_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_box(0);
v___x_1994_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1989_, v___x_1993_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2140_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2140_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2140_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; uint8_t v___y_2006_; lean_object* v_mvarId_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v_toCold_2063_; lean_object* v_options_2064_; lean_object* v_inheritedTraceOptions_2065_; uint8_t v_hasTrace_2066_; lean_object* v___x_2067_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; 
v_toCold_2063_ = lean_ctor_get(v___y_1985_, 0);
v_options_2064_ = lean_ctor_get(v_toCold_2063_, 2);
v_inheritedTraceOptions_2065_ = lean_ctor_get(v_toCold_2063_, 11);
v_hasTrace_2066_ = lean_ctor_get_uint8(v_options_2064_, sizeof(void*)*1);
v___x_2067_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2066_ == 0)
{
v___y_2069_ = v___y_1983_;
v___y_2070_ = v___y_1984_;
v___y_2071_ = v___y_1985_;
v___y_2072_ = v___y_1986_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2126_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2065_, v_options_2064_, v___x_2125_);
if (v___x_2126_ == 0)
{
v___y_2069_ = v___y_1983_;
v___y_2070_ = v___y_1984_;
v___y_2071_ = v___y_1985_;
v___y_2072_ = v___y_1986_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2127_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2128_ = l_Lean_Expr_mvarId_x21(v_a_1995_);
v___x_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2127_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2067_, v___x_2130_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_dec_ref_known(v___x_2131_, 1);
v___y_2069_ = v___y_1983_;
v___y_2070_ = v___y_1984_;
v___y_2071_ = v___y_1985_;
v___y_2072_ = v___y_1986_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_del_object(v___x_1997_);
lean_dec(v_a_1995_);
lean_del_object(v___x_1991_);
lean_dec(v_heqPos_1981_);
lean_dec(v___x_1979_);
lean_dec(v_matchDeclName_1978_);
lean_dec_ref(v___f_1977_);
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
v___jp_1999_:
{
if (v___y_2006_ == 0)
{
lean_object* v___x_2007_; 
lean_dec_ref(v___y_2005_);
lean_del_object(v___x_1997_);
v___x_2007_ = l_Lean_MVarId_deltaTarget(v___y_2004_, v___f_1977_, v___y_2000_, v___y_2003_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = l_Lean_MVarId_heqOfEq(v_a_2008_, v___y_2000_, v___y_2003_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2011_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1978_, v_a_2010_, v___x_1979_, v___y_2000_, v___y_2003_, v___y_2001_, v___y_2002_);
lean_dec(v___x_1979_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v___x_2012_; 
lean_dec_ref_known(v___x_2011_, 1);
v___x_2012_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1995_, v___y_2003_);
return v___x_2012_;
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_a_1995_);
v_a_2013_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2011_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2011_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_a_1995_);
lean_dec(v___x_1979_);
lean_dec(v_matchDeclName_1978_);
v_a_2021_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2009_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2009_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_a_1995_);
lean_dec(v___x_1979_);
lean_dec(v_matchDeclName_1978_);
v_a_2029_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2007_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2007_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v___x_2038_; 
lean_dec(v___y_2004_);
lean_dec(v_a_1995_);
lean_dec(v___x_1979_);
lean_dec(v_matchDeclName_1978_);
lean_dec_ref(v___f_1977_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 1);
lean_ctor_set(v___x_1997_, 0, v___y_2005_);
v___x_2038_ = v___x_1997_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___y_2005_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
v___jp_2040_:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_MVarId_intros(v_mvarId_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v_snd_2048_; uint8_t v___x_2049_; lean_object* v___x_2050_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 1);
v_snd_2048_ = lean_ctor_get(v_a_2047_, 1);
lean_inc_n(v_snd_2048_, 2);
lean_dec(v_a_2047_);
v___x_2049_ = 1;
v___x_2050_ = l_Lean_MVarId_refl(v_snd_2048_, v___x_2049_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v___x_2051_; 
lean_dec_ref_known(v___x_2050_, 1);
lean_dec(v_snd_2048_);
lean_del_object(v___x_1997_);
lean_dec(v___x_1979_);
lean_dec(v_matchDeclName_1978_);
lean_dec_ref(v___f_1977_);
v___x_2051_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1995_, v___y_2043_);
return v___x_2051_;
}
else
{
lean_object* v_a_2052_; uint8_t v___x_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2053_ = l_Lean_Exception_isInterrupt(v_a_2052_);
if (v___x_2053_ == 0)
{
uint8_t v___x_2054_; 
lean_inc(v_a_2052_);
v___x_2054_ = l_Lean_Exception_isRuntime(v_a_2052_);
v___y_2000_ = v___y_2042_;
v___y_2001_ = v___y_2044_;
v___y_2002_ = v___y_2045_;
v___y_2003_ = v___y_2043_;
v___y_2004_ = v_snd_2048_;
v___y_2005_ = v_a_2052_;
v___y_2006_ = v___x_2054_;
goto v___jp_1999_;
}
else
{
v___y_2000_ = v___y_2042_;
v___y_2001_ = v___y_2044_;
v___y_2002_ = v___y_2045_;
v___y_2003_ = v___y_2043_;
v___y_2004_ = v_snd_2048_;
v___y_2005_ = v_a_2052_;
v___y_2006_ = v___x_2053_;
goto v___jp_1999_;
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_del_object(v___x_1997_);
lean_dec(v_a_1995_);
lean_dec(v___x_1979_);
lean_dec(v_matchDeclName_1978_);
lean_dec_ref(v___f_1977_);
v_a_2055_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2046_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2046_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
v___jp_2068_:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_Expr_mvarId_x21(v_a_1995_);
if (v___x_1980_ == 0)
{
lean_del_object(v___x_1991_);
lean_dec(v_heqPos_1981_);
v_mvarId_2041_ = v___x_2073_;
v___y_2042_ = v___y_2069_;
v___y_2043_ = v___y_2070_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_box(0);
v___x_2075_ = 0;
v___x_2076_ = l_Lean_Meta_introNCore(v___x_2073_, v_heqPos_1981_, v___x_2074_, v___x_2075_, v___x_2075_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v_snd_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2115_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
v_snd_2078_ = lean_ctor_get(v_a_2077_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_a_2077_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v_a_2077_, 0);
lean_dec(v_unused_2116_);
v___x_2080_ = v_a_2077_;
v_isShared_2081_ = v_isSharedCheck_2115_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_snd_2078_);
lean_dec(v_a_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2115_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; 
lean_inc(v___x_1979_);
v___x_2082_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1982_, v___x_1979_, v_snd_2078_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_toCold_2083_; lean_object* v_options_2084_; uint8_t v_hasTrace_2085_; 
v_toCold_2083_ = lean_ctor_get(v___y_2071_, 0);
v_options_2084_ = lean_ctor_get(v_toCold_2083_, 2);
v_hasTrace_2085_ = lean_ctor_get_uint8(v_options_2084_, sizeof(void*)*1);
if (v_hasTrace_2085_ == 0)
{
lean_object* v_a_2086_; 
lean_del_object(v___x_2080_);
lean_del_object(v___x_1991_);
v_a_2086_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2082_, 1);
v_mvarId_2041_ = v_a_2086_;
v___y_2042_ = v___y_2069_;
v___y_2043_ = v___y_2070_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
goto v___jp_2040_;
}
else
{
lean_object* v_a_2087_; lean_object* v_inheritedTraceOptions_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v_a_2087_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2082_, 1);
v_inheritedTraceOptions_2088_ = lean_ctor_get(v_toCold_2083_, 11);
v___x_2089_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2090_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2088_, v_options_2084_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_del_object(v___x_2080_);
lean_del_object(v___x_1991_);
v_mvarId_2041_ = v_a_2087_;
v___y_2042_ = v___y_2069_;
v___y_2043_ = v___y_2070_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2087_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set_tag(v___x_1991_, 1);
lean_ctor_set(v___x_1991_, 0, v_a_2087_);
v___x_2093_ = v___x_1991_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2087_);
v___x_2093_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 7);
lean_ctor_set(v___x_2080_, 1, v___x_2093_);
lean_ctor_set(v___x_2080_, 0, v___x_2091_);
v___x_2095_ = v___x_2080_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2067_, v___x_2095_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_dec_ref_known(v___x_2096_, 1);
v_mvarId_2041_ = v_a_2087_;
v___y_2042_ = v___y_2069_;
v___y_2043_ = v___y_2070_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
goto v___jp_2040_;
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_a_2087_);
lean_del_object(v___x_1997_);
lean_dec(v_a_1995_);
lean_dec(v___x_1979_);
lean_dec(v_matchDeclName_1978_);
lean_dec_ref(v___f_1977_);
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
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
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_del_object(v___x_2080_);
lean_del_object(v___x_1997_);
lean_dec(v_a_1995_);
lean_del_object(v___x_1991_);
lean_dec(v___x_1979_);
lean_dec(v_matchDeclName_1978_);
lean_dec_ref(v___f_1977_);
v_a_2107_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2082_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2082_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_del_object(v___x_1997_);
lean_dec(v_a_1995_);
lean_del_object(v___x_1991_);
lean_dec(v___x_1979_);
lean_dec(v_matchDeclName_1978_);
lean_dec_ref(v___f_1977_);
v_a_2117_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2076_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2076_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1991_);
lean_dec(v_heqPos_1981_);
lean_dec(v___x_1979_);
lean_dec(v_matchDeclName_1978_);
lean_dec_ref(v___f_1977_);
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2142_, lean_object* v___f_2143_, lean_object* v_matchDeclName_2144_, lean_object* v___x_2145_, lean_object* v___x_2146_, lean_object* v_heqPos_2147_, lean_object* v_heqNum_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
uint8_t v___x_5931__boxed_2154_; lean_object* v_res_2155_; 
v___x_5931__boxed_2154_ = lean_unbox(v___x_2146_);
v_res_2155_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2142_, v___f_2143_, v_matchDeclName_2144_, v___x_2145_, v___x_5931__boxed_2154_, v_heqPos_2147_, v_heqNum_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v_heqNum_2148_);
return v_res_2155_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___f_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___f_2189_; lean_object* v___x_2190_; 
lean_inc(v_matchDeclName_2174_);
v___f_2183_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2183_, 0, v_matchDeclName_2174_);
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2186_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2187_ = lean_nat_dec_lt(v___x_2184_, v_heqNum_2177_);
v___x_2188_ = lean_box(v___x_2187_);
v___f_2189_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2189_, 0, v_type_2175_);
lean_closure_set(v___f_2189_, 1, v___f_2183_);
lean_closure_set(v___f_2189_, 2, v_matchDeclName_2174_);
lean_closure_set(v___f_2189_, 3, v___x_2184_);
lean_closure_set(v___f_2189_, 4, v___x_2188_);
lean_closure_set(v___f_2189_, 5, v_heqPos_2176_);
lean_closure_set(v___f_2189_, 6, v_heqNum_2177_);
v___x_2190_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2185_, v___x_2186_, v___f_2189_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
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
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_array_fget_borrowed(v_alts_2323_, v_i_2325_);
v___x_2336_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2335_, v_a_2327_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___f_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
lean_inc_ref(v_patterns_2322_);
lean_inc_ref(v_discrs_2321_);
v___f_2338_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2338_, 0, v_i_2325_);
lean_closure_set(v___f_2338_, 1, v_altsNew_2326_);
lean_closure_set(v___f_2338_, 2, v_discrs_2321_);
lean_closure_set(v___f_2338_, 3, v_patterns_2322_);
lean_closure_set(v___f_2338_, 4, v_alts_2323_);
lean_closure_set(v___f_2338_, 5, v_k_2324_);
v___x_2339_ = l_Lean_LocalDecl_type(v_a_2337_);
v___x_2340_ = l_Lean_Expr_replaceFVars(v___x_2339_, v_discrs_2321_, v_patterns_2322_);
lean_dec_ref(v_patterns_2322_);
lean_dec_ref(v_discrs_2321_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = l_Lean_LocalDecl_userName(v_a_2337_);
v___x_2342_ = l_Lean_LocalDecl_binderInfo(v_a_2337_);
lean_dec(v_a_2337_);
v___x_2343_ = 0;
v___x_2344_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2341_, v___x_2342_, v___x_2340_, v___f_2338_, v___x_2343_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
return v___x_2344_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v_altsNew_2326_);
lean_dec(v_i_2325_);
lean_dec_ref(v_k_2324_);
lean_dec_ref(v_alts_2323_);
lean_dec_ref(v_patterns_2322_);
lean_dec_ref(v_discrs_2321_);
v_a_2345_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2336_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2336_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(lean_object* v_declName_2459_, lean_object* v___y_2460_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg___boxed(lean_object* v_declName_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2466_, v___y_2467_);
lean_dec(v___y_2467_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_declName_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2470_, v___y_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___boxed(lean_object* v_declName_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v_declName_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
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
lean_object* v___f_2491_; lean_object* v___x_14341__overap_2492_; lean_object* v___x_2493_; 
v___f_2491_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14341__overap_2492_ = lean_panic_fn_borrowed(v___f_2491_, v_msg_2485_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v___y_2487_);
lean_inc_ref(v___y_2486_);
v___x_2493_ = lean_apply_5(v___x_14341__overap_2492_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, lean_box(0));
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
lean_object* v_a_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v_a_2685_ = lean_array_uget_borrowed(v_as_2658_, v_i_2660_);
v___x_2686_ = lean_array_fget_borrowed(v_array_2674_, v_start_2675_);
lean_inc(v___x_2686_);
lean_inc(v_a_2685_);
v___x_2687_ = l_Lean_Meta_mkEqHEq(v_a_2685_, v___x_2686_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2689_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v___x_2689_ = l_Lean_mkArrow(v_a_2688_, v_fst_2670_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v___x_2691_ = lean_unsigned_to_nat(1u);
v___x_2692_ = lean_nat_add(v_start_2675_, v___x_2691_);
lean_dec(v_start_2675_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 1, v___x_2692_);
v___x_2694_ = v___x_2683_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_array_2674_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2701_, 2, v_stop_2676_);
v___x_2694_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2696_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2694_);
lean_ctor_set(v___x_2672_, 0, v_a_2690_);
v___x_2696_ = v___x_2672_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2690_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2694_);
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
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_del_object(v___x_2683_);
lean_dec(v_stop_2676_);
lean_dec(v_start_2675_);
lean_dec_ref(v_array_2674_);
lean_del_object(v___x_2672_);
v_a_2702_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2689_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2689_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_del_object(v___x_2683_);
lean_dec(v_stop_2676_);
lean_dec(v_start_2675_);
lean_dec_ref(v_array_2674_);
lean_del_object(v___x_2672_);
lean_dec(v_fst_2670_);
v_a_2710_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2687_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2687_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
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
uint8_t v___x_2746_; 
v___x_2746_ = lean_usize_dec_lt(v_i_2739_, v_sz_2738_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_b_2740_);
return v___x_2747_;
}
else
{
lean_object* v___x_2748_; lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2748_ = l_Lean_instInhabitedExpr;
v_a_2749_ = lean_array_uget_borrowed(v_as_2737_, v_i_2739_);
v___x_2750_ = lean_array_get_borrowed(v___x_2748_, v___x_2735_, v_a_2749_);
lean_inc(v___x_2750_);
v___x_2751_ = l_Lean_Meta_instantiateForall(v___x_2750_, v___x_2736_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v___x_2751_, 1);
v___x_2753_ = lean_array_get_size(v___x_2736_);
v___x_2754_ = l_Lean_Meta_Match_simpH_x3f(v_a_2752_, v___x_2753_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v_a_2757_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v___x_2754_, 1);
if (lean_obj_tag(v_a_2755_) == 1)
{
lean_object* v_val_2761_; lean_object* v___x_2762_; 
v_val_2761_ = lean_ctor_get(v_a_2755_, 0);
lean_inc(v_val_2761_);
lean_dec_ref_known(v_a_2755_, 1);
v___x_2762_ = lean_array_push(v_b_2740_, v_val_2761_);
v_a_2757_ = v___x_2762_;
goto v___jp_2756_;
}
else
{
lean_dec(v_a_2755_);
v_a_2757_ = v_b_2740_;
goto v___jp_2756_;
}
v___jp_2756_:
{
size_t v___x_2758_; size_t v___x_2759_; 
v___x_2758_ = ((size_t)1ULL);
v___x_2759_ = lean_usize_add(v_i_2739_, v___x_2758_);
v_i_2739_ = v___x_2759_;
v_b_2740_ = v_a_2757_;
goto _start;
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v_b_2740_);
v_a_2763_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2754_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2754_);
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
v_a_2771_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2751_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2751_);
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
uint8_t v___x_18428__boxed_2935_; uint8_t v___x_18429__boxed_2936_; uint8_t v___x_18430__boxed_2937_; lean_object* v_res_2938_; 
v___x_18428__boxed_2935_ = lean_unbox(v___x_2918_);
v___x_18429__boxed_2936_ = lean_unbox(v___x_2919_);
v___x_18430__boxed_2937_ = lean_unbox(v___x_2920_);
v_res_2938_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2907_, v_a_2908_, v_a_2909_, v___x_2910_, v___x_2911_, v___x_2912_, v___x_2913_, v___x_2914_, v_rhsArgs_2915_, v_a_2916_, v_ys_2917_, v___x_18428__boxed_2935_, v___x_18429__boxed_2936_, v___x_18430__boxed_2937_, v_matchDeclName_2921_, v___x_2922_, v___x_2923_, v___x_2924_, v___x_2925_, v___x_2926_, v_argMask_2927_, v_a_2928_, v_alts_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
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
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; size_t v_sz_3002_; lean_object* v___x_3003_; 
v___x_2995_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2983_);
v___x_2996_ = l_Array_reverse___redArg(v___x_2983_);
v___x_2997_ = lean_array_get_size(v___x_2996_);
lean_inc(v___x_2955_);
v___x_2998_ = l_Array_toSubarray___redArg(v___x_2996_, v___x_2955_, v___x_2997_);
lean_inc_ref(v___x_2956_);
v___x_2999_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2956_, v___x_2954_);
v___x_3000_ = l_Array_reverse___redArg(v___x_2999_);
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2995_);
lean_ctor_set(v___x_3001_, 1, v___x_2998_);
v_sz_3002_ = lean_array_size(v___x_3000_);
v___x_3003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3000_, v_sz_3002_, v___x_2986_, v___x_3001_, v___y_2993_, v___y_2992_, v___y_2990_, v___y_2991_);
lean_dec_ref(v___x_3000_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v_fst_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; uint8_t v___x_3009_; lean_object* v___x_3010_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v_fst_3005_ = lean_ctor_get(v_a_3004_, 0);
lean_inc(v_fst_3005_);
lean_dec(v_a_3004_);
v___x_3006_ = l_Subarray_copy___redArg(v___x_2956_);
lean_inc_ref(v___x_3006_);
v___x_3007_ = l_Array_append___redArg(v___x_3006_, v_ys_2969_);
v___x_3008_ = 0;
v___x_3009_ = 1;
v___x_3010_ = l_Lean_Meta_mkForallFVars(v___x_3007_, v_fst_3005_, v___x_3008_, v___x_2957_, v___x_2957_, v___x_3009_, v___y_2993_, v___y_2992_, v___y_2990_, v___y_2991_);
lean_dec_ref(v___x_3007_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___f_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3012_ = lean_array_get_size(v_ys_2969_);
v___x_3013_ = lean_array_get_size(v_a_2988_);
v___x_3014_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
lean_ctor_set_uint8(v___x_3014_, sizeof(void*)*2, v___y_2994_);
v___x_3015_ = lean_box(v___x_3008_);
v___x_3016_ = lean_box(v___x_2957_);
v___x_3017_ = lean_box(v___x_3009_);
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
lean_closure_set(v___f_3018_, 19, v___x_3014_);
lean_closure_set(v___f_3018_, 20, v_argMask_2972_);
lean_closure_set(v___f_3018_, 21, v_a_3011_);
v___x_3019_ = l_Subarray_copy___redArg(v___x_2967_);
v___x_3020_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2968_, v___x_3006_, v___x_2983_, v___x_3019_, v___f_3018_, v___y_2993_, v___y_2992_, v___y_2990_, v___y_2991_);
return v___x_3020_;
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref(v___x_3006_);
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
v_a_3021_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3010_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3010_);
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
v_a_3029_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3003_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3003_);
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
v___y_2991_ = v___y_3041_;
v___y_2992_ = v___y_3039_;
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
v___y_2991_ = v___y_3041_;
v___y_2992_ = v___y_3039_;
v___y_2993_ = v___y_3038_;
v___y_2994_ = v___x_3045_;
goto v___jp_2989_;
}
else
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_nat_dec_eq(v___x_2968_, v___x_2955_);
v___y_2990_ = v___y_3040_;
v___y_2991_ = v___y_3041_;
v___y_2992_ = v___y_3039_;
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
uint8_t v___x_18696__boxed_3106_; lean_object* v_res_3107_; 
v___x_18696__boxed_3106_ = lean_unbox(v___x_3084_);
v_res_3107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3077_, v_overlaps_3078_, v_a_3079_, v_fst_3080_, v___x_3081_, v___x_3082_, v___x_3083_, v___x_18696__boxed_3106_, v___x_3085_, v_a_3086_, v___x_3087_, v___x_3088_, v___x_3089_, v_matchDeclName_3090_, v___x_3091_, v___x_3092_, v___x_3093_, v___x_3094_, v___x_3095_, v_ys_3096_, v___eqs_3097_, v_rhsArgs_3098_, v_argMask_3099_, v_altResultType_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
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
v___x_3297_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3261_, v___y_3296_, v___y_3295_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_dec_ref_known(v___x_3297_, 1);
v___y_3288_ = v___y_3293_;
v___y_3289_ = v___y_3294_;
goto v___jp_3287_;
}
else
{
lean_dec_ref(v___y_3294_);
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
lean_inc(v_start_3307_);
v_stop_3308_ = lean_ctor_get(v___x_3306_, 2);
lean_inc(v_stop_3308_);
v___x_3309_ = lean_unsigned_to_nat(1u);
v___x_3310_ = lean_nat_add(v_numParams_3262_, v___x_3309_);
v___x_3311_ = lean_nat_add(v___x_3310_, v_numDiscrs_3265_);
v___x_3312_ = lean_nat_sub(v_stop_3308_, v_start_3307_);
lean_dec(v_start_3307_);
lean_dec(v_stop_3308_);
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
v___y_3294_ = v___x_3325_;
v___y_3295_ = v___f_3274_;
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
v___y_3294_ = v___x_3325_;
v___y_3295_ = v___f_3274_;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
if (lean_obj_tag(v_a_3387_) == 0)
{
lean_object* v___x_3389_; 
v___x_3389_ = l_List_reverse___redArg(v_a_3388_);
return v___x_3389_;
}
else
{
lean_object* v_head_3390_; lean_object* v_tail_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3400_; 
v_head_3390_ = lean_ctor_get(v_a_3387_, 0);
v_tail_3391_ = lean_ctor_get(v_a_3387_, 1);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_a_3387_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3393_ = v_a_3387_;
v_isShared_3394_ = v_isSharedCheck_3400_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_tail_3391_);
lean_inc(v_head_3390_);
lean_dec(v_a_3387_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3400_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; lean_object* v___x_3397_; 
v___x_3395_ = l_Lean_mkLevelParam(v_head_3390_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 1, v_a_3388_);
lean_ctor_set(v___x_3393_, 0, v___x_3395_);
v___x_3397_ = v___x_3393_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3395_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_a_3388_);
v___x_3397_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
v_a_3387_ = v_tail_3391_;
v_a_3388_ = v___x_3397_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3401_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
return v___x_3403_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3404_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3405_ = lean_unsigned_to_nat(0u);
v___x_3406_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
lean_ctor_set(v___x_3406_, 2, v___x_3405_);
lean_ctor_set(v___x_3406_, 3, v___x_3405_);
lean_ctor_set(v___x_3406_, 4, v___x_3404_);
lean_ctor_set(v___x_3406_, 5, v___x_3404_);
lean_ctor_set(v___x_3406_, 6, v___x_3404_);
lean_ctor_set(v___x_3406_, 7, v___x_3404_);
lean_ctor_set(v___x_3406_, 8, v___x_3404_);
lean_ctor_set(v___x_3406_, 9, v___x_3404_);
lean_ctor_set(v___x_3406_, 10, v___x_3404_);
return v___x_3406_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3407_ = lean_box(1);
v___x_3408_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3409_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
lean_ctor_set(v___x_3410_, 1, v___x_3408_);
lean_ctor_set(v___x_3410_, 2, v___x_3407_);
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_3413_ = l_Lean_stringToMessageData(v___x_3412_);
return v___x_3413_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_3416_ = l_Lean_stringToMessageData(v___x_3415_);
return v___x_3416_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_3419_ = l_Lean_stringToMessageData(v___x_3418_);
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_3422_ = l_Lean_stringToMessageData(v___x_3421_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_3425_ = l_Lean_stringToMessageData(v___x_3424_);
return v___x_3425_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3432_, lean_object* v_declHint_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v___x_3436_; lean_object* v_env_3437_; uint8_t v___x_3438_; 
v___x_3436_ = lean_st_ref_get(v___y_3434_);
v_env_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc_ref(v_env_3437_);
lean_dec(v___x_3436_);
v___x_3438_ = l_Lean_Name_isAnonymous(v_declHint_3433_);
if (v___x_3438_ == 0)
{
uint8_t v_isExporting_3439_; 
v_isExporting_3439_ = lean_ctor_get_uint8(v_env_3437_, sizeof(void*)*8);
if (v_isExporting_3439_ == 0)
{
lean_object* v___x_3440_; 
lean_dec_ref(v_env_3437_);
lean_dec(v_declHint_3433_);
v___x_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3440_, 0, v_msg_3432_);
return v___x_3440_;
}
else
{
lean_object* v___x_3441_; uint8_t v___x_3442_; 
lean_inc_ref(v_env_3437_);
v___x_3441_ = l_Lean_Environment_setExporting(v_env_3437_, v___x_3438_);
lean_inc(v_declHint_3433_);
lean_inc_ref(v___x_3441_);
v___x_3442_ = l_Lean_Environment_contains(v___x_3441_, v_declHint_3433_, v_isExporting_3439_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; 
lean_dec_ref(v___x_3441_);
lean_dec_ref(v_env_3437_);
lean_dec(v_declHint_3433_);
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v_msg_3432_);
return v___x_3443_;
}
else
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v_c_3449_; lean_object* v___x_3450_; 
v___x_3444_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3445_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3446_ = l_Lean_Options_empty;
v___x_3447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3441_);
lean_ctor_set(v___x_3447_, 1, v___x_3444_);
lean_ctor_set(v___x_3447_, 2, v___x_3445_);
lean_ctor_set(v___x_3447_, 3, v___x_3446_);
lean_inc(v_declHint_3433_);
v___x_3448_ = l_Lean_MessageData_ofConstName(v_declHint_3433_, v___x_3438_);
v_c_3449_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3449_, 0, v___x_3447_);
lean_ctor_set(v_c_3449_, 1, v___x_3448_);
v___x_3450_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3437_, v_declHint_3433_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_dec_ref(v_env_3437_);
lean_dec(v_declHint_3433_);
v___x_3451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v_c_3449_);
v___x_3453_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_3454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = l_Lean_MessageData_note(v___x_3454_);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v_msg_3432_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
return v___x_3457_;
}
else
{
lean_object* v_val_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3493_; 
v_val_3458_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3460_ = v___x_3450_;
v_isShared_3461_ = v_isSharedCheck_3493_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_val_3458_);
lean_dec(v___x_3450_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3493_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v_mod_3465_; uint8_t v___x_3466_; 
v___x_3462_ = lean_box(0);
v___x_3463_ = l_Lean_Environment_header(v_env_3437_);
lean_dec_ref(v_env_3437_);
v___x_3464_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3463_);
v_mod_3465_ = lean_array_get(v___x_3462_, v___x_3464_, v_val_3458_);
lean_dec(v_val_3458_);
lean_dec_ref(v___x_3464_);
v___x_3466_ = l_Lean_isPrivateName(v_declHint_3433_);
lean_dec(v_declHint_3433_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
lean_ctor_set(v___x_3468_, 1, v_c_3449_);
v___x_3469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = l_Lean_MessageData_ofName(v_mod_3465_);
v___x_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3470_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3472_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = l_Lean_MessageData_note(v___x_3474_);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v_msg_3432_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set_tag(v___x_3460_, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3476_);
v___x_3478_ = v___x_3460_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
else
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3480_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
lean_ctor_set(v___x_3481_, 1, v_c_3449_);
v___x_3482_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = l_Lean_MessageData_ofName(v_mod_3465_);
v___x_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3483_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = l_Lean_MessageData_note(v___x_3487_);
v___x_3489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3489_, 0, v_msg_3432_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set_tag(v___x_3460_, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3489_);
v___x_3491_ = v___x_3460_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3494_; 
lean_dec_ref(v_env_3437_);
lean_dec(v_declHint_3433_);
v___x_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3494_, 0, v_msg_3432_);
return v___x_3494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3495_, lean_object* v_declHint_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3495_, v_declHint_3496_, v___y_3497_);
lean_dec(v___y_3497_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3500_, lean_object* v_declHint_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v___x_3507_; lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3517_; 
v___x_3507_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3500_, v_declHint_3501_, v___y_3505_);
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3517_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3517_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3512_ = l_Lean_unknownIdentifierMessageTag;
v___x_3513_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
lean_ctor_set(v___x_3513_, 1, v_a_3508_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3513_);
v___x_3515_ = v___x_3510_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3518_, lean_object* v_declHint_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3518_, v_declHint_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3526_, lean_object* v_msg_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v_toCold_3533_; lean_object* v_currRecDepth_3534_; lean_object* v_ref_3535_; uint8_t v_diag_3536_; uint8_t v_suppressElabErrors_3537_; lean_object* v_ref_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v_toCold_3533_ = lean_ctor_get(v___y_3530_, 0);
v_currRecDepth_3534_ = lean_ctor_get(v___y_3530_, 1);
v_ref_3535_ = lean_ctor_get(v___y_3530_, 2);
v_diag_3536_ = lean_ctor_get_uint8(v___y_3530_, sizeof(void*)*3);
v_suppressElabErrors_3537_ = lean_ctor_get_uint8(v___y_3530_, sizeof(void*)*3 + 1);
v_ref_3538_ = l_Lean_replaceRef(v_ref_3526_, v_ref_3535_);
lean_inc(v_currRecDepth_3534_);
lean_inc_ref(v_toCold_3533_);
v___x_3539_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3539_, 0, v_toCold_3533_);
lean_ctor_set(v___x_3539_, 1, v_currRecDepth_3534_);
lean_ctor_set(v___x_3539_, 2, v_ref_3538_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*3, v_diag_3536_);
lean_ctor_set_uint8(v___x_3539_, sizeof(void*)*3 + 1, v_suppressElabErrors_3537_);
v___x_3540_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3527_, v___y_3528_, v___y_3529_, v___x_3539_, v___y_3531_);
lean_dec_ref_known(v___x_3539_, 3);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3541_, lean_object* v_msg_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3541_, v_msg_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v_ref_3541_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3549_, lean_object* v_msg_3550_, lean_object* v_declHint_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v___x_3557_; lean_object* v_a_3558_; lean_object* v___x_3559_; 
v___x_3557_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3550_, v_declHint_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref(v___x_3557_);
v___x_3559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3549_, v_a_3558_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3560_, lean_object* v_msg_3561_, lean_object* v_declHint_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3560_, v_msg_3561_, v_declHint_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v_ref_3560_);
return v_res_3568_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3571_ = l_Lean_stringToMessageData(v___x_3570_);
return v___x_3571_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3574_ = l_Lean_stringToMessageData(v___x_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3575_, lean_object* v_constName_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v___x_3582_; uint8_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3582_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3583_ = 0;
lean_inc(v_constName_3576_);
v___x_3584_ = l_Lean_MessageData_ofConstName(v_constName_3576_, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3582_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3585_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
v___x_3588_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3575_, v___x_3587_, v_constName_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3589_, lean_object* v_constName_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3589_, v_constName_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v_ref_3589_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v_ref_3603_; lean_object* v___x_3604_; 
v_ref_3603_ = lean_ctor_get(v___y_3600_, 2);
v___x_3604_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3603_, v_constName_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v_env_3619_; uint8_t v___x_3620_; lean_object* v___x_3621_; 
v___x_3618_ = lean_st_ref_get(v___y_3616_);
v_env_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc_ref(v_env_3619_);
lean_dec(v___x_3618_);
v___x_3620_ = 0;
lean_inc(v_constName_3612_);
v___x_3621_ = l_Lean_Environment_find_x3f(v_env_3619_, v_constName_3612_, v___x_3620_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
return v___x_3622_;
}
else
{
lean_object* v_val_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v_constName_3612_);
v_val_3623_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3621_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_val_3623_);
lean_dec(v___x_3621_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set_tag(v___x_3625_, 0);
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_val_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3637_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3640_ = l_Lean_stringToMessageData(v___x_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3641_, lean_object* v_baseName_3642_, lean_object* v_splitterName_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v___x_3649_; uint8_t v_foApprox_3650_; uint8_t v_ctxApprox_3651_; uint8_t v_quasiPatternApprox_3652_; uint8_t v_constApprox_3653_; uint8_t v_isDefEqStuckEx_3654_; uint8_t v_unificationHints_3655_; uint8_t v_proofIrrelevance_3656_; uint8_t v_assignSyntheticOpaque_3657_; uint8_t v_offsetCnstrs_3658_; uint8_t v_transparency_3659_; uint8_t v_univApprox_3660_; uint8_t v_iota_3661_; uint8_t v_beta_3662_; uint8_t v_proj_3663_; uint8_t v_zeta_3664_; uint8_t v_zetaDelta_3665_; uint8_t v_zetaUnused_3666_; uint8_t v_zetaHave_3667_; uint8_t v_canUnfoldPredicateConfig_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3731_; 
v___x_3649_ = l_Lean_Meta_Context_config(v_a_3644_);
v_foApprox_3650_ = lean_ctor_get_uint8(v___x_3649_, 0);
v_ctxApprox_3651_ = lean_ctor_get_uint8(v___x_3649_, 1);
v_quasiPatternApprox_3652_ = lean_ctor_get_uint8(v___x_3649_, 2);
v_constApprox_3653_ = lean_ctor_get_uint8(v___x_3649_, 3);
v_isDefEqStuckEx_3654_ = lean_ctor_get_uint8(v___x_3649_, 4);
v_unificationHints_3655_ = lean_ctor_get_uint8(v___x_3649_, 5);
v_proofIrrelevance_3656_ = lean_ctor_get_uint8(v___x_3649_, 6);
v_assignSyntheticOpaque_3657_ = lean_ctor_get_uint8(v___x_3649_, 7);
v_offsetCnstrs_3658_ = lean_ctor_get_uint8(v___x_3649_, 8);
v_transparency_3659_ = lean_ctor_get_uint8(v___x_3649_, 9);
v_univApprox_3660_ = lean_ctor_get_uint8(v___x_3649_, 11);
v_iota_3661_ = lean_ctor_get_uint8(v___x_3649_, 12);
v_beta_3662_ = lean_ctor_get_uint8(v___x_3649_, 13);
v_proj_3663_ = lean_ctor_get_uint8(v___x_3649_, 14);
v_zeta_3664_ = lean_ctor_get_uint8(v___x_3649_, 15);
v_zetaDelta_3665_ = lean_ctor_get_uint8(v___x_3649_, 16);
v_zetaUnused_3666_ = lean_ctor_get_uint8(v___x_3649_, 17);
v_zetaHave_3667_ = lean_ctor_get_uint8(v___x_3649_, 18);
v_canUnfoldPredicateConfig_3668_ = lean_ctor_get_uint8(v___x_3649_, 19);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3670_ = v___x_3649_;
v_isShared_3671_ = v_isSharedCheck_3731_;
goto v_resetjp_3669_;
}
else
{
lean_dec(v___x_3649_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3731_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
uint8_t v_trackZetaDelta_3672_; lean_object* v_zetaDeltaSet_3673_; lean_object* v_lctx_3674_; lean_object* v_localInstances_3675_; lean_object* v_defEqCtx_x3f_3676_; lean_object* v_synthPendingDepth_3677_; lean_object* v_customCanUnfoldPredicate_x3f_3678_; uint8_t v_univApprox_3679_; uint8_t v_inTypeClassResolution_3680_; uint8_t v_cacheInferType_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3729_; 
v_trackZetaDelta_3672_ = lean_ctor_get_uint8(v_a_3644_, sizeof(void*)*7);
v_zetaDeltaSet_3673_ = lean_ctor_get(v_a_3644_, 1);
v_lctx_3674_ = lean_ctor_get(v_a_3644_, 2);
v_localInstances_3675_ = lean_ctor_get(v_a_3644_, 3);
v_defEqCtx_x3f_3676_ = lean_ctor_get(v_a_3644_, 4);
v_synthPendingDepth_3677_ = lean_ctor_get(v_a_3644_, 5);
v_customCanUnfoldPredicate_x3f_3678_ = lean_ctor_get(v_a_3644_, 6);
v_univApprox_3679_ = lean_ctor_get_uint8(v_a_3644_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3680_ = lean_ctor_get_uint8(v_a_3644_, sizeof(void*)*7 + 2);
v_cacheInferType_3681_ = lean_ctor_get_uint8(v_a_3644_, sizeof(void*)*7 + 3);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_a_3644_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v_a_3644_, 0);
lean_dec(v_unused_3730_);
v___x_3683_ = v_a_3644_;
v_isShared_3684_ = v_isSharedCheck_3729_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3678_);
lean_inc(v_synthPendingDepth_3677_);
lean_inc(v_defEqCtx_x3f_3676_);
lean_inc(v_localInstances_3675_);
lean_inc(v_lctx_3674_);
lean_inc(v_zetaDeltaSet_3673_);
lean_dec(v_a_3644_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3729_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
uint8_t v___x_3685_; lean_object* v___x_3687_; 
v___x_3685_ = 2;
if (v_isShared_3671_ == 0)
{
v___x_3687_ = v___x_3670_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 0, v_foApprox_3650_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 1, v_ctxApprox_3651_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 2, v_quasiPatternApprox_3652_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 3, v_constApprox_3653_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 4, v_isDefEqStuckEx_3654_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 5, v_unificationHints_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 6, v_proofIrrelevance_3656_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 7, v_assignSyntheticOpaque_3657_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 8, v_offsetCnstrs_3658_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 9, v_transparency_3659_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 11, v_univApprox_3660_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 12, v_iota_3661_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 13, v_beta_3662_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 14, v_proj_3663_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 15, v_zeta_3664_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 16, v_zetaDelta_3665_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 17, v_zetaUnused_3666_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 18, v_zetaHave_3667_);
lean_ctor_set_uint8(v_reuseFailAlloc_3728_, 19, v_canUnfoldPredicateConfig_3668_);
v___x_3687_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
uint64_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3691_; 
lean_ctor_set_uint8(v___x_3687_, 10, v___x_3685_);
v___x_3688_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3687_);
v___x_3689_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3689_, 0, v___x_3687_);
lean_ctor_set_uint64(v___x_3689_, sizeof(void*)*1, v___x_3688_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v___x_3689_);
v___x_3691_ = v___x_3683_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_zetaDeltaSet_3673_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_lctx_3674_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_localInstances_3675_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v_defEqCtx_x3f_3676_);
lean_ctor_set(v_reuseFailAlloc_3727_, 5, v_synthPendingDepth_3677_);
lean_ctor_set(v_reuseFailAlloc_3727_, 6, v_customCanUnfoldPredicate_x3f_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, sizeof(void*)*7, v_trackZetaDelta_3672_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, sizeof(void*)*7 + 1, v_univApprox_3679_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3727_, sizeof(void*)*7 + 3, v_cacheInferType_3681_);
v___x_3691_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3692_; 
lean_inc(v_matchDeclName_3641_);
v___x_3692_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3641_, v___x_3691_, v_a_3645_, v_a_3646_, v_a_3647_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3694_; lean_object* v_a_3695_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
lean_inc(v_matchDeclName_3641_);
v___x_3694_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_3641_, v_a_3647_);
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref(v___x_3694_);
if (lean_obj_tag(v_a_3695_) == 1)
{
lean_object* v_val_3696_; lean_object* v_numParams_3697_; lean_object* v_numDiscrs_3698_; lean_object* v_altInfos_3699_; lean_object* v_uElimPos_x3f_3700_; lean_object* v_discrInfos_3701_; lean_object* v_overlaps_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___f_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___f_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; 
v_val_3696_ = lean_ctor_get(v_a_3695_, 0);
lean_inc(v_val_3696_);
lean_dec_ref_known(v_a_3695_, 1);
v_numParams_3697_ = lean_ctor_get(v_val_3696_, 0);
lean_inc(v_numParams_3697_);
v_numDiscrs_3698_ = lean_ctor_get(v_val_3696_, 1);
lean_inc(v_numDiscrs_3698_);
v_altInfos_3699_ = lean_ctor_get(v_val_3696_, 2);
lean_inc_ref(v_altInfos_3699_);
v_uElimPos_x3f_3700_ = lean_ctor_get(v_val_3696_, 3);
lean_inc(v_uElimPos_x3f_3700_);
v_discrInfos_3701_ = lean_ctor_get(v_val_3696_, 4);
lean_inc_ref(v_discrInfos_3701_);
v_overlaps_3702_ = lean_ctor_get(v_val_3696_, 5);
lean_inc_ref_n(v_overlaps_3702_, 2);
v___x_3703_ = l_Lean_instInhabitedExpr;
v___x_3704_ = l_Lean_ConstantInfo_levelParams(v_a_3693_);
v___x_3705_ = lean_box(0);
lean_inc(v___x_3704_);
v___x_3706_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_3704_, v___x_3705_);
lean_inc(v_splitterName_3643_);
v___f_3707_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3707_, 0, v_overlaps_3702_);
lean_closure_set(v___f_3707_, 1, v_splitterName_3643_);
v___x_3708_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3701_);
v___x_3709_ = l_Lean_ConstantInfo_type(v_a_3693_);
lean_inc_ref(v___x_3709_);
v___f_3710_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3710_, 0, v_splitterName_3643_);
lean_closure_set(v___f_3710_, 1, v_matchDeclName_3641_);
lean_closure_set(v___f_3710_, 2, v_numParams_3697_);
lean_closure_set(v___f_3710_, 3, v_val_3696_);
lean_closure_set(v___f_3710_, 4, v___x_3703_);
lean_closure_set(v___f_3710_, 5, v_numDiscrs_3698_);
lean_closure_set(v___f_3710_, 6, v_baseName_3642_);
lean_closure_set(v___f_3710_, 7, v_a_3693_);
lean_closure_set(v___f_3710_, 8, v___x_3706_);
lean_closure_set(v___f_3710_, 9, v___x_3704_);
lean_closure_set(v___f_3710_, 10, v___x_3708_);
lean_closure_set(v___f_3710_, 11, v_uElimPos_x3f_3700_);
lean_closure_set(v___f_3710_, 12, v_discrInfos_3701_);
lean_closure_set(v___f_3710_, 13, v_overlaps_3702_);
lean_closure_set(v___f_3710_, 14, v___f_3707_);
lean_closure_set(v___f_3710_, 15, v___x_3709_);
lean_closure_set(v___f_3710_, 16, v_altInfos_3699_);
v___x_3711_ = 0;
v___x_3712_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3709_, v___f_3710_, v___x_3711_, v___x_3711_, v___x_3691_, v_a_3645_, v_a_3646_, v_a_3647_);
lean_dec_ref(v___x_3691_);
return v___x_3712_;
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
lean_dec(v_a_3695_);
lean_dec(v_a_3693_);
lean_dec(v_splitterName_3643_);
lean_dec(v_baseName_3642_);
v___x_3713_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3714_ = l_Lean_MessageData_ofName(v_matchDeclName_3641_);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3717_, v___x_3691_, v_a_3645_, v_a_3646_, v_a_3647_);
lean_dec_ref(v___x_3691_);
return v___x_3718_;
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_dec_ref(v___x_3691_);
lean_dec(v_splitterName_3643_);
lean_dec(v_baseName_3642_);
lean_dec(v_matchDeclName_3641_);
v_a_3719_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3692_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3692_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3732_, lean_object* v_baseName_3733_, lean_object* v_splitterName_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3732_, v_baseName_3733_, v_splitterName_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
lean_dec(v_a_3736_);
return v_res_3740_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3741_, lean_object* v_ys_3742_, lean_object* v_hsz_3743_, lean_object* v_x_3744_, lean_object* v_x_3745_){
_start:
{
uint8_t v___x_3746_; 
v___x_3746_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3741_, v_ys_3742_, v_x_3744_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3747_, lean_object* v_ys_3748_, lean_object* v_hsz_3749_, lean_object* v_x_3750_, lean_object* v_x_3751_){
_start:
{
uint8_t v_res_3752_; lean_object* v_r_3753_; 
v_res_3752_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3747_, v_ys_3748_, v_hsz_3749_, v_x_3750_, v_x_3751_);
lean_dec_ref(v_ys_3748_);
lean_dec_ref(v_xs_3747_);
v_r_3753_ = lean_box(v_res_3752_);
return v_r_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3754_, lean_object* v_R_3755_, lean_object* v_a_3756_, lean_object* v_b_3757_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3756_, v_b_3757_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3759_, lean_object* v_val_3760_, lean_object* v_baseName_3761_, lean_object* v___x_3762_, lean_object* v_a_3763_, lean_object* v___x_3764_, lean_object* v___x_3765_, lean_object* v___x_3766_, lean_object* v_matchDeclName_3767_, lean_object* v___x_3768_, lean_object* v___x_3769_, lean_object* v___x_3770_, lean_object* v_inst_3771_, lean_object* v_R_3772_, lean_object* v_a_3773_, lean_object* v_b_3774_, lean_object* v_c_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3759_, v_val_3760_, v_baseName_3761_, v___x_3762_, v_a_3763_, v___x_3764_, v___x_3765_, v___x_3766_, v_matchDeclName_3767_, v___x_3768_, v___x_3769_, v___x_3770_, v_a_3773_, v_b_3774_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3782_ = _args[0];
lean_object* v_val_3783_ = _args[1];
lean_object* v_baseName_3784_ = _args[2];
lean_object* v___x_3785_ = _args[3];
lean_object* v_a_3786_ = _args[4];
lean_object* v___x_3787_ = _args[5];
lean_object* v___x_3788_ = _args[6];
lean_object* v___x_3789_ = _args[7];
lean_object* v_matchDeclName_3790_ = _args[8];
lean_object* v___x_3791_ = _args[9];
lean_object* v___x_3792_ = _args[10];
lean_object* v___x_3793_ = _args[11];
lean_object* v_inst_3794_ = _args[12];
lean_object* v_R_3795_ = _args[13];
lean_object* v_a_3796_ = _args[14];
lean_object* v_b_3797_ = _args[15];
lean_object* v_c_3798_ = _args[16];
lean_object* v___y_3799_ = _args[17];
lean_object* v___y_3800_ = _args[18];
lean_object* v___y_3801_ = _args[19];
lean_object* v___y_3802_ = _args[20];
lean_object* v___y_3803_ = _args[21];
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3782_, v_val_3783_, v_baseName_3784_, v___x_3785_, v_a_3786_, v___x_3787_, v___x_3788_, v___x_3789_, v_matchDeclName_3790_, v___x_3791_, v___x_3792_, v___x_3793_, v_inst_3794_, v_R_3795_, v_a_3796_, v_b_3797_, v_c_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v_upperBound_3782_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3805_, lean_object* v_constName_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3813_, lean_object* v_constName_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3813_, v_constName_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3821_, lean_object* v_ref_3822_, lean_object* v_constName_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3822_, v_constName_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3830_, lean_object* v_ref_3831_, lean_object* v_constName_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3830_, v_ref_3831_, v_constName_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v_ref_3831_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3839_, lean_object* v_ref_3840_, lean_object* v_msg_3841_, lean_object* v_declHint_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3840_, v_msg_3841_, v_declHint_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3849_, lean_object* v_ref_3850_, lean_object* v_msg_3851_, lean_object* v_declHint_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3849_, v_ref_3850_, v_msg_3851_, v_declHint_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v_ref_3850_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3859_, lean_object* v_declHint_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3859_, v_declHint_3860_, v___y_3864_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3867_, lean_object* v_declHint_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3867_, v_declHint_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3875_, lean_object* v_ref_3876_, lean_object* v_msg_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3876_, v_msg_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3884_, lean_object* v_ref_3885_, lean_object* v_msg_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3884_, v_ref_3885_, v_msg_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v_ref_3885_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3893_, lean_object* v_vals_3894_, lean_object* v_i_3895_, lean_object* v_k_3896_){
_start:
{
lean_object* v___x_3897_; uint8_t v___x_3898_; 
v___x_3897_ = lean_array_get_size(v_keys_3893_);
v___x_3898_ = lean_nat_dec_lt(v_i_3895_, v___x_3897_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; 
lean_dec(v_i_3895_);
v___x_3899_ = lean_box(0);
return v___x_3899_;
}
else
{
lean_object* v_k_x27_3900_; uint8_t v___x_3901_; 
v_k_x27_3900_ = lean_array_fget_borrowed(v_keys_3893_, v_i_3895_);
v___x_3901_ = lean_name_eq(v_k_3896_, v_k_x27_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_unsigned_to_nat(1u);
v___x_3903_ = lean_nat_add(v_i_3895_, v___x_3902_);
lean_dec(v_i_3895_);
v_i_3895_ = v___x_3903_;
goto _start;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = lean_array_fget_borrowed(v_vals_3894_, v_i_3895_);
lean_dec(v_i_3895_);
lean_inc(v___x_3905_);
v___x_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
return v___x_3906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3907_, lean_object* v_vals_3908_, lean_object* v_i_3909_, lean_object* v_k_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3907_, v_vals_3908_, v_i_3909_, v_k_3910_);
lean_dec(v_k_3910_);
lean_dec_ref(v_vals_3908_);
lean_dec_ref(v_keys_3907_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3912_, size_t v_x_3913_, lean_object* v_x_3914_){
_start:
{
if (lean_obj_tag(v_x_3912_) == 0)
{
lean_object* v_es_3915_; lean_object* v___x_3916_; size_t v___x_3917_; size_t v___x_3918_; lean_object* v_j_3919_; lean_object* v___x_3920_; 
v_es_3915_ = lean_ctor_get(v_x_3912_, 0);
v___x_3916_ = lean_box(2);
v___x_3917_ = ((size_t)31ULL);
v___x_3918_ = lean_usize_land(v_x_3913_, v___x_3917_);
v_j_3919_ = lean_usize_to_nat(v___x_3918_);
v___x_3920_ = lean_array_get_borrowed(v___x_3916_, v_es_3915_, v_j_3919_);
lean_dec(v_j_3919_);
switch(lean_obj_tag(v___x_3920_))
{
case 0:
{
lean_object* v_key_3921_; lean_object* v_val_3922_; uint8_t v___x_3923_; 
v_key_3921_ = lean_ctor_get(v___x_3920_, 0);
v_val_3922_ = lean_ctor_get(v___x_3920_, 1);
v___x_3923_ = lean_name_eq(v_x_3914_, v_key_3921_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; 
v___x_3924_ = lean_box(0);
return v___x_3924_;
}
else
{
lean_object* v___x_3925_; 
lean_inc(v_val_3922_);
v___x_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3925_, 0, v_val_3922_);
return v___x_3925_;
}
}
case 1:
{
lean_object* v_node_3926_; size_t v___x_3927_; size_t v___x_3928_; 
v_node_3926_ = lean_ctor_get(v___x_3920_, 0);
v___x_3927_ = ((size_t)5ULL);
v___x_3928_ = lean_usize_shift_right(v_x_3913_, v___x_3927_);
v_x_3912_ = v_node_3926_;
v_x_3913_ = v___x_3928_;
goto _start;
}
default: 
{
lean_object* v___x_3930_; 
v___x_3930_ = lean_box(0);
return v___x_3930_;
}
}
}
else
{
lean_object* v_ks_3931_; lean_object* v_vs_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v_ks_3931_ = lean_ctor_get(v_x_3912_, 0);
v_vs_3932_ = lean_ctor_get(v_x_3912_, 1);
v___x_3933_ = lean_unsigned_to_nat(0u);
v___x_3934_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3931_, v_vs_3932_, v___x_3933_, v_x_3914_);
return v___x_3934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3935_, lean_object* v_x_3936_, lean_object* v_x_3937_){
_start:
{
size_t v_x_700__boxed_3938_; lean_object* v_res_3939_; 
v_x_700__boxed_3938_ = lean_unbox_usize(v_x_3936_);
lean_dec(v_x_3936_);
v_res_3939_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3935_, v_x_700__boxed_3938_, v_x_3937_);
lean_dec(v_x_3937_);
lean_dec_ref(v_x_3935_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3940_, lean_object* v_x_3941_){
_start:
{
uint64_t v___y_3943_; 
if (lean_obj_tag(v_x_3941_) == 0)
{
uint64_t v___x_3946_; 
v___x_3946_ = 1723ULL;
v___y_3943_ = v___x_3946_;
goto v___jp_3942_;
}
else
{
uint64_t v_hash_3947_; 
v_hash_3947_ = lean_ctor_get_uint64(v_x_3941_, sizeof(void*)*2);
v___y_3943_ = v_hash_3947_;
goto v___jp_3942_;
}
v___jp_3942_:
{
size_t v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = lean_uint64_to_usize(v___y_3943_);
v___x_3945_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3940_, v___x_3944_, v_x_3941_);
return v___x_3945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3948_, lean_object* v_x_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3948_, v_x_3949_);
lean_dec(v_x_3949_);
lean_dec_ref(v_x_3948_);
return v_res_3950_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3957_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3958_ = l_Lean_stringToMessageData(v___x_3957_);
return v___x_3958_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3961_ = l_Lean_stringToMessageData(v___x_3960_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v___x_3968_; lean_object* v_env_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3968_ = lean_st_ref_get(v_a_3966_);
v_env_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc_ref(v_env_3969_);
lean_dec(v___x_3968_);
lean_inc_n(v_matchDeclName_3962_, 3);
v___x_3970_ = l_Lean_mkPrivateName(v_env_3969_, v_matchDeclName_3962_);
lean_dec_ref(v_env_3969_);
v___x_3971_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_3970_);
v___x_3972_ = l_Lean_Name_append(v___x_3970_, v___x_3971_);
lean_inc_n(v___x_3972_, 2);
v___x_3973_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_3973_, 0, v_matchDeclName_3962_);
lean_closure_set(v___x_3973_, 1, v___x_3970_);
lean_closure_set(v___x_3973_, 2, v___x_3972_);
v___x_3974_ = l_Lean_Meta_realizeConst(v_matchDeclName_3962_, v___x_3972_, v___x_3973_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_4003_; 
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4003_ == 0)
{
lean_object* v_unused_4004_; 
v_unused_4004_ = lean_ctor_get(v___x_3974_, 0);
lean_dec(v_unused_4004_);
v___x_3976_ = v___x_3974_;
v_isShared_3977_ = v_isSharedCheck_4003_;
goto v_resetjp_3975_;
}
else
{
lean_dec(v___x_3974_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_4003_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3978_; lean_object* v_env_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v_map_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4001_; 
v___x_3978_ = lean_st_ref_get(v_a_3966_);
v_env_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc_ref(v_env_3979_);
lean_dec(v___x_3978_);
v___x_3980_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_3981_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_3982_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_3983_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3980_, v___x_3981_, v_env_3979_, v___x_3982_, v___x_3972_);
v_map_3984_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4001_ == 0)
{
lean_object* v_unused_4002_; 
v_unused_4002_ = lean_ctor_get(v___x_3983_, 1);
lean_dec(v_unused_4002_);
v___x_3986_ = v___x_3983_;
v_isShared_3987_ = v_isSharedCheck_4001_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_map_3984_);
lean_dec(v___x_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4001_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_3984_, v_matchDeclName_3962_);
lean_dec_ref(v_map_3984_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3992_; 
lean_del_object(v___x_3976_);
v___x_3989_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_3990_ = l_Lean_MessageData_ofName(v_matchDeclName_3962_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set_tag(v___x_3986_, 7);
lean_ctor_set(v___x_3986_, 1, v___x_3990_);
lean_ctor_set(v___x_3986_, 0, v___x_3989_);
v___x_3992_ = v___x_3986_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3989_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3993_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_3994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3992_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3994_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
return v___x_3995_;
}
}
else
{
lean_object* v_val_3997_; lean_object* v___x_3999_; 
lean_del_object(v___x_3986_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_matchDeclName_3962_);
v_val_3997_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_val_3997_);
lean_dec_ref_known(v___x_3988_, 1);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v_val_3997_);
v___x_3999_ = v___x_3976_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_val_3997_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_dec(v___x_3972_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_matchDeclName_3962_);
v_a_4005_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3974_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3974_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = lean_get_match_equations_for(v_matchDeclName_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4020_, lean_object* v_x_4021_, lean_object* v_x_4022_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4021_, v_x_4022_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4024_, lean_object* v_x_4025_, lean_object* v_x_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4024_, v_x_4025_, v_x_4026_);
lean_dec(v_x_4026_);
lean_dec_ref(v_x_4025_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4028_, lean_object* v_x_4029_, size_t v_x_4030_, lean_object* v_x_4031_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4029_, v_x_4030_, v_x_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4033_, lean_object* v_x_4034_, lean_object* v_x_4035_, lean_object* v_x_4036_){
_start:
{
size_t v_x_892__boxed_4037_; lean_object* v_res_4038_; 
v_x_892__boxed_4037_ = lean_unbox_usize(v_x_4035_);
lean_dec(v_x_4035_);
v_res_4038_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4033_, v_x_4034_, v_x_892__boxed_4037_, v_x_4036_);
lean_dec(v_x_4036_);
lean_dec_ref(v_x_4034_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4039_, lean_object* v_keys_4040_, lean_object* v_vals_4041_, lean_object* v_heq_4042_, lean_object* v_i_4043_, lean_object* v_k_4044_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4040_, v_vals_4041_, v_i_4043_, v_k_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4046_, lean_object* v_keys_4047_, lean_object* v_vals_4048_, lean_object* v_heq_4049_, lean_object* v_i_4050_, lean_object* v_k_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4046_, v_keys_4047_, v_vals_4048_, v_heq_4049_, v_i_4050_, v_k_4051_);
lean_dec(v_k_4051_);
lean_dec_ref(v_vals_4048_);
lean_dec_ref(v_keys_4047_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4053_, lean_object* v_k_4054_, uint8_t v_cleanupAnnotations_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v___f_4061_; uint8_t v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___f_4061_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4061_, 0, v_k_4054_);
v___x_4062_ = 0;
v___x_4063_ = lean_box(0);
v___x_4064_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4062_, v___x_4063_, v_type_4053_, v___f_4061_, v_cleanupAnnotations_4055_, v___x_4062_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4064_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4064_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
v_a_4073_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4064_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4064_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4081_, lean_object* v_k_4082_, lean_object* v_cleanupAnnotations_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4089_; lean_object* v_res_4090_; 
v_cleanupAnnotations_boxed_4089_ = lean_unbox(v_cleanupAnnotations_4083_);
v_res_4090_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4081_, v_k_4082_, v_cleanupAnnotations_boxed_4089_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4091_, lean_object* v_type_4092_, lean_object* v_k_4093_, uint8_t v_cleanupAnnotations_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4092_, v_k_4093_, v_cleanupAnnotations_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4101_, lean_object* v_type_4102_, lean_object* v_k_4103_, lean_object* v_cleanupAnnotations_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4110_; lean_object* v_res_4111_; 
v_cleanupAnnotations_boxed_4110_ = lean_unbox(v_cleanupAnnotations_4104_);
v_res_4111_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4101_, v_type_4102_, v_k_4103_, v_cleanupAnnotations_boxed_4110_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_msg_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v___f_4118_; lean_object* v___x_18817__overap_4119_; lean_object* v___x_4120_; 
v___f_4118_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_18817__overap_4119_ = lean_panic_fn_borrowed(v___f_4118_, v_msg_4112_);
lean_inc(v___y_4116_);
lean_inc_ref(v___y_4115_);
lean_inc(v___y_4114_);
lean_inc_ref(v___y_4113_);
v___x_4120_ = lean_apply_5(v___x_18817__overap_4119_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, lean_box(0));
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_msg_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_msg_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4128_){
_start:
{
uint8_t v_foApprox_4129_; uint8_t v_ctxApprox_4130_; uint8_t v_quasiPatternApprox_4131_; uint8_t v_constApprox_4132_; uint8_t v_isDefEqStuckEx_4133_; uint8_t v_unificationHints_4134_; uint8_t v_proofIrrelevance_4135_; uint8_t v_assignSyntheticOpaque_4136_; uint8_t v_offsetCnstrs_4137_; uint8_t v_transparency_4138_; uint8_t v_univApprox_4139_; uint8_t v_iota_4140_; uint8_t v_beta_4141_; uint8_t v_proj_4142_; uint8_t v_zeta_4143_; uint8_t v_zetaDelta_4144_; uint8_t v_zetaUnused_4145_; uint8_t v_zetaHave_4146_; uint8_t v_canUnfoldPredicateConfig_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4155_; 
v_foApprox_4129_ = lean_ctor_get_uint8(v_c_4128_, 0);
v_ctxApprox_4130_ = lean_ctor_get_uint8(v_c_4128_, 1);
v_quasiPatternApprox_4131_ = lean_ctor_get_uint8(v_c_4128_, 2);
v_constApprox_4132_ = lean_ctor_get_uint8(v_c_4128_, 3);
v_isDefEqStuckEx_4133_ = lean_ctor_get_uint8(v_c_4128_, 4);
v_unificationHints_4134_ = lean_ctor_get_uint8(v_c_4128_, 5);
v_proofIrrelevance_4135_ = lean_ctor_get_uint8(v_c_4128_, 6);
v_assignSyntheticOpaque_4136_ = lean_ctor_get_uint8(v_c_4128_, 7);
v_offsetCnstrs_4137_ = lean_ctor_get_uint8(v_c_4128_, 8);
v_transparency_4138_ = lean_ctor_get_uint8(v_c_4128_, 9);
v_univApprox_4139_ = lean_ctor_get_uint8(v_c_4128_, 11);
v_iota_4140_ = lean_ctor_get_uint8(v_c_4128_, 12);
v_beta_4141_ = lean_ctor_get_uint8(v_c_4128_, 13);
v_proj_4142_ = lean_ctor_get_uint8(v_c_4128_, 14);
v_zeta_4143_ = lean_ctor_get_uint8(v_c_4128_, 15);
v_zetaDelta_4144_ = lean_ctor_get_uint8(v_c_4128_, 16);
v_zetaUnused_4145_ = lean_ctor_get_uint8(v_c_4128_, 17);
v_zetaHave_4146_ = lean_ctor_get_uint8(v_c_4128_, 18);
v_canUnfoldPredicateConfig_4147_ = lean_ctor_get_uint8(v_c_4128_, 19);
v_isSharedCheck_4155_ = !lean_is_exclusive(v_c_4128_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4149_ = v_c_4128_;
v_isShared_4150_ = v_isSharedCheck_4155_;
goto v_resetjp_4148_;
}
else
{
lean_dec(v_c_4128_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4155_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
uint8_t v___x_4151_; lean_object* v___x_4153_; 
v___x_4151_ = 2;
if (v_isShared_4150_ == 0)
{
v___x_4153_ = v___x_4149_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 0, v_foApprox_4129_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 1, v_ctxApprox_4130_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 2, v_quasiPatternApprox_4131_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 3, v_constApprox_4132_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 4, v_isDefEqStuckEx_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 5, v_unificationHints_4134_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 6, v_proofIrrelevance_4135_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 7, v_assignSyntheticOpaque_4136_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 8, v_offsetCnstrs_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 9, v_transparency_4138_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 11, v_univApprox_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 12, v_iota_4140_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 13, v_beta_4141_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 14, v_proj_4142_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 15, v_zeta_4143_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 16, v_zetaDelta_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 17, v_zetaUnused_4145_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 18, v_zetaHave_4146_);
lean_ctor_set_uint8(v_reuseFailAlloc_4154_, 19, v_canUnfoldPredicateConfig_4147_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
lean_ctor_set_uint8(v___x_4153_, 10, v___x_4151_);
return v___x_4153_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4156_, lean_object* v_t_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_dummy_4163_; lean_object* v_nargs_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v_dummy_4163_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4164_ = l_Lean_Expr_getAppNumArgs(v_t_4157_);
lean_inc(v_nargs_4164_);
v___x_4165_ = lean_mk_array(v_nargs_4164_, v_dummy_4163_);
v___x_4166_ = lean_unsigned_to_nat(1u);
v___x_4167_ = lean_nat_sub(v_nargs_4164_, v___x_4166_);
lean_dec(v_nargs_4164_);
v___x_4168_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4157_, v___x_4165_, v___x_4167_);
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4170_, lean_object* v_t_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4170_, v_t_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec_ref(v_x_4170_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4178_, lean_object* v_x_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
lean_object* v___x_4185_; 
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v_snd_4178_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4186_, lean_object* v_x_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4186_, v_x_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec_ref(v_x_4187_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4194_, size_t v_i_4195_, lean_object* v_bs_4196_){
_start:
{
uint8_t v___x_4197_; 
v___x_4197_ = lean_usize_dec_lt(v_i_4195_, v_sz_4194_);
if (v___x_4197_ == 0)
{
return v_bs_4196_;
}
else
{
lean_object* v_v_4198_; lean_object* v_fst_4199_; lean_object* v_snd_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4214_; 
v_v_4198_ = lean_array_uget(v_bs_4196_, v_i_4195_);
v_fst_4199_ = lean_ctor_get(v_v_4198_, 0);
v_snd_4200_ = lean_ctor_get(v_v_4198_, 1);
v_isSharedCheck_4214_ = !lean_is_exclusive(v_v_4198_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4202_ = v_v_4198_;
v_isShared_4203_ = v_isSharedCheck_4214_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_snd_4200_);
lean_inc(v_fst_4199_);
lean_dec(v_v_4198_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4214_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4204_; lean_object* v_bs_x27_4205_; lean_object* v___f_4206_; lean_object* v___x_4208_; 
v___x_4204_ = lean_unsigned_to_nat(0u);
v_bs_x27_4205_ = lean_array_uset(v_bs_4196_, v_i_4195_, v___x_4204_);
v___f_4206_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4206_, 0, v_snd_4200_);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 1, v___f_4206_);
v___x_4208_ = v___x_4202_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_fst_4199_);
lean_ctor_set(v_reuseFailAlloc_4213_, 1, v___f_4206_);
v___x_4208_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
size_t v___x_4209_; size_t v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = ((size_t)1ULL);
v___x_4210_ = lean_usize_add(v_i_4195_, v___x_4209_);
v___x_4211_ = lean_array_uset(v_bs_x27_4205_, v_i_4195_, v___x_4208_);
v_i_4195_ = v___x_4210_;
v_bs_4196_ = v___x_4211_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4215_, lean_object* v_i_4216_, lean_object* v_bs_4217_){
_start:
{
size_t v_sz_boxed_4218_; size_t v_i_boxed_4219_; lean_object* v_res_4220_; 
v_sz_boxed_4218_ = lean_unbox_usize(v_sz_4215_);
lean_dec(v_sz_4215_);
v_i_boxed_4219_ = lean_unbox_usize(v_i_4216_);
lean_dec(v_i_4216_);
v_res_4220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4218_, v_i_boxed_4219_, v_bs_4217_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4221_, size_t v_i_4222_, lean_object* v_bs_4223_){
_start:
{
uint8_t v___x_4224_; 
v___x_4224_ = lean_usize_dec_lt(v_i_4222_, v_sz_4221_);
if (v___x_4224_ == 0)
{
return v_bs_4223_;
}
else
{
lean_object* v_v_4225_; lean_object* v_fst_4226_; lean_object* v_snd_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4243_; 
v_v_4225_ = lean_array_uget(v_bs_4223_, v_i_4222_);
v_fst_4226_ = lean_ctor_get(v_v_4225_, 0);
v_snd_4227_ = lean_ctor_get(v_v_4225_, 1);
v_isSharedCheck_4243_ = !lean_is_exclusive(v_v_4225_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4229_ = v_v_4225_;
v_isShared_4230_ = v_isSharedCheck_4243_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_snd_4227_);
lean_inc(v_fst_4226_);
lean_dec(v_v_4225_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4243_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4231_; lean_object* v_bs_x27_4232_; uint8_t v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4236_; 
v___x_4231_ = lean_unsigned_to_nat(0u);
v_bs_x27_4232_ = lean_array_uset(v_bs_4223_, v_i_4222_, v___x_4231_);
v___x_4233_ = 0;
v___x_4234_ = lean_box(v___x_4233_);
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v___x_4234_);
v___x_4236_ = v___x_4229_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4234_);
lean_ctor_set(v_reuseFailAlloc_4242_, 1, v_snd_4227_);
v___x_4236_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
lean_object* v___x_4237_; size_t v___x_4238_; size_t v___x_4239_; lean_object* v___x_4240_; 
v___x_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4237_, 0, v_fst_4226_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
v___x_4238_ = ((size_t)1ULL);
v___x_4239_ = lean_usize_add(v_i_4222_, v___x_4238_);
v___x_4240_ = lean_array_uset(v_bs_x27_4232_, v_i_4222_, v___x_4237_);
v_i_4222_ = v___x_4239_;
v_bs_4223_ = v___x_4240_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4244_, lean_object* v_i_4245_, lean_object* v_bs_4246_){
_start:
{
size_t v_sz_boxed_4247_; size_t v_i_boxed_4248_; lean_object* v_res_4249_; 
v_sz_boxed_4247_ = lean_unbox_usize(v_sz_4244_);
lean_dec(v_sz_4244_);
v_i_boxed_4248_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_res_4249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4247_, v_i_boxed_4248_, v_bs_4246_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4250_, lean_object* v___x_4251_, lean_object* v_a_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v___x_20498__overap_4258_; lean_object* v___x_4259_; 
v___x_20498__overap_4258_ = l_instInhabitedOfMonad___redArg(v___x_4250_, v___x_4251_);
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
lean_inc(v___y_4254_);
lean_inc_ref(v___y_4253_);
v___x_4259_ = lean_apply_5(v___x_20498__overap_4258_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, lean_box(0));
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4260_, lean_object* v___x_4261_, lean_object* v_a_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4260_, v___x_4261_, v_a_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v_a_4262_);
return v_res_4268_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_instMonadEIO(lean_box(0));
return v___x_4269_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4270_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4271_ = l_StateRefT_x27_instMonad___redArg(v___x_4270_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4276_, lean_object* v_declInfos_4277_, lean_object* v_k_4278_, lean_object* v_kind_4279_, lean_object* v_x_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
uint8_t v_kind_boxed_4286_; lean_object* v_res_4287_; 
v_kind_boxed_4286_ = lean_unbox(v_kind_4279_);
v_res_4287_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4276_, v_declInfos_4277_, v_k_4278_, v_kind_boxed_4286_, v_x_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4288_, lean_object* v_k_4289_, uint8_t v_kind_4290_, lean_object* v_acc_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v___x_4297_; lean_object* v_toApplicative_4298_; lean_object* v_toFunctor_4299_; lean_object* v_toSeq_4300_; lean_object* v_toSeqLeft_4301_; lean_object* v_toSeqRight_4302_; lean_object* v___f_4303_; lean_object* v___f_4304_; lean_object* v___f_4305_; lean_object* v___f_4306_; lean_object* v___x_4307_; lean_object* v___f_4308_; lean_object* v___f_4309_; lean_object* v___f_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v_toApplicative_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4364_; 
v___x_4297_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4298_ = lean_ctor_get(v___x_4297_, 0);
v_toFunctor_4299_ = lean_ctor_get(v_toApplicative_4298_, 0);
v_toSeq_4300_ = lean_ctor_get(v_toApplicative_4298_, 2);
v_toSeqLeft_4301_ = lean_ctor_get(v_toApplicative_4298_, 3);
v_toSeqRight_4302_ = lean_ctor_get(v_toApplicative_4298_, 4);
v___f_4303_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4304_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4299_, 2);
v___f_4305_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4305_, 0, v_toFunctor_4299_);
v___f_4306_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4306_, 0, v_toFunctor_4299_);
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___f_4305_);
lean_ctor_set(v___x_4307_, 1, v___f_4306_);
lean_inc(v_toSeqRight_4302_);
v___f_4308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4308_, 0, v_toSeqRight_4302_);
lean_inc(v_toSeqLeft_4301_);
v___f_4309_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4309_, 0, v_toSeqLeft_4301_);
lean_inc(v_toSeq_4300_);
v___f_4310_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4310_, 0, v_toSeq_4300_);
v___x_4311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4307_);
lean_ctor_set(v___x_4311_, 1, v___f_4303_);
lean_ctor_set(v___x_4311_, 2, v___f_4310_);
lean_ctor_set(v___x_4311_, 3, v___f_4309_);
lean_ctor_set(v___x_4311_, 4, v___f_4308_);
v___x_4312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4311_);
lean_ctor_set(v___x_4312_, 1, v___f_4304_);
v___x_4313_ = l_StateRefT_x27_instMonad___redArg(v___x_4312_);
v_toApplicative_4314_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4364_ == 0)
{
lean_object* v_unused_4365_; 
v_unused_4365_ = lean_ctor_get(v___x_4313_, 1);
lean_dec(v_unused_4365_);
v___x_4316_ = v___x_4313_;
v_isShared_4317_ = v_isSharedCheck_4364_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_toApplicative_4314_);
lean_dec(v___x_4313_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4364_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v_toFunctor_4318_; lean_object* v_toSeq_4319_; lean_object* v_toSeqLeft_4320_; lean_object* v_toSeqRight_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4362_; 
v_toFunctor_4318_ = lean_ctor_get(v_toApplicative_4314_, 0);
v_toSeq_4319_ = lean_ctor_get(v_toApplicative_4314_, 2);
v_toSeqLeft_4320_ = lean_ctor_get(v_toApplicative_4314_, 3);
v_toSeqRight_4321_ = lean_ctor_get(v_toApplicative_4314_, 4);
v_isSharedCheck_4362_ = !lean_is_exclusive(v_toApplicative_4314_);
if (v_isSharedCheck_4362_ == 0)
{
lean_object* v_unused_4363_; 
v_unused_4363_ = lean_ctor_get(v_toApplicative_4314_, 1);
lean_dec(v_unused_4363_);
v___x_4323_ = v_toApplicative_4314_;
v_isShared_4324_ = v_isSharedCheck_4362_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_toSeqRight_4321_);
lean_inc(v_toSeqLeft_4320_);
lean_inc(v_toSeq_4319_);
lean_inc(v_toFunctor_4318_);
lean_dec(v_toApplicative_4314_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4362_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___f_4325_; lean_object* v___f_4326_; lean_object* v___f_4327_; lean_object* v___f_4328_; lean_object* v___x_4329_; lean_object* v___f_4330_; lean_object* v___f_4331_; lean_object* v___f_4332_; lean_object* v___x_4334_; 
v___f_4325_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4326_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4318_);
v___f_4327_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4327_, 0, v_toFunctor_4318_);
v___f_4328_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4328_, 0, v_toFunctor_4318_);
v___x_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___f_4327_);
lean_ctor_set(v___x_4329_, 1, v___f_4328_);
v___f_4330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4330_, 0, v_toSeqRight_4321_);
v___f_4331_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4331_, 0, v_toSeqLeft_4320_);
v___f_4332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4332_, 0, v_toSeq_4319_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 4, v___f_4330_);
lean_ctor_set(v___x_4323_, 3, v___f_4331_);
lean_ctor_set(v___x_4323_, 2, v___f_4332_);
lean_ctor_set(v___x_4323_, 1, v___f_4325_);
lean_ctor_set(v___x_4323_, 0, v___x_4329_);
v___x_4334_ = v___x_4323_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4329_);
lean_ctor_set(v_reuseFailAlloc_4361_, 1, v___f_4325_);
lean_ctor_set(v_reuseFailAlloc_4361_, 2, v___f_4332_);
lean_ctor_set(v_reuseFailAlloc_4361_, 3, v___f_4331_);
lean_ctor_set(v_reuseFailAlloc_4361_, 4, v___f_4330_);
v___x_4334_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4336_; 
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 1, v___f_4326_);
lean_ctor_set(v___x_4316_, 0, v___x_4334_);
v___x_4336_ = v___x_4316_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4334_);
lean_ctor_set(v_reuseFailAlloc_4360_, 1, v___f_4326_);
v___x_4336_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4337_ = lean_array_get_size(v_acc_4291_);
v___x_4338_ = lean_array_get_size(v_declInfos_4288_);
v___x_4339_ = lean_nat_dec_lt(v___x_4337_, v___x_4338_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; 
lean_dec_ref(v___x_4336_);
lean_dec_ref(v_declInfos_4288_);
lean_inc(v___y_4295_);
lean_inc_ref(v___y_4294_);
lean_inc(v___y_4293_);
lean_inc_ref(v___y_4292_);
v___x_4340_ = lean_apply_6(v_k_4289_, v_acc_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, lean_box(0));
return v___x_4340_;
}
else
{
lean_object* v___x_4341_; uint8_t v___x_4342_; lean_object* v___x_4343_; lean_object* v___f_4344_; lean_object* v___f_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v_snd_4350_; lean_object* v_fst_4351_; lean_object* v_fst_4352_; lean_object* v_snd_4353_; lean_object* v___x_4354_; 
v___x_4341_ = lean_box(0);
v___x_4342_ = 0;
v___x_4343_ = l_Lean_instInhabitedExpr;
v___f_4344_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4344_, 0, v___x_4336_);
lean_closure_set(v___f_4344_, 1, v___x_4343_);
v___f_4345_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4345_, 0, v___f_4344_);
v___x_4346_ = lean_box(v___x_4342_);
v___x_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
lean_ctor_set(v___x_4347_, 1, v___f_4345_);
v___x_4348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4341_);
lean_ctor_set(v___x_4348_, 1, v___x_4347_);
v___x_4349_ = lean_array_get(v___x_4348_, v_declInfos_4288_, v___x_4337_);
lean_dec_ref_known(v___x_4348_, 2);
v_snd_4350_ = lean_ctor_get(v___x_4349_, 1);
lean_inc(v_snd_4350_);
v_fst_4351_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_fst_4351_);
lean_dec(v___x_4349_);
v_fst_4352_ = lean_ctor_get(v_snd_4350_, 0);
lean_inc(v_fst_4352_);
v_snd_4353_ = lean_ctor_get(v_snd_4350_, 1);
lean_inc(v_snd_4353_);
lean_dec(v_snd_4350_);
lean_inc(v___y_4295_);
lean_inc_ref(v___y_4294_);
lean_inc(v___y_4293_);
lean_inc_ref(v___y_4292_);
lean_inc_ref(v_acc_4291_);
v___x_4354_ = lean_apply_6(v_snd_4353_, v_acc_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, lean_box(0));
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4356_; lean_object* v___f_4357_; uint8_t v___x_4358_; lean_object* v___x_4359_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4356_ = lean_box(v_kind_4290_);
v___f_4357_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4357_, 0, v_acc_4291_);
lean_closure_set(v___f_4357_, 1, v_declInfos_4288_);
lean_closure_set(v___f_4357_, 2, v_k_4289_);
lean_closure_set(v___f_4357_, 3, v___x_4356_);
v___x_4358_ = lean_unbox(v_fst_4352_);
lean_dec(v_fst_4352_);
v___x_4359_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4351_, v___x_4358_, v_a_4355_, v___f_4357_, v_kind_4290_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
return v___x_4359_;
}
else
{
lean_dec(v_fst_4352_);
lean_dec(v_fst_4351_);
lean_dec_ref(v_acc_4291_);
lean_dec_ref(v_k_4289_);
lean_dec_ref(v_declInfos_4288_);
return v___x_4354_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4366_, lean_object* v_declInfos_4367_, lean_object* v_k_4368_, uint8_t v_kind_4369_, lean_object* v_x_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = lean_array_push(v_acc_4366_, v_x_4370_);
v___x_4377_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4367_, v_k_4368_, v_kind_4369_, v___x_4376_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4378_, lean_object* v_k_4379_, lean_object* v_kind_4380_, lean_object* v_acc_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
uint8_t v_kind_boxed_4387_; lean_object* v_res_4388_; 
v_kind_boxed_4387_ = lean_unbox(v_kind_4380_);
v_res_4388_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4378_, v_k_4379_, v_kind_boxed_4387_, v_acc_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4389_, lean_object* v_k_4390_, uint8_t v_kind_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4397_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4398_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4389_, v_k_4390_, v_kind_4391_, v___x_4397_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4399_, lean_object* v_k_4400_, lean_object* v_kind_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
uint8_t v_kind_boxed_4407_; lean_object* v_res_4408_; 
v_kind_boxed_4407_ = lean_unbox(v_kind_4401_);
v_res_4408_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4399_, v_k_4400_, v_kind_boxed_4407_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4409_, lean_object* v_k_4410_, uint8_t v_kind_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
size_t v_sz_4417_; size_t v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v_sz_4417_ = lean_array_size(v_declInfos_4409_);
v___x_4418_ = ((size_t)0ULL);
v___x_4419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4417_, v___x_4418_, v_declInfos_4409_);
v___x_4420_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4419_, v_k_4410_, v_kind_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4421_, lean_object* v_k_4422_, lean_object* v_kind_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
uint8_t v_kind_boxed_4429_; lean_object* v_res_4430_; 
v_kind_boxed_4429_ = lean_unbox(v_kind_4423_);
v_res_4430_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4421_, v_k_4422_, v_kind_boxed_4429_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4431_, lean_object* v_k_4432_, uint8_t v_kind_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
size_t v_sz_4439_; size_t v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v_sz_4439_ = lean_array_size(v_declInfos_4431_);
v___x_4440_ = ((size_t)0ULL);
v___x_4441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4439_, v___x_4440_, v_declInfos_4431_);
v___x_4442_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4441_, v_k_4432_, v_kind_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
return v___x_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4443_, lean_object* v_k_4444_, lean_object* v_kind_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
uint8_t v_kind_boxed_4451_; lean_object* v_res_4452_; 
v_kind_boxed_4451_ = lean_unbox(v_kind_4445_);
v_res_4452_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4443_, v_k_4444_, v_kind_boxed_4451_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(lean_object* v_a_4456_, lean_object* v_b_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_array_4463_; lean_object* v_start_4464_; lean_object* v_stop_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4523_; 
v_array_4463_ = lean_ctor_get(v_a_4456_, 0);
v_start_4464_ = lean_ctor_get(v_a_4456_, 1);
v_stop_4465_ = lean_ctor_get(v_a_4456_, 2);
v_isSharedCheck_4523_ = !lean_is_exclusive(v_a_4456_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4467_ = v_a_4456_;
v_isShared_4468_ = v_isSharedCheck_4523_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_stop_4465_);
lean_inc(v_start_4464_);
lean_inc(v_array_4463_);
lean_dec(v_a_4456_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4523_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
uint8_t v___x_4469_; 
v___x_4469_ = lean_nat_dec_lt(v_start_4464_, v_stop_4465_);
if (v___x_4469_ == 0)
{
lean_object* v___x_4470_; 
lean_del_object(v___x_4467_);
lean_dec(v_stop_4465_);
lean_dec(v_start_4464_);
lean_dec_ref(v_array_4463_);
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v_b_4457_);
return v___x_4470_;
}
else
{
lean_object* v_snd_4471_; lean_object* v_fst_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4522_; 
v_snd_4471_ = lean_ctor_get(v_b_4457_, 1);
v_fst_4472_ = lean_ctor_get(v_b_4457_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v_b_4457_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4474_ = v_b_4457_;
v_isShared_4475_ = v_isSharedCheck_4522_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_snd_4471_);
lean_inc(v_fst_4472_);
lean_dec(v_b_4457_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4522_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v_array_4476_; lean_object* v_start_4477_; lean_object* v_stop_4478_; uint8_t v___x_4479_; 
v_array_4476_ = lean_ctor_get(v_snd_4471_, 0);
v_start_4477_ = lean_ctor_get(v_snd_4471_, 1);
v_stop_4478_ = lean_ctor_get(v_snd_4471_, 2);
v___x_4479_ = lean_nat_dec_lt(v_start_4477_, v_stop_4478_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4481_; 
lean_del_object(v___x_4467_);
lean_dec(v_stop_4465_);
lean_dec(v_start_4464_);
lean_dec_ref(v_array_4463_);
if (v_isShared_4475_ == 0)
{
v___x_4481_ = v___x_4474_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_fst_4472_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v_snd_4471_);
v___x_4481_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
lean_object* v___x_4482_; 
v___x_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4481_);
return v___x_4482_;
}
}
else
{
lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4518_; 
lean_inc(v_stop_4478_);
lean_inc(v_start_4477_);
lean_inc_ref(v_array_4476_);
v_isSharedCheck_4518_ = !lean_is_exclusive(v_snd_4471_);
if (v_isSharedCheck_4518_ == 0)
{
lean_object* v_unused_4519_; lean_object* v_unused_4520_; lean_object* v_unused_4521_; 
v_unused_4519_ = lean_ctor_get(v_snd_4471_, 2);
lean_dec(v_unused_4519_);
v_unused_4520_ = lean_ctor_get(v_snd_4471_, 1);
lean_dec(v_unused_4520_);
v_unused_4521_ = lean_ctor_get(v_snd_4471_, 0);
lean_dec(v_unused_4521_);
v___x_4485_ = v_snd_4471_;
v_isShared_4486_ = v_isSharedCheck_4518_;
goto v_resetjp_4484_;
}
else
{
lean_dec(v_snd_4471_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4518_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4487_ = lean_array_fget_borrowed(v_array_4463_, v_start_4464_);
v___x_4488_ = lean_array_fget_borrowed(v_array_4476_, v_start_4477_);
lean_inc(v___x_4488_);
lean_inc(v___x_4487_);
v___x_4489_ = l_Lean_Meta_mkEqHEq(v___x_4487_, v___x_4488_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4494_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
v___x_4491_ = lean_unsigned_to_nat(1u);
v___x_4492_ = lean_nat_add(v_start_4464_, v___x_4491_);
lean_dec(v_start_4464_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 2, v_stop_4465_);
lean_ctor_set(v___x_4485_, 1, v___x_4492_);
lean_ctor_set(v___x_4485_, 0, v_array_4463_);
v___x_4494_ = v___x_4485_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_array_4463_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v___x_4492_);
lean_ctor_set(v_reuseFailAlloc_4509_, 2, v_stop_4465_);
v___x_4494_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4495_; lean_object* v___x_4497_; 
v___x_4495_ = lean_nat_add(v_start_4477_, v___x_4491_);
lean_dec(v_start_4477_);
if (v_isShared_4468_ == 0)
{
lean_ctor_set(v___x_4467_, 2, v_stop_4478_);
lean_ctor_set(v___x_4467_, 1, v___x_4495_);
lean_ctor_set(v___x_4467_, 0, v_array_4476_);
v___x_4497_ = v___x_4467_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_array_4476_);
lean_ctor_set(v_reuseFailAlloc_4508_, 1, v___x_4495_);
lean_ctor_set(v_reuseFailAlloc_4508_, 2, v_stop_4478_);
v___x_4497_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4503_; 
v___x_4498_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__1));
v___x_4499_ = lean_array_get_size(v_fst_4472_);
v___x_4500_ = lean_nat_add(v___x_4499_, v___x_4491_);
v___x_4501_ = lean_name_append_index_after(v___x_4498_, v___x_4500_);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 1, v_a_4490_);
lean_ctor_set(v___x_4474_, 0, v___x_4501_);
v___x_4503_ = v___x_4474_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4501_);
lean_ctor_set(v_reuseFailAlloc_4507_, 1, v_a_4490_);
v___x_4503_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = lean_array_push(v_fst_4472_, v___x_4503_);
v___x_4505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
lean_ctor_set(v___x_4505_, 1, v___x_4497_);
v_a_4456_ = v___x_4494_;
v_b_4457_ = v___x_4505_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_del_object(v___x_4485_);
lean_dec(v_stop_4478_);
lean_dec(v_start_4477_);
lean_dec_ref(v_array_4476_);
lean_del_object(v___x_4474_);
lean_dec(v_fst_4472_);
lean_del_object(v___x_4467_);
lean_dec(v_stop_4465_);
lean_dec(v_start_4464_);
lean_dec_ref(v_array_4463_);
v_a_4510_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4489_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4489_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___boxed(lean_object* v_a_4524_, lean_object* v_b_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_4524_, v_b_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v___x_4532_, lean_object* v_a_4533_, lean_object* v___x_4534_, lean_object* v_as_4535_, size_t v_sz_4536_, size_t v_i_4537_, lean_object* v_b_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_){
_start:
{
uint8_t v___x_4544_; 
v___x_4544_ = lean_usize_dec_lt(v_i_4537_, v_sz_4536_);
if (v___x_4544_ == 0)
{
lean_object* v___x_4545_; 
lean_dec(v___x_4534_);
v___x_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4545_, 0, v_b_4538_);
return v___x_4545_;
}
else
{
lean_object* v___x_4546_; lean_object* v_a_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4546_ = l_Lean_instInhabitedExpr;
v_a_4547_ = lean_array_uget_borrowed(v_as_4535_, v_i_4537_);
v___x_4548_ = lean_array_get_borrowed(v___x_4546_, v___x_4532_, v_a_4547_);
lean_inc(v___x_4548_);
v___x_4549_ = l_Lean_Meta_instantiateForall(v___x_4548_, v_a_4533_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v___x_4551_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
lean_inc(v___x_4534_);
v___x_4551_ = l_Lean_Meta_Match_simpH_x3f(v_a_4550_, v___x_4534_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; lean_object* v_a_4554_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref_known(v___x_4551_, 1);
if (lean_obj_tag(v_a_4552_) == 1)
{
lean_object* v_val_4558_; lean_object* v___x_4559_; 
v_val_4558_ = lean_ctor_get(v_a_4552_, 0);
lean_inc(v_val_4558_);
lean_dec_ref_known(v_a_4552_, 1);
v___x_4559_ = lean_array_push(v_b_4538_, v_val_4558_);
v_a_4554_ = v___x_4559_;
goto v___jp_4553_;
}
else
{
lean_dec(v_a_4552_);
v_a_4554_ = v_b_4538_;
goto v___jp_4553_;
}
v___jp_4553_:
{
size_t v___x_4555_; size_t v___x_4556_; 
v___x_4555_ = ((size_t)1ULL);
v___x_4556_ = lean_usize_add(v_i_4537_, v___x_4555_);
v_i_4537_ = v___x_4556_;
v_b_4538_ = v_a_4554_;
goto _start;
}
}
else
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4567_; 
lean_dec_ref(v_b_4538_);
lean_dec(v___x_4534_);
v_a_4560_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4562_ = v___x_4551_;
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4551_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4565_; 
if (v_isShared_4563_ == 0)
{
v___x_4565_ = v___x_4562_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4560_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec_ref(v_b_4538_);
lean_dec(v___x_4534_);
v_a_4568_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4549_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4549_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v___x_4576_, lean_object* v_a_4577_, lean_object* v___x_4578_, lean_object* v_as_4579_, lean_object* v_sz_4580_, lean_object* v_i_4581_, lean_object* v_b_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
size_t v_sz_boxed_4588_; size_t v_i_boxed_4589_; lean_object* v_res_4590_; 
v_sz_boxed_4588_ = lean_unbox_usize(v_sz_4580_);
lean_dec(v_sz_4580_);
v_i_boxed_4589_ = lean_unbox_usize(v_i_4581_);
lean_dec(v_i_4581_);
v_res_4590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4576_, v_a_4577_, v___x_4578_, v_as_4579_, v_sz_boxed_4588_, v_i_boxed_4589_, v_b_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec_ref(v_as_4579_);
lean_dec_ref(v_a_4577_);
lean_dec_ref(v___x_4576_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4591_, lean_object* v_args_4592_, lean_object* v___x_4593_, lean_object* v_overlaps_4594_, lean_object* v_a_4595_, lean_object* v_fst_4596_, lean_object* v_a_4597_, lean_object* v___x_4598_, lean_object* v___x_4599_, lean_object* v___x_4600_, lean_object* v___x_4601_, lean_object* v_altVars_4602_, uint8_t v___x_4603_, uint8_t v___x_4604_, lean_object* v_a_4605_, lean_object* v___x_4606_, lean_object* v___x_4607_, lean_object* v___x_4608_, lean_object* v___x_4609_, lean_object* v___x_4610_, lean_object* v___x_4611_, lean_object* v___x_4612_, lean_object* v_matchDeclName_4613_, lean_object* v___x_4614_, lean_object* v___x_4615_, lean_object* v___x_4616_, lean_object* v_heqs_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = l_Lean_mkAppN(v___y_4591_, v_args_4592_);
lean_inc_ref(v_heqs_4617_);
v___x_4624_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4623_, v_heqs_4617_, v___x_4593_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4626_; size_t v_sz_4627_; size_t v___x_4628_; lean_object* v___x_4629_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
lean_inc(v_a_4625_);
lean_dec_ref_known(v___x_4624_, 1);
v___x_4626_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4594_, v_a_4595_);
v_sz_4627_ = lean_array_size(v___x_4626_);
v___x_4628_ = ((size_t)0ULL);
lean_inc_ref(v___x_4599_);
v___x_4629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_fst_4596_, v_a_4597_, v___x_4598_, v___x_4626_, v_sz_4627_, v___x_4628_, v___x_4599_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
lean_dec_ref(v___x_4626_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v_a_4630_; lean_object* v___y_4632_; lean_object* v___y_4633_; lean_object* v___y_4634_; lean_object* v___y_4635_; lean_object* v_toCold_4742_; lean_object* v_options_4743_; uint8_t v_hasTrace_4744_; 
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc(v_a_4630_);
lean_dec_ref_known(v___x_4629_, 1);
v_toCold_4742_ = lean_ctor_get(v___y_4620_, 0);
v_options_4743_ = lean_ctor_get(v_toCold_4742_, 2);
v_hasTrace_4744_ = lean_ctor_get_uint8(v_options_4743_, sizeof(void*)*1);
if (v_hasTrace_4744_ == 0)
{
v___y_4632_ = v___y_4618_;
v___y_4633_ = v___y_4619_;
v___y_4634_ = v___y_4620_;
v___y_4635_ = v___y_4621_;
goto v___jp_4631_;
}
else
{
lean_object* v_inheritedTraceOptions_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; uint8_t v___x_4748_; 
v_inheritedTraceOptions_4745_ = lean_ctor_get(v_toCold_4742_, 11);
v___x_4746_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4747_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4748_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4745_, v_options_4743_, v___x_4747_);
if (v___x_4748_ == 0)
{
v___y_4632_ = v___y_4618_;
v___y_4633_ = v___y_4619_;
v___y_4634_ = v___y_4620_;
v___y_4635_ = v___y_4621_;
goto v___jp_4631_;
}
else
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4749_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4630_);
v___x_4750_ = lean_array_to_list(v_a_4630_);
v___x_4751_ = lean_box(0);
v___x_4752_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4750_, v___x_4751_);
v___x_4753_ = l_Lean_MessageData_ofList(v___x_4752_);
v___x_4754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4749_);
lean_ctor_set(v___x_4754_, 1, v___x_4753_);
v___x_4755_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4746_, v___x_4754_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_dec_ref_known(v___x_4755_, 1);
v___y_4632_ = v___y_4618_;
v___y_4633_ = v___y_4619_;
v___y_4634_ = v___y_4620_;
v___y_4635_ = v___y_4621_;
goto v___jp_4631_;
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec(v_a_4630_);
lean_dec(v_a_4625_);
lean_dec_ref(v_heqs_4617_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
lean_dec(v_matchDeclName_4613_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4609_);
lean_dec_ref(v___x_4607_);
lean_dec(v___x_4606_);
lean_dec_ref(v___x_4601_);
lean_dec(v___x_4600_);
lean_dec_ref(v___x_4599_);
lean_dec_ref(v_a_4597_);
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4755_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4755_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
}
v___jp_4631_:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; size_t v_sz_4643_; lean_object* v___x_4644_; 
v___x_4636_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4637_ = l_Array_reverse___redArg(v_a_4597_);
v___x_4638_ = lean_array_get_size(v___x_4637_);
v___x_4639_ = l_Array_toSubarray___redArg(v___x_4637_, v___x_4600_, v___x_4638_);
lean_inc_ref(v___x_4601_);
v___x_4640_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4601_, v___x_4599_);
v___x_4641_ = l_Array_reverse___redArg(v___x_4640_);
v___x_4642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4636_);
lean_ctor_set(v___x_4642_, 1, v___x_4639_);
v_sz_4643_ = lean_array_size(v___x_4641_);
v___x_4644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4641_, v_sz_4643_, v___x_4628_, v___x_4642_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec_ref(v___x_4641_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v_fst_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4732_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
lean_dec_ref_known(v___x_4644_, 1);
v_fst_4646_ = lean_ctor_get(v_a_4645_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v_a_4645_);
if (v_isSharedCheck_4732_ == 0)
{
lean_object* v_unused_4733_; 
v_unused_4733_ = lean_ctor_get(v_a_4645_, 1);
lean_dec(v_unused_4733_);
v___x_4648_ = v_a_4645_;
v_isShared_4649_ = v_isSharedCheck_4732_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_fst_4646_);
lean_dec(v_a_4645_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4732_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; uint8_t v___x_4652_; lean_object* v___x_4653_; 
v___x_4650_ = l_Subarray_copy___redArg(v___x_4601_);
lean_inc_ref(v___x_4650_);
v___x_4651_ = l_Array_append___redArg(v___x_4650_, v_altVars_4602_);
v___x_4652_ = 1;
v___x_4653_ = l_Lean_Meta_mkForallFVars(v___x_4651_, v_fst_4646_, v___x_4603_, v___x_4604_, v___x_4604_, v___x_4652_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec_ref(v___x_4651_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc(v_a_4654_);
lean_dec_ref_known(v___x_4653_, 1);
v___x_4655_ = l_Lean_ConstantInfo_name(v_a_4605_);
v___x_4656_ = l_Lean_mkConst(v___x_4655_, v___x_4606_);
lean_inc_ref(v___x_4607_);
v___x_4657_ = l_Subarray_copy___redArg(v___x_4607_);
v___x_4658_ = lean_mk_empty_array_with_capacity(v___x_4608_);
v___x_4659_ = lean_array_push(v___x_4658_, v___x_4609_);
v___x_4660_ = l_Array_append___redArg(v___x_4657_, v___x_4659_);
lean_dec_ref(v___x_4659_);
v___x_4661_ = l_Array_append___redArg(v___x_4660_, v___x_4650_);
lean_dec_ref(v___x_4650_);
v___x_4662_ = l_Subarray_copy___redArg(v___x_4610_);
v___x_4663_ = l_Array_append___redArg(v___x_4661_, v___x_4662_);
lean_dec_ref(v___x_4662_);
v___x_4664_ = l_Lean_mkAppN(v___x_4656_, v___x_4663_);
v___x_4665_ = l_Lean_Meta_mkHEq(v___x_4664_, v_a_4625_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4667_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
v___x_4667_ = l_Lean_mkArrowN(v_a_4630_, v_a_4666_, v___y_4634_, v___y_4635_);
lean_dec(v_a_4630_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref_known(v___x_4667_, 1);
v___x_4669_ = l_Array_append___redArg(v___x_4663_, v_altVars_4602_);
v___x_4670_ = l_Array_append___redArg(v___x_4669_, v_heqs_4617_);
v___x_4671_ = l_Lean_Meta_mkForallFVars(v___x_4670_, v_a_4668_, v___x_4603_, v___x_4604_, v___x_4604_, v___x_4652_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec_ref(v___x_4670_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4673_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v___x_4671_, 1);
v___x_4673_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4672_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4731_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4676_ = v___x_4673_;
v_isShared_4677_ = v_isSharedCheck_4731_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4673_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4731_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v_start_4678_; lean_object* v_stop_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4729_; 
v_start_4678_ = lean_ctor_get(v___x_4607_, 1);
v_stop_4679_ = lean_ctor_get(v___x_4607_, 2);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4729_ == 0)
{
lean_object* v_unused_4730_; 
v_unused_4730_ = lean_ctor_get(v___x_4607_, 0);
lean_dec(v_unused_4730_);
v___x_4681_ = v___x_4607_;
v_isShared_4682_ = v_isSharedCheck_4729_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_stop_4679_);
lean_inc(v_start_4678_);
lean_dec(v___x_4607_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4729_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4683_ = lean_nat_sub(v_stop_4679_, v_start_4678_);
lean_dec(v_start_4678_);
lean_dec(v_stop_4679_);
v___x_4684_ = lean_nat_add(v___x_4683_, v___x_4608_);
lean_dec(v___x_4683_);
v___x_4685_ = lean_nat_add(v___x_4684_, v___x_4611_);
lean_dec(v___x_4684_);
v___x_4686_ = lean_nat_add(v___x_4685_, v___x_4612_);
lean_dec(v___x_4685_);
v___x_4687_ = lean_array_get_size(v_altVars_4602_);
v___x_4688_ = lean_nat_add(v___x_4686_, v___x_4687_);
lean_dec(v___x_4686_);
v___x_4689_ = lean_array_get_size(v_heqs_4617_);
lean_dec_ref(v_heqs_4617_);
lean_inc(v_a_4674_);
v___x_4690_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4613_, v_a_4674_, v___x_4688_, v___x_4689_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4728_; 
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4693_ = v___x_4690_;
v_isShared_4694_ = v_isSharedCheck_4728_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4690_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4728_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4695_; lean_object* v_env_4696_; uint8_t v___x_4697_; 
v___x_4695_ = lean_st_ref_get(v___y_4635_);
v_env_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc_ref(v_env_4696_);
lean_dec(v___x_4695_);
lean_inc(v___x_4614_);
v___x_4697_ = l_Lean_Environment_contains(v_env_4696_, v___x_4614_, v___x_4604_);
if (v___x_4697_ == 0)
{
lean_object* v___x_4699_; 
lean_del_object(v___x_4693_);
lean_inc(v___x_4614_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 2, v_a_4674_);
lean_ctor_set(v___x_4681_, 1, v___x_4615_);
lean_ctor_set(v___x_4681_, 0, v___x_4614_);
v___x_4699_ = v___x_4681_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4614_);
lean_ctor_set(v_reuseFailAlloc_4724_, 1, v___x_4615_);
lean_ctor_set(v_reuseFailAlloc_4724_, 2, v_a_4674_);
v___x_4699_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
lean_object* v___x_4701_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set_tag(v___x_4648_, 1);
lean_ctor_set(v___x_4648_, 1, v___x_4616_);
lean_ctor_set(v___x_4648_, 0, v___x_4614_);
v___x_4701_ = v___x_4648_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4614_);
lean_ctor_set(v_reuseFailAlloc_4723_, 1, v___x_4616_);
v___x_4701_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
lean_object* v___x_4702_; lean_object* v___x_4704_; 
v___x_4702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4702_, 0, v___x_4699_);
lean_ctor_set(v___x_4702_, 1, v_a_4691_);
lean_ctor_set(v___x_4702_, 2, v___x_4701_);
if (v_isShared_4677_ == 0)
{
lean_ctor_set_tag(v___x_4676_, 2);
lean_ctor_set(v___x_4676_, 0, v___x_4702_);
v___x_4704_ = v___x_4676_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4702_);
v___x_4704_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
lean_object* v___x_4705_; 
v___x_4705_ = l_Lean_addDecl(v___x_4704_, v___x_4603_, v___y_4634_, v___y_4635_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4712_ == 0)
{
lean_object* v_unused_4713_; 
v_unused_4713_ = lean_ctor_get(v___x_4705_, 0);
lean_dec(v_unused_4713_);
v___x_4707_ = v___x_4705_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_dec(v___x_4705_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 0, v_a_4654_);
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4654_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
lean_dec(v_a_4654_);
v_a_4714_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4716_ = v___x_4705_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4705_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_a_4714_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4726_; 
lean_dec(v_a_4691_);
lean_del_object(v___x_4681_);
lean_del_object(v___x_4676_);
lean_dec(v_a_4674_);
lean_del_object(v___x_4648_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 0, v_a_4654_);
v___x_4726_ = v___x_4693_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4654_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
else
{
lean_del_object(v___x_4681_);
lean_del_object(v___x_4676_);
lean_dec(v_a_4674_);
lean_dec(v_a_4654_);
lean_del_object(v___x_4648_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
return v___x_4690_;
}
}
}
}
else
{
lean_dec(v_a_4654_);
lean_del_object(v___x_4648_);
lean_dec_ref(v_heqs_4617_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
lean_dec(v_matchDeclName_4613_);
lean_dec_ref(v___x_4607_);
return v___x_4673_;
}
}
else
{
lean_dec(v_a_4654_);
lean_del_object(v___x_4648_);
lean_dec_ref(v_heqs_4617_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
lean_dec(v_matchDeclName_4613_);
lean_dec_ref(v___x_4607_);
return v___x_4671_;
}
}
else
{
lean_dec_ref(v___x_4663_);
lean_dec(v_a_4654_);
lean_del_object(v___x_4648_);
lean_dec_ref(v_heqs_4617_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
lean_dec(v_matchDeclName_4613_);
lean_dec_ref(v___x_4607_);
return v___x_4667_;
}
}
else
{
lean_dec_ref(v___x_4663_);
lean_dec(v_a_4654_);
lean_del_object(v___x_4648_);
lean_dec(v_a_4630_);
lean_dec_ref(v_heqs_4617_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
lean_dec(v_matchDeclName_4613_);
lean_dec_ref(v___x_4607_);
return v___x_4665_;
}
}
else
{
lean_dec_ref(v___x_4650_);
lean_del_object(v___x_4648_);
lean_dec(v_a_4630_);
lean_dec(v_a_4625_);
lean_dec_ref(v_heqs_4617_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
lean_dec(v_matchDeclName_4613_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4609_);
lean_dec_ref(v___x_4607_);
lean_dec(v___x_4606_);
return v___x_4653_;
}
}
}
else
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4741_; 
lean_dec(v_a_4630_);
lean_dec(v_a_4625_);
lean_dec_ref(v_heqs_4617_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
lean_dec(v_matchDeclName_4613_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4609_);
lean_dec_ref(v___x_4607_);
lean_dec(v___x_4606_);
lean_dec_ref(v___x_4601_);
v_a_4734_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4736_ = v___x_4644_;
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___x_4644_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4739_; 
if (v_isShared_4737_ == 0)
{
v___x_4739_ = v___x_4736_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_a_4734_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
lean_dec(v_a_4625_);
lean_dec_ref(v_heqs_4617_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
lean_dec(v_matchDeclName_4613_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4609_);
lean_dec_ref(v___x_4607_);
lean_dec(v___x_4606_);
lean_dec_ref(v___x_4601_);
lean_dec(v___x_4600_);
lean_dec_ref(v___x_4599_);
lean_dec_ref(v_a_4597_);
v_a_4764_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4629_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4629_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4617_);
lean_dec(v___x_4616_);
lean_dec(v___x_4615_);
lean_dec(v___x_4614_);
lean_dec(v_matchDeclName_4613_);
lean_dec_ref(v___x_4610_);
lean_dec_ref(v___x_4609_);
lean_dec_ref(v___x_4607_);
lean_dec(v___x_4606_);
lean_dec_ref(v___x_4601_);
lean_dec(v___x_4600_);
lean_dec_ref(v___x_4599_);
lean_dec(v___x_4598_);
lean_dec_ref(v_a_4597_);
return v___x_4624_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4772_ = _args[0];
lean_object* v_args_4773_ = _args[1];
lean_object* v___x_4774_ = _args[2];
lean_object* v_overlaps_4775_ = _args[3];
lean_object* v_a_4776_ = _args[4];
lean_object* v_fst_4777_ = _args[5];
lean_object* v_a_4778_ = _args[6];
lean_object* v___x_4779_ = _args[7];
lean_object* v___x_4780_ = _args[8];
lean_object* v___x_4781_ = _args[9];
lean_object* v___x_4782_ = _args[10];
lean_object* v_altVars_4783_ = _args[11];
lean_object* v___x_4784_ = _args[12];
lean_object* v___x_4785_ = _args[13];
lean_object* v_a_4786_ = _args[14];
lean_object* v___x_4787_ = _args[15];
lean_object* v___x_4788_ = _args[16];
lean_object* v___x_4789_ = _args[17];
lean_object* v___x_4790_ = _args[18];
lean_object* v___x_4791_ = _args[19];
lean_object* v___x_4792_ = _args[20];
lean_object* v___x_4793_ = _args[21];
lean_object* v_matchDeclName_4794_ = _args[22];
lean_object* v___x_4795_ = _args[23];
lean_object* v___x_4796_ = _args[24];
lean_object* v___x_4797_ = _args[25];
lean_object* v_heqs_4798_ = _args[26];
lean_object* v___y_4799_ = _args[27];
lean_object* v___y_4800_ = _args[28];
lean_object* v___y_4801_ = _args[29];
lean_object* v___y_4802_ = _args[30];
lean_object* v___y_4803_ = _args[31];
_start:
{
uint8_t v___x_21241__boxed_4804_; uint8_t v___x_21242__boxed_4805_; lean_object* v_res_4806_; 
v___x_21241__boxed_4804_ = lean_unbox(v___x_4784_);
v___x_21242__boxed_4805_ = lean_unbox(v___x_4785_);
v_res_4806_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4772_, v_args_4773_, v___x_4774_, v_overlaps_4775_, v_a_4776_, v_fst_4777_, v_a_4778_, v___x_4779_, v___x_4780_, v___x_4781_, v___x_4782_, v_altVars_4783_, v___x_21241__boxed_4804_, v___x_21242__boxed_4805_, v_a_4786_, v___x_4787_, v___x_4788_, v___x_4789_, v___x_4790_, v___x_4791_, v___x_4792_, v___x_4793_, v_matchDeclName_4794_, v___x_4795_, v___x_4796_, v___x_4797_, v_heqs_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec(v___y_4800_);
lean_dec_ref(v___y_4799_);
lean_dec(v___x_4793_);
lean_dec(v___x_4792_);
lean_dec(v___x_4789_);
lean_dec_ref(v_a_4786_);
lean_dec_ref(v_altVars_4783_);
lean_dec(v_fst_4777_);
lean_dec(v_a_4776_);
lean_dec_ref(v_overlaps_4775_);
lean_dec_ref(v_args_4773_);
return v_res_4806_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4809_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4810_ = lean_unsigned_to_nat(8u);
v___x_4811_ = lean_unsigned_to_nat(295u);
v___x_4812_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4813_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4814_ = l_mkPanicMessageWithDecl(v___x_4813_, v___x_4812_, v___x_4811_, v___x_4810_, v___x_4809_);
return v___x_4814_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4815_, lean_object* v___x_4816_, lean_object* v___x_4817_, lean_object* v___y_4818_, lean_object* v___x_4819_, lean_object* v_overlaps_4820_, lean_object* v_a_4821_, lean_object* v_fst_4822_, lean_object* v___x_4823_, uint8_t v___x_4824_, lean_object* v_a_4825_, lean_object* v___x_4826_, lean_object* v___x_4827_, lean_object* v___x_4828_, lean_object* v___x_4829_, lean_object* v___x_4830_, lean_object* v___x_4831_, lean_object* v_matchDeclName_4832_, lean_object* v___x_4833_, lean_object* v___x_4834_, lean_object* v___x_4835_, lean_object* v_altVars_4836_, lean_object* v_args_4837_, lean_object* v___mask_4838_, lean_object* v_altResultType_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
uint8_t v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = 0;
v___x_4846_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4839_, v___f_4815_, v___x_4845_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v_start_4848_; lean_object* v_stop_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; uint8_t v___x_4852_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
lean_inc(v_a_4847_);
lean_dec_ref_known(v___x_4846_, 1);
v_start_4848_ = lean_ctor_get(v___x_4816_, 1);
v_stop_4849_ = lean_ctor_get(v___x_4816_, 2);
v___x_4850_ = lean_array_get_size(v_a_4847_);
v___x_4851_ = lean_nat_sub(v_stop_4849_, v_start_4848_);
v___x_4852_ = lean_nat_dec_eq(v___x_4850_, v___x_4851_);
if (v___x_4852_ == 0)
{
lean_object* v___x_4853_; lean_object* v___x_4854_; 
lean_dec(v___x_4851_);
lean_dec(v_a_4847_);
lean_dec_ref(v_args_4837_);
lean_dec_ref(v_altVars_4836_);
lean_dec(v___x_4835_);
lean_dec(v___x_4834_);
lean_dec(v___x_4833_);
lean_dec(v_matchDeclName_4832_);
lean_dec(v___x_4831_);
lean_dec_ref(v___x_4830_);
lean_dec_ref(v___x_4829_);
lean_dec(v___x_4828_);
lean_dec_ref(v___x_4827_);
lean_dec(v___x_4826_);
lean_dec_ref(v_a_4825_);
lean_dec_ref(v___x_4823_);
lean_dec(v_fst_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_overlaps_4820_);
lean_dec(v___x_4819_);
lean_dec_ref(v___y_4818_);
lean_dec(v___x_4817_);
lean_dec_ref(v___x_4816_);
v___x_4853_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4854_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v___x_4853_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
return v___x_4854_;
}
else
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4855_ = lean_mk_empty_array_with_capacity(v___x_4817_);
lean_inc(v___x_4817_);
lean_inc(v_a_4847_);
v___x_4856_ = l_Array_toSubarray___redArg(v_a_4847_, v___x_4817_, v___x_4850_);
v___x_4857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4855_);
lean_ctor_set(v___x_4857_, 1, v___x_4856_);
lean_inc_ref(v___x_4816_);
v___x_4858_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v___x_4816_, v___x_4857_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; lean_object* v_fst_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___f_4863_; uint8_t v___x_4864_; lean_object* v___x_4865_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
lean_inc(v_a_4859_);
lean_dec_ref_known(v___x_4858_, 1);
v_fst_4860_ = lean_ctor_get(v_a_4859_, 0);
lean_inc(v_fst_4860_);
lean_dec(v_a_4859_);
v___x_4861_ = lean_box(v___x_4845_);
v___x_4862_ = lean_box(v___x_4824_);
v___f_4863_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4863_, 0, v___y_4818_);
lean_closure_set(v___f_4863_, 1, v_args_4837_);
lean_closure_set(v___f_4863_, 2, v___x_4819_);
lean_closure_set(v___f_4863_, 3, v_overlaps_4820_);
lean_closure_set(v___f_4863_, 4, v_a_4821_);
lean_closure_set(v___f_4863_, 5, v_fst_4822_);
lean_closure_set(v___f_4863_, 6, v_a_4847_);
lean_closure_set(v___f_4863_, 7, v___x_4850_);
lean_closure_set(v___f_4863_, 8, v___x_4823_);
lean_closure_set(v___f_4863_, 9, v___x_4817_);
lean_closure_set(v___f_4863_, 10, v___x_4816_);
lean_closure_set(v___f_4863_, 11, v_altVars_4836_);
lean_closure_set(v___f_4863_, 12, v___x_4861_);
lean_closure_set(v___f_4863_, 13, v___x_4862_);
lean_closure_set(v___f_4863_, 14, v_a_4825_);
lean_closure_set(v___f_4863_, 15, v___x_4826_);
lean_closure_set(v___f_4863_, 16, v___x_4827_);
lean_closure_set(v___f_4863_, 17, v___x_4828_);
lean_closure_set(v___f_4863_, 18, v___x_4829_);
lean_closure_set(v___f_4863_, 19, v___x_4830_);
lean_closure_set(v___f_4863_, 20, v___x_4851_);
lean_closure_set(v___f_4863_, 21, v___x_4831_);
lean_closure_set(v___f_4863_, 22, v_matchDeclName_4832_);
lean_closure_set(v___f_4863_, 23, v___x_4833_);
lean_closure_set(v___f_4863_, 24, v___x_4834_);
lean_closure_set(v___f_4863_, 25, v___x_4835_);
v___x_4864_ = 0;
v___x_4865_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4860_, v___f_4863_, v___x_4864_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
return v___x_4865_;
}
else
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4873_; 
lean_dec(v___x_4851_);
lean_dec(v_a_4847_);
lean_dec_ref(v_args_4837_);
lean_dec_ref(v_altVars_4836_);
lean_dec(v___x_4835_);
lean_dec(v___x_4834_);
lean_dec(v___x_4833_);
lean_dec(v_matchDeclName_4832_);
lean_dec(v___x_4831_);
lean_dec_ref(v___x_4830_);
lean_dec_ref(v___x_4829_);
lean_dec(v___x_4828_);
lean_dec_ref(v___x_4827_);
lean_dec(v___x_4826_);
lean_dec_ref(v_a_4825_);
lean_dec_ref(v___x_4823_);
lean_dec(v_fst_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_overlaps_4820_);
lean_dec(v___x_4819_);
lean_dec_ref(v___y_4818_);
lean_dec(v___x_4817_);
lean_dec_ref(v___x_4816_);
v_a_4866_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4868_ = v___x_4858_;
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4858_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4871_; 
if (v_isShared_4869_ == 0)
{
v___x_4871_ = v___x_4868_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4866_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
}
}
else
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
lean_dec_ref(v_args_4837_);
lean_dec_ref(v_altVars_4836_);
lean_dec(v___x_4835_);
lean_dec(v___x_4834_);
lean_dec(v___x_4833_);
lean_dec(v_matchDeclName_4832_);
lean_dec(v___x_4831_);
lean_dec_ref(v___x_4830_);
lean_dec_ref(v___x_4829_);
lean_dec(v___x_4828_);
lean_dec_ref(v___x_4827_);
lean_dec(v___x_4826_);
lean_dec_ref(v_a_4825_);
lean_dec_ref(v___x_4823_);
lean_dec(v_fst_4822_);
lean_dec(v_a_4821_);
lean_dec_ref(v_overlaps_4820_);
lean_dec(v___x_4819_);
lean_dec_ref(v___y_4818_);
lean_dec(v___x_4817_);
lean_dec_ref(v___x_4816_);
v_a_4874_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4846_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4846_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4882_ = _args[0];
lean_object* v___x_4883_ = _args[1];
lean_object* v___x_4884_ = _args[2];
lean_object* v___y_4885_ = _args[3];
lean_object* v___x_4886_ = _args[4];
lean_object* v_overlaps_4887_ = _args[5];
lean_object* v_a_4888_ = _args[6];
lean_object* v_fst_4889_ = _args[7];
lean_object* v___x_4890_ = _args[8];
lean_object* v___x_4891_ = _args[9];
lean_object* v_a_4892_ = _args[10];
lean_object* v___x_4893_ = _args[11];
lean_object* v___x_4894_ = _args[12];
lean_object* v___x_4895_ = _args[13];
lean_object* v___x_4896_ = _args[14];
lean_object* v___x_4897_ = _args[15];
lean_object* v___x_4898_ = _args[16];
lean_object* v_matchDeclName_4899_ = _args[17];
lean_object* v___x_4900_ = _args[18];
lean_object* v___x_4901_ = _args[19];
lean_object* v___x_4902_ = _args[20];
lean_object* v_altVars_4903_ = _args[21];
lean_object* v_args_4904_ = _args[22];
lean_object* v___mask_4905_ = _args[23];
lean_object* v_altResultType_4906_ = _args[24];
lean_object* v___y_4907_ = _args[25];
lean_object* v___y_4908_ = _args[26];
lean_object* v___y_4909_ = _args[27];
lean_object* v___y_4910_ = _args[28];
lean_object* v___y_4911_ = _args[29];
_start:
{
uint8_t v___x_21628__boxed_4912_; lean_object* v_res_4913_; 
v___x_21628__boxed_4912_ = lean_unbox(v___x_4891_);
v_res_4913_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4882_, v___x_4883_, v___x_4884_, v___y_4885_, v___x_4886_, v_overlaps_4887_, v_a_4888_, v_fst_4889_, v___x_4890_, v___x_21628__boxed_4912_, v_a_4892_, v___x_4893_, v___x_4894_, v___x_4895_, v___x_4896_, v___x_4897_, v___x_4898_, v_matchDeclName_4899_, v___x_4900_, v___x_4901_, v___x_4902_, v_altVars_4903_, v_args_4904_, v___mask_4905_, v_altResultType_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
lean_dec(v___y_4908_);
lean_dec_ref(v___y_4907_);
lean_dec_ref(v___mask_4905_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4915_, lean_object* v_val_4916_, lean_object* v_matchDeclName_4917_, lean_object* v___x_4918_, lean_object* v___x_4919_, lean_object* v_a_4920_, lean_object* v___x_4921_, lean_object* v___x_4922_, lean_object* v___x_4923_, lean_object* v___x_4924_, lean_object* v___x_4925_, lean_object* v___x_4926_, lean_object* v_a_4927_, lean_object* v_b_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_){
_start:
{
uint8_t v___x_4934_; 
v___x_4934_ = lean_nat_dec_lt(v_a_4927_, v_upperBound_4915_);
if (v___x_4934_ == 0)
{
lean_object* v___x_4935_; 
lean_dec(v_a_4927_);
lean_dec(v___x_4926_);
lean_dec(v___x_4925_);
lean_dec_ref(v___x_4924_);
lean_dec_ref(v___x_4923_);
lean_dec_ref(v___x_4922_);
lean_dec(v___x_4921_);
lean_dec_ref(v_a_4920_);
lean_dec(v___x_4919_);
lean_dec_ref(v___x_4918_);
lean_dec(v_matchDeclName_4917_);
lean_dec_ref(v_val_4916_);
v___x_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4935_, 0, v_b_4928_);
return v___x_4935_;
}
else
{
lean_object* v_snd_4936_; lean_object* v_fst_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_5001_; 
v_snd_4936_ = lean_ctor_get(v_b_4928_, 1);
v_fst_4937_ = lean_ctor_get(v_b_4928_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v_b_4928_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4939_ = v_b_4928_;
v_isShared_4940_ = v_isSharedCheck_5001_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_snd_4936_);
lean_inc(v_fst_4937_);
lean_dec(v_b_4928_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_5001_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v_fst_4941_; lean_object* v_snd_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_5000_; 
v_fst_4941_ = lean_ctor_get(v_snd_4936_, 0);
v_snd_4942_ = lean_ctor_get(v_snd_4936_, 1);
v_isSharedCheck_5000_ = !lean_is_exclusive(v_snd_4936_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4944_ = v_snd_4936_;
v_isShared_4945_ = v_isSharedCheck_5000_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_snd_4942_);
lean_inc(v_fst_4941_);
lean_dec(v_snd_4936_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_5000_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v_altInfos_4946_; lean_object* v_overlaps_4947_; lean_object* v_start_4948_; lean_object* v_stop_4949_; lean_object* v___f_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___y_4962_; lean_object* v___x_4995_; uint8_t v___x_4996_; 
v_altInfos_4946_ = lean_ctor_get(v_val_4916_, 2);
v_overlaps_4947_ = lean_ctor_get(v_val_4916_, 5);
v_start_4948_ = lean_ctor_get(v___x_4924_, 1);
v_stop_4949_ = lean_ctor_get(v___x_4924_, 2);
v___f_4950_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4951_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4952_ = lean_unsigned_to_nat(0u);
v___x_4953_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4954_ = lean_unsigned_to_nat(1u);
v___x_4955_ = lean_box(0);
v___x_4956_ = lean_array_get_borrowed(v___x_4951_, v_altInfos_4946_, v_a_4927_);
v___x_4957_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4917_);
v___x_4958_ = l_Lean_Name_str___override(v_matchDeclName_4917_, v___x_4957_);
lean_inc(v_snd_4942_);
v___x_4959_ = lean_name_append_index_after(v___x_4958_, v_snd_4942_);
lean_inc(v___x_4959_);
v___x_4960_ = lean_array_push(v_fst_4937_, v___x_4959_);
v___x_4995_ = lean_nat_sub(v_stop_4949_, v_start_4948_);
v___x_4996_ = lean_nat_dec_lt(v_a_4927_, v___x_4995_);
lean_dec(v___x_4995_);
if (v___x_4996_ == 0)
{
lean_object* v___x_4997_; lean_object* v___x_4998_; 
v___x_4997_ = l_Lean_instInhabitedExpr;
v___x_4998_ = l_outOfBounds___redArg(v___x_4997_);
v___y_4962_ = v___x_4998_;
goto v___jp_4961_;
}
else
{
lean_object* v___x_4999_; 
v___x_4999_ = l_Subarray_get___redArg(v___x_4924_, v_a_4927_);
v___y_4962_ = v___x_4999_;
goto v___jp_4961_;
}
v___jp_4961_:
{
lean_object* v___x_4963_; 
lean_inc(v___y_4932_);
lean_inc_ref(v___y_4931_);
lean_inc(v___y_4930_);
lean_inc_ref(v___y_4929_);
lean_inc_ref(v___y_4962_);
v___x_4963_ = lean_infer_type(v___y_4962_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v___x_4965_; lean_object* v___f_4966_; lean_object* v___x_4967_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v___x_4963_, 1);
v___x_4965_ = lean_box(v___x_4934_);
lean_inc(v___x_4926_);
lean_inc(v_matchDeclName_4917_);
lean_inc(v___x_4925_);
lean_inc_ref(v___x_4924_);
lean_inc_ref(v___x_4923_);
lean_inc_ref(v___x_4922_);
lean_inc(v___x_4921_);
lean_inc_ref(v_a_4920_);
lean_inc(v_fst_4941_);
lean_inc(v_a_4927_);
lean_inc_ref(v_overlaps_4947_);
lean_inc(v___x_4919_);
lean_inc_ref(v___x_4918_);
v___f_4966_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 30, 21);
lean_closure_set(v___f_4966_, 0, v___f_4950_);
lean_closure_set(v___f_4966_, 1, v___x_4918_);
lean_closure_set(v___f_4966_, 2, v___x_4952_);
lean_closure_set(v___f_4966_, 3, v___y_4962_);
lean_closure_set(v___f_4966_, 4, v___x_4919_);
lean_closure_set(v___f_4966_, 5, v_overlaps_4947_);
lean_closure_set(v___f_4966_, 6, v_a_4927_);
lean_closure_set(v___f_4966_, 7, v_fst_4941_);
lean_closure_set(v___f_4966_, 8, v___x_4953_);
lean_closure_set(v___f_4966_, 9, v___x_4965_);
lean_closure_set(v___f_4966_, 10, v_a_4920_);
lean_closure_set(v___f_4966_, 11, v___x_4921_);
lean_closure_set(v___f_4966_, 12, v___x_4922_);
lean_closure_set(v___f_4966_, 13, v___x_4954_);
lean_closure_set(v___f_4966_, 14, v___x_4923_);
lean_closure_set(v___f_4966_, 15, v___x_4924_);
lean_closure_set(v___f_4966_, 16, v___x_4925_);
lean_closure_set(v___f_4966_, 17, v_matchDeclName_4917_);
lean_closure_set(v___f_4966_, 18, v___x_4959_);
lean_closure_set(v___f_4966_, 19, v___x_4926_);
lean_closure_set(v___f_4966_, 20, v___x_4955_);
lean_inc(v___x_4956_);
v___x_4967_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4964_, v___x_4956_, v___f_4966_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4972_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_a_4968_);
lean_dec_ref_known(v___x_4967_, 1);
v___x_4969_ = lean_array_push(v_fst_4941_, v_a_4968_);
v___x_4970_ = lean_nat_add(v_snd_4942_, v___x_4954_);
lean_dec(v_snd_4942_);
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 1, v___x_4970_);
lean_ctor_set(v___x_4944_, 0, v___x_4969_);
v___x_4972_ = v___x_4944_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4978_; 
v_reuseFailAlloc_4978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4978_, 0, v___x_4969_);
lean_ctor_set(v_reuseFailAlloc_4978_, 1, v___x_4970_);
v___x_4972_ = v_reuseFailAlloc_4978_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
lean_object* v___x_4974_; 
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 1, v___x_4972_);
lean_ctor_set(v___x_4939_, 0, v___x_4960_);
v___x_4974_ = v___x_4939_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4960_);
lean_ctor_set(v_reuseFailAlloc_4977_, 1, v___x_4972_);
v___x_4974_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
lean_object* v___x_4975_; 
v___x_4975_ = lean_nat_add(v_a_4927_, v___x_4954_);
lean_dec(v_a_4927_);
v_a_4927_ = v___x_4975_;
v_b_4928_ = v___x_4974_;
goto _start;
}
}
}
else
{
lean_object* v_a_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4986_; 
lean_dec_ref(v___x_4960_);
lean_del_object(v___x_4944_);
lean_dec(v_snd_4942_);
lean_dec(v_fst_4941_);
lean_del_object(v___x_4939_);
lean_dec(v_a_4927_);
lean_dec(v___x_4926_);
lean_dec(v___x_4925_);
lean_dec_ref(v___x_4924_);
lean_dec_ref(v___x_4923_);
lean_dec_ref(v___x_4922_);
lean_dec(v___x_4921_);
lean_dec_ref(v_a_4920_);
lean_dec(v___x_4919_);
lean_dec_ref(v___x_4918_);
lean_dec(v_matchDeclName_4917_);
lean_dec_ref(v_val_4916_);
v_a_4979_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4981_ = v___x_4967_;
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_a_4979_);
lean_dec(v___x_4967_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4984_; 
if (v_isShared_4982_ == 0)
{
v___x_4984_ = v___x_4981_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4979_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
}
else
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
lean_dec_ref(v___y_4962_);
lean_dec_ref(v___x_4960_);
lean_dec(v___x_4959_);
lean_del_object(v___x_4944_);
lean_dec(v_snd_4942_);
lean_dec(v_fst_4941_);
lean_del_object(v___x_4939_);
lean_dec(v_a_4927_);
lean_dec(v___x_4926_);
lean_dec(v___x_4925_);
lean_dec_ref(v___x_4924_);
lean_dec_ref(v___x_4923_);
lean_dec_ref(v___x_4922_);
lean_dec(v___x_4921_);
lean_dec_ref(v_a_4920_);
lean_dec(v___x_4919_);
lean_dec_ref(v___x_4918_);
lean_dec(v_matchDeclName_4917_);
lean_dec_ref(v_val_4916_);
v_a_4987_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4989_ = v___x_4963_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4963_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
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
lean_object* v_upperBound_5002_ = _args[0];
lean_object* v_val_5003_ = _args[1];
lean_object* v_matchDeclName_5004_ = _args[2];
lean_object* v___x_5005_ = _args[3];
lean_object* v___x_5006_ = _args[4];
lean_object* v_a_5007_ = _args[5];
lean_object* v___x_5008_ = _args[6];
lean_object* v___x_5009_ = _args[7];
lean_object* v___x_5010_ = _args[8];
lean_object* v___x_5011_ = _args[9];
lean_object* v___x_5012_ = _args[10];
lean_object* v___x_5013_ = _args[11];
lean_object* v_a_5014_ = _args[12];
lean_object* v_b_5015_ = _args[13];
lean_object* v___y_5016_ = _args[14];
lean_object* v___y_5017_ = _args[15];
lean_object* v___y_5018_ = _args[16];
lean_object* v___y_5019_ = _args[17];
lean_object* v___y_5020_ = _args[18];
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5002_, v_val_5003_, v_matchDeclName_5004_, v___x_5005_, v___x_5006_, v_a_5007_, v___x_5008_, v___x_5009_, v___x_5010_, v___x_5011_, v___x_5012_, v___x_5013_, v_a_5014_, v_b_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec(v_upperBound_5002_);
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5028_, lean_object* v___x_5029_, lean_object* v_matchDeclName_5030_, lean_object* v___x_5031_, lean_object* v_a_5032_, lean_object* v___x_5033_, lean_object* v___x_5034_, lean_object* v_xs_5035_, lean_object* v___matchResultType_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_){
_start:
{
lean_object* v_numParams_5042_; lean_object* v_numDiscrs_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v_lower_5049_; lean_object* v_upper_5050_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; uint8_t v___x_5081_; 
v_numParams_5042_ = lean_ctor_get(v_val_5028_, 0);
v_numDiscrs_5043_ = lean_ctor_get(v_val_5028_, 1);
v___x_5044_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5042_);
lean_inc_ref(v_xs_5035_);
v___x_5045_ = l_Array_toSubarray___redArg(v_xs_5035_, v___x_5044_, v_numParams_5042_);
v___x_5046_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5028_);
v___x_5047_ = lean_array_get(v___x_5029_, v_xs_5035_, v___x_5046_);
lean_dec(v___x_5046_);
v___x_5078_ = lean_array_get_size(v_xs_5035_);
v___x_5079_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5028_);
v___x_5080_ = lean_nat_sub(v___x_5078_, v___x_5079_);
lean_dec(v___x_5079_);
v___x_5081_ = lean_nat_dec_le(v___x_5080_, v___x_5044_);
if (v___x_5081_ == 0)
{
v_lower_5049_ = v___x_5080_;
v_upper_5050_ = v___x_5078_;
goto v___jp_5048_;
}
else
{
lean_dec(v___x_5080_);
v_lower_5049_ = v___x_5044_;
v_upper_5050_ = v___x_5078_;
goto v___jp_5048_;
}
v___jp_5048_:
{
lean_object* v___x_5051_; lean_object* v_start_5052_; lean_object* v_stop_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
lean_inc_ref(v_xs_5035_);
v___x_5051_ = l_Array_toSubarray___redArg(v_xs_5035_, v_lower_5049_, v_upper_5050_);
v_start_5052_ = lean_ctor_get(v___x_5051_, 1);
lean_inc(v_start_5052_);
v_stop_5053_ = lean_ctor_get(v___x_5051_, 2);
lean_inc(v_stop_5053_);
v___x_5054_ = lean_unsigned_to_nat(1u);
v___x_5055_ = lean_nat_add(v_numParams_5042_, v___x_5054_);
v___x_5056_ = lean_nat_add(v___x_5055_, v_numDiscrs_5043_);
v___x_5057_ = lean_nat_sub(v_stop_5053_, v_start_5052_);
lean_dec(v_start_5052_);
lean_dec(v_stop_5053_);
v___x_5058_ = l_Array_toSubarray___redArg(v_xs_5035_, v___x_5055_, v___x_5056_);
v___x_5059_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5057_);
v___x_5060_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5057_, v_val_5028_, v_matchDeclName_5030_, v___x_5058_, v___x_5031_, v_a_5032_, v___x_5033_, v___x_5045_, v___x_5047_, v___x_5051_, v___x_5057_, v___x_5034_, v___x_5044_, v___x_5059_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
lean_dec(v___x_5057_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5068_; 
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5068_ == 0)
{
lean_object* v_unused_5069_; 
v_unused_5069_ = lean_ctor_get(v___x_5060_, 0);
lean_dec(v_unused_5069_);
v___x_5062_ = v___x_5060_;
v_isShared_5063_ = v_isSharedCheck_5068_;
goto v_resetjp_5061_;
}
else
{
lean_dec(v___x_5060_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5068_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5064_; lean_object* v___x_5066_; 
v___x_5064_ = lean_box(0);
if (v_isShared_5063_ == 0)
{
lean_ctor_set(v___x_5062_, 0, v___x_5064_);
v___x_5066_ = v___x_5062_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v___x_5064_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
else
{
lean_object* v_a_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5077_; 
v_a_5070_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5077_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5077_ == 0)
{
v___x_5072_ = v___x_5060_;
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_a_5070_);
lean_dec(v___x_5060_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5077_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v___x_5075_; 
if (v_isShared_5073_ == 0)
{
v___x_5075_ = v___x_5072_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_a_5070_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5082_, lean_object* v___x_5083_, lean_object* v_matchDeclName_5084_, lean_object* v___x_5085_, lean_object* v_a_5086_, lean_object* v___x_5087_, lean_object* v___x_5088_, lean_object* v_xs_5089_, lean_object* v___matchResultType_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_){
_start:
{
lean_object* v_res_5096_; 
v_res_5096_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5082_, v___x_5083_, v_matchDeclName_5084_, v___x_5085_, v_a_5086_, v___x_5087_, v___x_5088_, v_xs_5089_, v___matchResultType_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_);
lean_dec(v___y_5094_);
lean_dec_ref(v___y_5093_);
lean_dec(v___y_5092_);
lean_dec_ref(v___y_5091_);
lean_dec_ref(v___matchResultType_5090_);
lean_dec_ref(v___x_5083_);
return v_res_5096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
uint8_t v_trackZetaDelta_5103_; lean_object* v_zetaDeltaSet_5104_; lean_object* v_lctx_5105_; lean_object* v_localInstances_5106_; lean_object* v_defEqCtx_x3f_5107_; lean_object* v_synthPendingDepth_5108_; lean_object* v_customCanUnfoldPredicate_x3f_5109_; uint8_t v_univApprox_5110_; uint8_t v_inTypeClassResolution_5111_; uint8_t v_cacheInferType_5112_; lean_object* v___x_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5156_; 
v_trackZetaDelta_5103_ = lean_ctor_get_uint8(v_a_5098_, sizeof(void*)*7);
v_zetaDeltaSet_5104_ = lean_ctor_get(v_a_5098_, 1);
lean_inc(v_zetaDeltaSet_5104_);
v_lctx_5105_ = lean_ctor_get(v_a_5098_, 2);
lean_inc_ref(v_lctx_5105_);
v_localInstances_5106_ = lean_ctor_get(v_a_5098_, 3);
lean_inc_ref(v_localInstances_5106_);
v_defEqCtx_x3f_5107_ = lean_ctor_get(v_a_5098_, 4);
lean_inc(v_defEqCtx_x3f_5107_);
v_synthPendingDepth_5108_ = lean_ctor_get(v_a_5098_, 5);
lean_inc(v_synthPendingDepth_5108_);
v_customCanUnfoldPredicate_x3f_5109_ = lean_ctor_get(v_a_5098_, 6);
lean_inc(v_customCanUnfoldPredicate_x3f_5109_);
v_univApprox_5110_ = lean_ctor_get_uint8(v_a_5098_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5111_ = lean_ctor_get_uint8(v_a_5098_, sizeof(void*)*7 + 2);
v_cacheInferType_5112_ = lean_ctor_get_uint8(v_a_5098_, sizeof(void*)*7 + 3);
v___x_5113_ = l_Lean_Meta_Context_config(v_a_5098_);
v_isSharedCheck_5156_ = !lean_is_exclusive(v_a_5098_);
if (v_isSharedCheck_5156_ == 0)
{
lean_object* v_unused_5157_; lean_object* v_unused_5158_; lean_object* v_unused_5159_; lean_object* v_unused_5160_; lean_object* v_unused_5161_; lean_object* v_unused_5162_; lean_object* v_unused_5163_; 
v_unused_5157_ = lean_ctor_get(v_a_5098_, 6);
lean_dec(v_unused_5157_);
v_unused_5158_ = lean_ctor_get(v_a_5098_, 5);
lean_dec(v_unused_5158_);
v_unused_5159_ = lean_ctor_get(v_a_5098_, 4);
lean_dec(v_unused_5159_);
v_unused_5160_ = lean_ctor_get(v_a_5098_, 3);
lean_dec(v_unused_5160_);
v_unused_5161_ = lean_ctor_get(v_a_5098_, 2);
lean_dec(v_unused_5161_);
v_unused_5162_ = lean_ctor_get(v_a_5098_, 1);
lean_dec(v_unused_5162_);
v_unused_5163_ = lean_ctor_get(v_a_5098_, 0);
lean_dec(v_unused_5163_);
v___x_5115_ = v_a_5098_;
v_isShared_5116_ = v_isSharedCheck_5156_;
goto v_resetjp_5114_;
}
else
{
lean_dec(v_a_5098_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5156_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5117_; uint64_t v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5121_; 
v___x_5117_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5113_);
v___x_5118_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5117_);
v___x_5119_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5119_, 0, v___x_5117_);
lean_ctor_set_uint64(v___x_5119_, sizeof(void*)*1, v___x_5118_);
lean_inc(v_customCanUnfoldPredicate_x3f_5109_);
lean_inc(v_synthPendingDepth_5108_);
lean_inc(v_defEqCtx_x3f_5107_);
lean_inc_ref(v_localInstances_5106_);
lean_inc_ref(v_lctx_5105_);
lean_inc(v_zetaDeltaSet_5104_);
if (v_isShared_5116_ == 0)
{
lean_ctor_set(v___x_5115_, 0, v___x_5119_);
v___x_5121_ = v___x_5115_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5119_);
lean_ctor_set(v_reuseFailAlloc_5155_, 1, v_zetaDeltaSet_5104_);
lean_ctor_set(v_reuseFailAlloc_5155_, 2, v_lctx_5105_);
lean_ctor_set(v_reuseFailAlloc_5155_, 3, v_localInstances_5106_);
lean_ctor_set(v_reuseFailAlloc_5155_, 4, v_defEqCtx_x3f_5107_);
lean_ctor_set(v_reuseFailAlloc_5155_, 5, v_synthPendingDepth_5108_);
lean_ctor_set(v_reuseFailAlloc_5155_, 6, v_customCanUnfoldPredicate_x3f_5109_);
lean_ctor_set_uint8(v_reuseFailAlloc_5155_, sizeof(void*)*7, v_trackZetaDelta_5103_);
lean_ctor_set_uint8(v_reuseFailAlloc_5155_, sizeof(void*)*7 + 1, v_univApprox_5110_);
lean_ctor_set_uint8(v_reuseFailAlloc_5155_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5111_);
lean_ctor_set_uint8(v_reuseFailAlloc_5155_, sizeof(void*)*7 + 3, v_cacheInferType_5112_);
v___x_5121_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; uint64_t v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v___x_5122_ = l_Lean_Meta_Context_config(v___x_5121_);
lean_dec_ref(v___x_5121_);
v___x_5123_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5122_);
v___x_5124_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5123_);
v___x_5125_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5125_, 0, v___x_5123_);
lean_ctor_set_uint64(v___x_5125_, sizeof(void*)*1, v___x_5124_);
v___x_5126_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5126_, 0, v___x_5125_);
lean_ctor_set(v___x_5126_, 1, v_zetaDeltaSet_5104_);
lean_ctor_set(v___x_5126_, 2, v_lctx_5105_);
lean_ctor_set(v___x_5126_, 3, v_localInstances_5106_);
lean_ctor_set(v___x_5126_, 4, v_defEqCtx_x3f_5107_);
lean_ctor_set(v___x_5126_, 5, v_synthPendingDepth_5108_);
lean_ctor_set(v___x_5126_, 6, v_customCanUnfoldPredicate_x3f_5109_);
lean_ctor_set_uint8(v___x_5126_, sizeof(void*)*7, v_trackZetaDelta_5103_);
lean_ctor_set_uint8(v___x_5126_, sizeof(void*)*7 + 1, v_univApprox_5110_);
lean_ctor_set_uint8(v___x_5126_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5111_);
lean_ctor_set_uint8(v___x_5126_, sizeof(void*)*7 + 3, v_cacheInferType_5112_);
lean_inc(v_matchDeclName_5097_);
v___x_5127_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5097_, v___x_5126_, v_a_5099_, v_a_5100_, v_a_5101_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; lean_object* v___x_5129_; lean_object* v_a_5130_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
lean_inc(v_a_5128_);
lean_dec_ref_known(v___x_5127_, 1);
lean_inc(v_matchDeclName_5097_);
v___x_5129_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5097_, v_a_5101_);
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref(v___x_5129_);
if (lean_obj_tag(v_a_5130_) == 1)
{
lean_object* v_val_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___f_5137_; lean_object* v___x_5138_; uint8_t v___x_5139_; lean_object* v___x_5140_; 
v_val_5131_ = lean_ctor_get(v_a_5130_, 0);
lean_inc(v_val_5131_);
lean_dec_ref_known(v_a_5130_, 1);
v___x_5132_ = l_Lean_instInhabitedExpr;
v___x_5133_ = l_Lean_ConstantInfo_levelParams(v_a_5128_);
v___x_5134_ = lean_box(0);
lean_inc(v___x_5133_);
v___x_5135_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_5133_, v___x_5134_);
v___x_5136_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5131_);
lean_inc(v_a_5128_);
v___f_5137_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5137_, 0, v_val_5131_);
lean_closure_set(v___f_5137_, 1, v___x_5132_);
lean_closure_set(v___f_5137_, 2, v_matchDeclName_5097_);
lean_closure_set(v___f_5137_, 3, v___x_5136_);
lean_closure_set(v___f_5137_, 4, v_a_5128_);
lean_closure_set(v___f_5137_, 5, v___x_5135_);
lean_closure_set(v___f_5137_, 6, v___x_5133_);
v___x_5138_ = l_Lean_ConstantInfo_type(v_a_5128_);
lean_dec(v_a_5128_);
v___x_5139_ = 0;
v___x_5140_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5138_, v___f_5137_, v___x_5139_, v___x_5139_, v___x_5126_, v_a_5099_, v_a_5100_, v_a_5101_);
lean_dec_ref_known(v___x_5126_, 7);
return v___x_5140_;
}
else
{
lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; 
lean_dec(v_a_5130_);
lean_dec(v_a_5128_);
v___x_5141_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5142_ = l_Lean_MessageData_ofName(v_matchDeclName_5097_);
v___x_5143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5141_);
lean_ctor_set(v___x_5143_, 1, v___x_5142_);
v___x_5144_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5143_);
lean_ctor_set(v___x_5145_, 1, v___x_5144_);
v___x_5146_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5145_, v___x_5126_, v_a_5099_, v_a_5100_, v_a_5101_);
lean_dec_ref_known(v___x_5126_, 7);
return v___x_5146_;
}
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
lean_dec_ref_known(v___x_5126_, 7);
lean_dec(v_matchDeclName_5097_);
v_a_5147_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5127_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5127_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_){
_start:
{
lean_object* v_res_5170_; 
v_res_5170_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
lean_dec(v_a_5168_);
lean_dec_ref(v_a_5167_);
lean_dec(v_a_5166_);
return v_res_5170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v_inst_5171_, lean_object* v_R_5172_, lean_object* v_a_5173_, lean_object* v_b_5174_, lean_object* v_c_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_){
_start:
{
lean_object* v___x_5181_; 
v___x_5181_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_5173_, v_b_5174_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v_inst_5182_, lean_object* v_R_5183_, lean_object* v_a_5184_, lean_object* v_b_5185_, lean_object* v_c_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_inst_5182_, v_R_5183_, v_a_5184_, v_b_5185_, v_c_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5193_, lean_object* v_val_5194_, lean_object* v_matchDeclName_5195_, lean_object* v___x_5196_, lean_object* v___x_5197_, lean_object* v_a_5198_, lean_object* v___x_5199_, lean_object* v___x_5200_, lean_object* v___x_5201_, lean_object* v___x_5202_, lean_object* v___x_5203_, lean_object* v___x_5204_, lean_object* v_inst_5205_, lean_object* v_R_5206_, lean_object* v_a_5207_, lean_object* v_b_5208_, lean_object* v_c_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v___x_5215_; 
v___x_5215_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5193_, v_val_5194_, v_matchDeclName_5195_, v___x_5196_, v___x_5197_, v_a_5198_, v___x_5199_, v___x_5200_, v___x_5201_, v___x_5202_, v___x_5203_, v___x_5204_, v_a_5207_, v_b_5208_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
return v___x_5215_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5216_ = _args[0];
lean_object* v_val_5217_ = _args[1];
lean_object* v_matchDeclName_5218_ = _args[2];
lean_object* v___x_5219_ = _args[3];
lean_object* v___x_5220_ = _args[4];
lean_object* v_a_5221_ = _args[5];
lean_object* v___x_5222_ = _args[6];
lean_object* v___x_5223_ = _args[7];
lean_object* v___x_5224_ = _args[8];
lean_object* v___x_5225_ = _args[9];
lean_object* v___x_5226_ = _args[10];
lean_object* v___x_5227_ = _args[11];
lean_object* v_inst_5228_ = _args[12];
lean_object* v_R_5229_ = _args[13];
lean_object* v_a_5230_ = _args[14];
lean_object* v_b_5231_ = _args[15];
lean_object* v_c_5232_ = _args[16];
lean_object* v___y_5233_ = _args[17];
lean_object* v___y_5234_ = _args[18];
lean_object* v___y_5235_ = _args[19];
lean_object* v___y_5236_ = _args[20];
lean_object* v___y_5237_ = _args[21];
_start:
{
lean_object* v_res_5238_; 
v_res_5238_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5216_, v_val_5217_, v_matchDeclName_5218_, v___x_5219_, v___x_5220_, v_a_5221_, v___x_5222_, v___x_5223_, v___x_5224_, v___x_5225_, v___x_5226_, v___x_5227_, v_inst_5228_, v_R_5229_, v_a_5230_, v_b_5231_, v_c_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
lean_dec(v___y_5234_);
lean_dec_ref(v___y_5233_);
lean_dec(v_upperBound_5216_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5239_, lean_object* v_matchDeclName_5240_, lean_object* v_a_5241_, lean_object* v_b_5242_){
_start:
{
uint8_t v___x_5244_; 
v___x_5244_ = lean_nat_dec_lt(v_a_5241_, v_upperBound_5239_);
if (v___x_5244_ == 0)
{
lean_object* v___x_5245_; 
lean_dec(v_a_5241_);
lean_dec(v_matchDeclName_5240_);
v___x_5245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5245_, 0, v_b_5242_);
return v___x_5245_;
}
else
{
lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; 
v___x_5246_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5240_);
v___x_5247_ = l_Lean_Name_str___override(v_matchDeclName_5240_, v___x_5246_);
v___x_5248_ = lean_unsigned_to_nat(1u);
v___x_5249_ = lean_nat_add(v_a_5241_, v___x_5248_);
lean_dec(v_a_5241_);
lean_inc(v___x_5249_);
v___x_5250_ = lean_name_append_index_after(v___x_5247_, v___x_5249_);
v___x_5251_ = lean_array_push(v_b_5242_, v___x_5250_);
v_a_5241_ = v___x_5249_;
v_b_5242_ = v___x_5251_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5253_, lean_object* v_matchDeclName_5254_, lean_object* v_a_5255_, lean_object* v_b_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5253_, v_matchDeclName_5254_, v_a_5255_, v_b_5256_);
lean_dec(v_upperBound_5253_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_, lean_object* v_a_5263_){
_start:
{
lean_object* v___x_5265_; lean_object* v_firstEqnName_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5265_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5259_, 3);
v_firstEqnName_5266_ = l_Lean_Name_str___override(v_matchDeclName_5259_, v___x_5265_);
v___x_5267_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5267_, 0, v_matchDeclName_5259_);
v___x_5268_ = l_Lean_Meta_realizeConst(v_matchDeclName_5259_, v_firstEqnName_5266_, v___x_5267_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_);
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_object* v___x_5269_; lean_object* v_a_5270_; 
lean_dec_ref_known(v___x_5268_, 1);
lean_inc(v_matchDeclName_5259_);
v___x_5269_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5259_, v_a_5263_);
v_a_5270_ = lean_ctor_get(v___x_5269_, 0);
lean_inc(v_a_5270_);
lean_dec_ref(v___x_5269_);
if (lean_obj_tag(v_a_5270_) == 1)
{
lean_object* v_val_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; 
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
v_val_5271_ = lean_ctor_get(v_a_5270_, 0);
lean_inc(v_val_5271_);
lean_dec_ref_known(v_a_5270_, 1);
v___x_5272_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5271_);
lean_dec(v_val_5271_);
v___x_5273_ = lean_unsigned_to_nat(0u);
v___x_5274_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5275_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5272_, v_matchDeclName_5259_, v___x_5273_, v___x_5274_);
lean_dec(v___x_5272_);
return v___x_5275_;
}
else
{
lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
lean_dec(v_a_5270_);
v___x_5276_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5277_ = l_Lean_MessageData_ofName(v_matchDeclName_5259_);
v___x_5278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5276_);
lean_ctor_set(v___x_5278_, 1, v___x_5277_);
v___x_5279_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5278_);
lean_ctor_set(v___x_5280_, 1, v___x_5279_);
v___x_5281_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5280_, v_a_5260_, v_a_5261_, v_a_5262_, v_a_5263_);
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
return v___x_5281_;
}
}
else
{
lean_object* v_a_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5289_; 
lean_dec(v_a_5263_);
lean_dec_ref(v_a_5262_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
lean_dec(v_matchDeclName_5259_);
v_a_5282_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5284_ = v___x_5268_;
v_isShared_5285_ = v_isSharedCheck_5289_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_a_5282_);
lean_dec(v___x_5268_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5289_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
lean_object* v___x_5287_; 
if (v_isShared_5285_ == 0)
{
v___x_5287_ = v___x_5284_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_a_5282_);
v___x_5287_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5286_;
}
v_reusejp_5286_:
{
return v___x_5287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = lean_get_congr_match_equations_for(v_matchDeclName_5290_, v_a_5291_, v_a_5292_, v_a_5293_, v_a_5294_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5297_, lean_object* v_matchDeclName_5298_, lean_object* v_inst_5299_, lean_object* v_R_5300_, lean_object* v_a_5301_, lean_object* v_b_5302_, lean_object* v_c_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_){
_start:
{
lean_object* v___x_5309_; 
v___x_5309_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5297_, v_matchDeclName_5298_, v_a_5301_, v_b_5302_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5310_, lean_object* v_matchDeclName_5311_, lean_object* v_inst_5312_, lean_object* v_R_5313_, lean_object* v_a_5314_, lean_object* v_b_5315_, lean_object* v_c_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5310_, v_matchDeclName_5311_, v_inst_5312_, v_R_5313_, v_a_5314_, v_b_5315_, v_c_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec(v_upperBound_5310_);
return v_res_5322_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; 
v___x_5373_ = lean_unsigned_to_nat(3248161880u);
v___x_5374_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5375_ = l_Lean_Name_num___override(v___x_5374_, v___x_5373_);
return v___x_5375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; 
v___x_5377_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5378_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5379_ = l_Lean_Name_str___override(v___x_5378_, v___x_5377_);
return v___x_5379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
v___x_5381_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5382_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5383_ = l_Lean_Name_str___override(v___x_5382_, v___x_5381_);
return v___x_5383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5384_ = lean_unsigned_to_nat(2u);
v___x_5385_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5386_ = l_Lean_Name_num___override(v___x_5385_, v___x_5384_);
return v___x_5386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5388_; uint8_t v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; 
v___x_5388_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5389_ = 0;
v___x_5390_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5391_ = l_Lean_registerTraceClass(v___x_5388_, v___x_5389_, v___x_5390_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5392_){
_start:
{
lean_object* v_res_5393_; 
v_res_5393_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5394_, lean_object* v_n_5395_){
_start:
{
if (lean_obj_tag(v_n_5395_) == 1)
{
lean_object* v_pre_5396_; lean_object* v_str_5397_; uint8_t v___y_5399_; uint8_t v___x_5405_; 
v_pre_5396_ = lean_ctor_get(v_n_5395_, 0);
lean_inc(v_pre_5396_);
v_str_5397_ = lean_ctor_get(v_n_5395_, 1);
lean_inc_ref_n(v_str_5397_, 2);
lean_dec_ref_known(v_n_5395_, 2);
v___x_5405_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5397_);
if (v___x_5405_ == 0)
{
lean_object* v___x_5406_; uint8_t v___x_5407_; 
v___x_5406_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5407_ = lean_string_dec_eq(v_str_5397_, v___x_5406_);
lean_dec_ref(v_str_5397_);
v___y_5399_ = v___x_5407_;
goto v___jp_5398_;
}
else
{
lean_dec_ref(v_str_5397_);
v___y_5399_ = v___x_5405_;
goto v___jp_5398_;
}
v___jp_5398_:
{
if (v___y_5399_ == 0)
{
lean_object* v___x_5400_; 
lean_dec(v_pre_5396_);
lean_dec_ref(v_env_5394_);
v___x_5400_ = lean_box(0);
return v___x_5400_;
}
else
{
lean_object* v___x_5401_; 
v___x_5401_ = l_Lean_privateToUserName_x3f(v_pre_5396_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_dec_ref(v_env_5394_);
return v___x_5401_;
}
else
{
lean_object* v_val_5402_; uint8_t v___x_5403_; 
v_val_5402_ = lean_ctor_get(v___x_5401_, 0);
lean_inc(v_val_5402_);
v___x_5403_ = l_Lean_Meta_isMatcherCore(v_env_5394_, v_val_5402_);
if (v___x_5403_ == 0)
{
lean_object* v___x_5404_; 
lean_dec_ref_known(v___x_5401_, 1);
v___x_5404_ = lean_box(0);
return v___x_5404_;
}
else
{
return v___x_5401_;
}
}
}
}
}
else
{
lean_object* v___x_5408_; 
lean_dec(v_n_5395_);
lean_dec_ref(v_env_5394_);
v___x_5408_ = lean_box(0);
return v___x_5408_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5409_, lean_object* v_x2_5410_){
_start:
{
lean_object* v___x_5411_; 
v___x_5411_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5409_, v_x2_5410_);
if (lean_obj_tag(v___x_5411_) == 0)
{
uint8_t v___x_5412_; 
v___x_5412_ = 0;
return v___x_5412_;
}
else
{
uint8_t v___x_5413_; 
lean_dec_ref_known(v___x_5411_, 1);
v___x_5413_ = 1;
return v___x_5413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5414_, lean_object* v_x2_5415_){
_start:
{
uint8_t v_res_5416_; lean_object* v_r_5417_; 
v_res_5416_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5414_, v_x2_5415_);
v_r_5417_ = lean_box(v_res_5416_);
return v_r_5417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5420_; lean_object* v___x_5421_; 
v___f_5420_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5421_ = l_Lean_registerReservedNamePredicate(v___f_5420_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5422_){
_start:
{
lean_object* v_res_5423_; 
v_res_5423_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5423_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5430_; uint64_t v___x_5431_; 
v___x_5430_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5431_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5430_);
return v___x_5431_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; 
v___x_5432_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5433_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5434_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5434_, 0, v___x_5433_);
lean_ctor_set_uint64(v___x_5434_, sizeof(void*)*1, v___x_5432_);
return v___x_5434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
v___x_5437_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5438_ = lean_unsigned_to_nat(0u);
v___x_5439_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5439_, 0, v___x_5438_);
lean_ctor_set(v___x_5439_, 1, v___x_5438_);
lean_ctor_set(v___x_5439_, 2, v___x_5438_);
lean_ctor_set(v___x_5439_, 3, v___x_5438_);
lean_ctor_set(v___x_5439_, 4, v___x_5437_);
lean_ctor_set(v___x_5439_, 5, v___x_5437_);
lean_ctor_set(v___x_5439_, 6, v___x_5437_);
lean_ctor_set(v___x_5439_, 7, v___x_5437_);
lean_ctor_set(v___x_5439_, 8, v___x_5437_);
lean_ctor_set(v___x_5439_, 9, v___x_5437_);
lean_ctor_set(v___x_5439_, 10, v___x_5437_);
return v___x_5439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5440_; lean_object* v___x_5441_; 
v___x_5440_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5441_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5441_, 0, v___x_5440_);
lean_ctor_set(v___x_5441_, 1, v___x_5440_);
lean_ctor_set(v___x_5441_, 2, v___x_5440_);
lean_ctor_set(v___x_5441_, 3, v___x_5440_);
lean_ctor_set(v___x_5441_, 4, v___x_5440_);
lean_ctor_set(v___x_5441_, 5, v___x_5440_);
return v___x_5441_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5442_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5442_);
lean_ctor_set(v___x_5443_, 1, v___x_5442_);
lean_ctor_set(v___x_5443_, 2, v___x_5442_);
lean_ctor_set(v___x_5443_, 3, v___x_5442_);
lean_ctor_set(v___x_5443_, 4, v___x_5442_);
return v___x_5443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5444_, lean_object* v_name_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v___x_5449_; lean_object* v_env_5450_; lean_object* v___x_5451_; 
v___x_5449_ = lean_st_ref_get(v___y_5447_);
v_env_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc_ref(v_env_5450_);
lean_dec(v___x_5449_);
v___x_5451_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5450_, v_name_5445_);
if (lean_obj_tag(v___x_5451_) == 1)
{
lean_object* v_val_5452_; uint8_t v___x_5453_; uint8_t v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; 
v_val_5452_ = lean_ctor_get(v___x_5451_, 0);
lean_inc(v_val_5452_);
lean_dec_ref_known(v___x_5451_, 1);
v___x_5453_ = 0;
v___x_5454_ = 1;
v___x_5455_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5456_ = lean_unsigned_to_nat(0u);
v___x_5457_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5458_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5459_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5460_ = lean_box(0);
lean_inc(v___x_5444_);
v___x_5461_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5461_, 0, v___x_5455_);
lean_ctor_set(v___x_5461_, 1, v___x_5444_);
lean_ctor_set(v___x_5461_, 2, v___x_5458_);
lean_ctor_set(v___x_5461_, 3, v___x_5459_);
lean_ctor_set(v___x_5461_, 4, v___x_5460_);
lean_ctor_set(v___x_5461_, 5, v___x_5456_);
lean_ctor_set(v___x_5461_, 6, v___x_5460_);
lean_ctor_set_uint8(v___x_5461_, sizeof(void*)*7, v___x_5453_);
lean_ctor_set_uint8(v___x_5461_, sizeof(void*)*7 + 1, v___x_5453_);
lean_ctor_set_uint8(v___x_5461_, sizeof(void*)*7 + 2, v___x_5453_);
lean_ctor_set_uint8(v___x_5461_, sizeof(void*)*7 + 3, v___x_5454_);
v___x_5462_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5463_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5464_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5465_, 0, v___x_5462_);
lean_ctor_set(v___x_5465_, 1, v___x_5463_);
lean_ctor_set(v___x_5465_, 2, v___x_5444_);
lean_ctor_set(v___x_5465_, 3, v___x_5457_);
lean_ctor_set(v___x_5465_, 4, v___x_5464_);
v___x_5466_ = lean_st_mk_ref(v___x_5465_);
lean_inc(v___y_5447_);
lean_inc_ref(v___y_5446_);
lean_inc(v___x_5466_);
v___x_5467_ = lean_get_match_equations_for(v_val_5452_, v___x_5461_, v___x_5466_, v___y_5446_, v___y_5447_);
if (lean_obj_tag(v___x_5467_) == 0)
{
lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5476_; 
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5467_);
if (v_isSharedCheck_5476_ == 0)
{
lean_object* v_unused_5477_; 
v_unused_5477_ = lean_ctor_get(v___x_5467_, 0);
lean_dec(v_unused_5477_);
v___x_5469_ = v___x_5467_;
v_isShared_5470_ = v_isSharedCheck_5476_;
goto v_resetjp_5468_;
}
else
{
lean_dec(v___x_5467_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5476_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5474_; 
v___x_5471_ = lean_st_ref_get(v___x_5466_);
lean_dec(v___x_5466_);
lean_dec(v___x_5471_);
v___x_5472_ = lean_box(v___x_5454_);
if (v_isShared_5470_ == 0)
{
lean_ctor_set(v___x_5469_, 0, v___x_5472_);
v___x_5474_ = v___x_5469_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v___x_5472_);
v___x_5474_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
return v___x_5474_;
}
}
}
else
{
lean_dec(v___x_5466_);
if (lean_obj_tag(v___x_5467_) == 0)
{
lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5485_; 
v_isSharedCheck_5485_ = !lean_is_exclusive(v___x_5467_);
if (v_isSharedCheck_5485_ == 0)
{
lean_object* v_unused_5486_; 
v_unused_5486_ = lean_ctor_get(v___x_5467_, 0);
lean_dec(v_unused_5486_);
v___x_5479_ = v___x_5467_;
v_isShared_5480_ = v_isSharedCheck_5485_;
goto v_resetjp_5478_;
}
else
{
lean_dec(v___x_5467_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5485_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v___x_5481_; lean_object* v___x_5483_; 
v___x_5481_ = lean_box(v___x_5454_);
if (v_isShared_5480_ == 0)
{
lean_ctor_set_tag(v___x_5479_, 0);
lean_ctor_set(v___x_5479_, 0, v___x_5481_);
v___x_5483_ = v___x_5479_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5481_);
v___x_5483_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
return v___x_5483_;
}
}
}
else
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
v_a_5487_ = lean_ctor_get(v___x_5467_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5467_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5467_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5467_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
if (v_isShared_5490_ == 0)
{
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
}
else
{
uint8_t v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; 
lean_dec(v___x_5451_);
lean_dec(v___x_5444_);
v___x_5495_ = 0;
v___x_5496_ = lean_box(v___x_5495_);
v___x_5497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5497_, 0, v___x_5496_);
return v___x_5497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5498_, lean_object* v_name_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_){
_start:
{
lean_object* v_res_5503_; 
v_res_5503_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5498_, v_name_5499_, v___y_5500_, v___y_5501_);
lean_dec(v___y_5501_);
lean_dec_ref(v___y_5500_);
return v_res_5503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5507_; lean_object* v___x_5508_; 
v___f_5507_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5508_ = l_Lean_registerReservedNameAction(v___f_5507_);
return v___x_5508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5509_){
_start:
{
lean_object* v_res_5510_; 
v_res_5510_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5511_, lean_object* v_n_5512_){
_start:
{
if (lean_obj_tag(v_n_5512_) == 1)
{
lean_object* v_pre_5513_; lean_object* v_str_5514_; uint8_t v___x_5515_; 
v_pre_5513_ = lean_ctor_get(v_n_5512_, 0);
lean_inc(v_pre_5513_);
v_str_5514_ = lean_ctor_get(v_n_5512_, 1);
lean_inc_ref(v_str_5514_);
lean_dec_ref_known(v_n_5512_, 2);
v___x_5515_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5514_);
if (v___x_5515_ == 0)
{
lean_object* v___x_5516_; 
lean_dec(v_pre_5513_);
lean_dec_ref(v_env_5511_);
v___x_5516_ = lean_box(0);
return v___x_5516_;
}
else
{
uint8_t v___x_5517_; 
lean_inc(v_pre_5513_);
v___x_5517_ = l_Lean_Meta_isMatcherCore(v_env_5511_, v_pre_5513_);
if (v___x_5517_ == 0)
{
lean_object* v___x_5518_; 
lean_dec(v_pre_5513_);
v___x_5518_ = lean_box(0);
return v___x_5518_;
}
else
{
lean_object* v___x_5519_; 
v___x_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5519_, 0, v_pre_5513_);
return v___x_5519_;
}
}
}
else
{
lean_object* v___x_5520_; 
lean_dec(v_n_5512_);
lean_dec_ref(v_env_5511_);
v___x_5520_ = lean_box(0);
return v___x_5520_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5521_, lean_object* v_x2_5522_){
_start:
{
lean_object* v___x_5523_; 
v___x_5523_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5521_, v_x2_5522_);
if (lean_obj_tag(v___x_5523_) == 0)
{
uint8_t v___x_5524_; 
v___x_5524_ = 0;
return v___x_5524_;
}
else
{
uint8_t v___x_5525_; 
lean_dec_ref_known(v___x_5523_, 1);
v___x_5525_ = 1;
return v___x_5525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5526_, lean_object* v_x2_5527_){
_start:
{
uint8_t v_res_5528_; lean_object* v_r_5529_; 
v_res_5528_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5526_, v_x2_5527_);
v_r_5529_ = lean_box(v_res_5528_);
return v_r_5529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5532_; lean_object* v___x_5533_; 
v___f_5532_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5533_ = l_Lean_registerReservedNamePredicate(v___f_5532_);
return v___x_5533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5534_){
_start:
{
lean_object* v_res_5535_; 
v_res_5535_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5536_, lean_object* v_name_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_){
_start:
{
lean_object* v___x_5541_; lean_object* v_env_5542_; lean_object* v___x_5543_; 
v___x_5541_ = lean_st_ref_get(v___y_5539_);
v_env_5542_ = lean_ctor_get(v___x_5541_, 0);
lean_inc_ref(v_env_5542_);
lean_dec(v___x_5541_);
v___x_5543_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5542_, v_name_5537_);
if (lean_obj_tag(v___x_5543_) == 1)
{
lean_object* v_val_5544_; uint8_t v___x_5545_; uint8_t v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; 
v_val_5544_ = lean_ctor_get(v___x_5543_, 0);
lean_inc(v_val_5544_);
lean_dec_ref_known(v___x_5543_, 1);
v___x_5545_ = 0;
v___x_5546_ = 1;
v___x_5547_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5548_ = lean_unsigned_to_nat(32u);
v___x_5549_ = lean_mk_empty_array_with_capacity(v___x_5548_);
lean_dec_ref(v___x_5549_);
v___x_5550_ = lean_unsigned_to_nat(0u);
v___x_5551_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5552_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5553_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5554_ = lean_box(0);
lean_inc(v___x_5536_);
v___x_5555_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5555_, 0, v___x_5547_);
lean_ctor_set(v___x_5555_, 1, v___x_5536_);
lean_ctor_set(v___x_5555_, 2, v___x_5552_);
lean_ctor_set(v___x_5555_, 3, v___x_5553_);
lean_ctor_set(v___x_5555_, 4, v___x_5554_);
lean_ctor_set(v___x_5555_, 5, v___x_5550_);
lean_ctor_set(v___x_5555_, 6, v___x_5554_);
lean_ctor_set_uint8(v___x_5555_, sizeof(void*)*7, v___x_5545_);
lean_ctor_set_uint8(v___x_5555_, sizeof(void*)*7 + 1, v___x_5545_);
lean_ctor_set_uint8(v___x_5555_, sizeof(void*)*7 + 2, v___x_5545_);
lean_ctor_set_uint8(v___x_5555_, sizeof(void*)*7 + 3, v___x_5546_);
v___x_5556_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5557_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5558_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5559_, 0, v___x_5556_);
lean_ctor_set(v___x_5559_, 1, v___x_5557_);
lean_ctor_set(v___x_5559_, 2, v___x_5536_);
lean_ctor_set(v___x_5559_, 3, v___x_5551_);
lean_ctor_set(v___x_5559_, 4, v___x_5558_);
v___x_5560_ = lean_st_mk_ref(v___x_5559_);
lean_inc(v___y_5539_);
lean_inc_ref(v___y_5538_);
lean_inc(v___x_5560_);
v___x_5561_ = lean_get_congr_match_equations_for(v_val_5544_, v___x_5555_, v___x_5560_, v___y_5538_, v___y_5539_);
if (lean_obj_tag(v___x_5561_) == 0)
{
lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5570_; 
v_isSharedCheck_5570_ = !lean_is_exclusive(v___x_5561_);
if (v_isSharedCheck_5570_ == 0)
{
lean_object* v_unused_5571_; 
v_unused_5571_ = lean_ctor_get(v___x_5561_, 0);
lean_dec(v_unused_5571_);
v___x_5563_ = v___x_5561_;
v_isShared_5564_ = v_isSharedCheck_5570_;
goto v_resetjp_5562_;
}
else
{
lean_dec(v___x_5561_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5570_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5568_; 
v___x_5565_ = lean_st_ref_get(v___x_5560_);
lean_dec(v___x_5560_);
lean_dec(v___x_5565_);
v___x_5566_ = lean_box(v___x_5546_);
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 0, v___x_5566_);
v___x_5568_ = v___x_5563_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v___x_5566_);
v___x_5568_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
return v___x_5568_;
}
}
}
else
{
lean_dec(v___x_5560_);
if (lean_obj_tag(v___x_5561_) == 0)
{
lean_object* v___x_5573_; uint8_t v_isShared_5574_; uint8_t v_isSharedCheck_5579_; 
v_isSharedCheck_5579_ = !lean_is_exclusive(v___x_5561_);
if (v_isSharedCheck_5579_ == 0)
{
lean_object* v_unused_5580_; 
v_unused_5580_ = lean_ctor_get(v___x_5561_, 0);
lean_dec(v_unused_5580_);
v___x_5573_ = v___x_5561_;
v_isShared_5574_ = v_isSharedCheck_5579_;
goto v_resetjp_5572_;
}
else
{
lean_dec(v___x_5561_);
v___x_5573_ = lean_box(0);
v_isShared_5574_ = v_isSharedCheck_5579_;
goto v_resetjp_5572_;
}
v_resetjp_5572_:
{
lean_object* v___x_5575_; lean_object* v___x_5577_; 
v___x_5575_ = lean_box(v___x_5546_);
if (v_isShared_5574_ == 0)
{
lean_ctor_set_tag(v___x_5573_, 0);
lean_ctor_set(v___x_5573_, 0, v___x_5575_);
v___x_5577_ = v___x_5573_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5575_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
return v___x_5577_;
}
}
}
else
{
lean_object* v_a_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5588_; 
v_a_5581_ = lean_ctor_get(v___x_5561_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v___x_5561_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5583_ = v___x_5561_;
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_a_5581_);
lean_dec(v___x_5561_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v___x_5586_; 
if (v_isShared_5584_ == 0)
{
v___x_5586_ = v___x_5583_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5581_);
v___x_5586_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
return v___x_5586_;
}
}
}
}
}
else
{
uint8_t v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; 
lean_dec(v___x_5543_);
lean_dec(v___x_5536_);
v___x_5589_ = 0;
v___x_5590_ = lean_box(v___x_5589_);
v___x_5591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5591_, 0, v___x_5590_);
return v___x_5591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5592_, lean_object* v_name_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_){
_start:
{
lean_object* v_res_5597_; 
v_res_5597_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5592_, v_name_5593_, v___y_5594_, v___y_5595_);
lean_dec(v___y_5595_);
lean_dec_ref(v___y_5594_);
return v_res_5597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5601_; lean_object* v___x_5602_; 
v___f_5601_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5602_ = l_Lean_registerReservedNameAction(v___f_5601_);
return v___x_5602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5603_){
_start:
{
lean_object* v_res_5604_; 
v_res_5604_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5604_;
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
