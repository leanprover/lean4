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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
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
v_ref_1313_ = lean_ctor_get(v___y_1310_, 5);
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
v___x_1350_ = lean_st_ref_set(v___y_1311_, v___x_1349_);
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
lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v_a_1412_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; uint8_t v___y_1449_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; uint8_t v___y_1474_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v_a_1498_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; uint8_t v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; uint8_t v___y_1510_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; uint8_t v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v_a_1552_; lean_object* v___y_1556_; lean_object* v___y_1557_; uint8_t v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; uint8_t v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; uint8_t v___y_1575_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; uint8_t v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; uint8_t v___y_1607_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; uint8_t v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; uint8_t v___y_1632_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; uint8_t v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; uint8_t v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; uint8_t v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v_fileName_1763_; lean_object* v_fileMap_1764_; lean_object* v_options_1765_; lean_object* v_currRecDepth_1766_; lean_object* v_maxRecDepth_1767_; lean_object* v_ref_1768_; lean_object* v_currNamespace_1769_; lean_object* v_openDecls_1770_; lean_object* v_initHeartbeats_1771_; lean_object* v_maxHeartbeats_1772_; lean_object* v_quotContext_1773_; lean_object* v_currMacroScope_1774_; uint8_t v_diag_1775_; lean_object* v_cancelTk_x3f_1776_; uint8_t v_suppressElabErrors_1777_; lean_object* v_inheritedTraceOptions_1778_; lean_object* v_cls_1779_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_fileName_1763_ = lean_ctor_get(v_a_1404_, 0);
v_fileMap_1764_ = lean_ctor_get(v_a_1404_, 1);
v_options_1765_ = lean_ctor_get(v_a_1404_, 2);
v_currRecDepth_1766_ = lean_ctor_get(v_a_1404_, 3);
v_maxRecDepth_1767_ = lean_ctor_get(v_a_1404_, 4);
v_ref_1768_ = lean_ctor_get(v_a_1404_, 5);
v_currNamespace_1769_ = lean_ctor_get(v_a_1404_, 6);
v_openDecls_1770_ = lean_ctor_get(v_a_1404_, 7);
v_initHeartbeats_1771_ = lean_ctor_get(v_a_1404_, 8);
v_maxHeartbeats_1772_ = lean_ctor_get(v_a_1404_, 9);
v_quotContext_1773_ = lean_ctor_get(v_a_1404_, 10);
v_currMacroScope_1774_ = lean_ctor_get(v_a_1404_, 11);
v_diag_1775_ = lean_ctor_get_uint8(v_a_1404_, sizeof(void*)*14);
v_cancelTk_x3f_1776_ = lean_ctor_get(v_a_1404_, 12);
v_suppressElabErrors_1777_ = lean_ctor_get_uint8(v_a_1404_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1778_ = lean_ctor_get(v_a_1404_, 13);
v_cls_1779_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = lean_nat_dec_eq(v_maxRecDepth_1767_, v___x_1791_);
if (v___x_1792_ == 0)
{
uint8_t v___x_1793_; 
v___x_1793_ = lean_nat_dec_eq(v_currRecDepth_1766_, v_maxRecDepth_1767_);
if (v___x_1793_ == 0)
{
goto v___jp_1780_;
}
else
{
lean_object* v___x_1794_; 
lean_dec(v_mvarId_1400_);
lean_dec(v_matchDeclName_1399_);
lean_inc(v_ref_1768_);
v___x_1794_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1768_);
return v___x_1794_;
}
}
else
{
goto v___jp_1780_;
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
lean_dec_ref(v___y_1409_);
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
lean_dec_ref(v___y_1409_);
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
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1401_, v_matchDeclName_1399_, v_a_1412_, v___x_1420_, v___x_1421_, v___x_1415_, v___y_1408_, v___y_1411_, v___y_1409_, v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec_ref(v_a_1412_);
return v___x_1422_;
}
}
else
{
size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = lean_usize_of_nat(v___x_1414_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1401_, v_matchDeclName_1399_, v_a_1412_, v___x_1423_, v___x_1424_, v___x_1415_, v___y_1408_, v___y_1411_, v___y_1409_, v___y_1410_);
lean_dec_ref(v___y_1409_);
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
lean_dec_ref(v___y_1428_);
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
lean_dec_ref(v___y_1443_);
v___x_1450_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1444_, v___y_1447_, v___y_1446_);
lean_dec_ref(v___y_1444_);
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
lean_ctor_set(v___x_1452_, 0, v___y_1448_);
v___x_1460_ = v___x_1452_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___y_1448_);
v___x_1460_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1458_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1461_, v___y_1442_, v___y_1447_, v___y_1445_, v___y_1446_);
v___y_1427_ = v___y_1442_;
v___y_1428_ = v___y_1445_;
v___y_1429_ = v___y_1446_;
v___y_1430_ = v___y_1447_;
v___y_1431_ = v___x_1462_;
goto v___jp_1426_;
}
}
}
else
{
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1445_);
lean_dec(v_matchDeclName_1399_);
return v___x_1450_;
}
}
else
{
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1444_);
v___y_1427_ = v___y_1442_;
v___y_1428_ = v___y_1445_;
v___y_1429_ = v___y_1446_;
v___y_1430_ = v___y_1447_;
v___y_1431_ = v___y_1443_;
goto v___jp_1426_;
}
}
v___jp_1466_:
{
if (v___y_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_dec_ref(v___y_1470_);
v___x_1475_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1468_, v___y_1472_, v___y_1471_);
lean_dec_ref(v___y_1468_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v___x_1476_; 
lean_dec_ref_known(v___x_1475_, 1);
v___x_1476_ = l_Lean_Meta_saveState___redArg(v___y_1472_, v___y_1471_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
lean_inc(v___y_1473_);
v___x_1478_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1473_, v___y_1467_, v___y_1472_, v___y_1469_, v___y_1471_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_dec(v_a_1477_);
lean_dec(v___y_1473_);
v___y_1427_ = v___y_1467_;
v___y_1428_ = v___y_1469_;
v___y_1429_ = v___y_1471_;
v___y_1430_ = v___y_1472_;
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
v___y_1442_ = v___y_1467_;
v___y_1443_ = v___x_1478_;
v___y_1444_ = v_a_1477_;
v___y_1445_ = v___y_1469_;
v___y_1446_ = v___y_1471_;
v___y_1447_ = v___y_1472_;
v___y_1448_ = v___y_1473_;
v___y_1449_ = v___x_1481_;
goto v___jp_1441_;
}
else
{
lean_dec(v_a_1479_);
v___y_1442_ = v___y_1467_;
v___y_1443_ = v___x_1478_;
v___y_1444_ = v_a_1477_;
v___y_1445_ = v___y_1469_;
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
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1469_);
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
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1469_);
lean_dec(v_matchDeclName_1399_);
return v___x_1475_;
}
}
else
{
lean_object* v___x_1490_; 
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v_matchDeclName_1399_);
v___x_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1470_);
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
v___y_1469_ = v___y_1494_;
v___y_1470_ = v_a_1498_;
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
v___y_1469_ = v___y_1494_;
v___y_1470_ = v_a_1498_;
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
lean_dec_ref(v___y_1503_);
v___x_1511_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1508_, v___y_1507_, v___y_1506_);
lean_dec_ref(v___y_1508_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v___x_1512_; 
lean_dec_ref_known(v___x_1511_, 1);
v___x_1512_ = l_Lean_Meta_saveState___redArg(v___y_1507_, v___y_1506_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = lean_box(0);
lean_inc(v___y_1509_);
v___x_1515_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1509_, v___x_1514_, v___y_1505_, v___y_1502_, v___y_1507_, v___y_1504_, v___y_1506_);
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
v___x_1522_ = l_Lean_Meta_trySubst(v_mvarId_1520_, v_fvarId_1521_, v___y_1502_, v___y_1507_, v___y_1504_, v___y_1506_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v_mvarId_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec(v_a_1513_);
lean_dec(v___y_1509_);
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
v___y_1408_ = v___y_1502_;
v___y_1409_ = v___y_1504_;
v___y_1410_ = v___y_1506_;
v___y_1411_ = v___y_1507_;
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
v___y_1492_ = v_a_1513_;
v___y_1493_ = v___y_1502_;
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1506_;
v___y_1496_ = v___y_1507_;
v___y_1497_ = v___y_1509_;
v_a_1498_ = v_a_1529_;
goto v___jp_1491_;
}
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_dec(v_a_1516_);
v___x_1530_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1531_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1530_, v___y_1502_, v___y_1507_, v___y_1504_, v___y_1506_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; 
lean_dec(v_a_1513_);
lean_dec(v___y_1509_);
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___y_1408_ = v___y_1502_;
v___y_1409_ = v___y_1504_;
v___y_1410_ = v___y_1506_;
v___y_1411_ = v___y_1507_;
v_a_1412_ = v_a_1532_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1533_; 
v_a_1533_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1531_, 1);
v___y_1492_ = v_a_1513_;
v___y_1493_ = v___y_1502_;
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1506_;
v___y_1496_ = v___y_1507_;
v___y_1497_ = v___y_1509_;
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
v___y_1492_ = v_a_1513_;
v___y_1493_ = v___y_1502_;
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1506_;
v___y_1496_ = v___y_1507_;
v___y_1497_ = v___y_1509_;
v_a_1498_ = v_a_1534_;
goto v___jp_1491_;
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1504_);
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
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1504_);
lean_dec(v_matchDeclName_1399_);
return v___x_1511_;
}
}
else
{
lean_object* v___x_1543_; 
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec_ref(v___y_1504_);
lean_dec(v_matchDeclName_1399_);
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___y_1503_);
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
v___y_1502_ = v___y_1545_;
v___y_1503_ = v_a_1552_;
v___y_1504_ = v___y_1546_;
v___y_1505_ = v___y_1548_;
v___y_1506_ = v___y_1547_;
v___y_1507_ = v___y_1549_;
v___y_1508_ = v___y_1550_;
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___x_1554_;
goto v___jp_1501_;
}
else
{
v___y_1502_ = v___y_1545_;
v___y_1503_ = v_a_1552_;
v___y_1504_ = v___y_1546_;
v___y_1505_ = v___y_1548_;
v___y_1506_ = v___y_1547_;
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
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
v_a_1564_ = lean_ctor_get(v___y_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___y_1563_, 1);
v___y_1408_ = v___y_1556_;
v___y_1409_ = v___y_1557_;
v___y_1410_ = v___y_1559_;
v___y_1411_ = v___y_1560_;
v_a_1412_ = v_a_1564_;
goto v___jp_1407_;
}
else
{
lean_object* v_a_1565_; 
v_a_1565_ = lean_ctor_get(v___y_1563_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___y_1563_, 1);
v___y_1545_ = v___y_1556_;
v___y_1546_ = v___y_1557_;
v___y_1547_ = v___y_1559_;
v___y_1548_ = v___y_1558_;
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
lean_dec_ref(v___y_1569_);
v___x_1576_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1567_, v___y_1573_, v___y_1572_);
lean_dec_ref(v___y_1567_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref_known(v___x_1576_, 1);
v___x_1577_ = l_Lean_Meta_saveState___redArg(v___y_1573_, v___y_1572_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
lean_inc(v___y_1574_);
v___x_1579_ = l_Lean_Meta_simpIfTarget(v___y_1574_, v___y_1571_, v___y_1571_, v___y_1568_, v___y_1573_, v___y_1570_, v___y_1572_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; uint8_t v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = l_Lean_instBEqMVarId_beq(v_a_1580_, v___y_1574_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1580_, v___x_1582_, v___y_1568_, v___y_1573_, v___y_1570_, v___y_1572_);
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___y_1571_;
v___y_1559_ = v___y_1572_;
v___y_1560_ = v___y_1573_;
v___y_1561_ = v_a_1578_;
v___y_1562_ = v___y_1574_;
v___y_1563_ = v___x_1583_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1585_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1584_, v___y_1568_, v___y_1573_, v___y_1570_, v___y_1572_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1580_, v_a_1586_, v___y_1568_, v___y_1573_, v___y_1570_, v___y_1572_);
v___y_1556_ = v___y_1568_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v___y_1571_;
v___y_1559_ = v___y_1572_;
v___y_1560_ = v___y_1573_;
v___y_1561_ = v_a_1578_;
v___y_1562_ = v___y_1574_;
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
v___y_1545_ = v___y_1568_;
v___y_1546_ = v___y_1570_;
v___y_1547_ = v___y_1572_;
v___y_1548_ = v___y_1571_;
v___y_1549_ = v___y_1573_;
v___y_1550_ = v_a_1578_;
v___y_1551_ = v___y_1574_;
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
v___y_1545_ = v___y_1568_;
v___y_1546_ = v___y_1570_;
v___y_1547_ = v___y_1572_;
v___y_1548_ = v___y_1571_;
v___y_1549_ = v___y_1573_;
v___y_1550_ = v_a_1578_;
v___y_1551_ = v___y_1574_;
v_a_1552_ = v_a_1589_;
goto v___jp_1544_;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1570_);
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
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1570_);
lean_dec(v_matchDeclName_1399_);
return v___x_1576_;
}
}
else
{
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1567_);
v___y_1427_ = v___y_1568_;
v___y_1428_ = v___y_1570_;
v___y_1429_ = v___y_1572_;
v___y_1430_ = v___y_1573_;
v___y_1431_ = v___y_1569_;
goto v___jp_1426_;
}
}
v___jp_1598_:
{
if (v___y_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref(v___y_1600_);
v___x_1608_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1604_, v___y_1605_, v___y_1603_);
lean_dec_ref(v___y_1604_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref_known(v___x_1608_, 1);
v___x_1609_ = l_Lean_Meta_saveState___redArg(v___y_1605_, v___y_1603_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
lean_inc(v___y_1606_);
v___x_1611_ = l_Lean_Meta_splitSparseCasesOn(v___y_1606_, v___y_1599_, v___y_1605_, v___y_1601_, v___y_1603_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_dec(v_a_1610_);
lean_dec(v___y_1606_);
v___y_1427_ = v___y_1599_;
v___y_1428_ = v___y_1601_;
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
v___y_1567_ = v_a_1610_;
v___y_1568_ = v___y_1599_;
v___y_1569_ = v___x_1611_;
v___y_1570_ = v___y_1601_;
v___y_1571_ = v___y_1602_;
v___y_1572_ = v___y_1603_;
v___y_1573_ = v___y_1605_;
v___y_1574_ = v___y_1606_;
v___y_1575_ = v___x_1614_;
goto v___jp_1566_;
}
else
{
lean_dec(v_a_1612_);
v___y_1567_ = v_a_1610_;
v___y_1568_ = v___y_1599_;
v___y_1569_ = v___x_1611_;
v___y_1570_ = v___y_1601_;
v___y_1571_ = v___y_1602_;
v___y_1572_ = v___y_1603_;
v___y_1573_ = v___y_1605_;
v___y_1574_ = v___y_1606_;
v___y_1575_ = v___x_1613_;
goto v___jp_1566_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1601_);
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
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1601_);
lean_dec(v_matchDeclName_1399_);
return v___x_1608_;
}
}
else
{
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1604_);
v___y_1427_ = v___y_1599_;
v___y_1428_ = v___y_1601_;
v___y_1429_ = v___y_1603_;
v___y_1430_ = v___y_1605_;
v___y_1431_ = v___y_1600_;
goto v___jp_1426_;
}
}
v___jp_1623_:
{
if (v___y_1632_ == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref(v___y_1629_);
v___x_1633_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1626_, v___y_1630_, v___y_1628_);
lean_dec_ref(v___y_1626_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1634_; 
lean_dec_ref_known(v___x_1633_, 1);
v___x_1634_ = l_Lean_Meta_saveState___redArg(v___y_1630_, v___y_1628_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1636_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
lean_inc(v___y_1631_);
v___x_1636_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1631_, v___y_1624_, v___y_1630_, v___y_1625_, v___y_1628_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_dec(v_a_1635_);
lean_dec(v___y_1631_);
v___y_1427_ = v___y_1624_;
v___y_1428_ = v___y_1625_;
v___y_1429_ = v___y_1628_;
v___y_1430_ = v___y_1630_;
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
v___y_1599_ = v___y_1624_;
v___y_1600_ = v___x_1636_;
v___y_1601_ = v___y_1625_;
v___y_1602_ = v___y_1627_;
v___y_1603_ = v___y_1628_;
v___y_1604_ = v_a_1635_;
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___y_1631_;
v___y_1607_ = v___x_1639_;
goto v___jp_1598_;
}
else
{
lean_dec(v_a_1637_);
v___y_1599_ = v___y_1624_;
v___y_1600_ = v___x_1636_;
v___y_1601_ = v___y_1625_;
v___y_1602_ = v___y_1627_;
v___y_1603_ = v___y_1628_;
v___y_1604_ = v_a_1635_;
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___y_1631_;
v___y_1607_ = v___x_1638_;
goto v___jp_1598_;
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1625_);
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
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1625_);
lean_dec(v_matchDeclName_1399_);
return v___x_1633_;
}
}
else
{
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1626_);
v___y_1427_ = v___y_1624_;
v___y_1428_ = v___y_1625_;
v___y_1429_ = v___y_1628_;
v___y_1430_ = v___y_1630_;
v___y_1431_ = v___y_1629_;
goto v___jp_1426_;
}
}
v___jp_1648_:
{
if (v___y_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref(v___y_1655_);
v___x_1658_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1650_, v___y_1654_, v___y_1653_);
lean_dec_ref(v___y_1650_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v___x_1659_; 
lean_dec_ref_known(v___x_1658_, 1);
v___x_1659_ = l_Lean_Meta_saveState___redArg(v___y_1654_, v___y_1653_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1661_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
lean_inc(v___y_1656_);
v___x_1661_ = l_Lean_Meta_casesOnStuckLHS(v___y_1656_, v___y_1649_, v___y_1654_, v___y_1651_, v___y_1653_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_dec(v_a_1660_);
lean_dec(v___y_1656_);
v___y_1427_ = v___y_1649_;
v___y_1428_ = v___y_1651_;
v___y_1429_ = v___y_1653_;
v___y_1430_ = v___y_1654_;
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
v___y_1624_ = v___y_1649_;
v___y_1625_ = v___y_1651_;
v___y_1626_ = v_a_1660_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1653_;
v___y_1629_ = v___x_1661_;
v___y_1630_ = v___y_1654_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___x_1664_;
goto v___jp_1623_;
}
else
{
lean_dec(v_a_1662_);
v___y_1624_ = v___y_1649_;
v___y_1625_ = v___y_1651_;
v___y_1626_ = v_a_1660_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1653_;
v___y_1629_ = v___x_1661_;
v___y_1630_ = v___y_1654_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___x_1663_;
goto v___jp_1623_;
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1651_);
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
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1651_);
lean_dec(v_matchDeclName_1399_);
return v___x_1658_;
}
}
else
{
lean_object* v___x_1673_; 
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v_matchDeclName_1399_);
v___x_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___y_1655_);
return v___x_1673_;
}
}
v___jp_1674_:
{
if (v___y_1683_ == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref(v___y_1675_);
v___x_1684_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1676_, v___y_1681_, v___y_1680_);
lean_dec_ref(v___y_1676_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v___x_1685_; 
lean_dec_ref_known(v___x_1684_, 1);
v___x_1685_ = l_Lean_Meta_saveState___redArg(v___y_1681_, v___y_1680_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1685_, 1);
lean_inc(v___y_1682_);
v___x_1687_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1682_, v___y_1677_, v___y_1681_, v___y_1678_, v___y_1680_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_a_1686_);
lean_dec(v___y_1682_);
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_mk_empty_array_with_capacity(v___x_1689_);
v___x_1691_ = lean_array_push(v___x_1690_, v_a_1688_);
v___y_1408_ = v___y_1677_;
v___y_1409_ = v___y_1678_;
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
v___y_1649_ = v___y_1677_;
v___y_1650_ = v_a_1686_;
v___y_1651_ = v___y_1678_;
v___y_1652_ = v___y_1679_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v___y_1681_;
v___y_1655_ = v_a_1692_;
v___y_1656_ = v___y_1682_;
v___y_1657_ = v___x_1694_;
goto v___jp_1648_;
}
else
{
v___y_1649_ = v___y_1677_;
v___y_1650_ = v_a_1686_;
v___y_1651_ = v___y_1678_;
v___y_1652_ = v___y_1679_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v___y_1681_;
v___y_1655_ = v_a_1692_;
v___y_1656_ = v___y_1682_;
v___y_1657_ = v___x_1693_;
goto v___jp_1648_;
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1678_);
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
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1678_);
lean_dec(v_matchDeclName_1399_);
return v___x_1684_;
}
}
else
{
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v___y_1676_);
lean_dec(v_matchDeclName_1399_);
return v___y_1675_;
}
}
v___jp_1703_:
{
if (v___y_1712_ == 0)
{
lean_object* v___x_1713_; 
lean_dec_ref(v___y_1710_);
v___x_1713_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1705_, v___y_1709_, v___y_1708_);
lean_dec_ref(v___y_1705_);
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
v___x_1716_ = l_Lean_Meta_saveState___redArg(v___y_1709_, v___y_1708_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
lean_inc(v___y_1711_);
v___x_1718_ = l_Lean_MVarId_contradiction(v___y_1711_, v___x_1715_, v___y_1704_, v___y_1709_, v___y_1706_, v___y_1708_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v___x_1719_; 
lean_dec_ref_known(v___x_1718_, 1);
lean_dec(v_a_1717_);
lean_dec(v___y_1711_);
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1408_ = v___y_1704_;
v___y_1409_ = v___y_1706_;
v___y_1410_ = v___y_1708_;
v___y_1411_ = v___y_1709_;
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
v___y_1675_ = v___x_1718_;
v___y_1676_ = v_a_1717_;
v___y_1677_ = v___y_1704_;
v___y_1678_ = v___y_1706_;
v___y_1679_ = v___y_1707_;
v___y_1680_ = v___y_1708_;
v___y_1681_ = v___y_1709_;
v___y_1682_ = v___y_1711_;
v___y_1683_ = v___x_1722_;
goto v___jp_1674_;
}
else
{
lean_dec(v_a_1720_);
v___y_1675_ = v___x_1718_;
v___y_1676_ = v_a_1717_;
v___y_1677_ = v___y_1704_;
v___y_1678_ = v___y_1706_;
v___y_1679_ = v___y_1707_;
v___y_1680_ = v___y_1708_;
v___y_1681_ = v___y_1709_;
v___y_1682_ = v___y_1711_;
v___y_1683_ = v___x_1721_;
goto v___jp_1674_;
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref_known(v___x_1715_, 1);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1706_);
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
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1706_);
lean_dec(v_matchDeclName_1399_);
return v___x_1713_;
}
}
else
{
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v_matchDeclName_1399_);
return v___y_1710_;
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
v___y_1408_ = v___y_1732_;
v___y_1409_ = v___y_1734_;
v___y_1410_ = v___y_1735_;
v___y_1411_ = v___y_1733_;
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
v___y_1704_ = v___y_1732_;
v___y_1705_ = v_a_1740_;
v___y_1706_ = v___y_1734_;
v___y_1707_ = v___x_1741_;
v___y_1708_ = v___y_1735_;
v___y_1709_ = v___y_1733_;
v___y_1710_ = v___x_1742_;
v___y_1711_ = v_a_1738_;
v___y_1712_ = v___x_1746_;
goto v___jp_1703_;
}
else
{
lean_dec(v_a_1744_);
v___y_1704_ = v___y_1732_;
v___y_1705_ = v_a_1740_;
v___y_1706_ = v___y_1734_;
v___y_1707_ = v___x_1741_;
v___y_1708_ = v___y_1735_;
v___y_1709_ = v___y_1733_;
v___y_1710_ = v___x_1742_;
v___y_1711_ = v_a_1738_;
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
v___jp_1780_:
{
uint8_t v_hasTrace_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v_hasTrace_1781_ = lean_ctor_get_uint8(v_options_1765_, sizeof(void*)*1);
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = lean_nat_add(v_currRecDepth_1766_, v___x_1782_);
lean_inc_ref(v_inheritedTraceOptions_1778_);
lean_inc(v_cancelTk_x3f_1776_);
lean_inc(v_currMacroScope_1774_);
lean_inc(v_quotContext_1773_);
lean_inc(v_maxHeartbeats_1772_);
lean_inc(v_initHeartbeats_1771_);
lean_inc(v_openDecls_1770_);
lean_inc(v_currNamespace_1769_);
lean_inc(v_ref_1768_);
lean_inc(v_maxRecDepth_1767_);
lean_inc_ref(v_options_1765_);
lean_inc_ref(v_fileMap_1764_);
lean_inc_ref(v_fileName_1763_);
v___x_1784_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1784_, 0, v_fileName_1763_);
lean_ctor_set(v___x_1784_, 1, v_fileMap_1764_);
lean_ctor_set(v___x_1784_, 2, v_options_1765_);
lean_ctor_set(v___x_1784_, 3, v___x_1783_);
lean_ctor_set(v___x_1784_, 4, v_maxRecDepth_1767_);
lean_ctor_set(v___x_1784_, 5, v_ref_1768_);
lean_ctor_set(v___x_1784_, 6, v_currNamespace_1769_);
lean_ctor_set(v___x_1784_, 7, v_openDecls_1770_);
lean_ctor_set(v___x_1784_, 8, v_initHeartbeats_1771_);
lean_ctor_set(v___x_1784_, 9, v_maxHeartbeats_1772_);
lean_ctor_set(v___x_1784_, 10, v_quotContext_1773_);
lean_ctor_set(v___x_1784_, 11, v_currMacroScope_1774_);
lean_ctor_set(v___x_1784_, 12, v_cancelTk_x3f_1776_);
lean_ctor_set(v___x_1784_, 13, v_inheritedTraceOptions_1778_);
lean_ctor_set_uint8(v___x_1784_, sizeof(void*)*14, v_diag_1775_);
lean_ctor_set_uint8(v___x_1784_, sizeof(void*)*14 + 1, v_suppressElabErrors_1777_);
if (v_hasTrace_1781_ == 0)
{
v___y_1732_ = v_a_1402_;
v___y_1733_ = v_a_1403_;
v___y_1734_ = v___x_1784_;
v___y_1735_ = v_a_1405_;
goto v___jp_1731_;
}
else
{
lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1785_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1786_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1778_, v_options_1765_, v___x_1785_);
if (v___x_1786_ == 0)
{
v___y_1732_ = v_a_1402_;
v___y_1733_ = v_a_1403_;
v___y_1734_ = v___x_1784_;
v___y_1735_ = v_a_1405_;
goto v___jp_1731_;
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1787_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1400_);
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_mvarId_1400_);
v___x_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1779_, v___x_1789_, v_a_1402_, v_a_1403_, v___x_1784_, v_a_1405_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_dec_ref_known(v___x_1790_, 1);
v___y_1732_ = v_a_1402_;
v___y_1733_ = v_a_1403_;
v___y_1734_ = v___x_1784_;
v___y_1735_ = v_a_1405_;
goto v___jp_1731_;
}
else
{
lean_dec_ref_known(v___x_1784_, 14);
lean_dec(v_mvarId_1400_);
lean_dec(v_matchDeclName_1399_);
return v___x_1790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1795_, lean_object* v_matchDeclName_1796_, lean_object* v_as_1797_, size_t v_i_1798_, size_t v_stop_1799_, lean_object* v_b_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_usize_dec_eq(v_i_1798_, v_stop_1799_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = lean_array_uget_borrowed(v_as_1797_, v_i_1798_);
v___x_1808_ = lean_unsigned_to_nat(1u);
v___x_1809_ = lean_nat_add(v_depth_1795_, v___x_1808_);
lean_inc(v___x_1807_);
lean_inc(v_matchDeclName_1796_);
v___x_1810_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1796_, v___x_1807_, v___x_1809_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___x_1809_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; size_t v___x_1812_; size_t v___x_1813_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1812_ = ((size_t)1ULL);
v___x_1813_ = lean_usize_add(v_i_1798_, v___x_1812_);
v_i_1798_ = v___x_1813_;
v_b_1800_ = v_a_1811_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1796_);
return v___x_1810_;
}
}
else
{
lean_object* v___x_1815_; 
lean_dec(v_matchDeclName_1796_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_b_1800_);
return v___x_1815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1816_, lean_object* v_matchDeclName_1817_, lean_object* v_as_1818_, lean_object* v_i_1819_, lean_object* v_stop_1820_, lean_object* v_b_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
size_t v_i_boxed_1827_; size_t v_stop_boxed_1828_; lean_object* v_res_1829_; 
v_i_boxed_1827_ = lean_unbox_usize(v_i_1819_);
lean_dec(v_i_1819_);
v_stop_boxed_1828_ = lean_unbox_usize(v_stop_1820_);
lean_dec(v_stop_1820_);
v_res_1829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1816_, v_matchDeclName_1817_, v_as_1818_, v_i_boxed_1827_, v_stop_boxed_1828_, v_b_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec_ref(v_as_1818_);
lean_dec(v_depth_1816_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1830_, lean_object* v_mvarId_1831_, lean_object* v_depth_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1830_, v_mvarId_1831_, v_depth_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_depth_1832_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v___x_1842_; 
v___x_1842_ = l_Lean_Expr_hasMVar(v_e_1839_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_e_1839_);
return v___x_1843_;
}
else
{
lean_object* v___x_1844_; lean_object* v_mctx_1845_; lean_object* v___x_1846_; lean_object* v_fst_1847_; lean_object* v_snd_1848_; lean_object* v___x_1849_; lean_object* v_cache_1850_; lean_object* v_zetaDeltaFVarIds_1851_; lean_object* v_postponed_1852_; lean_object* v_diag_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1862_; 
v___x_1844_ = lean_st_ref_get(v___y_1840_);
v_mctx_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc_ref(v_mctx_1845_);
lean_dec(v___x_1844_);
v___x_1846_ = l_Lean_instantiateMVarsCore(v_mctx_1845_, v_e_1839_);
v_fst_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_fst_1847_);
v_snd_1848_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_snd_1848_);
lean_dec_ref(v___x_1846_);
v___x_1849_ = lean_st_ref_take(v___y_1840_);
v_cache_1850_ = lean_ctor_get(v___x_1849_, 1);
v_zetaDeltaFVarIds_1851_ = lean_ctor_get(v___x_1849_, 2);
v_postponed_1852_ = lean_ctor_get(v___x_1849_, 3);
v_diag_1853_ = lean_ctor_get(v___x_1849_, 4);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1863_);
v___x_1855_ = v___x_1849_;
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_diag_1853_);
lean_inc(v_postponed_1852_);
lean_inc(v_zetaDeltaFVarIds_1851_);
lean_inc(v_cache_1850_);
lean_dec(v___x_1849_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1862_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_snd_1848_);
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_snd_1848_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_cache_1850_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_zetaDeltaFVarIds_1851_);
lean_ctor_set(v_reuseFailAlloc_1861_, 3, v_postponed_1852_);
lean_ctor_set(v_reuseFailAlloc_1861_, 4, v_diag_1853_);
v___x_1858_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_st_ref_set(v___y_1840_, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_fst_1847_);
return v___x_1860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1864_, v___y_1865_);
lean_dec(v___y_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1868_, v___y_1870_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1882_, lean_object* v_localInsts_1883_, lean_object* v_x_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1882_, v_localInsts_1883_, v_x_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
v_a_1899_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1890_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1890_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1907_, lean_object* v_localInsts_1908_, lean_object* v_x_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1907_, v_localInsts_1908_, v_x_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1916_, lean_object* v_lctx_1917_, lean_object* v_localInsts_1918_, lean_object* v_x_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1917_, v_localInsts_1918_, v_x_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1926_, lean_object* v_lctx_1927_, lean_object* v_localInsts_1928_, lean_object* v_x_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1926_, v_lctx_1927_, v_localInsts_1928_, v_x_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
return v_res_1935_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1936_, lean_object* v_x_1937_){
_start:
{
uint8_t v___x_1938_; 
v___x_1938_ = lean_name_eq(v_x_1937_, v_matchDeclName_1936_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1939_, lean_object* v_x_1940_){
_start:
{
uint8_t v_res_1941_; lean_object* v_r_1942_; 
v_res_1941_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1939_, v_x_1940_);
lean_dec(v_x_1940_);
lean_dec(v_matchDeclName_1939_);
v_r_1942_ = lean_box(v_res_1941_);
return v_r_1942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1943_, lean_object* v_a_1944_, lean_object* v_b_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_nat_dec_lt(v_a_1944_, v_upperBound_1943_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; 
lean_dec(v_a_1944_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v_b_1945_);
return v___x_1952_;
}
else
{
uint8_t v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = 0;
v___x_1954_ = l_Lean_Meta_introSubstEq(v_b_1945_, v___x_1953_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v_snd_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v_snd_1956_ = lean_ctor_get(v_a_1955_, 1);
lean_inc(v_snd_1956_);
lean_dec(v_a_1955_);
v___x_1957_ = lean_unsigned_to_nat(1u);
v___x_1958_ = lean_nat_add(v_a_1944_, v___x_1957_);
lean_dec(v_a_1944_);
v_a_1944_ = v___x_1958_;
v_b_1945_ = v_snd_1956_;
goto _start;
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec(v_a_1944_);
v_a_1960_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1954_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1954_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1968_, lean_object* v_a_1969_, lean_object* v_b_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1968_, v_a_1969_, v_b_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v_upperBound_1968_);
return v_res_1976_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1979_ = l_Lean_stringToMessageData(v___x_1978_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1982_ = l_Lean_stringToMessageData(v___x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1983_, lean_object* v___f_1984_, lean_object* v_matchDeclName_1985_, lean_object* v___x_1986_, uint8_t v___x_1987_, lean_object* v_heqPos_1988_, lean_object* v_heqNum_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___x_1995_; lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2146_; 
v___x_1995_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1983_, v___y_1991_);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2146_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2146_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_box(0);
v___x_2001_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1996_, v___x_2000_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2145_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2145_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2145_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; uint8_t v___y_2013_; lean_object* v_mvarId_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v_options_2070_; lean_object* v_inheritedTraceOptions_2071_; uint8_t v_hasTrace_2072_; lean_object* v___x_2073_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; 
v_options_2070_ = lean_ctor_get(v___y_1992_, 2);
v_inheritedTraceOptions_2071_ = lean_ctor_get(v___y_1992_, 13);
v_hasTrace_2072_ = lean_ctor_get_uint8(v_options_2070_, sizeof(void*)*1);
v___x_2073_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2072_ == 0)
{
v___y_2075_ = v___y_1990_;
v___y_2076_ = v___y_1991_;
v___y_2077_ = v___y_1992_;
v___y_2078_ = v___y_1993_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2071_, v_options_2070_, v___x_2130_);
if (v___x_2131_ == 0)
{
v___y_2075_ = v___y_1990_;
v___y_2076_ = v___y_1991_;
v___y_2077_ = v___y_1992_;
v___y_2078_ = v___y_1993_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2132_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2133_ = l_Lean_Expr_mvarId_x21(v_a_2002_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2132_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2073_, v___x_2135_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_dec_ref_known(v___x_2136_, 1);
v___y_2075_ = v___y_1990_;
v___y_2076_ = v___y_1991_;
v___y_2077_ = v___y_1992_;
v___y_2078_ = v___y_1993_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_del_object(v___x_2004_);
lean_dec(v_a_2002_);
lean_del_object(v___x_1998_);
lean_dec(v_heqPos_1988_);
lean_dec(v___x_1986_);
lean_dec(v_matchDeclName_1985_);
lean_dec_ref(v___f_1984_);
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
v___jp_2006_:
{
if (v___y_2013_ == 0)
{
lean_object* v___x_2014_; 
lean_dec_ref(v___y_2012_);
lean_del_object(v___x_2004_);
v___x_2014_ = l_Lean_MVarId_deltaTarget(v___y_2009_, v___f_1984_, v___y_2008_, v___y_2011_, v___y_2007_, v___y_2010_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = l_Lean_MVarId_heqOfEq(v_a_2015_, v___y_2008_, v___y_2011_, v___y_2007_, v___y_2010_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1985_, v_a_2017_, v___x_1986_, v___y_2008_, v___y_2011_, v___y_2007_, v___y_2010_);
lean_dec(v___x_1986_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; 
lean_dec_ref_known(v___x_2018_, 1);
v___x_2019_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2002_, v___y_2011_);
return v___x_2019_;
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_a_2002_);
v_a_2020_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2018_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_a_2002_);
lean_dec(v___x_1986_);
lean_dec(v_matchDeclName_1985_);
v_a_2028_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2016_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2016_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec(v_a_2002_);
lean_dec(v___x_1986_);
lean_dec(v_matchDeclName_1985_);
v_a_2036_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2014_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2014_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v___x_2045_; 
lean_dec(v___y_2009_);
lean_dec(v_a_2002_);
lean_dec(v___x_1986_);
lean_dec(v_matchDeclName_1985_);
lean_dec_ref(v___f_1984_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 1);
lean_ctor_set(v___x_2004_, 0, v___y_2012_);
v___x_2045_ = v___x_2004_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___y_2012_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
v___jp_2047_:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_MVarId_intros(v_mvarId_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v_snd_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v_snd_2055_ = lean_ctor_get(v_a_2054_, 1);
lean_inc_n(v_snd_2055_, 2);
lean_dec(v_a_2054_);
v___x_2056_ = 1;
v___x_2057_ = l_Lean_MVarId_refl(v_snd_2055_, v___x_2056_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v___x_2058_; 
lean_dec_ref_known(v___x_2057_, 1);
lean_dec(v_snd_2055_);
lean_del_object(v___x_2004_);
lean_dec(v___x_1986_);
lean_dec(v_matchDeclName_1985_);
lean_dec_ref(v___f_1984_);
v___x_2058_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2002_, v___y_2050_);
return v___x_2058_;
}
else
{
lean_object* v_a_2059_; uint8_t v___x_2060_; 
v_a_2059_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2060_ = l_Lean_Exception_isInterrupt(v_a_2059_);
if (v___x_2060_ == 0)
{
uint8_t v___x_2061_; 
lean_inc(v_a_2059_);
v___x_2061_ = l_Lean_Exception_isRuntime(v_a_2059_);
v___y_2007_ = v___y_2051_;
v___y_2008_ = v___y_2049_;
v___y_2009_ = v_snd_2055_;
v___y_2010_ = v___y_2052_;
v___y_2011_ = v___y_2050_;
v___y_2012_ = v_a_2059_;
v___y_2013_ = v___x_2061_;
goto v___jp_2006_;
}
else
{
v___y_2007_ = v___y_2051_;
v___y_2008_ = v___y_2049_;
v___y_2009_ = v_snd_2055_;
v___y_2010_ = v___y_2052_;
v___y_2011_ = v___y_2050_;
v___y_2012_ = v_a_2059_;
v___y_2013_ = v___x_2060_;
goto v___jp_2006_;
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_del_object(v___x_2004_);
lean_dec(v_a_2002_);
lean_dec(v___x_1986_);
lean_dec(v_matchDeclName_1985_);
lean_dec_ref(v___f_1984_);
v_a_2062_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2053_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2053_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
v___jp_2074_:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_Expr_mvarId_x21(v_a_2002_);
if (v___x_1987_ == 0)
{
lean_del_object(v___x_1998_);
lean_dec(v_heqPos_1988_);
v_mvarId_2048_ = v___x_2079_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
v___y_2051_ = v___y_2077_;
v___y_2052_ = v___y_2078_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2080_; uint8_t v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_box(0);
v___x_2081_ = 0;
v___x_2082_ = l_Lean_Meta_introNCore(v___x_2079_, v_heqPos_1988_, v___x_2080_, v___x_2081_, v___x_2081_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v_snd_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2120_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2082_, 1);
v_snd_2084_ = lean_ctor_get(v_a_2083_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_a_2083_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v_a_2083_, 0);
lean_dec(v_unused_2121_);
v___x_2086_ = v_a_2083_;
v_isShared_2087_ = v_isSharedCheck_2120_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_snd_2084_);
lean_dec(v_a_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2120_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; 
lean_inc(v___x_1986_);
v___x_2088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1989_, v___x_1986_, v_snd_2084_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_options_2089_; uint8_t v_hasTrace_2090_; 
v_options_2089_ = lean_ctor_get(v___y_2077_, 2);
v_hasTrace_2090_ = lean_ctor_get_uint8(v_options_2089_, sizeof(void*)*1);
if (v_hasTrace_2090_ == 0)
{
lean_object* v_a_2091_; 
lean_del_object(v___x_2086_);
lean_del_object(v___x_1998_);
v_a_2091_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2088_, 1);
v_mvarId_2048_ = v_a_2091_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
v___y_2051_ = v___y_2077_;
v___y_2052_ = v___y_2078_;
goto v___jp_2047_;
}
else
{
lean_object* v_a_2092_; lean_object* v_inheritedTraceOptions_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_a_2092_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2088_, 1);
v_inheritedTraceOptions_2093_ = lean_ctor_get(v___y_2077_, 13);
v___x_2094_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2095_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2093_, v_options_2089_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_del_object(v___x_2086_);
lean_del_object(v___x_1998_);
v_mvarId_2048_ = v_a_2092_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
v___y_2051_ = v___y_2077_;
v___y_2052_ = v___y_2078_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2092_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 1);
lean_ctor_set(v___x_1998_, 0, v_a_2092_);
v___x_2098_ = v___x_1998_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2092_);
v___x_2098_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set_tag(v___x_2086_, 7);
lean_ctor_set(v___x_2086_, 1, v___x_2098_);
lean_ctor_set(v___x_2086_, 0, v___x_2096_);
v___x_2100_ = v___x_2086_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2073_, v___x_2100_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_dec_ref_known(v___x_2101_, 1);
v_mvarId_2048_ = v_a_2092_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
v___y_2051_ = v___y_2077_;
v___y_2052_ = v___y_2078_;
goto v___jp_2047_;
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_a_2092_);
lean_del_object(v___x_2004_);
lean_dec(v_a_2002_);
lean_dec(v___x_1986_);
lean_dec(v_matchDeclName_1985_);
lean_dec_ref(v___f_1984_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2101_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2101_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
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
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_del_object(v___x_2086_);
lean_del_object(v___x_2004_);
lean_dec(v_a_2002_);
lean_del_object(v___x_1998_);
lean_dec(v___x_1986_);
lean_dec(v_matchDeclName_1985_);
lean_dec_ref(v___f_1984_);
v_a_2112_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2088_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2088_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_del_object(v___x_2004_);
lean_dec(v_a_2002_);
lean_del_object(v___x_1998_);
lean_dec(v___x_1986_);
lean_dec(v_matchDeclName_1985_);
lean_dec_ref(v___f_1984_);
v_a_2122_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2082_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2082_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1998_);
lean_dec(v_heqPos_1988_);
lean_dec(v___x_1986_);
lean_dec(v_matchDeclName_1985_);
lean_dec_ref(v___f_1984_);
return v___x_2001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2147_, lean_object* v___f_2148_, lean_object* v_matchDeclName_2149_, lean_object* v___x_2150_, lean_object* v___x_2151_, lean_object* v_heqPos_2152_, lean_object* v_heqNum_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v___x_6049__boxed_2159_; lean_object* v_res_2160_; 
v___x_6049__boxed_2159_ = lean_unbox(v___x_2151_);
v_res_2160_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2147_, v___f_2148_, v_matchDeclName_2149_, v___x_2150_, v___x_6049__boxed_2159_, v_heqPos_2152_, v_heqNum_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v_heqNum_2153_);
return v_res_2160_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_unsigned_to_nat(32u);
v___x_2165_ = lean_mk_empty_array_with_capacity(v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2167_ = ((size_t)5ULL);
v___x_2168_ = lean_unsigned_to_nat(0u);
v___x_2169_ = lean_unsigned_to_nat(32u);
v___x_2170_ = lean_mk_empty_array_with_capacity(v___x_2169_);
v___x_2171_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2172_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v___x_2170_);
lean_ctor_set(v___x_2172_, 2, v___x_2168_);
lean_ctor_set(v___x_2172_, 3, v___x_2168_);
lean_ctor_set_usize(v___x_2172_, 4, v___x_2167_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2173_ = lean_box(1);
v___x_2174_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2175_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_2174_);
lean_ctor_set(v___x_2176_, 2, v___x_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2179_, lean_object* v_type_2180_, lean_object* v_heqPos_2181_, lean_object* v_heqNum_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v___f_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___f_2194_; lean_object* v___x_2195_; 
lean_inc(v_matchDeclName_2179_);
v___f_2188_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2188_, 0, v_matchDeclName_2179_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2191_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2192_ = lean_nat_dec_lt(v___x_2189_, v_heqNum_2182_);
v___x_2193_ = lean_box(v___x_2192_);
v___f_2194_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2194_, 0, v_type_2180_);
lean_closure_set(v___f_2194_, 1, v___f_2188_);
lean_closure_set(v___f_2194_, 2, v_matchDeclName_2179_);
lean_closure_set(v___f_2194_, 3, v___x_2189_);
lean_closure_set(v___f_2194_, 4, v___x_2193_);
lean_closure_set(v___f_2194_, 5, v_heqPos_2181_);
lean_closure_set(v___f_2194_, 6, v_heqNum_2182_);
v___x_2195_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2190_, v___x_2191_, v___f_2194_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2196_, lean_object* v_type_2197_, lean_object* v_heqPos_2198_, lean_object* v_heqNum_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2196_, v_type_2197_, v_heqPos_2198_, v_heqNum_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2206_, lean_object* v_inst_2207_, lean_object* v_R_2208_, lean_object* v_a_2209_, lean_object* v_b_2210_, lean_object* v_c_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2206_, v_a_2209_, v_b_2210_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2218_, lean_object* v_inst_2219_, lean_object* v_R_2220_, lean_object* v_a_2221_, lean_object* v_b_2222_, lean_object* v_c_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2218_, v_inst_2219_, v_R_2220_, v_a_2221_, v_b_2222_, v_c_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v_upperBound_2218_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2230_, lean_object* v_b_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
lean_inc(v___y_2235_);
lean_inc_ref(v___y_2234_);
lean_inc(v___y_2233_);
lean_inc_ref(v___y_2232_);
v___x_2237_ = lean_apply_6(v_k_2230_, v_b_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, lean_box(0));
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2238_, lean_object* v_b_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2238_, v_b_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2246_, uint8_t v_bi_2247_, lean_object* v_type_2248_, lean_object* v_k_2249_, uint8_t v_kind_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___f_2256_; lean_object* v___x_2257_; 
v___f_2256_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2256_, 0, v_k_2249_);
v___x_2257_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2246_, v_bi_2247_, v_type_2248_, v___f_2256_, v_kind_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
v_a_2266_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2257_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2257_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2274_, lean_object* v_bi_2275_, lean_object* v_type_2276_, lean_object* v_k_2277_, lean_object* v_kind_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
uint8_t v_bi_boxed_2284_; uint8_t v_kind_boxed_2285_; lean_object* v_res_2286_; 
v_bi_boxed_2284_ = lean_unbox(v_bi_2275_);
v_kind_boxed_2285_ = lean_unbox(v_kind_2278_);
v_res_2286_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2274_, v_bi_boxed_2284_, v_type_2276_, v_k_2277_, v_kind_boxed_2285_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2287_, lean_object* v_name_2288_, uint8_t v_bi_2289_, lean_object* v_type_2290_, lean_object* v_k_2291_, uint8_t v_kind_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2288_, v_bi_2289_, v_type_2290_, v_k_2291_, v_kind_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2299_, lean_object* v_name_2300_, lean_object* v_bi_2301_, lean_object* v_type_2302_, lean_object* v_k_2303_, lean_object* v_kind_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
uint8_t v_bi_boxed_2310_; uint8_t v_kind_boxed_2311_; lean_object* v_res_2312_; 
v_bi_boxed_2310_ = lean_unbox(v_bi_2301_);
v_kind_boxed_2311_ = lean_unbox(v_kind_2304_);
v_res_2312_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2299_, v_name_2300_, v_bi_boxed_2310_, v_type_2302_, v_k_2303_, v_kind_boxed_2311_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2313_, lean_object* v_altsNew_2314_, lean_object* v_discrs_2315_, lean_object* v_patterns_2316_, lean_object* v_alts_2317_, lean_object* v_k_2318_, lean_object* v_altNew_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2313_, v_altsNew_2314_, v_discrs_2315_, v_patterns_2316_, v_alts_2317_, v_k_2318_, v_altNew_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v_i_2313_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2326_, lean_object* v_patterns_2327_, lean_object* v_alts_2328_, lean_object* v_k_2329_, lean_object* v_i_2330_, lean_object* v_altsNew_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = lean_array_get_size(v_alts_2328_);
v___x_2338_ = lean_nat_dec_lt(v_i_2330_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; 
lean_dec(v_i_2330_);
lean_dec_ref(v_alts_2328_);
lean_dec_ref(v_patterns_2327_);
lean_dec_ref(v_discrs_2326_);
lean_inc(v_a_2335_);
lean_inc_ref(v_a_2334_);
lean_inc(v_a_2333_);
lean_inc_ref(v_a_2332_);
v___x_2339_ = lean_apply_6(v_k_2329_, v_altsNew_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, lean_box(0));
return v___x_2339_;
}
else
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_array_fget_borrowed(v_alts_2328_, v_i_2330_);
v___x_2341_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2340_, v_a_2332_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
lean_inc_ref(v_patterns_2327_);
lean_inc_ref(v_discrs_2326_);
v___f_2343_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2343_, 0, v_i_2330_);
lean_closure_set(v___f_2343_, 1, v_altsNew_2331_);
lean_closure_set(v___f_2343_, 2, v_discrs_2326_);
lean_closure_set(v___f_2343_, 3, v_patterns_2327_);
lean_closure_set(v___f_2343_, 4, v_alts_2328_);
lean_closure_set(v___f_2343_, 5, v_k_2329_);
v___x_2344_ = l_Lean_LocalDecl_type(v_a_2342_);
v___x_2345_ = l_Lean_Expr_replaceFVars(v___x_2344_, v_discrs_2326_, v_patterns_2327_);
lean_dec_ref(v_patterns_2327_);
lean_dec_ref(v_discrs_2326_);
lean_dec_ref(v___x_2344_);
v___x_2346_ = l_Lean_LocalDecl_userName(v_a_2342_);
v___x_2347_ = l_Lean_LocalDecl_binderInfo(v_a_2342_);
lean_dec(v_a_2342_);
v___x_2348_ = 0;
v___x_2349_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2346_, v___x_2347_, v___x_2345_, v___f_2343_, v___x_2348_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_2349_;
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v_altsNew_2331_);
lean_dec(v_i_2330_);
lean_dec_ref(v_k_2329_);
lean_dec_ref(v_alts_2328_);
lean_dec_ref(v_patterns_2327_);
lean_dec_ref(v_discrs_2326_);
v_a_2350_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2341_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2341_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2358_, lean_object* v_altsNew_2359_, lean_object* v_discrs_2360_, lean_object* v_patterns_2361_, lean_object* v_alts_2362_, lean_object* v_k_2363_, lean_object* v_altNew_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2370_ = lean_unsigned_to_nat(1u);
v___x_2371_ = lean_nat_add(v_i_2358_, v___x_2370_);
v___x_2372_ = lean_array_push(v_altsNew_2359_, v_altNew_2364_);
v___x_2373_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2360_, v_patterns_2361_, v_alts_2362_, v_k_2363_, v___x_2371_, v___x_2372_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2374_, lean_object* v_patterns_2375_, lean_object* v_alts_2376_, lean_object* v_k_2377_, lean_object* v_i_2378_, lean_object* v_altsNew_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2374_, v_patterns_2375_, v_alts_2376_, v_k_2377_, v_i_2378_, v_altsNew_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2386_, lean_object* v_discrs_2387_, lean_object* v_patterns_2388_, lean_object* v_alts_2389_, lean_object* v_k_2390_, lean_object* v_i_2391_, lean_object* v_altsNew_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2387_, v_patterns_2388_, v_alts_2389_, v_k_2390_, v_i_2391_, v_altsNew_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2399_, lean_object* v_discrs_2400_, lean_object* v_patterns_2401_, lean_object* v_alts_2402_, lean_object* v_k_2403_, lean_object* v_i_2404_, lean_object* v_altsNew_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2399_, v_discrs_2400_, v_patterns_2401_, v_alts_2402_, v_k_2403_, v_i_2404_, v_altsNew_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2414_, lean_object* v_discrs_2415_, lean_object* v_patterns_2416_, lean_object* v_alts_2417_, lean_object* v_k_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v___x_2424_; uint8_t v___x_2425_; 
v___x_2424_ = lean_unsigned_to_nat(0u);
v___x_2425_ = lean_nat_dec_eq(v_numDiscrEqs_2414_, v___x_2424_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2427_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2415_, v_patterns_2416_, v_alts_2417_, v_k_2418_, v___x_2424_, v___x_2426_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v___x_2427_;
}
else
{
lean_object* v___x_2428_; 
lean_dec_ref(v_patterns_2416_);
lean_dec_ref(v_discrs_2415_);
lean_inc(v_a_2422_);
lean_inc_ref(v_a_2421_);
lean_inc(v_a_2420_);
lean_inc_ref(v_a_2419_);
v___x_2428_ = lean_apply_6(v_k_2418_, v_alts_2417_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, lean_box(0));
return v___x_2428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2429_, lean_object* v_discrs_2430_, lean_object* v_patterns_2431_, lean_object* v_alts_2432_, lean_object* v_k_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2429_, v_discrs_2430_, v_patterns_2431_, v_alts_2432_, v_k_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_numDiscrEqs_2429_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2440_, lean_object* v_numDiscrEqs_2441_, lean_object* v_discrs_2442_, lean_object* v_patterns_2443_, lean_object* v_alts_2444_, lean_object* v_k_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2441_, v_discrs_2442_, v_patterns_2443_, v_alts_2444_, v_k_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2452_, lean_object* v_numDiscrEqs_2453_, lean_object* v_discrs_2454_, lean_object* v_patterns_2455_, lean_object* v_alts_2456_, lean_object* v_k_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2452_, v_numDiscrEqs_2453_, v_discrs_2454_, v_patterns_2455_, v_alts_2456_, v_k_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_numDiscrEqs_2453_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(lean_object* v_declName_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; lean_object* v_env_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2467_ = lean_st_ref_get(v___y_2465_);
v_env_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc_ref(v_env_2468_);
lean_dec(v___x_2467_);
v___x_2469_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2468_, v_declName_2464_);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg___boxed(lean_object* v_declName_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2471_, v___y_2472_);
lean_dec(v___y_2472_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_declName_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2475_, v___y_2479_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___boxed(lean_object* v_declName_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v_declName_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___f_2496_; lean_object* v___x_14708__overap_2497_; lean_object* v___x_2498_; 
v___f_2496_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14708__overap_2497_ = lean_panic_fn_borrowed(v___f_2496_, v_msg_2490_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2493_);
lean_inc(v___y_2492_);
lean_inc_ref(v___y_2491_);
v___x_2498_ = lean_apply_5(v___x_14708__overap_2497_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, lean_box(0));
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2506_, lean_object* v_b_2507_, lean_object* v_c_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; 
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
v___x_2514_ = lean_apply_7(v_k_2506_, v_b_2507_, v_c_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, lean_box(0));
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2515_, lean_object* v_b_2516_, lean_object* v_c_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2515_, v_b_2516_, v_c_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2524_, lean_object* v_k_2525_, uint8_t v_cleanupAnnotations_2526_, uint8_t v_whnfType_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___f_2533_; lean_object* v___x_2534_; 
v___f_2533_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2533_, 0, v_k_2525_);
v___x_2534_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2524_, v___f_2533_, v_cleanupAnnotations_2526_, v_whnfType_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2534_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_a_2543_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2534_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2534_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2551_, lean_object* v_k_2552_, lean_object* v_cleanupAnnotations_2553_, lean_object* v_whnfType_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2560_; uint8_t v_whnfType_boxed_2561_; lean_object* v_res_2562_; 
v_cleanupAnnotations_boxed_2560_ = lean_unbox(v_cleanupAnnotations_2553_);
v_whnfType_boxed_2561_ = lean_unbox(v_whnfType_2554_);
v_res_2562_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2551_, v_k_2552_, v_cleanupAnnotations_boxed_2560_, v_whnfType_boxed_2561_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2563_, lean_object* v_type_2564_, lean_object* v_k_2565_, uint8_t v_cleanupAnnotations_2566_, uint8_t v_whnfType_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2564_, v_k_2565_, v_cleanupAnnotations_2566_, v_whnfType_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2574_, lean_object* v_type_2575_, lean_object* v_k_2576_, lean_object* v_cleanupAnnotations_2577_, lean_object* v_whnfType_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2584_; uint8_t v_whnfType_boxed_2585_; lean_object* v_res_2586_; 
v_cleanupAnnotations_boxed_2584_ = lean_unbox(v_cleanupAnnotations_2577_);
v_whnfType_boxed_2585_ = lean_unbox(v_whnfType_2578_);
v_res_2586_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2574_, v_type_2575_, v_k_2576_, v_cleanupAnnotations_boxed_2584_, v_whnfType_boxed_2585_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2587_, lean_object* v_splitterName_2588_, lean_object* v_matcherInput_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_matchType_2595_; lean_object* v_discrInfos_2596_; lean_object* v_lhss_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2617_; 
v_matchType_2595_ = lean_ctor_get(v_matcherInput_2589_, 1);
v_discrInfos_2596_ = lean_ctor_get(v_matcherInput_2589_, 2);
v_lhss_2597_ = lean_ctor_get(v_matcherInput_2589_, 3);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_matcherInput_2589_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; lean_object* v_unused_2619_; 
v_unused_2618_ = lean_ctor_get(v_matcherInput_2589_, 4);
lean_dec(v_unused_2618_);
v_unused_2619_ = lean_ctor_get(v_matcherInput_2589_, 0);
lean_dec(v_unused_2619_);
v___x_2599_ = v_matcherInput_2589_;
v_isShared_2600_ = v_isSharedCheck_2617_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_lhss_2597_);
lean_inc(v_discrInfos_2596_);
lean_inc(v_matchType_2595_);
lean_dec(v_matcherInput_2589_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2617_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_overlaps_2587_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 4, v___x_2601_);
lean_ctor_set(v___x_2599_, 0, v_splitterName_2588_);
v___x_2603_ = v___x_2599_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_splitterName_2588_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_matchType_2595_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_discrInfos_2596_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_lhss_2597_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_Meta_Match_mkMatcher(v___x_2603_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v_addMatcher_2606_; lean_object* v___x_2607_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v_addMatcher_2606_ = lean_ctor_get(v_a_2605_, 3);
lean_inc_ref(v_addMatcher_2606_);
lean_dec(v_a_2605_);
lean_inc(v___y_2593_);
lean_inc_ref(v___y_2592_);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
v___x_2607_ = lean_apply_5(v_addMatcher_2606_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, lean_box(0));
return v___x_2607_;
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
v_a_2608_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2604_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2604_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2620_, lean_object* v_splitterName_2621_, lean_object* v_matcherInput_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2620_, v_splitterName_2621_, v_matcherInput_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v_res_2628_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2629_, lean_object* v_ys_2630_, lean_object* v_x_2631_){
_start:
{
lean_object* v_zero_2632_; uint8_t v_isZero_2633_; 
v_zero_2632_ = lean_unsigned_to_nat(0u);
v_isZero_2633_ = lean_nat_dec_eq(v_x_2631_, v_zero_2632_);
if (v_isZero_2633_ == 1)
{
lean_dec(v_x_2631_);
return v_isZero_2633_;
}
else
{
lean_object* v_one_2634_; lean_object* v_n_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v_one_2634_ = lean_unsigned_to_nat(1u);
v_n_2635_ = lean_nat_sub(v_x_2631_, v_one_2634_);
lean_dec(v_x_2631_);
v___x_2636_ = lean_array_fget_borrowed(v_xs_2629_, v_n_2635_);
v___x_2637_ = lean_array_fget_borrowed(v_ys_2630_, v_n_2635_);
v___x_2638_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2636_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_dec(v_n_2635_);
return v___x_2638_;
}
else
{
v_x_2631_ = v_n_2635_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2640_, lean_object* v_ys_2641_, lean_object* v_x_2642_){
_start:
{
uint8_t v_res_2643_; lean_object* v_r_2644_; 
v_res_2643_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2640_, v_ys_2641_, v_x_2642_);
lean_dec_ref(v_ys_2641_);
lean_dec_ref(v_xs_2640_);
v_r_2644_ = lean_box(v_res_2643_);
return v_r_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2645_, lean_object* v_b_2646_){
_start:
{
lean_object* v_array_2647_; lean_object* v_start_2648_; lean_object* v_stop_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2662_; 
v_array_2647_ = lean_ctor_get(v_a_2645_, 0);
v_start_2648_ = lean_ctor_get(v_a_2645_, 1);
v_stop_2649_ = lean_ctor_get(v_a_2645_, 2);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_a_2645_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2651_ = v_a_2645_;
v_isShared_2652_ = v_isSharedCheck_2662_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_stop_2649_);
lean_inc(v_start_2648_);
lean_inc(v_array_2647_);
lean_dec(v_a_2645_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2662_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
uint8_t v___x_2653_; 
v___x_2653_ = lean_nat_dec_lt(v_start_2648_, v_stop_2649_);
if (v___x_2653_ == 0)
{
lean_del_object(v___x_2651_);
lean_dec(v_stop_2649_);
lean_dec(v_start_2648_);
lean_dec_ref(v_array_2647_);
return v_b_2646_;
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2657_; 
v___x_2654_ = lean_unsigned_to_nat(1u);
v___x_2655_ = lean_nat_add(v_start_2648_, v___x_2654_);
lean_inc_ref(v_array_2647_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2655_);
v___x_2657_ = v___x_2651_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_array_2647_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_stop_2649_);
v___x_2657_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_array_fget(v_array_2647_, v_start_2648_);
lean_dec(v_start_2648_);
lean_dec_ref(v_array_2647_);
v___x_2659_ = lean_array_push(v_b_2646_, v___x_2658_);
v_a_2645_ = v___x_2657_;
v_b_2646_ = v___x_2659_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2663_, size_t v_sz_2664_, size_t v_i_2665_, lean_object* v_b_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_usize_dec_lt(v_i_2665_, v_sz_2664_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v_b_2666_);
return v___x_2673_;
}
else
{
lean_object* v_snd_2674_; lean_object* v_fst_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2727_; 
v_snd_2674_ = lean_ctor_get(v_b_2666_, 1);
v_fst_2675_ = lean_ctor_get(v_b_2666_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_b_2666_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2677_ = v_b_2666_;
v_isShared_2678_ = v_isSharedCheck_2727_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_snd_2674_);
lean_inc(v_fst_2675_);
lean_dec(v_b_2666_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2727_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v_array_2679_; lean_object* v_start_2680_; lean_object* v_stop_2681_; uint8_t v___x_2682_; 
v_array_2679_ = lean_ctor_get(v_snd_2674_, 0);
v_start_2680_ = lean_ctor_get(v_snd_2674_, 1);
v_stop_2681_ = lean_ctor_get(v_snd_2674_, 2);
v___x_2682_ = lean_nat_dec_lt(v_start_2680_, v_stop_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2684_; 
if (v_isShared_2678_ == 0)
{
v___x_2684_ = v___x_2677_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_fst_2675_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_snd_2674_);
v___x_2684_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
else
{
lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2723_; 
lean_inc(v_stop_2681_);
lean_inc(v_start_2680_);
lean_inc_ref(v_array_2679_);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_snd_2674_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; lean_object* v_unused_2725_; lean_object* v_unused_2726_; 
v_unused_2724_ = lean_ctor_get(v_snd_2674_, 2);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_snd_2674_, 1);
lean_dec(v_unused_2725_);
v_unused_2726_ = lean_ctor_get(v_snd_2674_, 0);
lean_dec(v_unused_2726_);
v___x_2688_ = v_snd_2674_;
v_isShared_2689_ = v_isSharedCheck_2723_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v_snd_2674_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2723_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v_a_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_a_2690_ = lean_array_uget_borrowed(v_as_2663_, v_i_2665_);
v___x_2691_ = lean_array_fget_borrowed(v_array_2679_, v_start_2680_);
lean_inc(v___x_2691_);
lean_inc(v_a_2690_);
v___x_2692_ = l_Lean_Meta_mkEqHEq(v_a_2690_, v___x_2691_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v___x_2694_ = l_Lean_mkArrow(v_a_2693_, v_fst_2675_, v___y_2669_, v___y_2670_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_add(v_start_2680_, v___x_2696_);
lean_dec(v_start_2680_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 1, v___x_2697_);
v___x_2699_ = v___x_2688_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_array_2679_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2706_, 2, v_stop_2681_);
v___x_2699_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2701_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 1, v___x_2699_);
lean_ctor_set(v___x_2677_, 0, v_a_2695_);
v___x_2701_ = v___x_2677_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2695_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
size_t v___x_2702_; size_t v___x_2703_; 
v___x_2702_ = ((size_t)1ULL);
v___x_2703_ = lean_usize_add(v_i_2665_, v___x_2702_);
v_i_2665_ = v___x_2703_;
v_b_2666_ = v___x_2701_;
goto _start;
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_del_object(v___x_2688_);
lean_dec(v_stop_2681_);
lean_dec(v_start_2680_);
lean_dec_ref(v_array_2679_);
lean_del_object(v___x_2677_);
v_a_2707_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2694_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2694_);
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
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_del_object(v___x_2688_);
lean_dec(v_stop_2681_);
lean_dec(v_start_2680_);
lean_dec_ref(v_array_2679_);
lean_del_object(v___x_2677_);
lean_dec(v_fst_2675_);
v_a_2715_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2692_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2692_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2728_, lean_object* v_sz_2729_, lean_object* v_i_2730_, lean_object* v_b_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
size_t v_sz_boxed_2737_; size_t v_i_boxed_2738_; lean_object* v_res_2739_; 
v_sz_boxed_2737_ = lean_unbox_usize(v_sz_2729_);
lean_dec(v_sz_2729_);
v_i_boxed_2738_ = lean_unbox_usize(v_i_2730_);
lean_dec(v_i_2730_);
v_res_2739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2728_, v_sz_boxed_2737_, v_i_boxed_2738_, v_b_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v_as_2728_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2740_, lean_object* v___x_2741_, lean_object* v_as_2742_, size_t v_sz_2743_, size_t v_i_2744_, lean_object* v_b_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v___x_2751_; 
v___x_2751_ = lean_usize_dec_lt(v_i_2744_, v_sz_2743_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_b_2745_);
return v___x_2752_;
}
else
{
lean_object* v___x_2753_; lean_object* v_a_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2753_ = l_Lean_instInhabitedExpr;
v_a_2754_ = lean_array_uget_borrowed(v_as_2742_, v_i_2744_);
v___x_2755_ = lean_array_get_borrowed(v___x_2753_, v___x_2740_, v_a_2754_);
lean_inc(v___x_2755_);
v___x_2756_ = l_Lean_Meta_instantiateForall(v___x_2755_, v___x_2741_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2758_ = lean_array_get_size(v___x_2741_);
v___x_2759_ = l_Lean_Meta_Match_simpH_x3f(v_a_2757_, v___x_2758_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v_a_2762_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
if (lean_obj_tag(v_a_2760_) == 1)
{
lean_object* v_val_2766_; lean_object* v___x_2767_; 
v_val_2766_ = lean_ctor_get(v_a_2760_, 0);
lean_inc(v_val_2766_);
lean_dec_ref_known(v_a_2760_, 1);
v___x_2767_ = lean_array_push(v_b_2745_, v_val_2766_);
v_a_2762_ = v___x_2767_;
goto v___jp_2761_;
}
else
{
lean_dec(v_a_2760_);
v_a_2762_ = v_b_2745_;
goto v___jp_2761_;
}
v___jp_2761_:
{
size_t v___x_2763_; size_t v___x_2764_; 
v___x_2763_ = ((size_t)1ULL);
v___x_2764_ = lean_usize_add(v_i_2744_, v___x_2763_);
v_i_2744_ = v___x_2764_;
v_b_2745_ = v_a_2762_;
goto _start;
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v_b_2745_);
v_a_2768_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2759_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2759_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v_b_2745_);
v_a_2776_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2756_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2756_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2784_, lean_object* v___x_2785_, lean_object* v_as_2786_, lean_object* v_sz_2787_, lean_object* v_i_2788_, lean_object* v_b_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
size_t v_sz_boxed_2795_; size_t v_i_boxed_2796_; lean_object* v_res_2797_; 
v_sz_boxed_2795_ = lean_unbox_usize(v_sz_2787_);
lean_dec(v_sz_2787_);
v_i_boxed_2796_ = lean_unbox_usize(v_i_2788_);
lean_dec(v_i_2788_);
v_res_2797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2784_, v___x_2785_, v_as_2786_, v_sz_boxed_2795_, v_i_boxed_2796_, v_b_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec_ref(v_as_2786_);
lean_dec_ref(v___x_2785_);
lean_dec_ref(v___x_2784_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v___x_2801_, lean_object* v___x_2802_, lean_object* v___x_2803_, lean_object* v___x_2804_, lean_object* v___x_2805_, lean_object* v_rhsArgs_2806_, lean_object* v_a_2807_, lean_object* v_ys_2808_, uint8_t v___x_2809_, uint8_t v___x_2810_, uint8_t v___x_2811_, lean_object* v_matchDeclName_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v_argMask_2818_, lean_object* v_a_2819_, lean_object* v_alts_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2826_ = lean_array_get_borrowed(v___x_2798_, v_alts_2820_, v_a_2799_);
v___x_2827_ = l_Lean_ConstantInfo_name(v_a_2800_);
v___x_2828_ = l_Lean_mkConst(v___x_2827_, v___x_2801_);
v___x_2829_ = l_Subarray_copy___redArg(v___x_2802_);
v___x_2830_ = lean_mk_empty_array_with_capacity(v___x_2803_);
v___x_2831_ = lean_array_push(v___x_2830_, v___x_2804_);
v___x_2832_ = l_Array_append___redArg(v___x_2829_, v___x_2831_);
lean_dec_ref(v___x_2831_);
lean_inc_ref(v___x_2832_);
v___x_2833_ = l_Array_append___redArg(v___x_2832_, v___x_2805_);
v___x_2834_ = l_Array_append___redArg(v___x_2833_, v_alts_2820_);
v___x_2835_ = l_Lean_mkAppN(v___x_2828_, v___x_2834_);
lean_dec_ref(v___x_2834_);
lean_inc(v___x_2826_);
v___x_2836_ = l_Lean_mkAppN(v___x_2826_, v_rhsArgs_2806_);
v___x_2837_ = l_Lean_Meta_mkEq(v___x_2835_, v___x_2836_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2839_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2837_, 1);
v___x_2839_ = l_Lean_mkArrowN(v_a_2807_, v_a_2838_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = l_Array_append___redArg(v___x_2832_, v_ys_2808_);
v___x_2842_ = l_Array_append___redArg(v___x_2841_, v_alts_2820_);
v___x_2843_ = l_Lean_Meta_mkForallFVars(v___x_2842_, v_a_2840_, v___x_2809_, v___x_2810_, v___x_2810_, v___x_2811_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v___x_2842_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v___x_2845_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2844_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2847_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc_n(v_a_2846_, 2);
lean_dec_ref_known(v___x_2845_, 1);
lean_inc(v___x_2813_);
v___x_2847_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2812_, v_a_2846_, v___x_2813_, v___x_2813_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
lean_inc(v___x_2814_);
v___x_2849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2814_);
lean_ctor_set(v___x_2849_, 1, v___x_2815_);
lean_ctor_set(v___x_2849_, 2, v_a_2846_);
v___x_2850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2814_);
lean_ctor_set(v___x_2850_, 1, v___x_2816_);
v___x_2851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v_a_2848_);
lean_ctor_set(v___x_2851_, 2, v___x_2850_);
v___x_2852_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
v___x_2853_ = l_Lean_addDecl(v___x_2852_, v___x_2809_, v___y_2823_, v___y_2824_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2862_; 
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; 
v_unused_2863_ = lean_ctor_get(v___x_2853_, 0);
lean_dec(v_unused_2863_);
v___x_2855_ = v___x_2853_;
v_isShared_2856_ = v_isSharedCheck_2862_;
goto v_resetjp_2854_;
}
else
{
lean_dec(v___x_2853_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2862_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2817_);
lean_ctor_set(v___x_2857_, 1, v_argMask_2818_);
v___x_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2858_, 0, v_a_2819_);
lean_ctor_set(v___x_2858_, 1, v___x_2857_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2858_);
v___x_2860_ = v___x_2855_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_argMask_2818_);
lean_dec_ref(v___x_2817_);
v_a_2864_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2853_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2853_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_argMask_2818_);
lean_dec_ref(v___x_2817_);
lean_dec(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
v_a_2872_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2847_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2847_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_argMask_2818_);
lean_dec_ref(v___x_2817_);
lean_dec(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v_matchDeclName_2812_);
v_a_2880_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2845_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2845_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_argMask_2818_);
lean_dec_ref(v___x_2817_);
lean_dec(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v_matchDeclName_2812_);
v_a_2888_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2843_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2843_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec_ref(v___x_2832_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_argMask_2818_);
lean_dec_ref(v___x_2817_);
lean_dec(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v_matchDeclName_2812_);
v_a_2896_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2839_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2839_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec_ref(v___x_2832_);
lean_dec_ref(v_a_2819_);
lean_dec_ref(v_argMask_2818_);
lean_dec_ref(v___x_2817_);
lean_dec(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v_matchDeclName_2812_);
v_a_2904_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2837_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2837_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2912_ = _args[0];
lean_object* v_a_2913_ = _args[1];
lean_object* v_a_2914_ = _args[2];
lean_object* v___x_2915_ = _args[3];
lean_object* v___x_2916_ = _args[4];
lean_object* v___x_2917_ = _args[5];
lean_object* v___x_2918_ = _args[6];
lean_object* v___x_2919_ = _args[7];
lean_object* v_rhsArgs_2920_ = _args[8];
lean_object* v_a_2921_ = _args[9];
lean_object* v_ys_2922_ = _args[10];
lean_object* v___x_2923_ = _args[11];
lean_object* v___x_2924_ = _args[12];
lean_object* v___x_2925_ = _args[13];
lean_object* v_matchDeclName_2926_ = _args[14];
lean_object* v___x_2927_ = _args[15];
lean_object* v___x_2928_ = _args[16];
lean_object* v___x_2929_ = _args[17];
lean_object* v___x_2930_ = _args[18];
lean_object* v___x_2931_ = _args[19];
lean_object* v_argMask_2932_ = _args[20];
lean_object* v_a_2933_ = _args[21];
lean_object* v_alts_2934_ = _args[22];
lean_object* v___y_2935_ = _args[23];
lean_object* v___y_2936_ = _args[24];
lean_object* v___y_2937_ = _args[25];
lean_object* v___y_2938_ = _args[26];
lean_object* v___y_2939_ = _args[27];
_start:
{
uint8_t v___x_18942__boxed_2940_; uint8_t v___x_18943__boxed_2941_; uint8_t v___x_18944__boxed_2942_; lean_object* v_res_2943_; 
v___x_18942__boxed_2940_ = lean_unbox(v___x_2923_);
v___x_18943__boxed_2941_ = lean_unbox(v___x_2924_);
v___x_18944__boxed_2942_ = lean_unbox(v___x_2925_);
v_res_2943_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2912_, v_a_2913_, v_a_2914_, v___x_2915_, v___x_2916_, v___x_2917_, v___x_2918_, v___x_2919_, v_rhsArgs_2920_, v_a_2921_, v_ys_2922_, v___x_18942__boxed_2940_, v___x_18943__boxed_2941_, v___x_18944__boxed_2942_, v_matchDeclName_2926_, v___x_2927_, v___x_2928_, v___x_2929_, v___x_2930_, v___x_2931_, v_argMask_2932_, v_a_2933_, v_alts_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v_alts_2934_);
lean_dec_ref(v_ys_2922_);
lean_dec_ref(v_a_2921_);
lean_dec_ref(v_rhsArgs_2920_);
lean_dec_ref(v___x_2919_);
lean_dec(v___x_2917_);
lean_dec_ref(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec_ref(v___x_2912_);
return v_res_2943_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2944_; lean_object* v_dummy_2945_; 
v___x_2944_ = lean_box(0);
v_dummy_2945_ = l_Lean_Expr_sort___override(v___x_2944_);
return v_dummy_2945_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_box(0);
v___x_2950_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_2951_ = l_Lean_mkConst(v___x_2950_, v___x_2949_);
return v___x_2951_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_2954_ = l_Lean_stringToMessageData(v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_2955_, lean_object* v_overlaps_2956_, lean_object* v_a_2957_, lean_object* v_fst_2958_, lean_object* v___x_2959_, lean_object* v___x_2960_, lean_object* v___x_2961_, uint8_t v___x_2962_, lean_object* v___x_2963_, lean_object* v_a_2964_, lean_object* v___x_2965_, lean_object* v___x_2966_, lean_object* v___x_2967_, lean_object* v_matchDeclName_2968_, lean_object* v___x_2969_, lean_object* v___x_2970_, lean_object* v___x_2971_, lean_object* v___x_2972_, lean_object* v___x_2973_, lean_object* v_ys_2974_, lean_object* v___eqs_2975_, lean_object* v_rhsArgs_2976_, lean_object* v_argMask_2977_, lean_object* v_altResultType_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_dummy_2984_; lean_object* v_nargs_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; size_t v_sz_2990_; size_t v___x_2991_; lean_object* v___x_2992_; 
v_dummy_2984_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_2985_ = l_Lean_Expr_getAppNumArgs(v_altResultType_2978_);
lean_inc(v_nargs_2985_);
v___x_2986_ = lean_mk_array(v_nargs_2985_, v_dummy_2984_);
v___x_2987_ = lean_nat_sub(v_nargs_2985_, v___x_2955_);
lean_dec(v_nargs_2985_);
v___x_2988_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_2978_, v___x_2986_, v___x_2987_);
v___x_2989_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_2956_, v_a_2957_);
v_sz_2990_ = lean_array_size(v___x_2989_);
v___x_2991_ = ((size_t)0ULL);
lean_inc_ref(v___x_2959_);
v___x_2992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_2958_, v___x_2988_, v___x_2989_, v_sz_2990_, v___x_2991_, v___x_2959_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec_ref(v___x_2989_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; uint8_t v___y_2999_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; uint8_t v___y_3047_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v_options_3058_; uint8_t v_hasTrace_3059_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v_options_3058_ = lean_ctor_get(v___y_2981_, 2);
v_hasTrace_3059_ = lean_ctor_get_uint8(v_options_3058_, sizeof(void*)*1);
if (v_hasTrace_3059_ == 0)
{
v___y_3050_ = v___y_2979_;
v___y_3051_ = v___y_2980_;
v___y_3052_ = v___y_2981_;
v___y_3053_ = v___y_2982_;
goto v___jp_3049_;
}
else
{
lean_object* v_inheritedTraceOptions_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v_inheritedTraceOptions_3060_ = lean_ctor_get(v___y_2981_, 13);
v___x_3061_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3062_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_3063_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3060_, v_options_3058_, v___x_3062_);
if (v___x_3063_ == 0)
{
v___y_3050_ = v___y_2979_;
v___y_3051_ = v___y_2980_;
v___y_3052_ = v___y_2981_;
v___y_3053_ = v___y_2982_;
goto v___jp_3049_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3064_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_2993_);
v___x_3065_ = lean_array_to_list(v_a_2993_);
v___x_3066_ = lean_box(0);
v___x_3067_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3065_, v___x_3066_);
v___x_3068_ = l_Lean_MessageData_ofList(v___x_3067_);
v___x_3069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3064_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
v___x_3070_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3061_, v___x_3069_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_dec_ref_known(v___x_3070_, 1);
v___y_3050_ = v___y_2979_;
v___y_3051_ = v___y_2980_;
v___y_3052_ = v___y_2981_;
v___y_3053_ = v___y_2982_;
goto v___jp_3049_;
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v_a_2993_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_argMask_2977_);
lean_dec_ref(v_rhsArgs_2976_);
lean_dec_ref(v_ys_2974_);
lean_dec_ref(v___x_2972_);
lean_dec(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v_matchDeclName_2968_);
lean_dec_ref(v___x_2967_);
lean_dec_ref(v___x_2966_);
lean_dec(v___x_2965_);
lean_dec_ref(v_a_2964_);
lean_dec_ref(v___x_2963_);
lean_dec_ref(v___x_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v___x_2959_);
lean_dec(v_a_2957_);
lean_dec(v___x_2955_);
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_3070_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_3070_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
v___jp_2994_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; size_t v_sz_3007_; lean_object* v___x_3008_; 
v___x_3000_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2988_);
v___x_3001_ = l_Array_reverse___redArg(v___x_2988_);
v___x_3002_ = lean_array_get_size(v___x_3001_);
lean_inc(v___x_2960_);
v___x_3003_ = l_Array_toSubarray___redArg(v___x_3001_, v___x_2960_, v___x_3002_);
lean_inc_ref(v___x_2961_);
v___x_3004_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2961_, v___x_2959_);
v___x_3005_ = l_Array_reverse___redArg(v___x_3004_);
v___x_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3000_);
lean_ctor_set(v___x_3006_, 1, v___x_3003_);
v_sz_3007_ = lean_array_size(v___x_3005_);
v___x_3008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3005_, v_sz_3007_, v___x_2991_, v___x_3006_, v___y_2998_, v___y_2997_, v___y_2995_, v___y_2996_);
lean_dec_ref(v___x_3005_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v_fst_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v_fst_3010_ = lean_ctor_get(v_a_3009_, 0);
lean_inc(v_fst_3010_);
lean_dec(v_a_3009_);
v___x_3011_ = l_Subarray_copy___redArg(v___x_2961_);
lean_inc_ref(v___x_3011_);
v___x_3012_ = l_Array_append___redArg(v___x_3011_, v_ys_2974_);
v___x_3013_ = 0;
v___x_3014_ = 1;
v___x_3015_ = l_Lean_Meta_mkForallFVars(v___x_3012_, v_fst_3010_, v___x_3013_, v___x_2962_, v___x_2962_, v___x_3014_, v___y_2998_, v___y_2997_, v___y_2995_, v___y_2996_);
lean_dec_ref(v___x_3012_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___f_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = lean_array_get_size(v_ys_2974_);
v___x_3018_ = lean_array_get_size(v_a_2993_);
v___x_3019_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
lean_ctor_set_uint8(v___x_3019_, sizeof(void*)*2, v___y_2999_);
v___x_3020_ = lean_box(v___x_3013_);
v___x_3021_ = lean_box(v___x_2962_);
v___x_3022_ = lean_box(v___x_3014_);
lean_inc_ref(v___x_2988_);
v___f_3023_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_3023_, 0, v___x_2963_);
lean_closure_set(v___f_3023_, 1, v_a_2957_);
lean_closure_set(v___f_3023_, 2, v_a_2964_);
lean_closure_set(v___f_3023_, 3, v___x_2965_);
lean_closure_set(v___f_3023_, 4, v___x_2966_);
lean_closure_set(v___f_3023_, 5, v___x_2955_);
lean_closure_set(v___f_3023_, 6, v___x_2967_);
lean_closure_set(v___f_3023_, 7, v___x_2988_);
lean_closure_set(v___f_3023_, 8, v_rhsArgs_2976_);
lean_closure_set(v___f_3023_, 9, v_a_2993_);
lean_closure_set(v___f_3023_, 10, v_ys_2974_);
lean_closure_set(v___f_3023_, 11, v___x_3020_);
lean_closure_set(v___f_3023_, 12, v___x_3021_);
lean_closure_set(v___f_3023_, 13, v___x_3022_);
lean_closure_set(v___f_3023_, 14, v_matchDeclName_2968_);
lean_closure_set(v___f_3023_, 15, v___x_2960_);
lean_closure_set(v___f_3023_, 16, v___x_2969_);
lean_closure_set(v___f_3023_, 17, v___x_2970_);
lean_closure_set(v___f_3023_, 18, v___x_2971_);
lean_closure_set(v___f_3023_, 19, v___x_3019_);
lean_closure_set(v___f_3023_, 20, v_argMask_2977_);
lean_closure_set(v___f_3023_, 21, v_a_3016_);
v___x_3024_ = l_Subarray_copy___redArg(v___x_2972_);
v___x_3025_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2973_, v___x_3011_, v___x_2988_, v___x_3024_, v___f_3023_, v___y_2998_, v___y_2997_, v___y_2995_, v___y_2996_);
return v___x_3025_;
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v___x_3011_);
lean_dec(v_a_2993_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_argMask_2977_);
lean_dec_ref(v_rhsArgs_2976_);
lean_dec_ref(v_ys_2974_);
lean_dec_ref(v___x_2972_);
lean_dec(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v_matchDeclName_2968_);
lean_dec_ref(v___x_2967_);
lean_dec_ref(v___x_2966_);
lean_dec(v___x_2965_);
lean_dec_ref(v_a_2964_);
lean_dec_ref(v___x_2963_);
lean_dec(v___x_2960_);
lean_dec(v_a_2957_);
lean_dec(v___x_2955_);
v_a_3026_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3015_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3015_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_a_2993_);
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_argMask_2977_);
lean_dec_ref(v_rhsArgs_2976_);
lean_dec_ref(v_ys_2974_);
lean_dec_ref(v___x_2972_);
lean_dec(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v_matchDeclName_2968_);
lean_dec_ref(v___x_2967_);
lean_dec_ref(v___x_2966_);
lean_dec(v___x_2965_);
lean_dec_ref(v_a_2964_);
lean_dec_ref(v___x_2963_);
lean_dec_ref(v___x_2961_);
lean_dec(v___x_2960_);
lean_dec(v_a_2957_);
lean_dec(v___x_2955_);
v_a_3034_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3008_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3008_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
v___jp_3042_:
{
if (v___y_3047_ == 0)
{
v___y_2995_ = v___y_3043_;
v___y_2996_ = v___y_3044_;
v___y_2997_ = v___y_3045_;
v___y_2998_ = v___y_3046_;
v___y_2999_ = v___y_3047_;
goto v___jp_2994_;
}
else
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_nat_dec_eq(v___x_2973_, v___x_2960_);
v___y_2995_ = v___y_3043_;
v___y_2996_ = v___y_3044_;
v___y_2997_ = v___y_3045_;
v___y_2998_ = v___y_3046_;
v___y_2999_ = v___x_3048_;
goto v___jp_2994_;
}
}
v___jp_3049_:
{
lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = lean_array_get_size(v_ys_2974_);
v___x_3055_ = lean_nat_dec_eq(v___x_3054_, v___x_2960_);
if (v___x_3055_ == 0)
{
v___y_3043_ = v___y_3052_;
v___y_3044_ = v___y_3053_;
v___y_3045_ = v___y_3051_;
v___y_3046_ = v___y_3050_;
v___y_3047_ = v___x_3055_;
goto v___jp_3042_;
}
else
{
lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3056_ = lean_array_get_size(v_a_2993_);
v___x_3057_ = lean_nat_dec_eq(v___x_3056_, v___x_2960_);
v___y_3043_ = v___y_3052_;
v___y_3044_ = v___y_3053_;
v___y_3045_ = v___y_3051_;
v___y_3046_ = v___y_3050_;
v___y_3047_ = v___x_3057_;
goto v___jp_3042_;
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_argMask_2977_);
lean_dec_ref(v_rhsArgs_2976_);
lean_dec_ref(v_ys_2974_);
lean_dec_ref(v___x_2972_);
lean_dec(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v_matchDeclName_2968_);
lean_dec_ref(v___x_2967_);
lean_dec_ref(v___x_2966_);
lean_dec(v___x_2965_);
lean_dec_ref(v_a_2964_);
lean_dec_ref(v___x_2963_);
lean_dec_ref(v___x_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v___x_2959_);
lean_dec(v_a_2957_);
lean_dec(v___x_2955_);
v_a_3079_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_2992_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_2992_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3087_ = _args[0];
lean_object* v_overlaps_3088_ = _args[1];
lean_object* v_a_3089_ = _args[2];
lean_object* v_fst_3090_ = _args[3];
lean_object* v___x_3091_ = _args[4];
lean_object* v___x_3092_ = _args[5];
lean_object* v___x_3093_ = _args[6];
lean_object* v___x_3094_ = _args[7];
lean_object* v___x_3095_ = _args[8];
lean_object* v_a_3096_ = _args[9];
lean_object* v___x_3097_ = _args[10];
lean_object* v___x_3098_ = _args[11];
lean_object* v___x_3099_ = _args[12];
lean_object* v_matchDeclName_3100_ = _args[13];
lean_object* v___x_3101_ = _args[14];
lean_object* v___x_3102_ = _args[15];
lean_object* v___x_3103_ = _args[16];
lean_object* v___x_3104_ = _args[17];
lean_object* v___x_3105_ = _args[18];
lean_object* v_ys_3106_ = _args[19];
lean_object* v___eqs_3107_ = _args[20];
lean_object* v_rhsArgs_3108_ = _args[21];
lean_object* v_argMask_3109_ = _args[22];
lean_object* v_altResultType_3110_ = _args[23];
lean_object* v___y_3111_ = _args[24];
lean_object* v___y_3112_ = _args[25];
lean_object* v___y_3113_ = _args[26];
lean_object* v___y_3114_ = _args[27];
lean_object* v___y_3115_ = _args[28];
_start:
{
uint8_t v___x_19210__boxed_3116_; lean_object* v_res_3117_; 
v___x_19210__boxed_3116_ = lean_unbox(v___x_3094_);
v_res_3117_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3087_, v_overlaps_3088_, v_a_3089_, v_fst_3090_, v___x_3091_, v___x_3092_, v___x_3093_, v___x_19210__boxed_3116_, v___x_3095_, v_a_3096_, v___x_3097_, v___x_3098_, v___x_3099_, v_matchDeclName_3100_, v___x_3101_, v___x_3102_, v___x_3103_, v___x_3104_, v___x_3105_, v_ys_3106_, v___eqs_3107_, v_rhsArgs_3108_, v_argMask_3109_, v_altResultType_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v___eqs_3107_);
lean_dec(v___x_3105_);
lean_dec(v_fst_3090_);
lean_dec_ref(v_overlaps_3088_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3118_, lean_object* v_val_3119_, lean_object* v_baseName_3120_, lean_object* v___x_3121_, lean_object* v_a_3122_, lean_object* v___x_3123_, lean_object* v___x_3124_, lean_object* v___x_3125_, lean_object* v_matchDeclName_3126_, lean_object* v___x_3127_, lean_object* v___x_3128_, lean_object* v___x_3129_, lean_object* v_a_3130_, lean_object* v_b_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
uint8_t v___x_3137_; 
v___x_3137_ = lean_nat_dec_lt(v_a_3130_, v_upperBound_3118_);
if (v___x_3137_ == 0)
{
lean_object* v___x_3138_; 
lean_dec(v_a_3130_);
lean_dec(v___x_3129_);
lean_dec_ref(v___x_3128_);
lean_dec(v___x_3127_);
lean_dec(v_matchDeclName_3126_);
lean_dec_ref(v___x_3125_);
lean_dec_ref(v___x_3124_);
lean_dec(v___x_3123_);
lean_dec_ref(v_a_3122_);
lean_dec_ref(v___x_3121_);
lean_dec(v_baseName_3120_);
lean_dec_ref(v_val_3119_);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_b_3131_);
return v___x_3138_;
}
else
{
lean_object* v_snd_3139_; lean_object* v_snd_3140_; lean_object* v_snd_3141_; lean_object* v_fst_3142_; lean_object* v_fst_3143_; lean_object* v_fst_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3227_; 
v_snd_3139_ = lean_ctor_get(v_b_3131_, 1);
lean_inc(v_snd_3139_);
v_snd_3140_ = lean_ctor_get(v_snd_3139_, 1);
lean_inc(v_snd_3140_);
v_snd_3141_ = lean_ctor_get(v_snd_3140_, 1);
lean_inc(v_snd_3141_);
v_fst_3142_ = lean_ctor_get(v_b_3131_, 0);
lean_inc(v_fst_3142_);
lean_dec_ref(v_b_3131_);
v_fst_3143_ = lean_ctor_get(v_snd_3139_, 0);
lean_inc(v_fst_3143_);
lean_dec(v_snd_3139_);
v_fst_3144_ = lean_ctor_get(v_snd_3140_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_snd_3140_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v_snd_3140_, 1);
lean_dec(v_unused_3228_);
v___x_3146_ = v_snd_3140_;
v_isShared_3147_ = v_isSharedCheck_3227_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_fst_3144_);
lean_dec(v_snd_3140_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3227_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v_fst_3148_; lean_object* v_snd_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3226_; 
v_fst_3148_ = lean_ctor_get(v_snd_3141_, 0);
v_snd_3149_ = lean_ctor_get(v_snd_3141_, 1);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_snd_3141_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3151_ = v_snd_3141_;
v_isShared_3152_ = v_isSharedCheck_3226_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_snd_3149_);
lean_inc(v_fst_3148_);
lean_dec(v_snd_3141_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3226_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v_altInfos_3153_; lean_object* v_overlaps_3154_; lean_object* v_start_3155_; lean_object* v_stop_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___y_3171_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v_altInfos_3153_ = lean_ctor_get(v_val_3119_, 2);
v_overlaps_3154_ = lean_ctor_get(v_val_3119_, 5);
v_start_3155_ = lean_ctor_get(v___x_3128_, 1);
v_stop_3156_ = lean_ctor_get(v___x_3128_, 2);
v___x_3157_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3158_ = l_Lean_instInhabitedExpr;
v___x_3159_ = lean_unsigned_to_nat(0u);
v___x_3160_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_unsigned_to_nat(1u);
v___x_3163_ = lean_array_get_borrowed(v___x_3157_, v_altInfos_3153_, v_a_3130_);
v___x_3164_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3120_);
v___x_3165_ = l_Lean_Name_str___override(v_baseName_3120_, v___x_3164_);
lean_inc(v_fst_3144_);
v___x_3166_ = lean_name_append_index_after(v___x_3165_, v_fst_3144_);
v___x_3167_ = lean_box(v___x_3137_);
lean_inc(v___x_3129_);
lean_inc_ref(v___x_3128_);
lean_inc(v___x_3127_);
lean_inc(v___x_3166_);
lean_inc(v_matchDeclName_3126_);
lean_inc_ref(v___x_3125_);
lean_inc_ref(v___x_3124_);
lean_inc(v___x_3123_);
lean_inc_ref(v_a_3122_);
lean_inc_ref(v___x_3121_);
lean_inc(v_fst_3143_);
lean_inc(v_a_3130_);
lean_inc_ref(v_overlaps_3154_);
v___f_3168_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3168_, 0, v___x_3162_);
lean_closure_set(v___f_3168_, 1, v_overlaps_3154_);
lean_closure_set(v___f_3168_, 2, v_a_3130_);
lean_closure_set(v___f_3168_, 3, v_fst_3143_);
lean_closure_set(v___f_3168_, 4, v___x_3160_);
lean_closure_set(v___f_3168_, 5, v___x_3159_);
lean_closure_set(v___f_3168_, 6, v___x_3121_);
lean_closure_set(v___f_3168_, 7, v___x_3167_);
lean_closure_set(v___f_3168_, 8, v___x_3158_);
lean_closure_set(v___f_3168_, 9, v_a_3122_);
lean_closure_set(v___f_3168_, 10, v___x_3123_);
lean_closure_set(v___f_3168_, 11, v___x_3124_);
lean_closure_set(v___f_3168_, 12, v___x_3125_);
lean_closure_set(v___f_3168_, 13, v_matchDeclName_3126_);
lean_closure_set(v___f_3168_, 14, v___x_3166_);
lean_closure_set(v___f_3168_, 15, v___x_3127_);
lean_closure_set(v___f_3168_, 16, v___x_3161_);
lean_closure_set(v___f_3168_, 17, v___x_3128_);
lean_closure_set(v___f_3168_, 18, v___x_3129_);
v___x_3169_ = lean_array_push(v_fst_3142_, v___x_3166_);
v___x_3222_ = lean_nat_sub(v_stop_3156_, v_start_3155_);
v___x_3223_ = lean_nat_dec_lt(v_a_3130_, v___x_3222_);
lean_dec(v___x_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
v___x_3224_ = l_outOfBounds___redArg(v___x_3158_);
v___y_3171_ = v___x_3224_;
goto v___jp_3170_;
}
else
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Subarray_get___redArg(v___x_3128_, v_a_3130_);
v___y_3171_ = v___x_3225_;
goto v___jp_3170_;
}
v___jp_3170_:
{
lean_object* v___x_3172_; 
lean_inc(v___y_3135_);
lean_inc_ref(v___y_3134_);
lean_inc(v___y_3133_);
lean_inc_ref(v___y_3132_);
v___x_3172_ = lean_infer_type(v___y_3171_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3174_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3172_, 1);
lean_inc(v___x_3129_);
lean_inc(v___x_3163_);
v___x_3174_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3173_, v___x_3163_, v___x_3129_, v___f_3168_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v_snd_3176_; lean_object* v_fst_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3205_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3174_, 1);
v_snd_3176_ = lean_ctor_get(v_a_3175_, 1);
v_fst_3177_ = lean_ctor_get(v_a_3175_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_a_3175_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3179_ = v_a_3175_;
v_isShared_3180_ = v_isSharedCheck_3205_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_snd_3176_);
lean_inc(v_fst_3177_);
lean_dec(v_a_3175_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3205_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v_fst_3181_; lean_object* v_snd_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3204_; 
v_fst_3181_ = lean_ctor_get(v_snd_3176_, 0);
v_snd_3182_ = lean_ctor_get(v_snd_3176_, 1);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_snd_3176_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3184_ = v_snd_3176_;
v_isShared_3185_ = v_isSharedCheck_3204_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_snd_3182_);
lean_inc(v_fst_3181_);
lean_dec(v_snd_3176_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3204_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3186_ = lean_array_push(v_fst_3143_, v_fst_3177_);
v___x_3187_ = lean_array_push(v_fst_3148_, v_fst_3181_);
v___x_3188_ = lean_array_push(v_snd_3149_, v_snd_3182_);
v___x_3189_ = lean_nat_add(v_fst_3144_, v___x_3162_);
lean_dec(v_fst_3144_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 1, v___x_3188_);
lean_ctor_set(v___x_3184_, 0, v___x_3187_);
v___x_3191_ = v___x_3184_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v___x_3188_);
v___x_3191_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3193_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 1, v___x_3191_);
lean_ctor_set(v___x_3179_, 0, v___x_3189_);
v___x_3193_ = v___x_3179_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3195_; 
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 1, v___x_3193_);
lean_ctor_set(v___x_3151_, 0, v___x_3186_);
v___x_3195_ = v___x_3151_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3197_; 
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 1, v___x_3195_);
lean_ctor_set(v___x_3146_, 0, v___x_3169_);
v___x_3197_ = v___x_3146_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
lean_object* v___x_3198_; 
v___x_3198_ = lean_nat_add(v_a_3130_, v___x_3162_);
lean_dec(v_a_3130_);
v_a_3130_ = v___x_3198_;
v_b_3131_ = v___x_3197_;
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
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec_ref(v___x_3169_);
lean_del_object(v___x_3151_);
lean_dec(v_snd_3149_);
lean_dec(v_fst_3148_);
lean_del_object(v___x_3146_);
lean_dec(v_fst_3144_);
lean_dec(v_fst_3143_);
lean_dec(v_a_3130_);
lean_dec(v___x_3129_);
lean_dec_ref(v___x_3128_);
lean_dec(v___x_3127_);
lean_dec(v_matchDeclName_3126_);
lean_dec_ref(v___x_3125_);
lean_dec_ref(v___x_3124_);
lean_dec(v___x_3123_);
lean_dec_ref(v_a_3122_);
lean_dec_ref(v___x_3121_);
lean_dec(v_baseName_3120_);
lean_dec_ref(v_val_3119_);
v_a_3206_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3174_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3174_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v___x_3169_);
lean_dec_ref(v___f_3168_);
lean_del_object(v___x_3151_);
lean_dec(v_snd_3149_);
lean_dec(v_fst_3148_);
lean_del_object(v___x_3146_);
lean_dec(v_fst_3144_);
lean_dec(v_fst_3143_);
lean_dec(v_a_3130_);
lean_dec(v___x_3129_);
lean_dec_ref(v___x_3128_);
lean_dec(v___x_3127_);
lean_dec(v_matchDeclName_3126_);
lean_dec_ref(v___x_3125_);
lean_dec_ref(v___x_3124_);
lean_dec(v___x_3123_);
lean_dec_ref(v_a_3122_);
lean_dec_ref(v___x_3121_);
lean_dec(v_baseName_3120_);
lean_dec_ref(v_val_3119_);
v_a_3214_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3172_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3172_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
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
lean_object* v_upperBound_3229_ = _args[0];
lean_object* v_val_3230_ = _args[1];
lean_object* v_baseName_3231_ = _args[2];
lean_object* v___x_3232_ = _args[3];
lean_object* v_a_3233_ = _args[4];
lean_object* v___x_3234_ = _args[5];
lean_object* v___x_3235_ = _args[6];
lean_object* v___x_3236_ = _args[7];
lean_object* v_matchDeclName_3237_ = _args[8];
lean_object* v___x_3238_ = _args[9];
lean_object* v___x_3239_ = _args[10];
lean_object* v___x_3240_ = _args[11];
lean_object* v_a_3241_ = _args[12];
lean_object* v_b_3242_ = _args[13];
lean_object* v___y_3243_ = _args[14];
lean_object* v___y_3244_ = _args[15];
lean_object* v___y_3245_ = _args[16];
lean_object* v___y_3246_ = _args[17];
lean_object* v___y_3247_ = _args[18];
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3229_, v_val_3230_, v_baseName_3231_, v___x_3232_, v_a_3233_, v___x_3234_, v___x_3235_, v___x_3236_, v_matchDeclName_3237_, v___x_3238_, v___x_3239_, v___x_3240_, v_a_3241_, v_b_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v_upperBound_3229_);
return v_res_3248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3252_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3253_ = lean_unsigned_to_nat(6u);
v___x_3254_ = lean_unsigned_to_nat(233u);
v___x_3255_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3256_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3257_ = l_mkPanicMessageWithDecl(v___x_3256_, v___x_3255_, v___x_3254_, v___x_3253_, v___x_3252_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3270_, lean_object* v_matchDeclName_3271_, lean_object* v_numParams_3272_, lean_object* v_val_3273_, lean_object* v___x_3274_, lean_object* v_numDiscrs_3275_, lean_object* v_baseName_3276_, lean_object* v_a_3277_, lean_object* v___x_3278_, lean_object* v___x_3279_, lean_object* v___x_3280_, lean_object* v_uElimPos_x3f_3281_, lean_object* v_discrInfos_3282_, lean_object* v_overlaps_3283_, lean_object* v___f_3284_, lean_object* v___x_3285_, lean_object* v_altInfos_3286_, lean_object* v_xs_3287_, lean_object* v___matchResultType_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; uint8_t v___y_3306_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v_lower_3314_; lean_object* v_upper_3315_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v___x_3308_ = lean_box(0);
v___x_3309_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3272_);
lean_inc_ref(v_xs_3287_);
v___x_3310_ = l_Array_toSubarray___redArg(v_xs_3287_, v___x_3309_, v_numParams_3272_);
v___x_3311_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3273_);
v___x_3312_ = lean_array_get(v___x_3274_, v_xs_3287_, v___x_3311_);
lean_dec(v___x_3311_);
v___x_3368_ = lean_array_get_size(v_xs_3287_);
v___x_3369_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3273_);
v___x_3370_ = lean_nat_sub(v___x_3368_, v___x_3369_);
lean_dec(v___x_3369_);
v___x_3371_ = lean_nat_dec_le(v___x_3370_, v___x_3309_);
if (v___x_3371_ == 0)
{
v_lower_3314_ = v___x_3370_;
v_upper_3315_ = v___x_3368_;
goto v___jp_3313_;
}
else
{
lean_dec(v___x_3370_);
v_lower_3314_ = v___x_3309_;
v_upper_3315_ = v___x_3368_;
goto v___jp_3313_;
}
v___jp_3294_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3296_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3295_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
return v___x_3296_;
}
v___jp_3297_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3300_, 0, v___y_3299_);
lean_ctor_set(v___x_3300_, 1, v_splitterName_3270_);
lean_ctor_set(v___x_3300_, 2, v___y_3298_);
v___x_3301_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3271_, v___x_3300_, v___y_3292_);
return v___x_3301_;
}
v___jp_3302_:
{
lean_object* v___x_3307_; 
lean_inc(v_matchDeclName_3271_);
v___x_3307_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3271_, v___y_3306_, v___y_3305_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_dec_ref_known(v___x_3307_, 1);
v___y_3298_ = v___y_3303_;
v___y_3299_ = v___y_3304_;
goto v___jp_3297_;
}
else
{
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v_matchDeclName_3271_);
lean_dec(v_splitterName_3270_);
return v___x_3307_;
}
}
v___jp_3313_:
{
lean_object* v___x_3316_; lean_object* v_start_3317_; lean_object* v_stop_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_inc_ref(v_xs_3287_);
v___x_3316_ = l_Array_toSubarray___redArg(v_xs_3287_, v_lower_3314_, v_upper_3315_);
v_start_3317_ = lean_ctor_get(v___x_3316_, 1);
lean_inc(v_start_3317_);
v_stop_3318_ = lean_ctor_get(v___x_3316_, 2);
lean_inc(v_stop_3318_);
v___x_3319_ = lean_unsigned_to_nat(1u);
v___x_3320_ = lean_nat_add(v_numParams_3272_, v___x_3319_);
v___x_3321_ = lean_nat_add(v___x_3320_, v_numDiscrs_3275_);
v___x_3322_ = lean_nat_sub(v_stop_3318_, v_start_3317_);
lean_dec(v_start_3317_);
lean_dec(v_stop_3318_);
v___x_3323_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3324_ = l_Array_toSubarray___redArg(v_xs_3287_, v___x_3320_, v___x_3321_);
lean_inc(v___x_3279_);
lean_inc(v_matchDeclName_3271_);
lean_inc(v___x_3278_);
v___x_3325_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3322_, v_val_3273_, v_baseName_3276_, v___x_3324_, v_a_3277_, v___x_3278_, v___x_3310_, v___x_3312_, v_matchDeclName_3271_, v___x_3279_, v___x_3316_, v___x_3280_, v___x_3309_, v___x_3323_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___x_3322_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v_snd_3327_; lean_object* v_snd_3328_; lean_object* v_snd_3329_; lean_object* v_fst_3330_; lean_object* v_fst_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3358_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v_snd_3327_ = lean_ctor_get(v_a_3326_, 1);
v_snd_3328_ = lean_ctor_get(v_snd_3327_, 1);
v_snd_3329_ = lean_ctor_get(v_snd_3328_, 1);
lean_inc(v_snd_3329_);
v_fst_3330_ = lean_ctor_get(v_a_3326_, 0);
lean_inc(v_fst_3330_);
lean_dec(v_a_3326_);
v_fst_3331_ = lean_ctor_get(v_snd_3329_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_snd_3329_);
if (v_isSharedCheck_3358_ == 0)
{
lean_object* v_unused_3359_; 
v_unused_3359_ = lean_ctor_get(v_snd_3329_, 1);
lean_dec(v_unused_3359_);
v___x_3333_ = v_snd_3329_;
v_isShared_3334_ = v_isSharedCheck_3358_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_fst_3331_);
lean_dec(v_snd_3329_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3358_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; uint8_t v___x_3336_; 
lean_inc_ref(v_overlaps_3283_);
lean_inc(v_fst_3331_);
v___x_3335_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3335_, 0, v_numParams_3272_);
lean_ctor_set(v___x_3335_, 1, v_numDiscrs_3275_);
lean_ctor_set(v___x_3335_, 2, v_fst_3331_);
lean_ctor_set(v___x_3335_, 3, v_uElimPos_x3f_3281_);
lean_ctor_set(v___x_3335_, 4, v_discrInfos_3282_);
lean_ctor_set(v___x_3335_, 5, v_overlaps_3283_);
v___x_3336_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3283_);
lean_dec_ref(v_overlaps_3283_);
if (v___x_3336_ == 0)
{
uint8_t v___x_3337_; 
lean_del_object(v___x_3333_);
lean_dec(v_fst_3331_);
lean_dec_ref(v___x_3285_);
lean_dec(v___x_3279_);
lean_dec(v___x_3278_);
v___x_3337_ = 1;
v___y_3303_ = v___x_3335_;
v___y_3304_ = v_fst_3330_;
v___y_3305_ = v___f_3284_;
v___y_3306_ = v___x_3337_;
goto v___jp_3302_;
}
else
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3339_ = lean_find_expr(v___x_3338_, v___x_3285_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; 
lean_dec_ref(v___f_3284_);
v___x_3340_ = lean_array_get_size(v_altInfos_3286_);
v___x_3341_ = lean_array_get_size(v_fst_3331_);
v___x_3342_ = lean_nat_dec_eq(v___x_3340_, v___x_3341_);
if (v___x_3342_ == 0)
{
lean_dec_ref_known(v___x_3335_, 6);
lean_del_object(v___x_3333_);
lean_dec(v_fst_3331_);
lean_dec(v_fst_3330_);
lean_dec_ref(v___x_3285_);
lean_dec(v___x_3279_);
lean_dec(v___x_3278_);
lean_dec(v_matchDeclName_3271_);
lean_dec(v_splitterName_3270_);
goto v___jp_3294_;
}
else
{
uint8_t v___x_3343_; 
v___x_3343_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3286_, v_fst_3331_, v___x_3340_);
lean_dec(v_fst_3331_);
if (v___x_3343_ == 0)
{
lean_dec_ref_known(v___x_3335_, 6);
lean_del_object(v___x_3333_);
lean_dec(v_fst_3330_);
lean_dec_ref(v___x_3285_);
lean_dec(v___x_3279_);
lean_dec(v___x_3278_);
lean_dec(v_matchDeclName_3271_);
lean_dec(v_splitterName_3270_);
goto v___jp_3294_;
}
else
{
uint8_t v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; lean_object* v___x_3350_; 
v___x_3344_ = 0;
lean_inc_n(v_splitterName_3270_, 2);
v___x_3345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3345_, 0, v_splitterName_3270_);
lean_ctor_set(v___x_3345_, 1, v___x_3279_);
lean_ctor_set(v___x_3345_, 2, v___x_3285_);
lean_inc(v_matchDeclName_3271_);
v___x_3346_ = l_Lean_mkConst(v_matchDeclName_3271_, v___x_3278_);
v___x_3347_ = lean_box(1);
v___x_3348_ = 1;
if (v_isShared_3334_ == 0)
{
lean_ctor_set_tag(v___x_3333_, 1);
lean_ctor_set(v___x_3333_, 1, v___x_3308_);
lean_ctor_set(v___x_3333_, 0, v_splitterName_3270_);
v___x_3350_ = v___x_3333_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_splitterName_3270_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v___x_3308_);
v___x_3350_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3351_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3351_, 0, v___x_3345_);
lean_ctor_set(v___x_3351_, 1, v___x_3346_);
lean_ctor_set(v___x_3351_, 2, v___x_3347_);
lean_ctor_set(v___x_3351_, 3, v___x_3350_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*4, v___x_3348_);
v___x_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
lean_inc_ref(v___x_3352_);
v___x_3353_ = l_Lean_addDecl(v___x_3352_, v___x_3344_, v___y_3291_, v___y_3292_);
if (lean_obj_tag(v___x_3353_) == 0)
{
uint8_t v___x_3354_; lean_object* v___x_3355_; 
lean_dec_ref_known(v___x_3353_, 1);
v___x_3354_ = 0;
lean_inc(v_splitterName_3270_);
v___x_3355_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3270_, v___x_3354_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v___x_3356_; 
lean_dec_ref_known(v___x_3355_, 1);
v___x_3356_ = l_Lean_compileDecl(v___x_3352_, v___x_3344_, v___y_3291_, v___y_3292_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_dec_ref_known(v___x_3356_, 1);
v___y_3298_ = v___x_3335_;
v___y_3299_ = v_fst_3330_;
goto v___jp_3297_;
}
else
{
lean_dec_ref_known(v___x_3335_, 6);
lean_dec(v_fst_3330_);
lean_dec(v_matchDeclName_3271_);
lean_dec(v_splitterName_3270_);
return v___x_3356_;
}
}
else
{
lean_dec_ref_known(v___x_3352_, 1);
lean_dec_ref_known(v___x_3335_, 6);
lean_dec(v_fst_3330_);
lean_dec(v_matchDeclName_3271_);
lean_dec(v_splitterName_3270_);
return v___x_3355_;
}
}
else
{
lean_dec_ref_known(v___x_3352_, 1);
lean_dec_ref_known(v___x_3335_, 6);
lean_dec(v_fst_3330_);
lean_dec(v_matchDeclName_3271_);
lean_dec(v_splitterName_3270_);
return v___x_3353_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3339_, 1);
lean_del_object(v___x_3333_);
lean_dec(v_fst_3331_);
lean_dec_ref(v___x_3285_);
lean_dec(v___x_3279_);
lean_dec(v___x_3278_);
v___y_3303_ = v___x_3335_;
v___y_3304_ = v_fst_3330_;
v___y_3305_ = v___f_3284_;
v___y_3306_ = v___x_3336_;
goto v___jp_3302_;
}
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_dec_ref(v___x_3285_);
lean_dec_ref(v___f_3284_);
lean_dec_ref(v_overlaps_3283_);
lean_dec_ref(v_discrInfos_3282_);
lean_dec(v_uElimPos_x3f_3281_);
lean_dec(v___x_3279_);
lean_dec(v___x_3278_);
lean_dec(v_numDiscrs_3275_);
lean_dec(v_numParams_3272_);
lean_dec(v_matchDeclName_3271_);
lean_dec(v_splitterName_3270_);
v_a_3360_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3325_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3325_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3372_ = _args[0];
lean_object* v_matchDeclName_3373_ = _args[1];
lean_object* v_numParams_3374_ = _args[2];
lean_object* v_val_3375_ = _args[3];
lean_object* v___x_3376_ = _args[4];
lean_object* v_numDiscrs_3377_ = _args[5];
lean_object* v_baseName_3378_ = _args[6];
lean_object* v_a_3379_ = _args[7];
lean_object* v___x_3380_ = _args[8];
lean_object* v___x_3381_ = _args[9];
lean_object* v___x_3382_ = _args[10];
lean_object* v_uElimPos_x3f_3383_ = _args[11];
lean_object* v_discrInfos_3384_ = _args[12];
lean_object* v_overlaps_3385_ = _args[13];
lean_object* v___f_3386_ = _args[14];
lean_object* v___x_3387_ = _args[15];
lean_object* v_altInfos_3388_ = _args[16];
lean_object* v_xs_3389_ = _args[17];
lean_object* v___matchResultType_3390_ = _args[18];
lean_object* v___y_3391_ = _args[19];
lean_object* v___y_3392_ = _args[20];
lean_object* v___y_3393_ = _args[21];
lean_object* v___y_3394_ = _args[22];
lean_object* v___y_3395_ = _args[23];
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3372_, v_matchDeclName_3373_, v_numParams_3374_, v_val_3375_, v___x_3376_, v_numDiscrs_3377_, v_baseName_3378_, v_a_3379_, v___x_3380_, v___x_3381_, v___x_3382_, v_uElimPos_x3f_3383_, v_discrInfos_3384_, v_overlaps_3385_, v___f_3386_, v___x_3387_, v_altInfos_3388_, v_xs_3389_, v___matchResultType_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec_ref(v___matchResultType_3390_);
lean_dec_ref(v_altInfos_3388_);
lean_dec_ref(v___x_3376_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_a_3397_, lean_object* v_a_3398_){
_start:
{
if (lean_obj_tag(v_a_3397_) == 0)
{
lean_object* v___x_3399_; 
v___x_3399_ = l_List_reverse___redArg(v_a_3398_);
return v___x_3399_;
}
else
{
lean_object* v_head_3400_; lean_object* v_tail_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3410_; 
v_head_3400_ = lean_ctor_get(v_a_3397_, 0);
v_tail_3401_ = lean_ctor_get(v_a_3397_, 1);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_a_3397_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3403_ = v_a_3397_;
v_isShared_3404_ = v_isSharedCheck_3410_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_tail_3401_);
lean_inc(v_head_3400_);
lean_dec(v_a_3397_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3410_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3405_ = l_Lean_mkLevelParam(v_head_3400_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 1, v_a_3398_);
lean_ctor_set(v___x_3403_, 0, v___x_3405_);
v___x_3407_ = v___x_3403_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_a_3398_);
v___x_3407_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
v_a_3397_ = v_tail_3401_;
v_a_3398_ = v___x_3407_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3411_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
return v___x_3413_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3414_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3415_ = lean_unsigned_to_nat(0u);
v___x_3416_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
lean_ctor_set(v___x_3416_, 2, v___x_3415_);
lean_ctor_set(v___x_3416_, 3, v___x_3415_);
lean_ctor_set(v___x_3416_, 4, v___x_3414_);
lean_ctor_set(v___x_3416_, 5, v___x_3414_);
lean_ctor_set(v___x_3416_, 6, v___x_3414_);
lean_ctor_set(v___x_3416_, 7, v___x_3414_);
lean_ctor_set(v___x_3416_, 8, v___x_3414_);
lean_ctor_set(v___x_3416_, 9, v___x_3414_);
return v___x_3416_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3417_ = lean_box(1);
v___x_3418_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3419_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
lean_ctor_set(v___x_3420_, 1, v___x_3418_);
lean_ctor_set(v___x_3420_, 2, v___x_3417_);
return v___x_3420_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_3423_ = l_Lean_stringToMessageData(v___x_3422_);
return v___x_3423_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_3426_ = l_Lean_stringToMessageData(v___x_3425_);
return v___x_3426_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_3429_ = l_Lean_stringToMessageData(v___x_3428_);
return v___x_3429_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_3432_ = l_Lean_stringToMessageData(v___x_3431_);
return v___x_3432_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_3435_ = l_Lean_stringToMessageData(v___x_3434_);
return v___x_3435_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3437_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_3438_ = l_Lean_stringToMessageData(v___x_3437_);
return v___x_3438_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_3441_ = l_Lean_stringToMessageData(v___x_3440_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3442_, lean_object* v_declHint_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; lean_object* v_env_3447_; uint8_t v___x_3448_; 
v___x_3446_ = lean_st_ref_get(v___y_3444_);
v_env_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc_ref(v_env_3447_);
lean_dec(v___x_3446_);
v___x_3448_ = l_Lean_Name_isAnonymous(v_declHint_3443_);
if (v___x_3448_ == 0)
{
uint8_t v_isExporting_3449_; 
v_isExporting_3449_ = lean_ctor_get_uint8(v_env_3447_, sizeof(void*)*8);
if (v_isExporting_3449_ == 0)
{
lean_object* v___x_3450_; 
lean_dec_ref(v_env_3447_);
lean_dec(v_declHint_3443_);
v___x_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3450_, 0, v_msg_3442_);
return v___x_3450_;
}
else
{
lean_object* v___x_3451_; uint8_t v___x_3452_; 
lean_inc_ref(v_env_3447_);
v___x_3451_ = l_Lean_Environment_setExporting(v_env_3447_, v___x_3448_);
lean_inc(v_declHint_3443_);
lean_inc_ref(v___x_3451_);
v___x_3452_ = l_Lean_Environment_contains(v___x_3451_, v_declHint_3443_, v_isExporting_3449_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; 
lean_dec_ref(v___x_3451_);
lean_dec_ref(v_env_3447_);
lean_dec(v_declHint_3443_);
v___x_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3453_, 0, v_msg_3442_);
return v___x_3453_;
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v_c_3459_; lean_object* v___x_3460_; 
v___x_3454_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3456_ = l_Lean_Options_empty;
v___x_3457_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3451_);
lean_ctor_set(v___x_3457_, 1, v___x_3454_);
lean_ctor_set(v___x_3457_, 2, v___x_3455_);
lean_ctor_set(v___x_3457_, 3, v___x_3456_);
lean_inc(v_declHint_3443_);
v___x_3458_ = l_Lean_MessageData_ofConstName(v_declHint_3443_, v___x_3448_);
v_c_3459_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3459_, 0, v___x_3457_);
lean_ctor_set(v_c_3459_, 1, v___x_3458_);
v___x_3460_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3447_, v_declHint_3443_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec_ref(v_env_3447_);
lean_dec(v_declHint_3443_);
v___x_3461_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
lean_ctor_set(v___x_3462_, 1, v_c_3459_);
v___x_3463_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3462_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = l_Lean_MessageData_note(v___x_3464_);
v___x_3466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3466_, 0, v_msg_3442_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
return v___x_3467_;
}
else
{
lean_object* v_val_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3503_; 
v_val_3468_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3470_ = v___x_3460_;
v_isShared_3471_ = v_isSharedCheck_3503_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_val_3468_);
lean_dec(v___x_3460_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3503_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v_mod_3475_; uint8_t v___x_3476_; 
v___x_3472_ = lean_box(0);
v___x_3473_ = l_Lean_Environment_header(v_env_3447_);
lean_dec_ref(v_env_3447_);
v___x_3474_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3473_);
v_mod_3475_ = lean_array_get(v___x_3472_, v___x_3474_, v_val_3468_);
lean_dec(v_val_3468_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = l_Lean_isPrivateName(v_declHint_3443_);
lean_dec(v_declHint_3443_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3477_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v_c_3459_);
v___x_3479_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = l_Lean_MessageData_ofName(v_mod_3475_);
v___x_3482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3482_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = l_Lean_MessageData_note(v___x_3484_);
v___x_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3486_, 0, v_msg_3442_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set_tag(v___x_3470_, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3486_);
v___x_3488_ = v___x_3470_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3490_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v_c_3459_);
v___x_3492_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3491_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = l_Lean_MessageData_ofName(v_mod_3475_);
v___x_3495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3495_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = l_Lean_MessageData_note(v___x_3497_);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v_msg_3442_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set_tag(v___x_3470_, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3499_);
v___x_3501_ = v___x_3470_;
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
}
}
}
else
{
lean_object* v___x_3504_; 
lean_dec_ref(v_env_3447_);
lean_dec(v_declHint_3443_);
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v_msg_3442_);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3505_, lean_object* v_declHint_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3505_, v_declHint_3506_, v___y_3507_);
lean_dec(v___y_3507_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3510_, lean_object* v_declHint_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3527_; 
v___x_3517_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3510_, v_declHint_3511_, v___y_3515_);
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3520_ = v___x_3517_;
v_isShared_3521_ = v_isSharedCheck_3527_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3517_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3527_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3522_ = l_Lean_unknownIdentifierMessageTag;
v___x_3523_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
lean_ctor_set(v___x_3523_, 1, v_a_3518_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3523_);
v___x_3525_ = v___x_3520_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3528_, lean_object* v_declHint_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3528_, v_declHint_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3536_, lean_object* v_msg_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v_fileName_3543_; lean_object* v_fileMap_3544_; lean_object* v_options_3545_; lean_object* v_currRecDepth_3546_; lean_object* v_maxRecDepth_3547_; lean_object* v_ref_3548_; lean_object* v_currNamespace_3549_; lean_object* v_openDecls_3550_; lean_object* v_initHeartbeats_3551_; lean_object* v_maxHeartbeats_3552_; lean_object* v_quotContext_3553_; lean_object* v_currMacroScope_3554_; uint8_t v_diag_3555_; lean_object* v_cancelTk_x3f_3556_; uint8_t v_suppressElabErrors_3557_; lean_object* v_inheritedTraceOptions_3558_; lean_object* v_ref_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v_fileName_3543_ = lean_ctor_get(v___y_3540_, 0);
v_fileMap_3544_ = lean_ctor_get(v___y_3540_, 1);
v_options_3545_ = lean_ctor_get(v___y_3540_, 2);
v_currRecDepth_3546_ = lean_ctor_get(v___y_3540_, 3);
v_maxRecDepth_3547_ = lean_ctor_get(v___y_3540_, 4);
v_ref_3548_ = lean_ctor_get(v___y_3540_, 5);
v_currNamespace_3549_ = lean_ctor_get(v___y_3540_, 6);
v_openDecls_3550_ = lean_ctor_get(v___y_3540_, 7);
v_initHeartbeats_3551_ = lean_ctor_get(v___y_3540_, 8);
v_maxHeartbeats_3552_ = lean_ctor_get(v___y_3540_, 9);
v_quotContext_3553_ = lean_ctor_get(v___y_3540_, 10);
v_currMacroScope_3554_ = lean_ctor_get(v___y_3540_, 11);
v_diag_3555_ = lean_ctor_get_uint8(v___y_3540_, sizeof(void*)*14);
v_cancelTk_x3f_3556_ = lean_ctor_get(v___y_3540_, 12);
v_suppressElabErrors_3557_ = lean_ctor_get_uint8(v___y_3540_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3558_ = lean_ctor_get(v___y_3540_, 13);
v_ref_3559_ = l_Lean_replaceRef(v_ref_3536_, v_ref_3548_);
lean_inc_ref(v_inheritedTraceOptions_3558_);
lean_inc(v_cancelTk_x3f_3556_);
lean_inc(v_currMacroScope_3554_);
lean_inc(v_quotContext_3553_);
lean_inc(v_maxHeartbeats_3552_);
lean_inc(v_initHeartbeats_3551_);
lean_inc(v_openDecls_3550_);
lean_inc(v_currNamespace_3549_);
lean_inc(v_maxRecDepth_3547_);
lean_inc(v_currRecDepth_3546_);
lean_inc_ref(v_options_3545_);
lean_inc_ref(v_fileMap_3544_);
lean_inc_ref(v_fileName_3543_);
v___x_3560_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3560_, 0, v_fileName_3543_);
lean_ctor_set(v___x_3560_, 1, v_fileMap_3544_);
lean_ctor_set(v___x_3560_, 2, v_options_3545_);
lean_ctor_set(v___x_3560_, 3, v_currRecDepth_3546_);
lean_ctor_set(v___x_3560_, 4, v_maxRecDepth_3547_);
lean_ctor_set(v___x_3560_, 5, v_ref_3559_);
lean_ctor_set(v___x_3560_, 6, v_currNamespace_3549_);
lean_ctor_set(v___x_3560_, 7, v_openDecls_3550_);
lean_ctor_set(v___x_3560_, 8, v_initHeartbeats_3551_);
lean_ctor_set(v___x_3560_, 9, v_maxHeartbeats_3552_);
lean_ctor_set(v___x_3560_, 10, v_quotContext_3553_);
lean_ctor_set(v___x_3560_, 11, v_currMacroScope_3554_);
lean_ctor_set(v___x_3560_, 12, v_cancelTk_x3f_3556_);
lean_ctor_set(v___x_3560_, 13, v_inheritedTraceOptions_3558_);
lean_ctor_set_uint8(v___x_3560_, sizeof(void*)*14, v_diag_3555_);
lean_ctor_set_uint8(v___x_3560_, sizeof(void*)*14 + 1, v_suppressElabErrors_3557_);
v___x_3561_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3537_, v___y_3538_, v___y_3539_, v___x_3560_, v___y_3541_);
lean_dec_ref_known(v___x_3560_, 14);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3562_, lean_object* v_msg_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3562_, v_msg_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v_ref_3562_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3570_, lean_object* v_msg_3571_, lean_object* v_declHint_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v___x_3578_; lean_object* v_a_3579_; lean_object* v___x_3580_; 
v___x_3578_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3571_, v_declHint_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_a_3579_);
lean_dec_ref(v___x_3578_);
v___x_3580_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3570_, v_a_3579_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3581_, lean_object* v_msg_3582_, lean_object* v_declHint_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3581_, v_msg_3582_, v_declHint_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v_ref_3581_);
return v_res_3589_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3592_ = l_Lean_stringToMessageData(v___x_3591_);
return v___x_3592_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3595_ = l_Lean_stringToMessageData(v___x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3596_, lean_object* v_constName_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___x_3603_; uint8_t v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3603_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3604_ = 0;
lean_inc(v_constName_3597_);
v___x_3605_ = l_Lean_MessageData_ofConstName(v_constName_3597_, v___x_3604_);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3603_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3606_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3596_, v___x_3608_, v_constName_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3610_, lean_object* v_constName_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3610_, v_constName_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v_ref_3610_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_ref_3624_; lean_object* v___x_3625_; 
v_ref_3624_ = lean_ctor_get(v___y_3621_, 5);
v___x_3625_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3624_, v_constName_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3639_; lean_object* v_env_3640_; uint8_t v___x_3641_; lean_object* v___x_3642_; 
v___x_3639_ = lean_st_ref_get(v___y_3637_);
v_env_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc_ref(v_env_3640_);
lean_dec(v___x_3639_);
v___x_3641_ = 0;
lean_inc(v_constName_3633_);
v___x_3642_ = l_Lean_Environment_find_x3f(v_env_3640_, v_constName_3633_, v___x_3641_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v___x_3643_; 
v___x_3643_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
return v___x_3643_;
}
else
{
lean_object* v_val_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_dec(v_constName_3633_);
v_val_3644_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3642_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_val_3644_);
lean_dec(v___x_3642_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set_tag(v___x_3646_, 0);
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_val_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
return v_res_3658_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3661_ = l_Lean_stringToMessageData(v___x_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3662_, lean_object* v_baseName_3663_, lean_object* v_splitterName_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v___x_3670_; uint8_t v_foApprox_3671_; uint8_t v_ctxApprox_3672_; uint8_t v_quasiPatternApprox_3673_; uint8_t v_constApprox_3674_; uint8_t v_isDefEqStuckEx_3675_; uint8_t v_unificationHints_3676_; uint8_t v_proofIrrelevance_3677_; uint8_t v_assignSyntheticOpaque_3678_; uint8_t v_offsetCnstrs_3679_; uint8_t v_transparency_3680_; uint8_t v_univApprox_3681_; uint8_t v_iota_3682_; uint8_t v_beta_3683_; uint8_t v_proj_3684_; uint8_t v_zeta_3685_; uint8_t v_zetaDelta_3686_; uint8_t v_zetaUnused_3687_; uint8_t v_zetaHave_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3751_; 
v___x_3670_ = l_Lean_Meta_Context_config(v_a_3665_);
v_foApprox_3671_ = lean_ctor_get_uint8(v___x_3670_, 0);
v_ctxApprox_3672_ = lean_ctor_get_uint8(v___x_3670_, 1);
v_quasiPatternApprox_3673_ = lean_ctor_get_uint8(v___x_3670_, 2);
v_constApprox_3674_ = lean_ctor_get_uint8(v___x_3670_, 3);
v_isDefEqStuckEx_3675_ = lean_ctor_get_uint8(v___x_3670_, 4);
v_unificationHints_3676_ = lean_ctor_get_uint8(v___x_3670_, 5);
v_proofIrrelevance_3677_ = lean_ctor_get_uint8(v___x_3670_, 6);
v_assignSyntheticOpaque_3678_ = lean_ctor_get_uint8(v___x_3670_, 7);
v_offsetCnstrs_3679_ = lean_ctor_get_uint8(v___x_3670_, 8);
v_transparency_3680_ = lean_ctor_get_uint8(v___x_3670_, 9);
v_univApprox_3681_ = lean_ctor_get_uint8(v___x_3670_, 11);
v_iota_3682_ = lean_ctor_get_uint8(v___x_3670_, 12);
v_beta_3683_ = lean_ctor_get_uint8(v___x_3670_, 13);
v_proj_3684_ = lean_ctor_get_uint8(v___x_3670_, 14);
v_zeta_3685_ = lean_ctor_get_uint8(v___x_3670_, 15);
v_zetaDelta_3686_ = lean_ctor_get_uint8(v___x_3670_, 16);
v_zetaUnused_3687_ = lean_ctor_get_uint8(v___x_3670_, 17);
v_zetaHave_3688_ = lean_ctor_get_uint8(v___x_3670_, 18);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3690_ = v___x_3670_;
v_isShared_3691_ = v_isSharedCheck_3751_;
goto v_resetjp_3689_;
}
else
{
lean_dec(v___x_3670_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3751_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
uint8_t v_trackZetaDelta_3692_; lean_object* v_zetaDeltaSet_3693_; lean_object* v_lctx_3694_; lean_object* v_localInstances_3695_; lean_object* v_defEqCtx_x3f_3696_; lean_object* v_synthPendingDepth_3697_; lean_object* v_canUnfold_x3f_3698_; uint8_t v_univApprox_3699_; uint8_t v_inTypeClassResolution_3700_; uint8_t v_cacheInferType_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3749_; 
v_trackZetaDelta_3692_ = lean_ctor_get_uint8(v_a_3665_, sizeof(void*)*7);
v_zetaDeltaSet_3693_ = lean_ctor_get(v_a_3665_, 1);
v_lctx_3694_ = lean_ctor_get(v_a_3665_, 2);
v_localInstances_3695_ = lean_ctor_get(v_a_3665_, 3);
v_defEqCtx_x3f_3696_ = lean_ctor_get(v_a_3665_, 4);
v_synthPendingDepth_3697_ = lean_ctor_get(v_a_3665_, 5);
v_canUnfold_x3f_3698_ = lean_ctor_get(v_a_3665_, 6);
v_univApprox_3699_ = lean_ctor_get_uint8(v_a_3665_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3700_ = lean_ctor_get_uint8(v_a_3665_, sizeof(void*)*7 + 2);
v_cacheInferType_3701_ = lean_ctor_get_uint8(v_a_3665_, sizeof(void*)*7 + 3);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_a_3665_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; 
v_unused_3750_ = lean_ctor_get(v_a_3665_, 0);
lean_dec(v_unused_3750_);
v___x_3703_ = v_a_3665_;
v_isShared_3704_ = v_isSharedCheck_3749_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_canUnfold_x3f_3698_);
lean_inc(v_synthPendingDepth_3697_);
lean_inc(v_defEqCtx_x3f_3696_);
lean_inc(v_localInstances_3695_);
lean_inc(v_lctx_3694_);
lean_inc(v_zetaDeltaSet_3693_);
lean_dec(v_a_3665_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3749_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
uint8_t v___x_3705_; lean_object* v___x_3707_; 
v___x_3705_ = 2;
if (v_isShared_3691_ == 0)
{
v___x_3707_ = v___x_3690_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 0, v_foApprox_3671_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 1, v_ctxApprox_3672_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 2, v_quasiPatternApprox_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 3, v_constApprox_3674_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 4, v_isDefEqStuckEx_3675_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 5, v_unificationHints_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 6, v_proofIrrelevance_3677_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 7, v_assignSyntheticOpaque_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 8, v_offsetCnstrs_3679_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 9, v_transparency_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 11, v_univApprox_3681_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 12, v_iota_3682_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 13, v_beta_3683_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 14, v_proj_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 15, v_zeta_3685_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 16, v_zetaDelta_3686_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 17, v_zetaUnused_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3748_, 18, v_zetaHave_3688_);
v___x_3707_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
uint64_t v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3711_; 
lean_ctor_set_uint8(v___x_3707_, 10, v___x_3705_);
v___x_3708_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3707_);
v___x_3709_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set_uint64(v___x_3709_, sizeof(void*)*1, v___x_3708_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3709_);
v___x_3711_ = v___x_3703_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_zetaDeltaSet_3693_);
lean_ctor_set(v_reuseFailAlloc_3747_, 2, v_lctx_3694_);
lean_ctor_set(v_reuseFailAlloc_3747_, 3, v_localInstances_3695_);
lean_ctor_set(v_reuseFailAlloc_3747_, 4, v_defEqCtx_x3f_3696_);
lean_ctor_set(v_reuseFailAlloc_3747_, 5, v_synthPendingDepth_3697_);
lean_ctor_set(v_reuseFailAlloc_3747_, 6, v_canUnfold_x3f_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, sizeof(void*)*7, v_trackZetaDelta_3692_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, sizeof(void*)*7 + 1, v_univApprox_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3700_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, sizeof(void*)*7 + 3, v_cacheInferType_3701_);
v___x_3711_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3712_; 
lean_inc(v_matchDeclName_3662_);
v___x_3712_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3662_, v___x_3711_, v_a_3666_, v_a_3667_, v_a_3668_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; lean_object* v_a_3715_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
lean_inc(v_matchDeclName_3662_);
v___x_3714_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_3662_, v_a_3668_);
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc(v_a_3715_);
lean_dec_ref(v___x_3714_);
if (lean_obj_tag(v_a_3715_) == 1)
{
lean_object* v_val_3716_; lean_object* v_numParams_3717_; lean_object* v_numDiscrs_3718_; lean_object* v_altInfos_3719_; lean_object* v_uElimPos_x3f_3720_; lean_object* v_discrInfos_3721_; lean_object* v_overlaps_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___f_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___f_3730_; uint8_t v___x_3731_; lean_object* v___x_3732_; 
v_val_3716_ = lean_ctor_get(v_a_3715_, 0);
lean_inc(v_val_3716_);
lean_dec_ref_known(v_a_3715_, 1);
v_numParams_3717_ = lean_ctor_get(v_val_3716_, 0);
lean_inc(v_numParams_3717_);
v_numDiscrs_3718_ = lean_ctor_get(v_val_3716_, 1);
lean_inc(v_numDiscrs_3718_);
v_altInfos_3719_ = lean_ctor_get(v_val_3716_, 2);
lean_inc_ref(v_altInfos_3719_);
v_uElimPos_x3f_3720_ = lean_ctor_get(v_val_3716_, 3);
lean_inc(v_uElimPos_x3f_3720_);
v_discrInfos_3721_ = lean_ctor_get(v_val_3716_, 4);
lean_inc_ref(v_discrInfos_3721_);
v_overlaps_3722_ = lean_ctor_get(v_val_3716_, 5);
lean_inc_ref_n(v_overlaps_3722_, 2);
v___x_3723_ = l_Lean_instInhabitedExpr;
v___x_3724_ = l_Lean_ConstantInfo_levelParams(v_a_3713_);
v___x_3725_ = lean_box(0);
lean_inc(v___x_3724_);
v___x_3726_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_3724_, v___x_3725_);
lean_inc(v_splitterName_3664_);
v___f_3727_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3727_, 0, v_overlaps_3722_);
lean_closure_set(v___f_3727_, 1, v_splitterName_3664_);
v___x_3728_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3721_);
v___x_3729_ = l_Lean_ConstantInfo_type(v_a_3713_);
lean_inc_ref(v___x_3729_);
v___f_3730_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3730_, 0, v_splitterName_3664_);
lean_closure_set(v___f_3730_, 1, v_matchDeclName_3662_);
lean_closure_set(v___f_3730_, 2, v_numParams_3717_);
lean_closure_set(v___f_3730_, 3, v_val_3716_);
lean_closure_set(v___f_3730_, 4, v___x_3723_);
lean_closure_set(v___f_3730_, 5, v_numDiscrs_3718_);
lean_closure_set(v___f_3730_, 6, v_baseName_3663_);
lean_closure_set(v___f_3730_, 7, v_a_3713_);
lean_closure_set(v___f_3730_, 8, v___x_3726_);
lean_closure_set(v___f_3730_, 9, v___x_3724_);
lean_closure_set(v___f_3730_, 10, v___x_3728_);
lean_closure_set(v___f_3730_, 11, v_uElimPos_x3f_3720_);
lean_closure_set(v___f_3730_, 12, v_discrInfos_3721_);
lean_closure_set(v___f_3730_, 13, v_overlaps_3722_);
lean_closure_set(v___f_3730_, 14, v___f_3727_);
lean_closure_set(v___f_3730_, 15, v___x_3729_);
lean_closure_set(v___f_3730_, 16, v_altInfos_3719_);
v___x_3731_ = 0;
v___x_3732_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3729_, v___f_3730_, v___x_3731_, v___x_3731_, v___x_3711_, v_a_3666_, v_a_3667_, v_a_3668_);
lean_dec_ref(v___x_3711_);
return v___x_3732_;
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
lean_dec(v_a_3715_);
lean_dec(v_a_3713_);
lean_dec(v_splitterName_3664_);
lean_dec(v_baseName_3663_);
v___x_3733_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3734_ = l_Lean_MessageData_ofName(v_matchDeclName_3662_);
v___x_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3735_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3737_, v___x_3711_, v_a_3666_, v_a_3667_, v_a_3668_);
lean_dec_ref(v___x_3711_);
return v___x_3738_;
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec_ref(v___x_3711_);
lean_dec(v_splitterName_3664_);
lean_dec(v_baseName_3663_);
lean_dec(v_matchDeclName_3662_);
v_a_3739_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3712_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3712_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3752_, lean_object* v_baseName_3753_, lean_object* v_splitterName_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3752_, v_baseName_3753_, v_splitterName_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
return v_res_3760_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3761_, lean_object* v_ys_3762_, lean_object* v_hsz_3763_, lean_object* v_x_3764_, lean_object* v_x_3765_){
_start:
{
uint8_t v___x_3766_; 
v___x_3766_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3761_, v_ys_3762_, v_x_3764_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3767_, lean_object* v_ys_3768_, lean_object* v_hsz_3769_, lean_object* v_x_3770_, lean_object* v_x_3771_){
_start:
{
uint8_t v_res_3772_; lean_object* v_r_3773_; 
v_res_3772_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3767_, v_ys_3768_, v_hsz_3769_, v_x_3770_, v_x_3771_);
lean_dec_ref(v_ys_3768_);
lean_dec_ref(v_xs_3767_);
v_r_3773_ = lean_box(v_res_3772_);
return v_r_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3774_, lean_object* v_R_3775_, lean_object* v_a_3776_, lean_object* v_b_3777_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3776_, v_b_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3779_, lean_object* v_val_3780_, lean_object* v_baseName_3781_, lean_object* v___x_3782_, lean_object* v_a_3783_, lean_object* v___x_3784_, lean_object* v___x_3785_, lean_object* v___x_3786_, lean_object* v_matchDeclName_3787_, lean_object* v___x_3788_, lean_object* v___x_3789_, lean_object* v___x_3790_, lean_object* v_inst_3791_, lean_object* v_R_3792_, lean_object* v_a_3793_, lean_object* v_b_3794_, lean_object* v_c_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3779_, v_val_3780_, v_baseName_3781_, v___x_3782_, v_a_3783_, v___x_3784_, v___x_3785_, v___x_3786_, v_matchDeclName_3787_, v___x_3788_, v___x_3789_, v___x_3790_, v_a_3793_, v_b_3794_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3802_ = _args[0];
lean_object* v_val_3803_ = _args[1];
lean_object* v_baseName_3804_ = _args[2];
lean_object* v___x_3805_ = _args[3];
lean_object* v_a_3806_ = _args[4];
lean_object* v___x_3807_ = _args[5];
lean_object* v___x_3808_ = _args[6];
lean_object* v___x_3809_ = _args[7];
lean_object* v_matchDeclName_3810_ = _args[8];
lean_object* v___x_3811_ = _args[9];
lean_object* v___x_3812_ = _args[10];
lean_object* v___x_3813_ = _args[11];
lean_object* v_inst_3814_ = _args[12];
lean_object* v_R_3815_ = _args[13];
lean_object* v_a_3816_ = _args[14];
lean_object* v_b_3817_ = _args[15];
lean_object* v_c_3818_ = _args[16];
lean_object* v___y_3819_ = _args[17];
lean_object* v___y_3820_ = _args[18];
lean_object* v___y_3821_ = _args[19];
lean_object* v___y_3822_ = _args[20];
lean_object* v___y_3823_ = _args[21];
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3802_, v_val_3803_, v_baseName_3804_, v___x_3805_, v_a_3806_, v___x_3807_, v___x_3808_, v___x_3809_, v_matchDeclName_3810_, v___x_3811_, v___x_3812_, v___x_3813_, v_inst_3814_, v_R_3815_, v_a_3816_, v_b_3817_, v_c_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v_upperBound_3802_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3825_, lean_object* v_constName_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3833_, lean_object* v_constName_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3833_, v_constName_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3841_, lean_object* v_ref_3842_, lean_object* v_constName_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3842_, v_constName_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3850_, lean_object* v_ref_3851_, lean_object* v_constName_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3850_, v_ref_3851_, v_constName_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v_ref_3851_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3859_, lean_object* v_ref_3860_, lean_object* v_msg_3861_, lean_object* v_declHint_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3860_, v_msg_3861_, v_declHint_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3869_, lean_object* v_ref_3870_, lean_object* v_msg_3871_, lean_object* v_declHint_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3869_, v_ref_3870_, v_msg_3871_, v_declHint_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v_ref_3870_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3879_, lean_object* v_declHint_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3879_, v_declHint_3880_, v___y_3884_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3887_, lean_object* v_declHint_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3887_, v_declHint_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3895_, lean_object* v_ref_3896_, lean_object* v_msg_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v___x_3903_; 
v___x_3903_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3896_, v_msg_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3904_, lean_object* v_ref_3905_, lean_object* v_msg_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3904_, v_ref_3905_, v_msg_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v_ref_3905_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3913_, lean_object* v_vals_3914_, lean_object* v_i_3915_, lean_object* v_k_3916_){
_start:
{
lean_object* v___x_3917_; uint8_t v___x_3918_; 
v___x_3917_ = lean_array_get_size(v_keys_3913_);
v___x_3918_ = lean_nat_dec_lt(v_i_3915_, v___x_3917_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; 
lean_dec(v_i_3915_);
v___x_3919_ = lean_box(0);
return v___x_3919_;
}
else
{
lean_object* v_k_x27_3920_; uint8_t v___x_3921_; 
v_k_x27_3920_ = lean_array_fget_borrowed(v_keys_3913_, v_i_3915_);
v___x_3921_ = lean_name_eq(v_k_3916_, v_k_x27_3920_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = lean_unsigned_to_nat(1u);
v___x_3923_ = lean_nat_add(v_i_3915_, v___x_3922_);
lean_dec(v_i_3915_);
v_i_3915_ = v___x_3923_;
goto _start;
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = lean_array_fget_borrowed(v_vals_3914_, v_i_3915_);
lean_dec(v_i_3915_);
lean_inc(v___x_3925_);
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
return v___x_3926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3927_, lean_object* v_vals_3928_, lean_object* v_i_3929_, lean_object* v_k_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3927_, v_vals_3928_, v_i_3929_, v_k_3930_);
lean_dec(v_k_3930_);
lean_dec_ref(v_vals_3928_);
lean_dec_ref(v_keys_3927_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3932_, size_t v_x_3933_, lean_object* v_x_3934_){
_start:
{
if (lean_obj_tag(v_x_3932_) == 0)
{
lean_object* v_es_3935_; lean_object* v___x_3936_; size_t v___x_3937_; size_t v___x_3938_; lean_object* v_j_3939_; lean_object* v___x_3940_; 
v_es_3935_ = lean_ctor_get(v_x_3932_, 0);
v___x_3936_ = lean_box(2);
v___x_3937_ = ((size_t)31ULL);
v___x_3938_ = lean_usize_land(v_x_3933_, v___x_3937_);
v_j_3939_ = lean_usize_to_nat(v___x_3938_);
v___x_3940_ = lean_array_get_borrowed(v___x_3936_, v_es_3935_, v_j_3939_);
lean_dec(v_j_3939_);
switch(lean_obj_tag(v___x_3940_))
{
case 0:
{
lean_object* v_key_3941_; lean_object* v_val_3942_; uint8_t v___x_3943_; 
v_key_3941_ = lean_ctor_get(v___x_3940_, 0);
v_val_3942_ = lean_ctor_get(v___x_3940_, 1);
v___x_3943_ = lean_name_eq(v_x_3934_, v_key_3941_);
if (v___x_3943_ == 0)
{
lean_object* v___x_3944_; 
v___x_3944_ = lean_box(0);
return v___x_3944_;
}
else
{
lean_object* v___x_3945_; 
lean_inc(v_val_3942_);
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v_val_3942_);
return v___x_3945_;
}
}
case 1:
{
lean_object* v_node_3946_; size_t v___x_3947_; size_t v___x_3948_; 
v_node_3946_ = lean_ctor_get(v___x_3940_, 0);
v___x_3947_ = ((size_t)5ULL);
v___x_3948_ = lean_usize_shift_right(v_x_3933_, v___x_3947_);
v_x_3932_ = v_node_3946_;
v_x_3933_ = v___x_3948_;
goto _start;
}
default: 
{
lean_object* v___x_3950_; 
v___x_3950_ = lean_box(0);
return v___x_3950_;
}
}
}
else
{
lean_object* v_ks_3951_; lean_object* v_vs_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_ks_3951_ = lean_ctor_get(v_x_3932_, 0);
v_vs_3952_ = lean_ctor_get(v_x_3932_, 1);
v___x_3953_ = lean_unsigned_to_nat(0u);
v___x_3954_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3951_, v_vs_3952_, v___x_3953_, v_x_3934_);
return v___x_3954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3955_, lean_object* v_x_3956_, lean_object* v_x_3957_){
_start:
{
size_t v_x_699__boxed_3958_; lean_object* v_res_3959_; 
v_x_699__boxed_3958_ = lean_unbox_usize(v_x_3956_);
lean_dec(v_x_3956_);
v_res_3959_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3955_, v_x_699__boxed_3958_, v_x_3957_);
lean_dec(v_x_3957_);
lean_dec_ref(v_x_3955_);
return v_res_3959_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3960_; uint64_t v___x_3961_; 
v___x_3960_ = lean_unsigned_to_nat(1723u);
v___x_3961_ = lean_uint64_of_nat(v___x_3960_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3962_, lean_object* v_x_3963_){
_start:
{
uint64_t v___y_3965_; 
if (lean_obj_tag(v_x_3963_) == 0)
{
uint64_t v___x_3968_; 
v___x_3968_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0);
v___y_3965_ = v___x_3968_;
goto v___jp_3964_;
}
else
{
uint64_t v_hash_3969_; 
v_hash_3969_ = lean_ctor_get_uint64(v_x_3963_, sizeof(void*)*2);
v___y_3965_ = v_hash_3969_;
goto v___jp_3964_;
}
v___jp_3964_:
{
size_t v___x_3966_; lean_object* v___x_3967_; 
v___x_3966_ = lean_uint64_to_usize(v___y_3965_);
v___x_3967_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3962_, v___x_3966_, v_x_3963_);
return v___x_3967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3970_, lean_object* v_x_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3970_, v_x_3971_);
lean_dec(v_x_3971_);
lean_dec_ref(v_x_3970_);
return v_res_3972_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3979_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3980_ = l_Lean_stringToMessageData(v___x_3979_);
return v___x_3980_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3983_ = l_Lean_stringToMessageData(v___x_3982_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v___x_3990_; lean_object* v_env_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3990_ = lean_st_ref_get(v_a_3988_);
v_env_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc_ref(v_env_3991_);
lean_dec(v___x_3990_);
lean_inc_n(v_matchDeclName_3984_, 3);
v___x_3992_ = l_Lean_mkPrivateName(v_env_3991_, v_matchDeclName_3984_);
lean_dec_ref(v_env_3991_);
v___x_3993_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_3992_);
v___x_3994_ = l_Lean_Name_append(v___x_3992_, v___x_3993_);
lean_inc_n(v___x_3994_, 2);
v___x_3995_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_3995_, 0, v_matchDeclName_3984_);
lean_closure_set(v___x_3995_, 1, v___x_3992_);
lean_closure_set(v___x_3995_, 2, v___x_3994_);
v___x_3996_ = l_Lean_Meta_realizeConst(v_matchDeclName_3984_, v___x_3994_, v___x_3995_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4025_; 
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4025_ == 0)
{
lean_object* v_unused_4026_; 
v_unused_4026_ = lean_ctor_get(v___x_3996_, 0);
lean_dec(v_unused_4026_);
v___x_3998_ = v___x_3996_;
v_isShared_3999_ = v_isSharedCheck_4025_;
goto v_resetjp_3997_;
}
else
{
lean_dec(v___x_3996_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4025_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4000_; lean_object* v_env_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v_map_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4023_; 
v___x_4000_ = lean_st_ref_get(v_a_3988_);
v_env_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc_ref(v_env_4001_);
lean_dec(v___x_4000_);
v___x_4002_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_4003_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_4004_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_4005_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4002_, v___x_4003_, v_env_4001_, v___x_4004_, v___x_3994_);
v_map_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; 
v_unused_4024_ = lean_ctor_get(v___x_4005_, 1);
lean_dec(v_unused_4024_);
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4023_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_map_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4023_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_4006_, v_matchDeclName_3984_);
lean_dec_ref(v_map_4006_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4014_; 
lean_del_object(v___x_3998_);
v___x_4011_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_4012_ = l_Lean_MessageData_ofName(v_matchDeclName_3984_);
if (v_isShared_4009_ == 0)
{
lean_ctor_set_tag(v___x_4008_, 7);
lean_ctor_set(v___x_4008_, 1, v___x_4012_);
lean_ctor_set(v___x_4008_, 0, v___x_4011_);
v___x_4014_ = v___x_4008_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_4011_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4015_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_4016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4014_);
lean_ctor_set(v___x_4016_, 1, v___x_4015_);
v___x_4017_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_4016_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
return v___x_4017_;
}
}
else
{
lean_object* v_val_4019_; lean_object* v___x_4021_; 
lean_del_object(v___x_4008_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_matchDeclName_3984_);
v_val_4019_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_val_4019_);
lean_dec_ref_known(v___x_4010_, 1);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 0, v_val_4019_);
v___x_4021_ = v___x_3998_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_val_4019_);
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
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec(v___x_3994_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_matchDeclName_3984_);
v_a_4027_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_3996_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_3996_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = lean_get_match_equations_for(v_matchDeclName_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4042_, lean_object* v_x_4043_, lean_object* v_x_4044_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4043_, v_x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4046_, lean_object* v_x_4047_, lean_object* v_x_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4046_, v_x_4047_, v_x_4048_);
lean_dec(v_x_4048_);
lean_dec_ref(v_x_4047_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4050_, lean_object* v_x_4051_, size_t v_x_4052_, lean_object* v_x_4053_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4051_, v_x_4052_, v_x_4053_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4055_, lean_object* v_x_4056_, lean_object* v_x_4057_, lean_object* v_x_4058_){
_start:
{
size_t v_x_897__boxed_4059_; lean_object* v_res_4060_; 
v_x_897__boxed_4059_ = lean_unbox_usize(v_x_4057_);
lean_dec(v_x_4057_);
v_res_4060_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4055_, v_x_4056_, v_x_897__boxed_4059_, v_x_4058_);
lean_dec(v_x_4058_);
lean_dec_ref(v_x_4056_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4061_, lean_object* v_keys_4062_, lean_object* v_vals_4063_, lean_object* v_heq_4064_, lean_object* v_i_4065_, lean_object* v_k_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4062_, v_vals_4063_, v_i_4065_, v_k_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4068_, lean_object* v_keys_4069_, lean_object* v_vals_4070_, lean_object* v_heq_4071_, lean_object* v_i_4072_, lean_object* v_k_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4068_, v_keys_4069_, v_vals_4070_, v_heq_4071_, v_i_4072_, v_k_4073_);
lean_dec(v_k_4073_);
lean_dec_ref(v_vals_4070_);
lean_dec_ref(v_keys_4069_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4075_, lean_object* v_k_4076_, uint8_t v_cleanupAnnotations_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___f_4083_; uint8_t v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___f_4083_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4083_, 0, v_k_4076_);
v___x_4084_ = 0;
v___x_4085_ = lean_box(0);
v___x_4086_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4084_, v___x_4085_, v_type_4075_, v___f_4083_, v_cleanupAnnotations_4077_, v___x_4084_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4086_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4086_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
v_a_4095_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4086_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4086_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4103_, lean_object* v_k_4104_, lean_object* v_cleanupAnnotations_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4111_; lean_object* v_res_4112_; 
v_cleanupAnnotations_boxed_4111_ = lean_unbox(v_cleanupAnnotations_4105_);
v_res_4112_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4103_, v_k_4104_, v_cleanupAnnotations_boxed_4111_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4113_, lean_object* v_type_4114_, lean_object* v_k_4115_, uint8_t v_cleanupAnnotations_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4114_, v_k_4115_, v_cleanupAnnotations_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4123_, lean_object* v_type_4124_, lean_object* v_k_4125_, lean_object* v_cleanupAnnotations_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4132_; lean_object* v_res_4133_; 
v_cleanupAnnotations_boxed_4132_ = lean_unbox(v_cleanupAnnotations_4126_);
v_res_4133_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4123_, v_type_4124_, v_k_4125_, v_cleanupAnnotations_boxed_4132_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v_msg_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___f_4140_; lean_object* v___x_19933__overap_4141_; lean_object* v___x_4142_; 
v___f_4140_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_19933__overap_4141_ = lean_panic_fn_borrowed(v___f_4140_, v_msg_4134_);
lean_inc(v___y_4138_);
lean_inc_ref(v___y_4137_);
lean_inc(v___y_4136_);
lean_inc_ref(v___y_4135_);
v___x_4142_ = lean_apply_5(v___x_19933__overap_4141_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, lean_box(0));
return v___x_4142_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v_msg_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_msg_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4150_){
_start:
{
uint8_t v_foApprox_4151_; uint8_t v_ctxApprox_4152_; uint8_t v_quasiPatternApprox_4153_; uint8_t v_constApprox_4154_; uint8_t v_isDefEqStuckEx_4155_; uint8_t v_unificationHints_4156_; uint8_t v_proofIrrelevance_4157_; uint8_t v_assignSyntheticOpaque_4158_; uint8_t v_offsetCnstrs_4159_; uint8_t v_transparency_4160_; uint8_t v_univApprox_4161_; uint8_t v_iota_4162_; uint8_t v_beta_4163_; uint8_t v_proj_4164_; uint8_t v_zeta_4165_; uint8_t v_zetaDelta_4166_; uint8_t v_zetaUnused_4167_; uint8_t v_zetaHave_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4176_; 
v_foApprox_4151_ = lean_ctor_get_uint8(v_c_4150_, 0);
v_ctxApprox_4152_ = lean_ctor_get_uint8(v_c_4150_, 1);
v_quasiPatternApprox_4153_ = lean_ctor_get_uint8(v_c_4150_, 2);
v_constApprox_4154_ = lean_ctor_get_uint8(v_c_4150_, 3);
v_isDefEqStuckEx_4155_ = lean_ctor_get_uint8(v_c_4150_, 4);
v_unificationHints_4156_ = lean_ctor_get_uint8(v_c_4150_, 5);
v_proofIrrelevance_4157_ = lean_ctor_get_uint8(v_c_4150_, 6);
v_assignSyntheticOpaque_4158_ = lean_ctor_get_uint8(v_c_4150_, 7);
v_offsetCnstrs_4159_ = lean_ctor_get_uint8(v_c_4150_, 8);
v_transparency_4160_ = lean_ctor_get_uint8(v_c_4150_, 9);
v_univApprox_4161_ = lean_ctor_get_uint8(v_c_4150_, 11);
v_iota_4162_ = lean_ctor_get_uint8(v_c_4150_, 12);
v_beta_4163_ = lean_ctor_get_uint8(v_c_4150_, 13);
v_proj_4164_ = lean_ctor_get_uint8(v_c_4150_, 14);
v_zeta_4165_ = lean_ctor_get_uint8(v_c_4150_, 15);
v_zetaDelta_4166_ = lean_ctor_get_uint8(v_c_4150_, 16);
v_zetaUnused_4167_ = lean_ctor_get_uint8(v_c_4150_, 17);
v_zetaHave_4168_ = lean_ctor_get_uint8(v_c_4150_, 18);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_c_4150_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4170_ = v_c_4150_;
v_isShared_4171_ = v_isSharedCheck_4176_;
goto v_resetjp_4169_;
}
else
{
lean_dec(v_c_4150_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4176_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
uint8_t v___x_4172_; lean_object* v___x_4174_; 
v___x_4172_ = 2;
if (v_isShared_4171_ == 0)
{
v___x_4174_ = v___x_4170_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 0, v_foApprox_4151_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 1, v_ctxApprox_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 2, v_quasiPatternApprox_4153_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 3, v_constApprox_4154_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 4, v_isDefEqStuckEx_4155_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 5, v_unificationHints_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 6, v_proofIrrelevance_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 7, v_assignSyntheticOpaque_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 8, v_offsetCnstrs_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 9, v_transparency_4160_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 11, v_univApprox_4161_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 12, v_iota_4162_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 13, v_beta_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 14, v_proj_4164_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 15, v_zeta_4165_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 16, v_zetaDelta_4166_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 17, v_zetaUnused_4167_);
lean_ctor_set_uint8(v_reuseFailAlloc_4175_, 18, v_zetaHave_4168_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
lean_ctor_set_uint8(v___x_4174_, 10, v___x_4172_);
return v___x_4174_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4177_, lean_object* v_t_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v_dummy_4184_; lean_object* v_nargs_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v_dummy_4184_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4185_ = l_Lean_Expr_getAppNumArgs(v_t_4178_);
lean_inc(v_nargs_4185_);
v___x_4186_ = lean_mk_array(v_nargs_4185_, v_dummy_4184_);
v___x_4187_ = lean_unsigned_to_nat(1u);
v___x_4188_ = lean_nat_sub(v_nargs_4185_, v___x_4187_);
lean_dec(v_nargs_4185_);
v___x_4189_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4178_, v___x_4186_, v___x_4188_);
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4191_, lean_object* v_t_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4191_, v_t_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec_ref(v_x_4191_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4199_, lean_object* v_x_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v_snd_4199_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4207_, lean_object* v_x_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4207_, v_x_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec_ref(v_x_4208_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4215_, size_t v_i_4216_, lean_object* v_bs_4217_){
_start:
{
uint8_t v___x_4218_; 
v___x_4218_ = lean_usize_dec_lt(v_i_4216_, v_sz_4215_);
if (v___x_4218_ == 0)
{
return v_bs_4217_;
}
else
{
lean_object* v_v_4219_; lean_object* v_fst_4220_; lean_object* v_snd_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4235_; 
v_v_4219_ = lean_array_uget(v_bs_4217_, v_i_4216_);
v_fst_4220_ = lean_ctor_get(v_v_4219_, 0);
v_snd_4221_ = lean_ctor_get(v_v_4219_, 1);
v_isSharedCheck_4235_ = !lean_is_exclusive(v_v_4219_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4223_ = v_v_4219_;
v_isShared_4224_ = v_isSharedCheck_4235_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_snd_4221_);
lean_inc(v_fst_4220_);
lean_dec(v_v_4219_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4235_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4225_; lean_object* v_bs_x27_4226_; lean_object* v___f_4227_; lean_object* v___x_4229_; 
v___x_4225_ = lean_unsigned_to_nat(0u);
v_bs_x27_4226_ = lean_array_uset(v_bs_4217_, v_i_4216_, v___x_4225_);
v___f_4227_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4227_, 0, v_snd_4221_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 1, v___f_4227_);
v___x_4229_ = v___x_4223_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_fst_4220_);
lean_ctor_set(v_reuseFailAlloc_4234_, 1, v___f_4227_);
v___x_4229_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
size_t v___x_4230_; size_t v___x_4231_; lean_object* v___x_4232_; 
v___x_4230_ = ((size_t)1ULL);
v___x_4231_ = lean_usize_add(v_i_4216_, v___x_4230_);
v___x_4232_ = lean_array_uset(v_bs_x27_4226_, v_i_4216_, v___x_4229_);
v_i_4216_ = v___x_4231_;
v_bs_4217_ = v___x_4232_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4236_, lean_object* v_i_4237_, lean_object* v_bs_4238_){
_start:
{
size_t v_sz_boxed_4239_; size_t v_i_boxed_4240_; lean_object* v_res_4241_; 
v_sz_boxed_4239_ = lean_unbox_usize(v_sz_4236_);
lean_dec(v_sz_4236_);
v_i_boxed_4240_ = lean_unbox_usize(v_i_4237_);
lean_dec(v_i_4237_);
v_res_4241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4239_, v_i_boxed_4240_, v_bs_4238_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4242_, size_t v_i_4243_, lean_object* v_bs_4244_){
_start:
{
uint8_t v___x_4245_; 
v___x_4245_ = lean_usize_dec_lt(v_i_4243_, v_sz_4242_);
if (v___x_4245_ == 0)
{
return v_bs_4244_;
}
else
{
lean_object* v_v_4246_; lean_object* v_fst_4247_; lean_object* v_snd_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4264_; 
v_v_4246_ = lean_array_uget(v_bs_4244_, v_i_4243_);
v_fst_4247_ = lean_ctor_get(v_v_4246_, 0);
v_snd_4248_ = lean_ctor_get(v_v_4246_, 1);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_v_4246_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4250_ = v_v_4246_;
v_isShared_4251_ = v_isSharedCheck_4264_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_snd_4248_);
lean_inc(v_fst_4247_);
lean_dec(v_v_4246_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4264_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4252_; lean_object* v_bs_x27_4253_; uint8_t v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4257_; 
v___x_4252_ = lean_unsigned_to_nat(0u);
v_bs_x27_4253_ = lean_array_uset(v_bs_4244_, v_i_4243_, v___x_4252_);
v___x_4254_ = 0;
v___x_4255_ = lean_box(v___x_4254_);
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 0, v___x_4255_);
v___x_4257_ = v___x_4250_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4255_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v_snd_4248_);
v___x_4257_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
lean_object* v___x_4258_; size_t v___x_4259_; size_t v___x_4260_; lean_object* v___x_4261_; 
v___x_4258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4258_, 0, v_fst_4247_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = ((size_t)1ULL);
v___x_4260_ = lean_usize_add(v_i_4243_, v___x_4259_);
v___x_4261_ = lean_array_uset(v_bs_x27_4253_, v_i_4243_, v___x_4258_);
v_i_4243_ = v___x_4260_;
v_bs_4244_ = v___x_4261_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4265_, lean_object* v_i_4266_, lean_object* v_bs_4267_){
_start:
{
size_t v_sz_boxed_4268_; size_t v_i_boxed_4269_; lean_object* v_res_4270_; 
v_sz_boxed_4268_ = lean_unbox_usize(v_sz_4265_);
lean_dec(v_sz_4265_);
v_i_boxed_4269_ = lean_unbox_usize(v_i_4266_);
lean_dec(v_i_4266_);
v_res_4270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4268_, v_i_boxed_4269_, v_bs_4267_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4271_, lean_object* v_a_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_21855__overap_4279_; lean_object* v___x_4280_; 
v___x_4278_ = l_Lean_instInhabitedExpr;
v___x_21855__overap_4279_ = l_instInhabitedOfMonad___redArg(v___x_4271_, v___x_4278_);
lean_inc(v___y_4276_);
lean_inc_ref(v___y_4275_);
lean_inc(v___y_4274_);
lean_inc_ref(v___y_4273_);
v___x_4280_ = lean_apply_5(v___x_21855__overap_4279_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, lean_box(0));
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4281_, lean_object* v_a_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4281_, v_a_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec_ref(v_a_4282_);
return v_res_4288_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_instMonadEIO(lean_box(0));
return v___x_4289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4290_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4291_ = l_StateRefT_x27_instMonad___redArg(v___x_4290_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4296_, lean_object* v_declInfos_4297_, lean_object* v_k_4298_, lean_object* v_kind_4299_, lean_object* v_x_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
uint8_t v_kind_boxed_4306_; lean_object* v_res_4307_; 
v_kind_boxed_4306_ = lean_unbox(v_kind_4299_);
v_res_4307_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4296_, v_declInfos_4297_, v_k_4298_, v_kind_boxed_4306_, v_x_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4308_, lean_object* v_k_4309_, uint8_t v_kind_4310_, lean_object* v_acc_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v___x_4317_; lean_object* v_toApplicative_4318_; lean_object* v_toFunctor_4319_; lean_object* v_toSeq_4320_; lean_object* v_toSeqLeft_4321_; lean_object* v_toSeqRight_4322_; lean_object* v___f_4323_; lean_object* v___f_4324_; lean_object* v___f_4325_; lean_object* v___f_4326_; lean_object* v___x_4327_; lean_object* v___f_4328_; lean_object* v___f_4329_; lean_object* v___f_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v_toApplicative_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4383_; 
v___x_4317_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4318_ = lean_ctor_get(v___x_4317_, 0);
v_toFunctor_4319_ = lean_ctor_get(v_toApplicative_4318_, 0);
v_toSeq_4320_ = lean_ctor_get(v_toApplicative_4318_, 2);
v_toSeqLeft_4321_ = lean_ctor_get(v_toApplicative_4318_, 3);
v_toSeqRight_4322_ = lean_ctor_get(v_toApplicative_4318_, 4);
v___f_4323_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4324_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4319_, 2);
v___f_4325_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4325_, 0, v_toFunctor_4319_);
v___f_4326_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4326_, 0, v_toFunctor_4319_);
v___x_4327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___f_4325_);
lean_ctor_set(v___x_4327_, 1, v___f_4326_);
lean_inc(v_toSeqRight_4322_);
v___f_4328_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4328_, 0, v_toSeqRight_4322_);
lean_inc(v_toSeqLeft_4321_);
v___f_4329_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4329_, 0, v_toSeqLeft_4321_);
lean_inc(v_toSeq_4320_);
v___f_4330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4330_, 0, v_toSeq_4320_);
v___x_4331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4327_);
lean_ctor_set(v___x_4331_, 1, v___f_4323_);
lean_ctor_set(v___x_4331_, 2, v___f_4330_);
lean_ctor_set(v___x_4331_, 3, v___f_4329_);
lean_ctor_set(v___x_4331_, 4, v___f_4328_);
v___x_4332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4331_);
lean_ctor_set(v___x_4332_, 1, v___f_4324_);
v___x_4333_ = l_StateRefT_x27_instMonad___redArg(v___x_4332_);
v_toApplicative_4334_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; 
v_unused_4384_ = lean_ctor_get(v___x_4333_, 1);
lean_dec(v_unused_4384_);
v___x_4336_ = v___x_4333_;
v_isShared_4337_ = v_isSharedCheck_4383_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_toApplicative_4334_);
lean_dec(v___x_4333_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4383_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v_toFunctor_4338_; lean_object* v_toSeq_4339_; lean_object* v_toSeqLeft_4340_; lean_object* v_toSeqRight_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4381_; 
v_toFunctor_4338_ = lean_ctor_get(v_toApplicative_4334_, 0);
v_toSeq_4339_ = lean_ctor_get(v_toApplicative_4334_, 2);
v_toSeqLeft_4340_ = lean_ctor_get(v_toApplicative_4334_, 3);
v_toSeqRight_4341_ = lean_ctor_get(v_toApplicative_4334_, 4);
v_isSharedCheck_4381_ = !lean_is_exclusive(v_toApplicative_4334_);
if (v_isSharedCheck_4381_ == 0)
{
lean_object* v_unused_4382_; 
v_unused_4382_ = lean_ctor_get(v_toApplicative_4334_, 1);
lean_dec(v_unused_4382_);
v___x_4343_ = v_toApplicative_4334_;
v_isShared_4344_ = v_isSharedCheck_4381_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_toSeqRight_4341_);
lean_inc(v_toSeqLeft_4340_);
lean_inc(v_toSeq_4339_);
lean_inc(v_toFunctor_4338_);
lean_dec(v_toApplicative_4334_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4381_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___f_4345_; lean_object* v___f_4346_; lean_object* v___f_4347_; lean_object* v___f_4348_; lean_object* v___x_4349_; lean_object* v___f_4350_; lean_object* v___f_4351_; lean_object* v___f_4352_; lean_object* v___x_4354_; 
v___f_4345_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4346_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4338_);
v___f_4347_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4347_, 0, v_toFunctor_4338_);
v___f_4348_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4348_, 0, v_toFunctor_4338_);
v___x_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___f_4347_);
lean_ctor_set(v___x_4349_, 1, v___f_4348_);
v___f_4350_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4350_, 0, v_toSeqRight_4341_);
v___f_4351_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4351_, 0, v_toSeqLeft_4340_);
v___f_4352_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4352_, 0, v_toSeq_4339_);
if (v_isShared_4344_ == 0)
{
lean_ctor_set(v___x_4343_, 4, v___f_4350_);
lean_ctor_set(v___x_4343_, 3, v___f_4351_);
lean_ctor_set(v___x_4343_, 2, v___f_4352_);
lean_ctor_set(v___x_4343_, 1, v___f_4345_);
lean_ctor_set(v___x_4343_, 0, v___x_4349_);
v___x_4354_ = v___x_4343_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4349_);
lean_ctor_set(v_reuseFailAlloc_4380_, 1, v___f_4345_);
lean_ctor_set(v_reuseFailAlloc_4380_, 2, v___f_4352_);
lean_ctor_set(v_reuseFailAlloc_4380_, 3, v___f_4351_);
lean_ctor_set(v_reuseFailAlloc_4380_, 4, v___f_4350_);
v___x_4354_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
lean_object* v___x_4356_; 
if (v_isShared_4337_ == 0)
{
lean_ctor_set(v___x_4336_, 1, v___f_4346_);
lean_ctor_set(v___x_4336_, 0, v___x_4354_);
v___x_4356_ = v___x_4336_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4354_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v___f_4346_);
v___x_4356_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; uint8_t v___x_4359_; 
v___x_4357_ = lean_array_get_size(v_acc_4311_);
v___x_4358_ = lean_array_get_size(v_declInfos_4308_);
v___x_4359_ = lean_nat_dec_lt(v___x_4357_, v___x_4358_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; 
lean_dec_ref(v___x_4356_);
lean_dec_ref(v_declInfos_4308_);
lean_inc(v___y_4315_);
lean_inc_ref(v___y_4314_);
lean_inc(v___y_4313_);
lean_inc_ref(v___y_4312_);
v___x_4360_ = lean_apply_6(v_k_4309_, v_acc_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, lean_box(0));
return v___x_4360_;
}
else
{
lean_object* v___f_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; lean_object* v___f_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v_snd_4369_; lean_object* v_fst_4370_; lean_object* v_fst_4371_; lean_object* v_snd_4372_; lean_object* v___x_4373_; 
v___f_4361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4361_, 0, v___x_4356_);
v___x_4362_ = lean_box(0);
v___x_4363_ = 0;
v___f_4364_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4364_, 0, v___f_4361_);
v___x_4365_ = lean_box(v___x_4363_);
v___x_4366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4365_);
lean_ctor_set(v___x_4366_, 1, v___f_4364_);
v___x_4367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4362_);
lean_ctor_set(v___x_4367_, 1, v___x_4366_);
v___x_4368_ = lean_array_get(v___x_4367_, v_declInfos_4308_, v___x_4357_);
lean_dec_ref_known(v___x_4367_, 2);
v_snd_4369_ = lean_ctor_get(v___x_4368_, 1);
lean_inc(v_snd_4369_);
v_fst_4370_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_fst_4370_);
lean_dec(v___x_4368_);
v_fst_4371_ = lean_ctor_get(v_snd_4369_, 0);
lean_inc(v_fst_4371_);
v_snd_4372_ = lean_ctor_get(v_snd_4369_, 1);
lean_inc(v_snd_4372_);
lean_dec(v_snd_4369_);
lean_inc(v___y_4315_);
lean_inc_ref(v___y_4314_);
lean_inc(v___y_4313_);
lean_inc_ref(v___y_4312_);
lean_inc_ref(v_acc_4311_);
v___x_4373_ = lean_apply_6(v_snd_4372_, v_acc_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, lean_box(0));
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; lean_object* v___x_4375_; lean_object* v___f_4376_; uint8_t v___x_4377_; lean_object* v___x_4378_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_a_4374_);
lean_dec_ref_known(v___x_4373_, 1);
v___x_4375_ = lean_box(v_kind_4310_);
v___f_4376_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4376_, 0, v_acc_4311_);
lean_closure_set(v___f_4376_, 1, v_declInfos_4308_);
lean_closure_set(v___f_4376_, 2, v_k_4309_);
lean_closure_set(v___f_4376_, 3, v___x_4375_);
v___x_4377_ = lean_unbox(v_fst_4371_);
lean_dec(v_fst_4371_);
v___x_4378_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4370_, v___x_4377_, v_a_4374_, v___f_4376_, v_kind_4310_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
return v___x_4378_;
}
else
{
lean_dec(v_fst_4371_);
lean_dec(v_fst_4370_);
lean_dec_ref(v_acc_4311_);
lean_dec_ref(v_k_4309_);
lean_dec_ref(v_declInfos_4308_);
return v___x_4373_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4385_, lean_object* v_declInfos_4386_, lean_object* v_k_4387_, uint8_t v_kind_4388_, lean_object* v_x_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4395_ = lean_array_push(v_acc_4385_, v_x_4389_);
v___x_4396_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4386_, v_k_4387_, v_kind_4388_, v___x_4395_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4397_, lean_object* v_k_4398_, lean_object* v_kind_4399_, lean_object* v_acc_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
uint8_t v_kind_boxed_4406_; lean_object* v_res_4407_; 
v_kind_boxed_4406_ = lean_unbox(v_kind_4399_);
v_res_4407_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4397_, v_k_4398_, v_kind_boxed_4406_, v_acc_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4408_, lean_object* v_k_4409_, uint8_t v_kind_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4416_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4417_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4408_, v_k_4409_, v_kind_4410_, v___x_4416_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4418_, lean_object* v_k_4419_, lean_object* v_kind_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
uint8_t v_kind_boxed_4426_; lean_object* v_res_4427_; 
v_kind_boxed_4426_ = lean_unbox(v_kind_4420_);
v_res_4427_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4418_, v_k_4419_, v_kind_boxed_4426_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4428_, lean_object* v_k_4429_, uint8_t v_kind_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
size_t v_sz_4436_; size_t v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v_sz_4436_ = lean_array_size(v_declInfos_4428_);
v___x_4437_ = ((size_t)0ULL);
v___x_4438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4436_, v___x_4437_, v_declInfos_4428_);
v___x_4439_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4438_, v_k_4429_, v_kind_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4440_, lean_object* v_k_4441_, lean_object* v_kind_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
uint8_t v_kind_boxed_4448_; lean_object* v_res_4449_; 
v_kind_boxed_4448_ = lean_unbox(v_kind_4442_);
v_res_4449_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4440_, v_k_4441_, v_kind_boxed_4448_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4450_, lean_object* v_k_4451_, uint8_t v_kind_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
size_t v_sz_4458_; size_t v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v_sz_4458_ = lean_array_size(v_declInfos_4450_);
v___x_4459_ = ((size_t)0ULL);
v___x_4460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4458_, v___x_4459_, v_declInfos_4450_);
v___x_4461_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4460_, v_k_4451_, v_kind_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
return v___x_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4462_, lean_object* v_k_4463_, lean_object* v_kind_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
uint8_t v_kind_boxed_4470_; lean_object* v_res_4471_; 
v_kind_boxed_4470_ = lean_unbox(v_kind_4464_);
v_res_4471_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4462_, v_k_4463_, v_kind_boxed_4470_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(lean_object* v_a_4475_, lean_object* v_b_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v_array_4482_; lean_object* v_start_4483_; lean_object* v_stop_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4542_; 
v_array_4482_ = lean_ctor_get(v_a_4475_, 0);
v_start_4483_ = lean_ctor_get(v_a_4475_, 1);
v_stop_4484_ = lean_ctor_get(v_a_4475_, 2);
v_isSharedCheck_4542_ = !lean_is_exclusive(v_a_4475_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4486_ = v_a_4475_;
v_isShared_4487_ = v_isSharedCheck_4542_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_stop_4484_);
lean_inc(v_start_4483_);
lean_inc(v_array_4482_);
lean_dec(v_a_4475_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4542_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
uint8_t v___x_4488_; 
v___x_4488_ = lean_nat_dec_lt(v_start_4483_, v_stop_4484_);
if (v___x_4488_ == 0)
{
lean_object* v___x_4489_; 
lean_del_object(v___x_4486_);
lean_dec(v_stop_4484_);
lean_dec(v_start_4483_);
lean_dec_ref(v_array_4482_);
v___x_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4489_, 0, v_b_4476_);
return v___x_4489_;
}
else
{
lean_object* v_snd_4490_; lean_object* v_fst_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4541_; 
v_snd_4490_ = lean_ctor_get(v_b_4476_, 1);
v_fst_4491_ = lean_ctor_get(v_b_4476_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v_b_4476_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4493_ = v_b_4476_;
v_isShared_4494_ = v_isSharedCheck_4541_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_snd_4490_);
lean_inc(v_fst_4491_);
lean_dec(v_b_4476_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4541_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v_array_4495_; lean_object* v_start_4496_; lean_object* v_stop_4497_; uint8_t v___x_4498_; 
v_array_4495_ = lean_ctor_get(v_snd_4490_, 0);
v_start_4496_ = lean_ctor_get(v_snd_4490_, 1);
v_stop_4497_ = lean_ctor_get(v_snd_4490_, 2);
v___x_4498_ = lean_nat_dec_lt(v_start_4496_, v_stop_4497_);
if (v___x_4498_ == 0)
{
lean_object* v___x_4500_; 
lean_del_object(v___x_4486_);
lean_dec(v_stop_4484_);
lean_dec(v_start_4483_);
lean_dec_ref(v_array_4482_);
if (v_isShared_4494_ == 0)
{
v___x_4500_ = v___x_4493_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_fst_4491_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_snd_4490_);
v___x_4500_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4501_; 
v___x_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
return v___x_4501_;
}
}
else
{
lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4537_; 
lean_inc(v_stop_4497_);
lean_inc(v_start_4496_);
lean_inc_ref(v_array_4495_);
v_isSharedCheck_4537_ = !lean_is_exclusive(v_snd_4490_);
if (v_isSharedCheck_4537_ == 0)
{
lean_object* v_unused_4538_; lean_object* v_unused_4539_; lean_object* v_unused_4540_; 
v_unused_4538_ = lean_ctor_get(v_snd_4490_, 2);
lean_dec(v_unused_4538_);
v_unused_4539_ = lean_ctor_get(v_snd_4490_, 1);
lean_dec(v_unused_4539_);
v_unused_4540_ = lean_ctor_get(v_snd_4490_, 0);
lean_dec(v_unused_4540_);
v___x_4504_ = v_snd_4490_;
v_isShared_4505_ = v_isSharedCheck_4537_;
goto v_resetjp_4503_;
}
else
{
lean_dec(v_snd_4490_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4537_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4506_ = lean_array_fget_borrowed(v_array_4482_, v_start_4483_);
v___x_4507_ = lean_array_fget_borrowed(v_array_4495_, v_start_4496_);
lean_inc(v___x_4507_);
lean_inc(v___x_4506_);
v___x_4508_ = l_Lean_Meta_mkEqHEq(v___x_4506_, v___x_4507_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4508_) == 0)
{
lean_object* v_a_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4513_; 
v_a_4509_ = lean_ctor_get(v___x_4508_, 0);
lean_inc(v_a_4509_);
lean_dec_ref_known(v___x_4508_, 1);
v___x_4510_ = lean_unsigned_to_nat(1u);
v___x_4511_ = lean_nat_add(v_start_4483_, v___x_4510_);
lean_dec(v_start_4483_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 2, v_stop_4484_);
lean_ctor_set(v___x_4504_, 1, v___x_4511_);
lean_ctor_set(v___x_4504_, 0, v_array_4482_);
v___x_4513_ = v___x_4504_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_array_4482_);
lean_ctor_set(v_reuseFailAlloc_4528_, 1, v___x_4511_);
lean_ctor_set(v_reuseFailAlloc_4528_, 2, v_stop_4484_);
v___x_4513_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
lean_object* v___x_4514_; lean_object* v___x_4516_; 
v___x_4514_ = lean_nat_add(v_start_4496_, v___x_4510_);
lean_dec(v_start_4496_);
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 2, v_stop_4497_);
lean_ctor_set(v___x_4486_, 1, v___x_4514_);
lean_ctor_set(v___x_4486_, 0, v_array_4495_);
v___x_4516_ = v___x_4486_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_array_4495_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v___x_4514_);
lean_ctor_set(v_reuseFailAlloc_4527_, 2, v_stop_4497_);
v___x_4516_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4522_; 
v___x_4517_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__1));
v___x_4518_ = lean_array_get_size(v_fst_4491_);
v___x_4519_ = lean_nat_add(v___x_4518_, v___x_4510_);
v___x_4520_ = lean_name_append_index_after(v___x_4517_, v___x_4519_);
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 1, v_a_4509_);
lean_ctor_set(v___x_4493_, 0, v___x_4520_);
v___x_4522_ = v___x_4493_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4520_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_a_4509_);
v___x_4522_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = lean_array_push(v_fst_4491_, v___x_4522_);
v___x_4524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
lean_ctor_set(v___x_4524_, 1, v___x_4516_);
v_a_4475_ = v___x_4513_;
v_b_4476_ = v___x_4524_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_del_object(v___x_4504_);
lean_dec(v_stop_4497_);
lean_dec(v_start_4496_);
lean_dec_ref(v_array_4495_);
lean_del_object(v___x_4493_);
lean_dec(v_fst_4491_);
lean_del_object(v___x_4486_);
lean_dec(v_stop_4484_);
lean_dec(v_start_4483_);
lean_dec_ref(v_array_4482_);
v_a_4529_ = lean_ctor_get(v___x_4508_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4508_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4508_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___boxed(lean_object* v_a_4543_, lean_object* v_b_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_4543_, v_b_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v___x_4551_, lean_object* v_a_4552_, lean_object* v___x_4553_, lean_object* v_as_4554_, size_t v_sz_4555_, size_t v_i_4556_, lean_object* v_b_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
uint8_t v___x_4563_; 
v___x_4563_ = lean_usize_dec_lt(v_i_4556_, v_sz_4555_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; 
lean_dec(v___x_4553_);
v___x_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4564_, 0, v_b_4557_);
return v___x_4564_;
}
else
{
lean_object* v___x_4565_; lean_object* v_a_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4565_ = l_Lean_instInhabitedExpr;
v_a_4566_ = lean_array_uget_borrowed(v_as_4554_, v_i_4556_);
v___x_4567_ = lean_array_get_borrowed(v___x_4565_, v___x_4551_, v_a_4566_);
lean_inc(v___x_4567_);
v___x_4568_ = l_Lean_Meta_instantiateForall(v___x_4567_, v_a_4552_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_object* v_a_4569_; lean_object* v___x_4570_; 
v_a_4569_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_a_4569_);
lean_dec_ref_known(v___x_4568_, 1);
lean_inc(v___x_4553_);
v___x_4570_ = l_Lean_Meta_Match_simpH_x3f(v_a_4569_, v___x_4553_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v_a_4573_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4571_);
lean_dec_ref_known(v___x_4570_, 1);
if (lean_obj_tag(v_a_4571_) == 1)
{
lean_object* v_val_4577_; lean_object* v___x_4578_; 
v_val_4577_ = lean_ctor_get(v_a_4571_, 0);
lean_inc(v_val_4577_);
lean_dec_ref_known(v_a_4571_, 1);
v___x_4578_ = lean_array_push(v_b_4557_, v_val_4577_);
v_a_4573_ = v___x_4578_;
goto v___jp_4572_;
}
else
{
lean_dec(v_a_4571_);
v_a_4573_ = v_b_4557_;
goto v___jp_4572_;
}
v___jp_4572_:
{
size_t v___x_4574_; size_t v___x_4575_; 
v___x_4574_ = ((size_t)1ULL);
v___x_4575_ = lean_usize_add(v_i_4556_, v___x_4574_);
v_i_4556_ = v___x_4575_;
v_b_4557_ = v_a_4573_;
goto _start;
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec_ref(v_b_4557_);
lean_dec(v___x_4553_);
v_a_4579_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4570_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4570_);
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
else
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
lean_dec_ref(v_b_4557_);
lean_dec(v___x_4553_);
v_a_4587_ = lean_ctor_get(v___x_4568_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4568_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4568_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v___x_4595_, lean_object* v_a_4596_, lean_object* v___x_4597_, lean_object* v_as_4598_, lean_object* v_sz_4599_, lean_object* v_i_4600_, lean_object* v_b_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
size_t v_sz_boxed_4607_; size_t v_i_boxed_4608_; lean_object* v_res_4609_; 
v_sz_boxed_4607_ = lean_unbox_usize(v_sz_4599_);
lean_dec(v_sz_4599_);
v_i_boxed_4608_ = lean_unbox_usize(v_i_4600_);
lean_dec(v_i_4600_);
v_res_4609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v___x_4595_, v_a_4596_, v___x_4597_, v_as_4598_, v_sz_boxed_4607_, v_i_boxed_4608_, v_b_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec_ref(v_as_4598_);
lean_dec_ref(v_a_4596_);
lean_dec_ref(v___x_4595_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4610_, lean_object* v_args_4611_, lean_object* v___x_4612_, lean_object* v_overlaps_4613_, lean_object* v_a_4614_, lean_object* v_fst_4615_, lean_object* v_a_4616_, lean_object* v___x_4617_, lean_object* v___x_4618_, lean_object* v___x_4619_, lean_object* v___x_4620_, lean_object* v_altVars_4621_, uint8_t v___x_4622_, uint8_t v___x_4623_, lean_object* v_a_4624_, lean_object* v___x_4625_, lean_object* v___x_4626_, lean_object* v___x_4627_, lean_object* v___x_4628_, lean_object* v___x_4629_, lean_object* v___x_4630_, lean_object* v___x_4631_, lean_object* v_matchDeclName_4632_, lean_object* v___x_4633_, lean_object* v___x_4634_, lean_object* v___x_4635_, lean_object* v_heqs_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4642_ = l_Lean_mkAppN(v___y_4610_, v_args_4611_);
lean_inc_ref(v_heqs_4636_);
v___x_4643_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4642_, v_heqs_4636_, v___x_4612_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v_a_4644_; lean_object* v___x_4645_; size_t v_sz_4646_; size_t v___x_4647_; lean_object* v___x_4648_; 
v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
lean_inc(v_a_4644_);
lean_dec_ref_known(v___x_4643_, 1);
v___x_4645_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4613_, v_a_4614_);
v_sz_4646_ = lean_array_size(v___x_4645_);
v___x_4647_ = ((size_t)0ULL);
lean_inc_ref(v___x_4618_);
v___x_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_fst_4615_, v_a_4616_, v___x_4617_, v___x_4645_, v_sz_4646_, v___x_4647_, v___x_4618_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
lean_dec_ref(v___x_4645_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v_a_4649_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v_options_4761_; uint8_t v_hasTrace_4762_; 
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
lean_inc(v_a_4649_);
lean_dec_ref_known(v___x_4648_, 1);
v_options_4761_ = lean_ctor_get(v___y_4639_, 2);
v_hasTrace_4762_ = lean_ctor_get_uint8(v_options_4761_, sizeof(void*)*1);
if (v_hasTrace_4762_ == 0)
{
v___y_4651_ = v___y_4637_;
v___y_4652_ = v___y_4638_;
v___y_4653_ = v___y_4639_;
v___y_4654_ = v___y_4640_;
goto v___jp_4650_;
}
else
{
lean_object* v_inheritedTraceOptions_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; uint8_t v___x_4766_; 
v_inheritedTraceOptions_4763_ = lean_ctor_get(v___y_4639_, 13);
v___x_4764_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4765_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4763_, v_options_4761_, v___x_4765_);
if (v___x_4766_ == 0)
{
v___y_4651_ = v___y_4637_;
v___y_4652_ = v___y_4638_;
v___y_4653_ = v___y_4639_;
v___y_4654_ = v___y_4640_;
goto v___jp_4650_;
}
else
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4767_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4649_);
v___x_4768_ = lean_array_to_list(v_a_4649_);
v___x_4769_ = lean_box(0);
v___x_4770_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4768_, v___x_4769_);
v___x_4771_ = l_Lean_MessageData_ofList(v___x_4770_);
v___x_4772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4767_);
lean_ctor_set(v___x_4772_, 1, v___x_4771_);
v___x_4773_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4764_, v___x_4772_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_dec_ref_known(v___x_4773_, 1);
v___y_4651_ = v___y_4637_;
v___y_4652_ = v___y_4638_;
v___y_4653_ = v___y_4639_;
v___y_4654_ = v___y_4640_;
goto v___jp_4650_;
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4781_; 
lean_dec(v_a_4649_);
lean_dec(v_a_4644_);
lean_dec_ref(v_heqs_4636_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
lean_dec(v_matchDeclName_4632_);
lean_dec_ref(v___x_4629_);
lean_dec_ref(v___x_4628_);
lean_dec_ref(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec(v___x_4619_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v_a_4616_);
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4776_ = v___x_4773_;
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4773_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
}
v___jp_4650_:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; size_t v_sz_4662_; lean_object* v___x_4663_; 
v___x_4655_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4656_ = l_Array_reverse___redArg(v_a_4616_);
v___x_4657_ = lean_array_get_size(v___x_4656_);
v___x_4658_ = l_Array_toSubarray___redArg(v___x_4656_, v___x_4619_, v___x_4657_);
lean_inc_ref(v___x_4620_);
v___x_4659_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4620_, v___x_4618_);
v___x_4660_ = l_Array_reverse___redArg(v___x_4659_);
v___x_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4655_);
lean_ctor_set(v___x_4661_, 1, v___x_4658_);
v_sz_4662_ = lean_array_size(v___x_4660_);
v___x_4663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4660_, v_sz_4662_, v___x_4647_, v___x_4661_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
lean_dec_ref(v___x_4660_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; lean_object* v_fst_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4751_; 
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
lean_inc(v_a_4664_);
lean_dec_ref_known(v___x_4663_, 1);
v_fst_4665_ = lean_ctor_get(v_a_4664_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v_a_4664_);
if (v_isSharedCheck_4751_ == 0)
{
lean_object* v_unused_4752_; 
v_unused_4752_ = lean_ctor_get(v_a_4664_, 1);
lean_dec(v_unused_4752_);
v___x_4667_ = v_a_4664_;
v_isShared_4668_ = v_isSharedCheck_4751_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_fst_4665_);
lean_dec(v_a_4664_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4751_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; lean_object* v___x_4672_; 
v___x_4669_ = l_Subarray_copy___redArg(v___x_4620_);
lean_inc_ref(v___x_4669_);
v___x_4670_ = l_Array_append___redArg(v___x_4669_, v_altVars_4621_);
v___x_4671_ = 1;
v___x_4672_ = l_Lean_Meta_mkForallFVars(v___x_4670_, v_fst_4665_, v___x_4622_, v___x_4623_, v___x_4623_, v___x_4671_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
lean_dec_ref(v___x_4670_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4673_);
lean_dec_ref_known(v___x_4672_, 1);
v___x_4674_ = l_Lean_ConstantInfo_name(v_a_4624_);
v___x_4675_ = l_Lean_mkConst(v___x_4674_, v___x_4625_);
lean_inc_ref(v___x_4626_);
v___x_4676_ = l_Subarray_copy___redArg(v___x_4626_);
v___x_4677_ = lean_mk_empty_array_with_capacity(v___x_4627_);
v___x_4678_ = lean_array_push(v___x_4677_, v___x_4628_);
v___x_4679_ = l_Array_append___redArg(v___x_4676_, v___x_4678_);
lean_dec_ref(v___x_4678_);
v___x_4680_ = l_Array_append___redArg(v___x_4679_, v___x_4669_);
lean_dec_ref(v___x_4669_);
v___x_4681_ = l_Subarray_copy___redArg(v___x_4629_);
v___x_4682_ = l_Array_append___redArg(v___x_4680_, v___x_4681_);
lean_dec_ref(v___x_4681_);
v___x_4683_ = l_Lean_mkAppN(v___x_4675_, v___x_4682_);
v___x_4684_ = l_Lean_Meta_mkHEq(v___x_4683_, v_a_4644_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_object* v_a_4685_; lean_object* v___x_4686_; 
v_a_4685_ = lean_ctor_get(v___x_4684_, 0);
lean_inc(v_a_4685_);
lean_dec_ref_known(v___x_4684_, 1);
v___x_4686_ = l_Lean_mkArrowN(v_a_4649_, v_a_4685_, v___y_4653_, v___y_4654_);
lean_dec(v_a_4649_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4687_);
lean_dec_ref_known(v___x_4686_, 1);
v___x_4688_ = l_Array_append___redArg(v___x_4682_, v_altVars_4621_);
v___x_4689_ = l_Array_append___redArg(v___x_4688_, v_heqs_4636_);
v___x_4690_ = l_Lean_Meta_mkForallFVars(v___x_4689_, v_a_4687_, v___x_4622_, v___x_4623_, v___x_4623_, v___x_4671_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
lean_dec_ref(v___x_4689_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4692_; 
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
lean_inc(v_a_4691_);
lean_dec_ref_known(v___x_4690_, 1);
v___x_4692_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4691_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4750_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4692_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4695_ = v___x_4692_;
v_isShared_4696_ = v_isSharedCheck_4750_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4692_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4750_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v_start_4697_; lean_object* v_stop_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4748_; 
v_start_4697_ = lean_ctor_get(v___x_4626_, 1);
v_stop_4698_ = lean_ctor_get(v___x_4626_, 2);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4748_ == 0)
{
lean_object* v_unused_4749_; 
v_unused_4749_ = lean_ctor_get(v___x_4626_, 0);
lean_dec(v_unused_4749_);
v___x_4700_ = v___x_4626_;
v_isShared_4701_ = v_isSharedCheck_4748_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_stop_4698_);
lean_inc(v_start_4697_);
lean_dec(v___x_4626_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4748_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4702_ = lean_nat_sub(v_stop_4698_, v_start_4697_);
lean_dec(v_start_4697_);
lean_dec(v_stop_4698_);
v___x_4703_ = lean_nat_add(v___x_4702_, v___x_4627_);
lean_dec(v___x_4702_);
v___x_4704_ = lean_nat_add(v___x_4703_, v___x_4630_);
lean_dec(v___x_4703_);
v___x_4705_ = lean_nat_add(v___x_4704_, v___x_4631_);
lean_dec(v___x_4704_);
v___x_4706_ = lean_array_get_size(v_altVars_4621_);
v___x_4707_ = lean_nat_add(v___x_4705_, v___x_4706_);
lean_dec(v___x_4705_);
v___x_4708_ = lean_array_get_size(v_heqs_4636_);
lean_dec_ref(v_heqs_4636_);
lean_inc(v_a_4693_);
v___x_4709_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4632_, v_a_4693_, v___x_4707_, v___x_4708_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4747_; 
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4712_ = v___x_4709_;
v_isShared_4713_ = v_isSharedCheck_4747_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4709_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4747_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4714_; lean_object* v_env_4715_; uint8_t v___x_4716_; 
v___x_4714_ = lean_st_ref_get(v___y_4654_);
v_env_4715_ = lean_ctor_get(v___x_4714_, 0);
lean_inc_ref(v_env_4715_);
lean_dec(v___x_4714_);
lean_inc(v___x_4633_);
v___x_4716_ = l_Lean_Environment_contains(v_env_4715_, v___x_4633_, v___x_4623_);
if (v___x_4716_ == 0)
{
lean_object* v___x_4718_; 
lean_del_object(v___x_4712_);
lean_inc(v___x_4633_);
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 2, v_a_4693_);
lean_ctor_set(v___x_4700_, 1, v___x_4634_);
lean_ctor_set(v___x_4700_, 0, v___x_4633_);
v___x_4718_ = v___x_4700_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4633_);
lean_ctor_set(v_reuseFailAlloc_4743_, 1, v___x_4634_);
lean_ctor_set(v_reuseFailAlloc_4743_, 2, v_a_4693_);
v___x_4718_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
lean_object* v___x_4720_; 
if (v_isShared_4668_ == 0)
{
lean_ctor_set_tag(v___x_4667_, 1);
lean_ctor_set(v___x_4667_, 1, v___x_4635_);
lean_ctor_set(v___x_4667_, 0, v___x_4633_);
v___x_4720_ = v___x_4667_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v___x_4633_);
lean_ctor_set(v_reuseFailAlloc_4742_, 1, v___x_4635_);
v___x_4720_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4721_; lean_object* v___x_4723_; 
v___x_4721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4718_);
lean_ctor_set(v___x_4721_, 1, v_a_4710_);
lean_ctor_set(v___x_4721_, 2, v___x_4720_);
if (v_isShared_4696_ == 0)
{
lean_ctor_set_tag(v___x_4695_, 2);
lean_ctor_set(v___x_4695_, 0, v___x_4721_);
v___x_4723_ = v___x_4695_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v___x_4721_);
v___x_4723_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4724_; 
v___x_4724_ = l_Lean_addDecl(v___x_4723_, v___x_4622_, v___y_4653_, v___y_4654_);
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4731_; 
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; 
v_unused_4732_ = lean_ctor_get(v___x_4724_, 0);
lean_dec(v_unused_4732_);
v___x_4726_ = v___x_4724_;
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
else
{
lean_dec(v___x_4724_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
if (v_isShared_4727_ == 0)
{
lean_ctor_set(v___x_4726_, 0, v_a_4673_);
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4673_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
else
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4740_; 
lean_dec(v_a_4673_);
v_a_4733_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4735_ = v___x_4724_;
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4724_);
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
}
}
}
else
{
lean_object* v___x_4745_; 
lean_dec(v_a_4710_);
lean_del_object(v___x_4700_);
lean_del_object(v___x_4695_);
lean_dec(v_a_4693_);
lean_del_object(v___x_4667_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
if (v_isShared_4713_ == 0)
{
lean_ctor_set(v___x_4712_, 0, v_a_4673_);
v___x_4745_ = v___x_4712_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4673_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
else
{
lean_del_object(v___x_4700_);
lean_del_object(v___x_4695_);
lean_dec(v_a_4693_);
lean_dec(v_a_4673_);
lean_del_object(v___x_4667_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
return v___x_4709_;
}
}
}
}
else
{
lean_dec(v_a_4673_);
lean_del_object(v___x_4667_);
lean_dec_ref(v_heqs_4636_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
lean_dec(v_matchDeclName_4632_);
lean_dec_ref(v___x_4626_);
return v___x_4692_;
}
}
else
{
lean_dec(v_a_4673_);
lean_del_object(v___x_4667_);
lean_dec_ref(v_heqs_4636_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
lean_dec(v_matchDeclName_4632_);
lean_dec_ref(v___x_4626_);
return v___x_4690_;
}
}
else
{
lean_dec_ref(v___x_4682_);
lean_dec(v_a_4673_);
lean_del_object(v___x_4667_);
lean_dec_ref(v_heqs_4636_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
lean_dec(v_matchDeclName_4632_);
lean_dec_ref(v___x_4626_);
return v___x_4686_;
}
}
else
{
lean_dec_ref(v___x_4682_);
lean_dec(v_a_4673_);
lean_del_object(v___x_4667_);
lean_dec(v_a_4649_);
lean_dec_ref(v_heqs_4636_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
lean_dec(v_matchDeclName_4632_);
lean_dec_ref(v___x_4626_);
return v___x_4684_;
}
}
else
{
lean_dec_ref(v___x_4669_);
lean_del_object(v___x_4667_);
lean_dec(v_a_4649_);
lean_dec(v_a_4644_);
lean_dec_ref(v_heqs_4636_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
lean_dec(v_matchDeclName_4632_);
lean_dec_ref(v___x_4629_);
lean_dec_ref(v___x_4628_);
lean_dec_ref(v___x_4626_);
lean_dec(v___x_4625_);
return v___x_4672_;
}
}
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4760_; 
lean_dec(v_a_4649_);
lean_dec(v_a_4644_);
lean_dec_ref(v_heqs_4636_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
lean_dec(v_matchDeclName_4632_);
lean_dec_ref(v___x_4629_);
lean_dec_ref(v___x_4628_);
lean_dec_ref(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec_ref(v___x_4620_);
v_a_4753_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4755_ = v___x_4663_;
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4663_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_dec(v_a_4644_);
lean_dec_ref(v_heqs_4636_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
lean_dec(v_matchDeclName_4632_);
lean_dec_ref(v___x_4629_);
lean_dec_ref(v___x_4628_);
lean_dec_ref(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec(v___x_4619_);
lean_dec_ref(v___x_4618_);
lean_dec_ref(v_a_4616_);
v_a_4782_ = lean_ctor_get(v___x_4648_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4648_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4648_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4636_);
lean_dec(v___x_4635_);
lean_dec(v___x_4634_);
lean_dec(v___x_4633_);
lean_dec(v_matchDeclName_4632_);
lean_dec_ref(v___x_4629_);
lean_dec_ref(v___x_4628_);
lean_dec_ref(v___x_4626_);
lean_dec(v___x_4625_);
lean_dec_ref(v___x_4620_);
lean_dec(v___x_4619_);
lean_dec_ref(v___x_4618_);
lean_dec(v___x_4617_);
lean_dec_ref(v_a_4616_);
return v___x_4643_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4790_ = _args[0];
lean_object* v_args_4791_ = _args[1];
lean_object* v___x_4792_ = _args[2];
lean_object* v_overlaps_4793_ = _args[3];
lean_object* v_a_4794_ = _args[4];
lean_object* v_fst_4795_ = _args[5];
lean_object* v_a_4796_ = _args[6];
lean_object* v___x_4797_ = _args[7];
lean_object* v___x_4798_ = _args[8];
lean_object* v___x_4799_ = _args[9];
lean_object* v___x_4800_ = _args[10];
lean_object* v_altVars_4801_ = _args[11];
lean_object* v___x_4802_ = _args[12];
lean_object* v___x_4803_ = _args[13];
lean_object* v_a_4804_ = _args[14];
lean_object* v___x_4805_ = _args[15];
lean_object* v___x_4806_ = _args[16];
lean_object* v___x_4807_ = _args[17];
lean_object* v___x_4808_ = _args[18];
lean_object* v___x_4809_ = _args[19];
lean_object* v___x_4810_ = _args[20];
lean_object* v___x_4811_ = _args[21];
lean_object* v_matchDeclName_4812_ = _args[22];
lean_object* v___x_4813_ = _args[23];
lean_object* v___x_4814_ = _args[24];
lean_object* v___x_4815_ = _args[25];
lean_object* v_heqs_4816_ = _args[26];
lean_object* v___y_4817_ = _args[27];
lean_object* v___y_4818_ = _args[28];
lean_object* v___y_4819_ = _args[29];
lean_object* v___y_4820_ = _args[30];
lean_object* v___y_4821_ = _args[31];
_start:
{
uint8_t v___x_22595__boxed_4822_; uint8_t v___x_22596__boxed_4823_; lean_object* v_res_4824_; 
v___x_22595__boxed_4822_ = lean_unbox(v___x_4802_);
v___x_22596__boxed_4823_ = lean_unbox(v___x_4803_);
v_res_4824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4790_, v_args_4791_, v___x_4792_, v_overlaps_4793_, v_a_4794_, v_fst_4795_, v_a_4796_, v___x_4797_, v___x_4798_, v___x_4799_, v___x_4800_, v_altVars_4801_, v___x_22595__boxed_4822_, v___x_22596__boxed_4823_, v_a_4804_, v___x_4805_, v___x_4806_, v___x_4807_, v___x_4808_, v___x_4809_, v___x_4810_, v___x_4811_, v_matchDeclName_4812_, v___x_4813_, v___x_4814_, v___x_4815_, v_heqs_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec(v___y_4818_);
lean_dec_ref(v___y_4817_);
lean_dec(v___x_4811_);
lean_dec(v___x_4810_);
lean_dec(v___x_4807_);
lean_dec_ref(v_a_4804_);
lean_dec_ref(v_altVars_4801_);
lean_dec(v_fst_4795_);
lean_dec(v_a_4794_);
lean_dec_ref(v_overlaps_4793_);
lean_dec_ref(v_args_4791_);
return v_res_4824_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4827_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4828_ = lean_unsigned_to_nat(8u);
v___x_4829_ = lean_unsigned_to_nat(295u);
v___x_4830_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4831_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4832_ = l_mkPanicMessageWithDecl(v___x_4831_, v___x_4830_, v___x_4829_, v___x_4828_, v___x_4827_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4833_, lean_object* v___x_4834_, lean_object* v___x_4835_, lean_object* v___y_4836_, lean_object* v___x_4837_, lean_object* v_overlaps_4838_, lean_object* v_a_4839_, lean_object* v_fst_4840_, lean_object* v___x_4841_, lean_object* v_a_4842_, lean_object* v___x_4843_, lean_object* v___x_4844_, lean_object* v___x_4845_, lean_object* v___x_4846_, lean_object* v___x_4847_, lean_object* v___x_4848_, lean_object* v_matchDeclName_4849_, lean_object* v___x_4850_, lean_object* v___x_4851_, lean_object* v___x_4852_, lean_object* v_altVars_4853_, lean_object* v_args_4854_, lean_object* v___mask_4855_, lean_object* v_altResultType_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
uint8_t v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = 0;
v___x_4863_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4856_, v___f_4833_, v___x_4862_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v_start_4865_; lean_object* v_stop_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; uint8_t v___x_4869_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref_known(v___x_4863_, 1);
v_start_4865_ = lean_ctor_get(v___x_4834_, 1);
v_stop_4866_ = lean_ctor_get(v___x_4834_, 2);
v___x_4867_ = lean_array_get_size(v_a_4864_);
v___x_4868_ = lean_nat_sub(v_stop_4866_, v_start_4865_);
v___x_4869_ = lean_nat_dec_eq(v___x_4867_, v___x_4868_);
if (v___x_4869_ == 0)
{
lean_object* v___x_4870_; lean_object* v___x_4871_; 
lean_dec(v___x_4868_);
lean_dec(v_a_4864_);
lean_dec_ref(v_args_4854_);
lean_dec_ref(v_altVars_4853_);
lean_dec(v___x_4852_);
lean_dec(v___x_4851_);
lean_dec(v___x_4850_);
lean_dec(v_matchDeclName_4849_);
lean_dec(v___x_4848_);
lean_dec_ref(v___x_4847_);
lean_dec_ref(v___x_4846_);
lean_dec(v___x_4845_);
lean_dec_ref(v___x_4844_);
lean_dec(v___x_4843_);
lean_dec_ref(v_a_4842_);
lean_dec_ref(v___x_4841_);
lean_dec(v_fst_4840_);
lean_dec(v_a_4839_);
lean_dec_ref(v_overlaps_4838_);
lean_dec(v___x_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___x_4835_);
lean_dec_ref(v___x_4834_);
v___x_4870_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4871_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4870_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
return v___x_4871_;
}
else
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; 
v___x_4872_ = lean_mk_empty_array_with_capacity(v___x_4835_);
lean_inc(v___x_4835_);
lean_inc(v_a_4864_);
v___x_4873_ = l_Array_toSubarray___redArg(v_a_4864_, v___x_4835_, v___x_4867_);
v___x_4874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4872_);
lean_ctor_set(v___x_4874_, 1, v___x_4873_);
lean_inc_ref(v___x_4834_);
v___x_4875_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v___x_4834_, v___x_4874_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v_fst_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___f_4880_; uint8_t v___x_4881_; lean_object* v___x_4882_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
lean_inc(v_a_4876_);
lean_dec_ref_known(v___x_4875_, 1);
v_fst_4877_ = lean_ctor_get(v_a_4876_, 0);
lean_inc(v_fst_4877_);
lean_dec(v_a_4876_);
v___x_4878_ = lean_box(v___x_4862_);
v___x_4879_ = lean_box(v___x_4869_);
v___f_4880_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4880_, 0, v___y_4836_);
lean_closure_set(v___f_4880_, 1, v_args_4854_);
lean_closure_set(v___f_4880_, 2, v___x_4837_);
lean_closure_set(v___f_4880_, 3, v_overlaps_4838_);
lean_closure_set(v___f_4880_, 4, v_a_4839_);
lean_closure_set(v___f_4880_, 5, v_fst_4840_);
lean_closure_set(v___f_4880_, 6, v_a_4864_);
lean_closure_set(v___f_4880_, 7, v___x_4867_);
lean_closure_set(v___f_4880_, 8, v___x_4841_);
lean_closure_set(v___f_4880_, 9, v___x_4835_);
lean_closure_set(v___f_4880_, 10, v___x_4834_);
lean_closure_set(v___f_4880_, 11, v_altVars_4853_);
lean_closure_set(v___f_4880_, 12, v___x_4878_);
lean_closure_set(v___f_4880_, 13, v___x_4879_);
lean_closure_set(v___f_4880_, 14, v_a_4842_);
lean_closure_set(v___f_4880_, 15, v___x_4843_);
lean_closure_set(v___f_4880_, 16, v___x_4844_);
lean_closure_set(v___f_4880_, 17, v___x_4845_);
lean_closure_set(v___f_4880_, 18, v___x_4846_);
lean_closure_set(v___f_4880_, 19, v___x_4847_);
lean_closure_set(v___f_4880_, 20, v___x_4868_);
lean_closure_set(v___f_4880_, 21, v___x_4848_);
lean_closure_set(v___f_4880_, 22, v_matchDeclName_4849_);
lean_closure_set(v___f_4880_, 23, v___x_4850_);
lean_closure_set(v___f_4880_, 24, v___x_4851_);
lean_closure_set(v___f_4880_, 25, v___x_4852_);
v___x_4881_ = 0;
v___x_4882_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4877_, v___f_4880_, v___x_4881_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
return v___x_4882_;
}
else
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4890_; 
lean_dec(v___x_4868_);
lean_dec(v_a_4864_);
lean_dec_ref(v_args_4854_);
lean_dec_ref(v_altVars_4853_);
lean_dec(v___x_4852_);
lean_dec(v___x_4851_);
lean_dec(v___x_4850_);
lean_dec(v_matchDeclName_4849_);
lean_dec(v___x_4848_);
lean_dec_ref(v___x_4847_);
lean_dec_ref(v___x_4846_);
lean_dec(v___x_4845_);
lean_dec_ref(v___x_4844_);
lean_dec(v___x_4843_);
lean_dec_ref(v_a_4842_);
lean_dec_ref(v___x_4841_);
lean_dec(v_fst_4840_);
lean_dec(v_a_4839_);
lean_dec_ref(v_overlaps_4838_);
lean_dec(v___x_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___x_4835_);
lean_dec_ref(v___x_4834_);
v_a_4883_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4885_ = v___x_4875_;
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4875_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4888_; 
if (v_isShared_4886_ == 0)
{
v___x_4888_ = v___x_4885_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_a_4883_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
}
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4898_; 
lean_dec_ref(v_args_4854_);
lean_dec_ref(v_altVars_4853_);
lean_dec(v___x_4852_);
lean_dec(v___x_4851_);
lean_dec(v___x_4850_);
lean_dec(v_matchDeclName_4849_);
lean_dec(v___x_4848_);
lean_dec_ref(v___x_4847_);
lean_dec_ref(v___x_4846_);
lean_dec(v___x_4845_);
lean_dec_ref(v___x_4844_);
lean_dec(v___x_4843_);
lean_dec_ref(v_a_4842_);
lean_dec_ref(v___x_4841_);
lean_dec(v_fst_4840_);
lean_dec(v_a_4839_);
lean_dec_ref(v_overlaps_4838_);
lean_dec(v___x_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___x_4835_);
lean_dec_ref(v___x_4834_);
v_a_4891_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4893_ = v___x_4863_;
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4863_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4899_ = _args[0];
lean_object* v___x_4900_ = _args[1];
lean_object* v___x_4901_ = _args[2];
lean_object* v___y_4902_ = _args[3];
lean_object* v___x_4903_ = _args[4];
lean_object* v_overlaps_4904_ = _args[5];
lean_object* v_a_4905_ = _args[6];
lean_object* v_fst_4906_ = _args[7];
lean_object* v___x_4907_ = _args[8];
lean_object* v_a_4908_ = _args[9];
lean_object* v___x_4909_ = _args[10];
lean_object* v___x_4910_ = _args[11];
lean_object* v___x_4911_ = _args[12];
lean_object* v___x_4912_ = _args[13];
lean_object* v___x_4913_ = _args[14];
lean_object* v___x_4914_ = _args[15];
lean_object* v_matchDeclName_4915_ = _args[16];
lean_object* v___x_4916_ = _args[17];
lean_object* v___x_4917_ = _args[18];
lean_object* v___x_4918_ = _args[19];
lean_object* v_altVars_4919_ = _args[20];
lean_object* v_args_4920_ = _args[21];
lean_object* v___mask_4921_ = _args[22];
lean_object* v_altResultType_4922_ = _args[23];
lean_object* v___y_4923_ = _args[24];
lean_object* v___y_4924_ = _args[25];
lean_object* v___y_4925_ = _args[26];
lean_object* v___y_4926_ = _args[27];
lean_object* v___y_4927_ = _args[28];
_start:
{
lean_object* v_res_4928_; 
v_res_4928_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4899_, v___x_4900_, v___x_4901_, v___y_4902_, v___x_4903_, v_overlaps_4904_, v_a_4905_, v_fst_4906_, v___x_4907_, v_a_4908_, v___x_4909_, v___x_4910_, v___x_4911_, v___x_4912_, v___x_4913_, v___x_4914_, v_matchDeclName_4915_, v___x_4916_, v___x_4917_, v___x_4918_, v_altVars_4919_, v_args_4920_, v___mask_4921_, v_altResultType_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_);
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec_ref(v___mask_4921_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4930_, lean_object* v_val_4931_, lean_object* v_matchDeclName_4932_, lean_object* v___x_4933_, lean_object* v___x_4934_, lean_object* v_a_4935_, lean_object* v___x_4936_, lean_object* v___x_4937_, lean_object* v___x_4938_, lean_object* v___x_4939_, lean_object* v___x_4940_, lean_object* v___x_4941_, lean_object* v_a_4942_, lean_object* v_b_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
uint8_t v___x_4949_; 
v___x_4949_ = lean_nat_dec_lt(v_a_4942_, v_upperBound_4930_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4950_; 
lean_dec(v_a_4942_);
lean_dec(v___x_4941_);
lean_dec(v___x_4940_);
lean_dec_ref(v___x_4939_);
lean_dec_ref(v___x_4938_);
lean_dec_ref(v___x_4937_);
lean_dec(v___x_4936_);
lean_dec_ref(v_a_4935_);
lean_dec(v___x_4934_);
lean_dec_ref(v___x_4933_);
lean_dec(v_matchDeclName_4932_);
lean_dec_ref(v_val_4931_);
v___x_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4950_, 0, v_b_4943_);
return v___x_4950_;
}
else
{
lean_object* v_snd_4951_; lean_object* v_fst_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_5015_; 
v_snd_4951_ = lean_ctor_get(v_b_4943_, 1);
v_fst_4952_ = lean_ctor_get(v_b_4943_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v_b_4943_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_4954_ = v_b_4943_;
v_isShared_4955_ = v_isSharedCheck_5015_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_snd_4951_);
lean_inc(v_fst_4952_);
lean_dec(v_b_4943_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_5015_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v_fst_4956_; lean_object* v_snd_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_5014_; 
v_fst_4956_ = lean_ctor_get(v_snd_4951_, 0);
v_snd_4957_ = lean_ctor_get(v_snd_4951_, 1);
v_isSharedCheck_5014_ = !lean_is_exclusive(v_snd_4951_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_4959_ = v_snd_4951_;
v_isShared_4960_ = v_isSharedCheck_5014_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_snd_4957_);
lean_inc(v_fst_4956_);
lean_dec(v_snd_4951_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_5014_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v_altInfos_4961_; lean_object* v_overlaps_4962_; lean_object* v_start_4963_; lean_object* v_stop_4964_; lean_object* v___f_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___y_4977_; lean_object* v___x_5009_; uint8_t v___x_5010_; 
v_altInfos_4961_ = lean_ctor_get(v_val_4931_, 2);
v_overlaps_4962_ = lean_ctor_get(v_val_4931_, 5);
v_start_4963_ = lean_ctor_get(v___x_4939_, 1);
v_stop_4964_ = lean_ctor_get(v___x_4939_, 2);
v___f_4965_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4966_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4967_ = lean_unsigned_to_nat(0u);
v___x_4968_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4969_ = lean_unsigned_to_nat(1u);
v___x_4970_ = lean_box(0);
v___x_4971_ = lean_array_get_borrowed(v___x_4966_, v_altInfos_4961_, v_a_4942_);
v___x_4972_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4932_);
v___x_4973_ = l_Lean_Name_str___override(v_matchDeclName_4932_, v___x_4972_);
lean_inc(v_snd_4957_);
v___x_4974_ = lean_name_append_index_after(v___x_4973_, v_snd_4957_);
lean_inc(v___x_4974_);
v___x_4975_ = lean_array_push(v_fst_4952_, v___x_4974_);
v___x_5009_ = lean_nat_sub(v_stop_4964_, v_start_4963_);
v___x_5010_ = lean_nat_dec_lt(v_a_4942_, v___x_5009_);
lean_dec(v___x_5009_);
if (v___x_5010_ == 0)
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5011_ = l_Lean_instInhabitedExpr;
v___x_5012_ = l_outOfBounds___redArg(v___x_5011_);
v___y_4977_ = v___x_5012_;
goto v___jp_4976_;
}
else
{
lean_object* v___x_5013_; 
v___x_5013_ = l_Subarray_get___redArg(v___x_4939_, v_a_4942_);
v___y_4977_ = v___x_5013_;
goto v___jp_4976_;
}
v___jp_4976_:
{
lean_object* v___x_4978_; 
lean_inc(v___y_4947_);
lean_inc_ref(v___y_4946_);
lean_inc(v___y_4945_);
lean_inc_ref(v___y_4944_);
lean_inc_ref(v___y_4977_);
v___x_4978_ = lean_infer_type(v___y_4977_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_object* v_a_4979_; lean_object* v___f_4980_; lean_object* v___x_4981_; 
v_a_4979_ = lean_ctor_get(v___x_4978_, 0);
lean_inc(v_a_4979_);
lean_dec_ref_known(v___x_4978_, 1);
lean_inc(v___x_4941_);
lean_inc(v_matchDeclName_4932_);
lean_inc(v___x_4940_);
lean_inc_ref(v___x_4939_);
lean_inc_ref(v___x_4938_);
lean_inc_ref(v___x_4937_);
lean_inc(v___x_4936_);
lean_inc_ref(v_a_4935_);
lean_inc(v_fst_4956_);
lean_inc(v_a_4942_);
lean_inc_ref(v_overlaps_4962_);
lean_inc(v___x_4934_);
lean_inc_ref(v___x_4933_);
v___f_4980_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 29, 20);
lean_closure_set(v___f_4980_, 0, v___f_4965_);
lean_closure_set(v___f_4980_, 1, v___x_4933_);
lean_closure_set(v___f_4980_, 2, v___x_4967_);
lean_closure_set(v___f_4980_, 3, v___y_4977_);
lean_closure_set(v___f_4980_, 4, v___x_4934_);
lean_closure_set(v___f_4980_, 5, v_overlaps_4962_);
lean_closure_set(v___f_4980_, 6, v_a_4942_);
lean_closure_set(v___f_4980_, 7, v_fst_4956_);
lean_closure_set(v___f_4980_, 8, v___x_4968_);
lean_closure_set(v___f_4980_, 9, v_a_4935_);
lean_closure_set(v___f_4980_, 10, v___x_4936_);
lean_closure_set(v___f_4980_, 11, v___x_4937_);
lean_closure_set(v___f_4980_, 12, v___x_4969_);
lean_closure_set(v___f_4980_, 13, v___x_4938_);
lean_closure_set(v___f_4980_, 14, v___x_4939_);
lean_closure_set(v___f_4980_, 15, v___x_4940_);
lean_closure_set(v___f_4980_, 16, v_matchDeclName_4932_);
lean_closure_set(v___f_4980_, 17, v___x_4974_);
lean_closure_set(v___f_4980_, 18, v___x_4941_);
lean_closure_set(v___f_4980_, 19, v___x_4970_);
lean_inc(v___x_4971_);
v___x_4981_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4979_, v___x_4971_, v___f_4980_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4986_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_a_4982_);
lean_dec_ref_known(v___x_4981_, 1);
v___x_4983_ = lean_array_push(v_fst_4956_, v_a_4982_);
v___x_4984_ = lean_nat_add(v_snd_4957_, v___x_4969_);
lean_dec(v_snd_4957_);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 1, v___x_4984_);
lean_ctor_set(v___x_4959_, 0, v___x_4983_);
v___x_4986_ = v___x_4959_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4983_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v___x_4984_);
v___x_4986_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
lean_object* v___x_4988_; 
if (v_isShared_4955_ == 0)
{
lean_ctor_set(v___x_4954_, 1, v___x_4986_);
lean_ctor_set(v___x_4954_, 0, v___x_4975_);
v___x_4988_ = v___x_4954_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v___x_4975_);
lean_ctor_set(v_reuseFailAlloc_4991_, 1, v___x_4986_);
v___x_4988_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
lean_object* v___x_4989_; 
v___x_4989_ = lean_nat_add(v_a_4942_, v___x_4969_);
lean_dec(v_a_4942_);
v_a_4942_ = v___x_4989_;
v_b_4943_ = v___x_4988_;
goto _start;
}
}
}
else
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5000_; 
lean_dec_ref(v___x_4975_);
lean_del_object(v___x_4959_);
lean_dec(v_snd_4957_);
lean_dec(v_fst_4956_);
lean_del_object(v___x_4954_);
lean_dec(v_a_4942_);
lean_dec(v___x_4941_);
lean_dec(v___x_4940_);
lean_dec_ref(v___x_4939_);
lean_dec_ref(v___x_4938_);
lean_dec_ref(v___x_4937_);
lean_dec(v___x_4936_);
lean_dec_ref(v_a_4935_);
lean_dec(v___x_4934_);
lean_dec_ref(v___x_4933_);
lean_dec(v_matchDeclName_4932_);
lean_dec_ref(v_val_4931_);
v_a_4993_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4981_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4981_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5008_; 
lean_dec_ref(v___y_4977_);
lean_dec_ref(v___x_4975_);
lean_dec(v___x_4974_);
lean_del_object(v___x_4959_);
lean_dec(v_snd_4957_);
lean_dec(v_fst_4956_);
lean_del_object(v___x_4954_);
lean_dec(v_a_4942_);
lean_dec(v___x_4941_);
lean_dec(v___x_4940_);
lean_dec_ref(v___x_4939_);
lean_dec_ref(v___x_4938_);
lean_dec_ref(v___x_4937_);
lean_dec(v___x_4936_);
lean_dec_ref(v_a_4935_);
lean_dec(v___x_4934_);
lean_dec_ref(v___x_4933_);
lean_dec(v_matchDeclName_4932_);
lean_dec_ref(v_val_4931_);
v_a_5001_ = lean_ctor_get(v___x_4978_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4978_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5003_ = v___x_4978_;
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_4978_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5006_; 
if (v_isShared_5004_ == 0)
{
v___x_5006_ = v___x_5003_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
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
lean_object* v_upperBound_5016_ = _args[0];
lean_object* v_val_5017_ = _args[1];
lean_object* v_matchDeclName_5018_ = _args[2];
lean_object* v___x_5019_ = _args[3];
lean_object* v___x_5020_ = _args[4];
lean_object* v_a_5021_ = _args[5];
lean_object* v___x_5022_ = _args[6];
lean_object* v___x_5023_ = _args[7];
lean_object* v___x_5024_ = _args[8];
lean_object* v___x_5025_ = _args[9];
lean_object* v___x_5026_ = _args[10];
lean_object* v___x_5027_ = _args[11];
lean_object* v_a_5028_ = _args[12];
lean_object* v_b_5029_ = _args[13];
lean_object* v___y_5030_ = _args[14];
lean_object* v___y_5031_ = _args[15];
lean_object* v___y_5032_ = _args[16];
lean_object* v___y_5033_ = _args[17];
lean_object* v___y_5034_ = _args[18];
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5016_, v_val_5017_, v_matchDeclName_5018_, v___x_5019_, v___x_5020_, v_a_5021_, v___x_5022_, v___x_5023_, v___x_5024_, v___x_5025_, v___x_5026_, v___x_5027_, v_a_5028_, v_b_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v___y_5031_);
lean_dec_ref(v___y_5030_);
lean_dec(v_upperBound_5016_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5042_, lean_object* v___x_5043_, lean_object* v_matchDeclName_5044_, lean_object* v___x_5045_, lean_object* v_a_5046_, lean_object* v___x_5047_, lean_object* v___x_5048_, lean_object* v_xs_5049_, lean_object* v___matchResultType_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v_numParams_5056_; lean_object* v_numDiscrs_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v_lower_5063_; lean_object* v_upper_5064_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; uint8_t v___x_5095_; 
v_numParams_5056_ = lean_ctor_get(v_val_5042_, 0);
v_numDiscrs_5057_ = lean_ctor_get(v_val_5042_, 1);
v___x_5058_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5056_);
lean_inc_ref(v_xs_5049_);
v___x_5059_ = l_Array_toSubarray___redArg(v_xs_5049_, v___x_5058_, v_numParams_5056_);
v___x_5060_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5042_);
v___x_5061_ = lean_array_get(v___x_5043_, v_xs_5049_, v___x_5060_);
lean_dec(v___x_5060_);
v___x_5092_ = lean_array_get_size(v_xs_5049_);
v___x_5093_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5042_);
v___x_5094_ = lean_nat_sub(v___x_5092_, v___x_5093_);
lean_dec(v___x_5093_);
v___x_5095_ = lean_nat_dec_le(v___x_5094_, v___x_5058_);
if (v___x_5095_ == 0)
{
v_lower_5063_ = v___x_5094_;
v_upper_5064_ = v___x_5092_;
goto v___jp_5062_;
}
else
{
lean_dec(v___x_5094_);
v_lower_5063_ = v___x_5058_;
v_upper_5064_ = v___x_5092_;
goto v___jp_5062_;
}
v___jp_5062_:
{
lean_object* v___x_5065_; lean_object* v_start_5066_; lean_object* v_stop_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
lean_inc_ref(v_xs_5049_);
v___x_5065_ = l_Array_toSubarray___redArg(v_xs_5049_, v_lower_5063_, v_upper_5064_);
v_start_5066_ = lean_ctor_get(v___x_5065_, 1);
lean_inc(v_start_5066_);
v_stop_5067_ = lean_ctor_get(v___x_5065_, 2);
lean_inc(v_stop_5067_);
v___x_5068_ = lean_unsigned_to_nat(1u);
v___x_5069_ = lean_nat_add(v_numParams_5056_, v___x_5068_);
v___x_5070_ = lean_nat_add(v___x_5069_, v_numDiscrs_5057_);
v___x_5071_ = lean_nat_sub(v_stop_5067_, v_start_5066_);
lean_dec(v_start_5066_);
lean_dec(v_stop_5067_);
v___x_5072_ = l_Array_toSubarray___redArg(v_xs_5049_, v___x_5069_, v___x_5070_);
v___x_5073_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5071_);
v___x_5074_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5071_, v_val_5042_, v_matchDeclName_5044_, v___x_5072_, v___x_5045_, v_a_5046_, v___x_5047_, v___x_5059_, v___x_5061_, v___x_5065_, v___x_5071_, v___x_5048_, v___x_5058_, v___x_5073_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
lean_dec(v___x_5071_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5082_; 
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5082_ == 0)
{
lean_object* v_unused_5083_; 
v_unused_5083_ = lean_ctor_get(v___x_5074_, 0);
lean_dec(v_unused_5083_);
v___x_5076_ = v___x_5074_;
v_isShared_5077_ = v_isSharedCheck_5082_;
goto v_resetjp_5075_;
}
else
{
lean_dec(v___x_5074_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5082_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5078_; lean_object* v___x_5080_; 
v___x_5078_ = lean_box(0);
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 0, v___x_5078_);
v___x_5080_ = v___x_5076_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5078_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
else
{
lean_object* v_a_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5091_; 
v_a_5084_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5086_ = v___x_5074_;
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_a_5084_);
lean_dec(v___x_5074_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5089_; 
if (v_isShared_5087_ == 0)
{
v___x_5089_ = v___x_5086_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_a_5084_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
return v___x_5089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5096_, lean_object* v___x_5097_, lean_object* v_matchDeclName_5098_, lean_object* v___x_5099_, lean_object* v_a_5100_, lean_object* v___x_5101_, lean_object* v___x_5102_, lean_object* v_xs_5103_, lean_object* v___matchResultType_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_){
_start:
{
lean_object* v_res_5110_; 
v_res_5110_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5096_, v___x_5097_, v_matchDeclName_5098_, v___x_5099_, v_a_5100_, v___x_5101_, v___x_5102_, v_xs_5103_, v___matchResultType_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
lean_dec(v___y_5106_);
lean_dec_ref(v___y_5105_);
lean_dec_ref(v___matchResultType_5104_);
lean_dec_ref(v___x_5097_);
return v_res_5110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_){
_start:
{
uint8_t v_trackZetaDelta_5117_; lean_object* v_zetaDeltaSet_5118_; lean_object* v_lctx_5119_; lean_object* v_localInstances_5120_; lean_object* v_defEqCtx_x3f_5121_; lean_object* v_synthPendingDepth_5122_; lean_object* v_canUnfold_x3f_5123_; uint8_t v_univApprox_5124_; uint8_t v_inTypeClassResolution_5125_; uint8_t v_cacheInferType_5126_; lean_object* v___x_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5170_; 
v_trackZetaDelta_5117_ = lean_ctor_get_uint8(v_a_5112_, sizeof(void*)*7);
v_zetaDeltaSet_5118_ = lean_ctor_get(v_a_5112_, 1);
lean_inc(v_zetaDeltaSet_5118_);
v_lctx_5119_ = lean_ctor_get(v_a_5112_, 2);
lean_inc_ref(v_lctx_5119_);
v_localInstances_5120_ = lean_ctor_get(v_a_5112_, 3);
lean_inc_ref(v_localInstances_5120_);
v_defEqCtx_x3f_5121_ = lean_ctor_get(v_a_5112_, 4);
lean_inc(v_defEqCtx_x3f_5121_);
v_synthPendingDepth_5122_ = lean_ctor_get(v_a_5112_, 5);
lean_inc(v_synthPendingDepth_5122_);
v_canUnfold_x3f_5123_ = lean_ctor_get(v_a_5112_, 6);
lean_inc(v_canUnfold_x3f_5123_);
v_univApprox_5124_ = lean_ctor_get_uint8(v_a_5112_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5125_ = lean_ctor_get_uint8(v_a_5112_, sizeof(void*)*7 + 2);
v_cacheInferType_5126_ = lean_ctor_get_uint8(v_a_5112_, sizeof(void*)*7 + 3);
v___x_5127_ = l_Lean_Meta_Context_config(v_a_5112_);
v_isSharedCheck_5170_ = !lean_is_exclusive(v_a_5112_);
if (v_isSharedCheck_5170_ == 0)
{
lean_object* v_unused_5171_; lean_object* v_unused_5172_; lean_object* v_unused_5173_; lean_object* v_unused_5174_; lean_object* v_unused_5175_; lean_object* v_unused_5176_; lean_object* v_unused_5177_; 
v_unused_5171_ = lean_ctor_get(v_a_5112_, 6);
lean_dec(v_unused_5171_);
v_unused_5172_ = lean_ctor_get(v_a_5112_, 5);
lean_dec(v_unused_5172_);
v_unused_5173_ = lean_ctor_get(v_a_5112_, 4);
lean_dec(v_unused_5173_);
v_unused_5174_ = lean_ctor_get(v_a_5112_, 3);
lean_dec(v_unused_5174_);
v_unused_5175_ = lean_ctor_get(v_a_5112_, 2);
lean_dec(v_unused_5175_);
v_unused_5176_ = lean_ctor_get(v_a_5112_, 1);
lean_dec(v_unused_5176_);
v_unused_5177_ = lean_ctor_get(v_a_5112_, 0);
lean_dec(v_unused_5177_);
v___x_5129_ = v_a_5112_;
v_isShared_5130_ = v_isSharedCheck_5170_;
goto v_resetjp_5128_;
}
else
{
lean_dec(v_a_5112_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5170_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5131_; uint64_t v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5135_; 
v___x_5131_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5127_);
v___x_5132_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5131_);
v___x_5133_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5133_, 0, v___x_5131_);
lean_ctor_set_uint64(v___x_5133_, sizeof(void*)*1, v___x_5132_);
lean_inc(v_canUnfold_x3f_5123_);
lean_inc(v_synthPendingDepth_5122_);
lean_inc(v_defEqCtx_x3f_5121_);
lean_inc_ref(v_localInstances_5120_);
lean_inc_ref(v_lctx_5119_);
lean_inc(v_zetaDeltaSet_5118_);
if (v_isShared_5130_ == 0)
{
lean_ctor_set(v___x_5129_, 0, v___x_5133_);
v___x_5135_ = v___x_5129_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5133_);
lean_ctor_set(v_reuseFailAlloc_5169_, 1, v_zetaDeltaSet_5118_);
lean_ctor_set(v_reuseFailAlloc_5169_, 2, v_lctx_5119_);
lean_ctor_set(v_reuseFailAlloc_5169_, 3, v_localInstances_5120_);
lean_ctor_set(v_reuseFailAlloc_5169_, 4, v_defEqCtx_x3f_5121_);
lean_ctor_set(v_reuseFailAlloc_5169_, 5, v_synthPendingDepth_5122_);
lean_ctor_set(v_reuseFailAlloc_5169_, 6, v_canUnfold_x3f_5123_);
lean_ctor_set_uint8(v_reuseFailAlloc_5169_, sizeof(void*)*7, v_trackZetaDelta_5117_);
lean_ctor_set_uint8(v_reuseFailAlloc_5169_, sizeof(void*)*7 + 1, v_univApprox_5124_);
lean_ctor_set_uint8(v_reuseFailAlloc_5169_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5125_);
lean_ctor_set_uint8(v_reuseFailAlloc_5169_, sizeof(void*)*7 + 3, v_cacheInferType_5126_);
v___x_5135_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; uint64_t v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; 
v___x_5136_ = l_Lean_Meta_Context_config(v___x_5135_);
lean_dec_ref(v___x_5135_);
v___x_5137_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5136_);
v___x_5138_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5137_);
v___x_5139_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5139_, 0, v___x_5137_);
lean_ctor_set_uint64(v___x_5139_, sizeof(void*)*1, v___x_5138_);
v___x_5140_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5140_, 0, v___x_5139_);
lean_ctor_set(v___x_5140_, 1, v_zetaDeltaSet_5118_);
lean_ctor_set(v___x_5140_, 2, v_lctx_5119_);
lean_ctor_set(v___x_5140_, 3, v_localInstances_5120_);
lean_ctor_set(v___x_5140_, 4, v_defEqCtx_x3f_5121_);
lean_ctor_set(v___x_5140_, 5, v_synthPendingDepth_5122_);
lean_ctor_set(v___x_5140_, 6, v_canUnfold_x3f_5123_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*7, v_trackZetaDelta_5117_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*7 + 1, v_univApprox_5124_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5125_);
lean_ctor_set_uint8(v___x_5140_, sizeof(void*)*7 + 3, v_cacheInferType_5126_);
lean_inc(v_matchDeclName_5111_);
v___x_5141_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5111_, v___x_5140_, v_a_5113_, v_a_5114_, v_a_5115_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v_a_5142_; lean_object* v___x_5143_; lean_object* v_a_5144_; 
v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_a_5142_);
lean_dec_ref_known(v___x_5141_, 1);
lean_inc(v_matchDeclName_5111_);
v___x_5143_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5111_, v_a_5115_);
v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
lean_inc(v_a_5144_);
lean_dec_ref(v___x_5143_);
if (lean_obj_tag(v_a_5144_) == 1)
{
lean_object* v_val_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___f_5151_; lean_object* v___x_5152_; uint8_t v___x_5153_; lean_object* v___x_5154_; 
v_val_5145_ = lean_ctor_get(v_a_5144_, 0);
lean_inc(v_val_5145_);
lean_dec_ref_known(v_a_5144_, 1);
v___x_5146_ = l_Lean_instInhabitedExpr;
v___x_5147_ = l_Lean_ConstantInfo_levelParams(v_a_5142_);
v___x_5148_ = lean_box(0);
lean_inc(v___x_5147_);
v___x_5149_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_5147_, v___x_5148_);
v___x_5150_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5145_);
lean_inc(v_a_5142_);
v___f_5151_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5151_, 0, v_val_5145_);
lean_closure_set(v___f_5151_, 1, v___x_5146_);
lean_closure_set(v___f_5151_, 2, v_matchDeclName_5111_);
lean_closure_set(v___f_5151_, 3, v___x_5150_);
lean_closure_set(v___f_5151_, 4, v_a_5142_);
lean_closure_set(v___f_5151_, 5, v___x_5149_);
lean_closure_set(v___f_5151_, 6, v___x_5147_);
v___x_5152_ = l_Lean_ConstantInfo_type(v_a_5142_);
lean_dec(v_a_5142_);
v___x_5153_ = 0;
v___x_5154_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5152_, v___f_5151_, v___x_5153_, v___x_5153_, v___x_5140_, v_a_5113_, v_a_5114_, v_a_5115_);
lean_dec_ref_known(v___x_5140_, 7);
return v___x_5154_;
}
else
{
lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; 
lean_dec(v_a_5144_);
lean_dec(v_a_5142_);
v___x_5155_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5156_ = l_Lean_MessageData_ofName(v_matchDeclName_5111_);
v___x_5157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5157_, 0, v___x_5155_);
lean_ctor_set(v___x_5157_, 1, v___x_5156_);
v___x_5158_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5157_);
lean_ctor_set(v___x_5159_, 1, v___x_5158_);
v___x_5160_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5159_, v___x_5140_, v_a_5113_, v_a_5114_, v_a_5115_);
lean_dec_ref_known(v___x_5140_, 7);
return v___x_5160_;
}
}
else
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5168_; 
lean_dec_ref_known(v___x_5140_, 7);
lean_dec(v_matchDeclName_5111_);
v_a_5161_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5163_ = v___x_5141_;
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5141_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5161_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_){
_start:
{
lean_object* v_res_5184_; 
v_res_5184_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5178_, v_a_5179_, v_a_5180_, v_a_5181_, v_a_5182_);
lean_dec(v_a_5182_);
lean_dec_ref(v_a_5181_);
lean_dec(v_a_5180_);
return v_res_5184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_inst_5185_, lean_object* v_R_5186_, lean_object* v_a_5187_, lean_object* v_b_5188_, lean_object* v_c_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
lean_object* v___x_5195_; 
v___x_5195_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_5187_, v_b_5188_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_);
return v___x_5195_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_inst_5196_, lean_object* v_R_5197_, lean_object* v_a_5198_, lean_object* v_b_5199_, lean_object* v_c_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_inst_5196_, v_R_5197_, v_a_5198_, v_b_5199_, v_c_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5207_, lean_object* v_val_5208_, lean_object* v_matchDeclName_5209_, lean_object* v___x_5210_, lean_object* v___x_5211_, lean_object* v_a_5212_, lean_object* v___x_5213_, lean_object* v___x_5214_, lean_object* v___x_5215_, lean_object* v___x_5216_, lean_object* v___x_5217_, lean_object* v___x_5218_, lean_object* v_inst_5219_, lean_object* v_R_5220_, lean_object* v_a_5221_, lean_object* v_b_5222_, lean_object* v_c_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
lean_object* v___x_5229_; 
v___x_5229_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5207_, v_val_5208_, v_matchDeclName_5209_, v___x_5210_, v___x_5211_, v_a_5212_, v___x_5213_, v___x_5214_, v___x_5215_, v___x_5216_, v___x_5217_, v___x_5218_, v_a_5221_, v_b_5222_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_);
return v___x_5229_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5230_ = _args[0];
lean_object* v_val_5231_ = _args[1];
lean_object* v_matchDeclName_5232_ = _args[2];
lean_object* v___x_5233_ = _args[3];
lean_object* v___x_5234_ = _args[4];
lean_object* v_a_5235_ = _args[5];
lean_object* v___x_5236_ = _args[6];
lean_object* v___x_5237_ = _args[7];
lean_object* v___x_5238_ = _args[8];
lean_object* v___x_5239_ = _args[9];
lean_object* v___x_5240_ = _args[10];
lean_object* v___x_5241_ = _args[11];
lean_object* v_inst_5242_ = _args[12];
lean_object* v_R_5243_ = _args[13];
lean_object* v_a_5244_ = _args[14];
lean_object* v_b_5245_ = _args[15];
lean_object* v_c_5246_ = _args[16];
lean_object* v___y_5247_ = _args[17];
lean_object* v___y_5248_ = _args[18];
lean_object* v___y_5249_ = _args[19];
lean_object* v___y_5250_ = _args[20];
lean_object* v___y_5251_ = _args[21];
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5230_, v_val_5231_, v_matchDeclName_5232_, v___x_5233_, v___x_5234_, v_a_5235_, v___x_5236_, v___x_5237_, v___x_5238_, v___x_5239_, v___x_5240_, v___x_5241_, v_inst_5242_, v_R_5243_, v_a_5244_, v_b_5245_, v_c_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v_upperBound_5230_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5253_, lean_object* v_matchDeclName_5254_, lean_object* v_a_5255_, lean_object* v_b_5256_){
_start:
{
uint8_t v___x_5258_; 
v___x_5258_ = lean_nat_dec_lt(v_a_5255_, v_upperBound_5253_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; 
lean_dec(v_a_5255_);
lean_dec(v_matchDeclName_5254_);
v___x_5259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5259_, 0, v_b_5256_);
return v___x_5259_;
}
else
{
lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; 
v___x_5260_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5254_);
v___x_5261_ = l_Lean_Name_str___override(v_matchDeclName_5254_, v___x_5260_);
v___x_5262_ = lean_unsigned_to_nat(1u);
v___x_5263_ = lean_nat_add(v_a_5255_, v___x_5262_);
lean_dec(v_a_5255_);
lean_inc(v___x_5263_);
v___x_5264_ = lean_name_append_index_after(v___x_5261_, v___x_5263_);
v___x_5265_ = lean_array_push(v_b_5256_, v___x_5264_);
v_a_5255_ = v___x_5263_;
v_b_5256_ = v___x_5265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5267_, lean_object* v_matchDeclName_5268_, lean_object* v_a_5269_, lean_object* v_b_5270_, lean_object* v___y_5271_){
_start:
{
lean_object* v_res_5272_; 
v_res_5272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5267_, v_matchDeclName_5268_, v_a_5269_, v_b_5270_);
lean_dec(v_upperBound_5267_);
return v_res_5272_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_){
_start:
{
lean_object* v___x_5279_; lean_object* v_firstEqnName_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v___x_5279_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5273_, 3);
v_firstEqnName_5280_ = l_Lean_Name_str___override(v_matchDeclName_5273_, v___x_5279_);
v___x_5281_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5281_, 0, v_matchDeclName_5273_);
v___x_5282_ = l_Lean_Meta_realizeConst(v_matchDeclName_5273_, v_firstEqnName_5280_, v___x_5281_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_object* v___x_5283_; lean_object* v_a_5284_; 
lean_dec_ref_known(v___x_5282_, 1);
lean_inc(v_matchDeclName_5273_);
v___x_5283_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5273_, v_a_5277_);
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
lean_inc(v_a_5284_);
lean_dec_ref(v___x_5283_);
if (lean_obj_tag(v_a_5284_) == 1)
{
lean_object* v_val_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
lean_dec(v_a_5277_);
lean_dec_ref(v_a_5276_);
lean_dec(v_a_5275_);
lean_dec_ref(v_a_5274_);
v_val_5285_ = lean_ctor_get(v_a_5284_, 0);
lean_inc(v_val_5285_);
lean_dec_ref_known(v_a_5284_, 1);
v___x_5286_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5285_);
lean_dec(v_val_5285_);
v___x_5287_ = lean_unsigned_to_nat(0u);
v___x_5288_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5286_, v_matchDeclName_5273_, v___x_5287_, v___x_5288_);
lean_dec(v___x_5286_);
return v___x_5289_;
}
else
{
lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; 
lean_dec(v_a_5284_);
v___x_5290_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5291_ = l_Lean_MessageData_ofName(v_matchDeclName_5273_);
v___x_5292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5290_);
lean_ctor_set(v___x_5292_, 1, v___x_5291_);
v___x_5293_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5292_);
lean_ctor_set(v___x_5294_, 1, v___x_5293_);
v___x_5295_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5294_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_);
lean_dec(v_a_5277_);
lean_dec_ref(v_a_5276_);
lean_dec(v_a_5275_);
lean_dec_ref(v_a_5274_);
return v___x_5295_;
}
}
else
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5303_; 
lean_dec(v_a_5277_);
lean_dec_ref(v_a_5276_);
lean_dec(v_a_5275_);
lean_dec_ref(v_a_5274_);
lean_dec(v_matchDeclName_5273_);
v_a_5296_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5298_ = v___x_5282_;
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5282_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5301_; 
if (v_isShared_5299_ == 0)
{
v___x_5301_ = v___x_5298_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = lean_get_congr_match_equations_for(v_matchDeclName_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5311_, lean_object* v_matchDeclName_5312_, lean_object* v_inst_5313_, lean_object* v_R_5314_, lean_object* v_a_5315_, lean_object* v_b_5316_, lean_object* v_c_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v___x_5323_; 
v___x_5323_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5311_, v_matchDeclName_5312_, v_a_5315_, v_b_5316_);
return v___x_5323_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5324_, lean_object* v_matchDeclName_5325_, lean_object* v_inst_5326_, lean_object* v_R_5327_, lean_object* v_a_5328_, lean_object* v_b_5329_, lean_object* v_c_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5324_, v_matchDeclName_5325_, v_inst_5326_, v_R_5327_, v_a_5328_, v_b_5329_, v_c_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
lean_dec(v___y_5334_);
lean_dec_ref(v___y_5333_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
lean_dec(v_upperBound_5324_);
return v_res_5336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; 
v___x_5387_ = lean_unsigned_to_nat(3248161880u);
v___x_5388_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5389_ = l_Lean_Name_num___override(v___x_5388_, v___x_5387_);
return v___x_5389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5391_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5392_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5393_ = l_Lean_Name_str___override(v___x_5392_, v___x_5391_);
return v___x_5393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5395_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5396_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5397_ = l_Lean_Name_str___override(v___x_5396_, v___x_5395_);
return v___x_5397_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5398_ = lean_unsigned_to_nat(2u);
v___x_5399_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5400_ = l_Lean_Name_num___override(v___x_5399_, v___x_5398_);
return v___x_5400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5402_; uint8_t v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
v___x_5402_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5403_ = 0;
v___x_5404_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5405_ = l_Lean_registerTraceClass(v___x_5402_, v___x_5403_, v___x_5404_);
return v___x_5405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5406_){
_start:
{
lean_object* v_res_5407_; 
v_res_5407_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5408_, lean_object* v_n_5409_){
_start:
{
if (lean_obj_tag(v_n_5409_) == 1)
{
lean_object* v_pre_5410_; lean_object* v_str_5411_; uint8_t v___y_5413_; uint8_t v___x_5419_; 
v_pre_5410_ = lean_ctor_get(v_n_5409_, 0);
lean_inc(v_pre_5410_);
v_str_5411_ = lean_ctor_get(v_n_5409_, 1);
lean_inc_ref_n(v_str_5411_, 2);
lean_dec_ref_known(v_n_5409_, 2);
v___x_5419_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5411_);
if (v___x_5419_ == 0)
{
lean_object* v___x_5420_; uint8_t v___x_5421_; 
v___x_5420_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5421_ = lean_string_dec_eq(v_str_5411_, v___x_5420_);
lean_dec_ref(v_str_5411_);
v___y_5413_ = v___x_5421_;
goto v___jp_5412_;
}
else
{
lean_dec_ref(v_str_5411_);
v___y_5413_ = v___x_5419_;
goto v___jp_5412_;
}
v___jp_5412_:
{
if (v___y_5413_ == 0)
{
lean_object* v___x_5414_; 
lean_dec(v_pre_5410_);
lean_dec_ref(v_env_5408_);
v___x_5414_ = lean_box(0);
return v___x_5414_;
}
else
{
lean_object* v___x_5415_; 
v___x_5415_ = l_Lean_privateToUserName_x3f(v_pre_5410_);
if (lean_obj_tag(v___x_5415_) == 0)
{
lean_dec_ref(v_env_5408_);
return v___x_5415_;
}
else
{
lean_object* v_val_5416_; uint8_t v___x_5417_; 
v_val_5416_ = lean_ctor_get(v___x_5415_, 0);
lean_inc(v_val_5416_);
v___x_5417_ = l_Lean_Meta_isMatcherCore(v_env_5408_, v_val_5416_);
if (v___x_5417_ == 0)
{
lean_object* v___x_5418_; 
lean_dec_ref_known(v___x_5415_, 1);
v___x_5418_ = lean_box(0);
return v___x_5418_;
}
else
{
return v___x_5415_;
}
}
}
}
}
else
{
lean_object* v___x_5422_; 
lean_dec(v_n_5409_);
lean_dec_ref(v_env_5408_);
v___x_5422_ = lean_box(0);
return v___x_5422_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5423_, lean_object* v_x2_5424_){
_start:
{
lean_object* v___x_5425_; 
v___x_5425_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5423_, v_x2_5424_);
if (lean_obj_tag(v___x_5425_) == 0)
{
uint8_t v___x_5426_; 
v___x_5426_ = 0;
return v___x_5426_;
}
else
{
uint8_t v___x_5427_; 
lean_dec_ref_known(v___x_5425_, 1);
v___x_5427_ = 1;
return v___x_5427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5428_, lean_object* v_x2_5429_){
_start:
{
uint8_t v_res_5430_; lean_object* v_r_5431_; 
v_res_5430_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5428_, v_x2_5429_);
v_r_5431_ = lean_box(v_res_5430_);
return v_r_5431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5434_; lean_object* v___x_5435_; 
v___f_5434_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5435_ = l_Lean_registerReservedNamePredicate(v___f_5434_);
return v___x_5435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5437_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5444_; uint64_t v___x_5445_; 
v___x_5444_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5445_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5444_);
return v___x_5445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5446_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5447_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5448_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5448_, 0, v___x_5447_);
lean_ctor_set_uint64(v___x_5448_, sizeof(void*)*1, v___x_5446_);
return v___x_5448_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5451_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5452_ = lean_unsigned_to_nat(0u);
v___x_5453_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5453_, 0, v___x_5452_);
lean_ctor_set(v___x_5453_, 1, v___x_5452_);
lean_ctor_set(v___x_5453_, 2, v___x_5452_);
lean_ctor_set(v___x_5453_, 3, v___x_5452_);
lean_ctor_set(v___x_5453_, 4, v___x_5451_);
lean_ctor_set(v___x_5453_, 5, v___x_5451_);
lean_ctor_set(v___x_5453_, 6, v___x_5451_);
lean_ctor_set(v___x_5453_, 7, v___x_5451_);
lean_ctor_set(v___x_5453_, 8, v___x_5451_);
lean_ctor_set(v___x_5453_, 9, v___x_5451_);
return v___x_5453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5454_; lean_object* v___x_5455_; 
v___x_5454_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5455_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5455_, 0, v___x_5454_);
lean_ctor_set(v___x_5455_, 1, v___x_5454_);
lean_ctor_set(v___x_5455_, 2, v___x_5454_);
lean_ctor_set(v___x_5455_, 3, v___x_5454_);
lean_ctor_set(v___x_5455_, 4, v___x_5454_);
lean_ctor_set(v___x_5455_, 5, v___x_5454_);
return v___x_5455_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5456_; lean_object* v___x_5457_; 
v___x_5456_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5457_, 0, v___x_5456_);
lean_ctor_set(v___x_5457_, 1, v___x_5456_);
lean_ctor_set(v___x_5457_, 2, v___x_5456_);
lean_ctor_set(v___x_5457_, 3, v___x_5456_);
lean_ctor_set(v___x_5457_, 4, v___x_5456_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5458_, lean_object* v_name_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v___x_5463_; lean_object* v_env_5464_; lean_object* v___x_5465_; 
v___x_5463_ = lean_st_ref_get(v___y_5461_);
v_env_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc_ref(v_env_5464_);
lean_dec(v___x_5463_);
v___x_5465_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5464_, v_name_5459_);
if (lean_obj_tag(v___x_5465_) == 1)
{
lean_object* v_val_5466_; uint8_t v___x_5467_; uint8_t v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; 
v_val_5466_ = lean_ctor_get(v___x_5465_, 0);
lean_inc(v_val_5466_);
lean_dec_ref_known(v___x_5465_, 1);
v___x_5467_ = 0;
v___x_5468_ = 1;
v___x_5469_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5470_ = lean_unsigned_to_nat(0u);
v___x_5471_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5472_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5473_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5474_ = lean_box(0);
lean_inc(v___x_5458_);
v___x_5475_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5475_, 0, v___x_5469_);
lean_ctor_set(v___x_5475_, 1, v___x_5458_);
lean_ctor_set(v___x_5475_, 2, v___x_5472_);
lean_ctor_set(v___x_5475_, 3, v___x_5473_);
lean_ctor_set(v___x_5475_, 4, v___x_5474_);
lean_ctor_set(v___x_5475_, 5, v___x_5470_);
lean_ctor_set(v___x_5475_, 6, v___x_5474_);
lean_ctor_set_uint8(v___x_5475_, sizeof(void*)*7, v___x_5467_);
lean_ctor_set_uint8(v___x_5475_, sizeof(void*)*7 + 1, v___x_5467_);
lean_ctor_set_uint8(v___x_5475_, sizeof(void*)*7 + 2, v___x_5467_);
lean_ctor_set_uint8(v___x_5475_, sizeof(void*)*7 + 3, v___x_5468_);
v___x_5476_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5477_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5478_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5479_, 0, v___x_5476_);
lean_ctor_set(v___x_5479_, 1, v___x_5477_);
lean_ctor_set(v___x_5479_, 2, v___x_5458_);
lean_ctor_set(v___x_5479_, 3, v___x_5471_);
lean_ctor_set(v___x_5479_, 4, v___x_5478_);
v___x_5480_ = lean_st_mk_ref(v___x_5479_);
lean_inc(v___y_5461_);
lean_inc_ref(v___y_5460_);
lean_inc(v___x_5480_);
v___x_5481_ = lean_get_match_equations_for(v_val_5466_, v___x_5475_, v___x_5480_, v___y_5460_, v___y_5461_);
if (lean_obj_tag(v___x_5481_) == 0)
{
lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5490_; 
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5481_);
if (v_isSharedCheck_5490_ == 0)
{
lean_object* v_unused_5491_; 
v_unused_5491_ = lean_ctor_get(v___x_5481_, 0);
lean_dec(v_unused_5491_);
v___x_5483_ = v___x_5481_;
v_isShared_5484_ = v_isSharedCheck_5490_;
goto v_resetjp_5482_;
}
else
{
lean_dec(v___x_5481_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5490_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5488_; 
v___x_5485_ = lean_st_ref_get(v___x_5480_);
lean_dec(v___x_5480_);
lean_dec(v___x_5485_);
v___x_5486_ = lean_box(v___x_5468_);
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 0, v___x_5486_);
v___x_5488_ = v___x_5483_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v___x_5486_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
else
{
lean_dec(v___x_5480_);
if (lean_obj_tag(v___x_5481_) == 0)
{
lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5499_; 
v_isSharedCheck_5499_ = !lean_is_exclusive(v___x_5481_);
if (v_isSharedCheck_5499_ == 0)
{
lean_object* v_unused_5500_; 
v_unused_5500_ = lean_ctor_get(v___x_5481_, 0);
lean_dec(v_unused_5500_);
v___x_5493_ = v___x_5481_;
v_isShared_5494_ = v_isSharedCheck_5499_;
goto v_resetjp_5492_;
}
else
{
lean_dec(v___x_5481_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5499_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5495_; lean_object* v___x_5497_; 
v___x_5495_ = lean_box(v___x_5468_);
if (v_isShared_5494_ == 0)
{
lean_ctor_set_tag(v___x_5493_, 0);
lean_ctor_set(v___x_5493_, 0, v___x_5495_);
v___x_5497_ = v___x_5493_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v___x_5495_);
v___x_5497_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
return v___x_5497_;
}
}
}
else
{
lean_object* v_a_5501_; lean_object* v___x_5503_; uint8_t v_isShared_5504_; uint8_t v_isSharedCheck_5508_; 
v_a_5501_ = lean_ctor_get(v___x_5481_, 0);
v_isSharedCheck_5508_ = !lean_is_exclusive(v___x_5481_);
if (v_isSharedCheck_5508_ == 0)
{
v___x_5503_ = v___x_5481_;
v_isShared_5504_ = v_isSharedCheck_5508_;
goto v_resetjp_5502_;
}
else
{
lean_inc(v_a_5501_);
lean_dec(v___x_5481_);
v___x_5503_ = lean_box(0);
v_isShared_5504_ = v_isSharedCheck_5508_;
goto v_resetjp_5502_;
}
v_resetjp_5502_:
{
lean_object* v___x_5506_; 
if (v_isShared_5504_ == 0)
{
v___x_5506_ = v___x_5503_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5507_; 
v_reuseFailAlloc_5507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_a_5501_);
v___x_5506_ = v_reuseFailAlloc_5507_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
return v___x_5506_;
}
}
}
}
}
else
{
uint8_t v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; 
lean_dec(v___x_5465_);
lean_dec(v___x_5458_);
v___x_5509_ = 0;
v___x_5510_ = lean_box(v___x_5509_);
v___x_5511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5511_, 0, v___x_5510_);
return v___x_5511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5512_, lean_object* v_name_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_){
_start:
{
lean_object* v_res_5517_; 
v_res_5517_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5512_, v_name_5513_, v___y_5514_, v___y_5515_);
lean_dec(v___y_5515_);
lean_dec_ref(v___y_5514_);
return v_res_5517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5521_; lean_object* v___x_5522_; 
v___f_5521_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5522_ = l_Lean_registerReservedNameAction(v___f_5521_);
return v___x_5522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5523_){
_start:
{
lean_object* v_res_5524_; 
v_res_5524_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5525_, lean_object* v_n_5526_){
_start:
{
if (lean_obj_tag(v_n_5526_) == 1)
{
lean_object* v_pre_5527_; lean_object* v_str_5528_; uint8_t v___x_5529_; 
v_pre_5527_ = lean_ctor_get(v_n_5526_, 0);
lean_inc(v_pre_5527_);
v_str_5528_ = lean_ctor_get(v_n_5526_, 1);
lean_inc_ref(v_str_5528_);
lean_dec_ref_known(v_n_5526_, 2);
v___x_5529_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5528_);
if (v___x_5529_ == 0)
{
lean_object* v___x_5530_; 
lean_dec(v_pre_5527_);
lean_dec_ref(v_env_5525_);
v___x_5530_ = lean_box(0);
return v___x_5530_;
}
else
{
uint8_t v___x_5531_; 
lean_inc(v_pre_5527_);
v___x_5531_ = l_Lean_Meta_isMatcherCore(v_env_5525_, v_pre_5527_);
if (v___x_5531_ == 0)
{
lean_object* v___x_5532_; 
lean_dec(v_pre_5527_);
v___x_5532_ = lean_box(0);
return v___x_5532_;
}
else
{
lean_object* v___x_5533_; 
v___x_5533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5533_, 0, v_pre_5527_);
return v___x_5533_;
}
}
}
else
{
lean_object* v___x_5534_; 
lean_dec(v_n_5526_);
lean_dec_ref(v_env_5525_);
v___x_5534_ = lean_box(0);
return v___x_5534_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5535_, lean_object* v_x2_5536_){
_start:
{
lean_object* v___x_5537_; 
v___x_5537_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5535_, v_x2_5536_);
if (lean_obj_tag(v___x_5537_) == 0)
{
uint8_t v___x_5538_; 
v___x_5538_ = 0;
return v___x_5538_;
}
else
{
uint8_t v___x_5539_; 
lean_dec_ref_known(v___x_5537_, 1);
v___x_5539_ = 1;
return v___x_5539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5540_, lean_object* v_x2_5541_){
_start:
{
uint8_t v_res_5542_; lean_object* v_r_5543_; 
v_res_5542_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5540_, v_x2_5541_);
v_r_5543_ = lean_box(v_res_5542_);
return v_r_5543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5546_; lean_object* v___x_5547_; 
v___f_5546_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5547_ = l_Lean_registerReservedNamePredicate(v___f_5546_);
return v___x_5547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5548_){
_start:
{
lean_object* v_res_5549_; 
v_res_5549_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5550_, lean_object* v_name_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_){
_start:
{
lean_object* v___x_5555_; lean_object* v_env_5556_; lean_object* v___x_5557_; 
v___x_5555_ = lean_st_ref_get(v___y_5553_);
v_env_5556_ = lean_ctor_get(v___x_5555_, 0);
lean_inc_ref(v_env_5556_);
lean_dec(v___x_5555_);
v___x_5557_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5556_, v_name_5551_);
if (lean_obj_tag(v___x_5557_) == 1)
{
lean_object* v_val_5558_; uint8_t v___x_5559_; uint8_t v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; 
v_val_5558_ = lean_ctor_get(v___x_5557_, 0);
lean_inc(v_val_5558_);
lean_dec_ref_known(v___x_5557_, 1);
v___x_5559_ = 0;
v___x_5560_ = 1;
v___x_5561_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5562_ = lean_unsigned_to_nat(32u);
v___x_5563_ = lean_mk_empty_array_with_capacity(v___x_5562_);
lean_dec_ref(v___x_5563_);
v___x_5564_ = lean_unsigned_to_nat(0u);
v___x_5565_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5566_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5567_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5568_ = lean_box(0);
lean_inc(v___x_5550_);
v___x_5569_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5569_, 0, v___x_5561_);
lean_ctor_set(v___x_5569_, 1, v___x_5550_);
lean_ctor_set(v___x_5569_, 2, v___x_5566_);
lean_ctor_set(v___x_5569_, 3, v___x_5567_);
lean_ctor_set(v___x_5569_, 4, v___x_5568_);
lean_ctor_set(v___x_5569_, 5, v___x_5564_);
lean_ctor_set(v___x_5569_, 6, v___x_5568_);
lean_ctor_set_uint8(v___x_5569_, sizeof(void*)*7, v___x_5559_);
lean_ctor_set_uint8(v___x_5569_, sizeof(void*)*7 + 1, v___x_5559_);
lean_ctor_set_uint8(v___x_5569_, sizeof(void*)*7 + 2, v___x_5559_);
lean_ctor_set_uint8(v___x_5569_, sizeof(void*)*7 + 3, v___x_5560_);
v___x_5570_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5571_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5572_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5573_, 0, v___x_5570_);
lean_ctor_set(v___x_5573_, 1, v___x_5571_);
lean_ctor_set(v___x_5573_, 2, v___x_5550_);
lean_ctor_set(v___x_5573_, 3, v___x_5565_);
lean_ctor_set(v___x_5573_, 4, v___x_5572_);
v___x_5574_ = lean_st_mk_ref(v___x_5573_);
lean_inc(v___y_5553_);
lean_inc_ref(v___y_5552_);
lean_inc(v___x_5574_);
v___x_5575_ = lean_get_congr_match_equations_for(v_val_5558_, v___x_5569_, v___x_5574_, v___y_5552_, v___y_5553_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5584_; 
v_isSharedCheck_5584_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5584_ == 0)
{
lean_object* v_unused_5585_; 
v_unused_5585_ = lean_ctor_get(v___x_5575_, 0);
lean_dec(v_unused_5585_);
v___x_5577_ = v___x_5575_;
v_isShared_5578_ = v_isSharedCheck_5584_;
goto v_resetjp_5576_;
}
else
{
lean_dec(v___x_5575_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5584_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5582_; 
v___x_5579_ = lean_st_ref_get(v___x_5574_);
lean_dec(v___x_5574_);
lean_dec(v___x_5579_);
v___x_5580_ = lean_box(v___x_5560_);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 0, v___x_5580_);
v___x_5582_ = v___x_5577_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v___x_5580_);
v___x_5582_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
return v___x_5582_;
}
}
}
else
{
lean_dec(v___x_5574_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5593_; 
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5593_ == 0)
{
lean_object* v_unused_5594_; 
v_unused_5594_ = lean_ctor_get(v___x_5575_, 0);
lean_dec(v_unused_5594_);
v___x_5587_ = v___x_5575_;
v_isShared_5588_ = v_isSharedCheck_5593_;
goto v_resetjp_5586_;
}
else
{
lean_dec(v___x_5575_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5593_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5589_; lean_object* v___x_5591_; 
v___x_5589_ = lean_box(v___x_5560_);
if (v_isShared_5588_ == 0)
{
lean_ctor_set_tag(v___x_5587_, 0);
lean_ctor_set(v___x_5587_, 0, v___x_5589_);
v___x_5591_ = v___x_5587_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5589_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
return v___x_5591_;
}
}
}
else
{
lean_object* v_a_5595_; lean_object* v___x_5597_; uint8_t v_isShared_5598_; uint8_t v_isSharedCheck_5602_; 
v_a_5595_ = lean_ctor_get(v___x_5575_, 0);
v_isSharedCheck_5602_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5602_ == 0)
{
v___x_5597_ = v___x_5575_;
v_isShared_5598_ = v_isSharedCheck_5602_;
goto v_resetjp_5596_;
}
else
{
lean_inc(v_a_5595_);
lean_dec(v___x_5575_);
v___x_5597_ = lean_box(0);
v_isShared_5598_ = v_isSharedCheck_5602_;
goto v_resetjp_5596_;
}
v_resetjp_5596_:
{
lean_object* v___x_5600_; 
if (v_isShared_5598_ == 0)
{
v___x_5600_ = v___x_5597_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5595_);
v___x_5600_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
return v___x_5600_;
}
}
}
}
}
else
{
uint8_t v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; 
lean_dec(v___x_5557_);
lean_dec(v___x_5550_);
v___x_5603_ = 0;
v___x_5604_ = lean_box(v___x_5603_);
v___x_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5604_);
return v___x_5605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5606_, lean_object* v_name_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_){
_start:
{
lean_object* v_res_5611_; 
v_res_5611_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5606_, v_name_5607_, v___y_5608_, v___y_5609_);
lean_dec(v___y_5609_);
lean_dec_ref(v___y_5608_);
return v_res_5611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5615_; lean_object* v___x_5616_; 
v___f_5615_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5616_ = l_Lean_registerReservedNameAction(v___f_5615_);
return v___x_5616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5617_){
_start:
{
lean_object* v_res_5618_; 
v_res_5618_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5618_;
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
