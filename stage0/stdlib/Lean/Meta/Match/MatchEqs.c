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
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_subst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint8_t l_Lean_Meta_Match_instBEqAltParamInfo_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
uint8_t l_Lean_Meta_Match_Overlaps_isEmpty(lean_object*);
lean_object* l_Lean_Meta_Match_isNamedPattern___boxed(lean_object*);
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
lean_object* v___x_308_; uint8_t v_fst_310_; lean_object* v_mctx_311_; lean_object* v_mctx_328_; lean_object* v___f_329_; lean_object* v___f_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___y_334_; uint8_t v___x_341_; uint8_t v___x_342_; 
v___x_308_ = lean_st_ref_get(v___y_306_);
v_mctx_328_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref_n(v_mctx_328_, 2);
lean_dec(v___x_308_);
v___f_329_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0));
v___f_330_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_330_, 0, v_fvarId_305_);
v___x_331_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2);
v___x_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_mctx_328_);
v___x_341_ = l_Lean_Expr_hasFVar(v_e_304_);
v___x_342_ = lean_bool_not(v___x_341_);
if (v___x_342_ == 0)
{
v___y_334_ = v___x_342_;
goto v___jp_333_;
}
else
{
uint8_t v___x_343_; uint8_t v___x_344_; 
v___x_343_ = l_Lean_Expr_hasMVar(v_e_304_);
v___x_344_ = lean_bool_not(v___x_343_);
v___y_334_ = v___x_344_;
goto v___jp_333_;
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
v___jp_333_:
{
if (v___y_334_ == 0)
{
lean_object* v___x_335_; lean_object* v_snd_336_; lean_object* v_fst_337_; lean_object* v_mctx_338_; uint8_t v___x_339_; 
lean_dec_ref(v_mctx_328_);
v___x_335_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_330_, v___f_329_, v_e_304_, v___x_332_);
v_snd_336_ = lean_ctor_get(v___x_335_, 1);
lean_inc(v_snd_336_);
v_fst_337_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_fst_337_);
lean_dec_ref(v___x_335_);
v_mctx_338_ = lean_ctor_get(v_snd_336_, 1);
lean_inc_ref(v_mctx_338_);
lean_dec(v_snd_336_);
v___x_339_ = lean_unbox(v_fst_337_);
lean_dec(v_fst_337_);
v_fst_310_ = v___x_339_;
v_mctx_311_ = v_mctx_338_;
goto v___jp_309_;
}
else
{
uint8_t v___x_340_; 
lean_dec_ref_known(v___x_332_, 2);
lean_dec_ref(v___f_330_);
lean_dec_ref(v_e_304_);
v___x_340_ = 0;
v_fst_310_ = v___x_340_;
v_mctx_311_ = v_mctx_328_;
goto v___jp_309_;
}
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
lean_object* v_snd_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_534_; 
v_snd_431_ = lean_ctor_get(v_b_423_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_b_423_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v_b_423_, 0);
lean_dec(v_unused_535_);
v___x_433_ = v_b_423_;
v_isShared_434_ = v_isSharedCheck_534_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_snd_431_);
lean_dec(v_b_423_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_534_;
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
lean_object* v_val_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_533_; 
v_val_445_ = lean_ctor_get(v_a_444_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v_a_444_);
if (v_isSharedCheck_533_ == 0)
{
v___x_447_ = v_a_444_;
v_isShared_448_ = v_isSharedCheck_533_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_val_445_);
lean_dec(v_a_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_533_;
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
lean_object* v_val_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_524_; 
v_val_454_ = lean_ctor_get(v_a_451_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_524_ == 0)
{
v___x_456_ = v_a_451_;
v_isShared_457_ = v_isSharedCheck_524_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_val_454_);
lean_dec(v_a_451_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_524_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_snd_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_522_; 
v_snd_458_ = lean_ctor_get(v_val_454_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_val_454_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v_val_454_, 0);
lean_dec(v_unused_523_);
v___x_460_ = v_val_454_;
v_isShared_461_ = v_isSharedCheck_522_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_snd_458_);
lean_dec(v_val_454_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_522_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v_fst_462_; lean_object* v_snd_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_521_; 
v_fst_462_ = lean_ctor_get(v_snd_458_, 0);
v_snd_463_ = lean_ctor_get(v_snd_458_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_snd_458_);
if (v_isSharedCheck_521_ == 0)
{
v___x_465_ = v_snd_458_;
v_isShared_466_ = v_isSharedCheck_521_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_snd_463_);
lean_inc(v_fst_462_);
lean_dec(v_snd_458_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_521_;
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
lean_object* v_a_470_; uint8_t v___x_471_; uint8_t v___x_472_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = lean_unbox(v_a_470_);
lean_dec(v_a_470_);
v___x_472_ = lean_bool_not(v___x_471_);
if (v___x_472_ == 0)
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
lean_object* v___x_473_; 
lean_inc(v_mvarId_419_);
v___x_473_ = l_Lean_Meta_subst_x3f(v_mvarId_419_, v___x_468_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
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
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_503_; 
lean_del_object(v___x_433_);
lean_dec(v_mvarId_419_);
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
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_452_);
lean_ctor_set(v___x_465_, 0, v___x_486_);
v___x_488_ = v___x_465_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_452_);
v___x_488_ = v_reuseFailAlloc_501_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 0);
lean_ctor_set(v___x_447_, 0, v___x_488_);
v___x_490_ = v___x_447_;
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
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_490_);
v___x_492_ = v___x_456_;
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
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v_snd_431_);
lean_ctor_set(v___x_460_, 0, v___x_492_);
v___x_494_ = v___x_460_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_snd_431_);
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
lean_del_object(v___x_465_);
lean_del_object(v___x_460_);
lean_del_object(v___x_456_);
lean_del_object(v___x_447_);
lean_del_object(v___x_433_);
lean_dec(v_snd_431_);
lean_dec(v_mvarId_419_);
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
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v___x_468_);
lean_del_object(v___x_465_);
lean_del_object(v___x_460_);
lean_del_object(v___x_456_);
lean_del_object(v___x_447_);
lean_del_object(v___x_433_);
lean_dec(v_snd_431_);
lean_dec(v_mvarId_419_);
v_a_513_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_469_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_469_);
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
lean_dec(v_a_451_);
lean_del_object(v___x_447_);
lean_dec(v_snd_431_);
v_a_437_ = v___x_453_;
goto v___jp_436_;
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_del_object(v___x_447_);
lean_del_object(v___x_433_);
lean_dec(v_snd_431_);
lean_dec(v_mvarId_419_);
v_a_525_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_450_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_450_);
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
lean_object* v_snd_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_664_; 
v_snd_561_ = lean_ctor_get(v_b_553_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_b_553_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v_b_553_, 0);
lean_dec(v_unused_665_);
v___x_563_ = v_b_553_;
v_isShared_564_ = v_isSharedCheck_664_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_snd_561_);
lean_dec(v_b_553_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_664_;
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
lean_object* v_val_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_663_; 
v_val_575_ = lean_ctor_get(v_a_574_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v_a_574_);
if (v_isSharedCheck_663_ == 0)
{
v___x_577_ = v_a_574_;
v_isShared_578_ = v_isSharedCheck_663_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_val_575_);
lean_dec(v_a_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_663_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = l_Lean_LocalDecl_type(v_val_575_);
lean_dec(v_val_575_);
v___x_580_ = l_Lean_Meta_matchEq_x3f(v___x_579_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = lean_box(0);
v___x_583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
if (lean_obj_tag(v_a_581_) == 1)
{
lean_object* v_val_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_654_; 
v_val_584_ = lean_ctor_get(v_a_581_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_581_);
if (v_isSharedCheck_654_ == 0)
{
v___x_586_ = v_a_581_;
v_isShared_587_ = v_isSharedCheck_654_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_val_584_);
lean_dec(v_a_581_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_654_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v_snd_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_652_; 
v_snd_588_ = lean_ctor_get(v_val_584_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_val_584_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v_val_584_, 0);
lean_dec(v_unused_653_);
v___x_590_ = v_val_584_;
v_isShared_591_ = v_isSharedCheck_652_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snd_588_);
lean_dec(v_val_584_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_652_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_651_; 
v_fst_592_ = lean_ctor_get(v_snd_588_, 0);
v_snd_593_ = lean_ctor_get(v_snd_588_, 1);
v_isSharedCheck_651_ = !lean_is_exclusive(v_snd_588_);
if (v_isSharedCheck_651_ == 0)
{
v___x_595_ = v_snd_588_;
v_isShared_596_ = v_isSharedCheck_651_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_snd_593_);
lean_inc(v_fst_592_);
lean_dec(v_snd_588_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_651_;
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
v_a_567_ = v___x_583_;
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
lean_object* v_a_600_; uint8_t v___x_601_; uint8_t v___x_602_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = lean_unbox(v_a_600_);
lean_dec(v_a_600_);
v___x_602_ = lean_bool_not(v___x_601_);
if (v___x_602_ == 0)
{
lean_dec(v___x_598_);
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_del_object(v___x_586_);
lean_del_object(v___x_577_);
lean_dec(v_snd_561_);
v_a_567_ = v___x_583_;
goto v___jp_566_;
}
else
{
lean_object* v___x_603_; 
lean_inc(v_mvarId_549_);
v___x_603_ = l_Lean_Meta_subst_x3f(v_mvarId_549_, v___x_598_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_634_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_634_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_634_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_634_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
if (lean_obj_tag(v_a_604_) == 0)
{
lean_del_object(v___x_606_);
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_del_object(v___x_586_);
lean_del_object(v___x_577_);
lean_dec(v_snd_561_);
v_a_567_ = v___x_583_;
goto v___jp_566_;
}
else
{
lean_object* v_val_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_633_; 
lean_del_object(v___x_563_);
lean_dec(v_mvarId_549_);
v_val_608_ = lean_ctor_get(v_a_604_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_633_ == 0)
{
v___x_610_ = v_a_604_;
v_isShared_611_ = v_isSharedCheck_633_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_val_608_);
lean_dec(v_a_604_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_633_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_mk_empty_array_with_capacity(v___x_612_);
v___x_614_ = lean_array_push(v___x_613_, v_val_608_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_614_);
v___x_616_ = v___x_610_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_632_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___x_582_);
lean_ctor_set(v___x_595_, 0, v___x_616_);
v___x_618_ = v___x_595_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_616_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_582_);
v___x_618_ = v_reuseFailAlloc_631_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_620_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 0);
lean_ctor_set(v___x_577_, 0, v___x_618_);
v___x_620_ = v___x_577_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_630_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_622_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_620_);
v___x_622_ = v___x_586_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_629_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_snd_561_);
lean_ctor_set(v___x_590_, 0, v___x_622_);
v___x_624_ = v___x_590_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_snd_561_);
v___x_624_ = v_reuseFailAlloc_628_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_624_);
v___x_626_ = v___x_606_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
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
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_del_object(v___x_586_);
lean_del_object(v___x_577_);
lean_del_object(v___x_563_);
lean_dec(v_snd_561_);
lean_dec(v_mvarId_549_);
v_a_635_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_603_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_603_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v___x_598_);
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
lean_del_object(v___x_586_);
lean_del_object(v___x_577_);
lean_del_object(v___x_563_);
lean_dec(v_snd_561_);
lean_dec(v_mvarId_549_);
v_a_643_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_599_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_599_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
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
lean_del_object(v___x_577_);
lean_dec(v_snd_561_);
v_a_567_ = v___x_583_;
goto v___jp_566_;
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_del_object(v___x_577_);
lean_del_object(v___x_563_);
lean_dec(v_snd_561_);
lean_dec(v_mvarId_549_);
v_a_655_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_580_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_580_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4___boxed(lean_object* v_mvarId_666_, lean_object* v_as_667_, lean_object* v_sz_668_, lean_object* v_i_669_, lean_object* v_b_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
size_t v_sz_boxed_676_; size_t v_i_boxed_677_; lean_object* v_res_678_; 
v_sz_boxed_676_ = lean_unbox_usize(v_sz_668_);
lean_dec(v_sz_668_);
v_i_boxed_677_ = lean_unbox_usize(v_i_669_);
lean_dec(v_i_669_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_666_, v_as_667_, v_sz_boxed_676_, v_i_boxed_677_, v_b_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec_ref(v_as_667_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(lean_object* v_init_679_, lean_object* v_mvarId_680_, lean_object* v_n_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
if (lean_obj_tag(v_n_681_) == 0)
{
lean_object* v_cs_688_; lean_object* v___x_689_; lean_object* v___x_690_; size_t v_sz_691_; size_t v___x_692_; lean_object* v___x_693_; 
v_cs_688_ = lean_ctor_get(v_n_681_, 0);
v___x_689_ = lean_box(0);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_b_682_);
v_sz_691_ = lean_array_size(v_cs_688_);
v___x_692_ = ((size_t)0ULL);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_679_, v_mvarId_680_, v_cs_688_, v_sz_691_, v___x_692_, v___x_690_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_708_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_708_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_708_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_708_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_fst_698_; 
v_fst_698_ = lean_ctor_get(v_a_694_, 0);
if (lean_obj_tag(v_fst_698_) == 0)
{
lean_object* v_snd_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v_snd_699_ = lean_ctor_get(v_a_694_, 1);
lean_inc(v_snd_699_);
lean_dec(v_a_694_);
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v_snd_699_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_700_);
v___x_702_ = v___x_696_;
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
else
{
lean_object* v_val_704_; lean_object* v___x_706_; 
lean_inc_ref(v_fst_698_);
lean_dec(v_a_694_);
v_val_704_ = lean_ctor_get(v_fst_698_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v_fst_698_, 1);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v_val_704_);
v___x_706_ = v___x_696_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_val_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
v_a_709_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_693_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_693_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v_vs_717_; lean_object* v___x_718_; lean_object* v___x_719_; size_t v_sz_720_; size_t v___x_721_; lean_object* v___x_722_; 
v_vs_717_ = lean_ctor_get(v_n_681_, 0);
v___x_718_ = lean_box(0);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_b_682_);
v_sz_720_ = lean_array_size(v_vs_717_);
v___x_721_ = ((size_t)0ULL);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_680_, v_vs_717_, v_sz_720_, v___x_721_, v___x_719_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_737_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_737_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_737_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_737_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_fst_727_; 
v_fst_727_ = lean_ctor_get(v_a_723_, 0);
if (lean_obj_tag(v_fst_727_) == 0)
{
lean_object* v_snd_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v_snd_728_ = lean_ctor_get(v_a_723_, 1);
lean_inc(v_snd_728_);
lean_dec(v_a_723_);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v_snd_728_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_729_);
v___x_731_ = v___x_725_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_object* v_val_733_; lean_object* v___x_735_; 
lean_inc_ref(v_fst_727_);
lean_dec(v_a_723_);
v_val_733_ = lean_ctor_get(v_fst_727_, 0);
lean_inc(v_val_733_);
lean_dec_ref_known(v_fst_727_, 1);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v_val_733_);
v___x_735_ = v___x_725_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_val_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_a_738_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_722_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_722_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(lean_object* v_init_746_, lean_object* v_mvarId_747_, lean_object* v_as_748_, size_t v_sz_749_, size_t v_i_750_, lean_object* v_b_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = lean_usize_dec_lt(v_i_750_, v_sz_749_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_dec(v_mvarId_747_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v_b_751_);
return v___x_758_;
}
else
{
lean_object* v_snd_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_793_; 
v_snd_759_ = lean_ctor_get(v_b_751_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_b_751_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_b_751_, 0);
lean_dec(v_unused_794_);
v___x_761_ = v_b_751_;
v_isShared_762_ = v_isSharedCheck_793_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_snd_759_);
lean_dec(v_b_751_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_793_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_a_763_; lean_object* v___x_764_; 
v_a_763_ = lean_array_uget_borrowed(v_as_748_, v_i_750_);
lean_inc(v_snd_759_);
lean_inc(v_mvarId_747_);
v___x_764_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_746_, v_mvarId_747_, v_a_763_, v_snd_759_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_784_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_784_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_784_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_784_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
if (lean_obj_tag(v_a_765_) == 0)
{
lean_object* v___x_769_; lean_object* v___x_771_; 
lean_dec(v_mvarId_747_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v_a_765_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_769_);
v___x_771_ = v___x_761_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_snd_759_);
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
lean_object* v_a_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
lean_del_object(v___x_767_);
lean_dec(v_snd_759_);
v_a_776_ = lean_ctor_get(v_a_765_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v_a_765_, 1);
v___x_777_ = lean_box(0);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_a_776_);
lean_ctor_set(v___x_761_, 0, v___x_777_);
v___x_779_ = v___x_761_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_a_776_);
v___x_779_ = v_reuseFailAlloc_783_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
size_t v___x_780_; size_t v___x_781_; 
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_add(v_i_750_, v___x_780_);
v_i_750_ = v___x_781_;
v_b_751_ = v___x_779_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_del_object(v___x_761_);
lean_dec(v_snd_759_);
lean_dec(v_mvarId_747_);
v_a_785_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_764_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_764_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3___boxed(lean_object* v_init_795_, lean_object* v_mvarId_796_, lean_object* v_as_797_, lean_object* v_sz_798_, lean_object* v_i_799_, lean_object* v_b_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
size_t v_sz_boxed_806_; size_t v_i_boxed_807_; lean_object* v_res_808_; 
v_sz_boxed_806_ = lean_unbox_usize(v_sz_798_);
lean_dec(v_sz_798_);
v_i_boxed_807_ = lean_unbox_usize(v_i_799_);
lean_dec(v_i_799_);
v_res_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_795_, v_mvarId_796_, v_as_797_, v_sz_boxed_806_, v_i_boxed_807_, v_b_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_as_797_);
lean_dec_ref(v_init_795_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1___boxed(lean_object* v_init_809_, lean_object* v_mvarId_810_, lean_object* v_n_811_, lean_object* v_b_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_809_, v_mvarId_810_, v_n_811_, v_b_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v_n_811_);
lean_dec_ref(v_init_809_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(lean_object* v_mvarId_822_, lean_object* v_as_823_, size_t v_sz_824_, size_t v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = lean_usize_dec_lt(v_i_825_, v_sz_824_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
lean_dec(v_mvarId_822_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v_b_826_);
return v___x_833_;
}
else
{
lean_object* v_snd_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_930_; 
v_snd_834_ = lean_ctor_get(v_b_826_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v_b_826_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_b_826_, 0);
lean_dec(v_unused_931_);
v___x_836_ = v_b_826_;
v_isShared_837_ = v_isSharedCheck_930_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_snd_834_);
lean_dec(v_b_826_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_930_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v_a_840_; lean_object* v_a_847_; 
v___x_838_ = lean_box(0);
v_a_847_ = lean_array_uget_borrowed(v_as_823_, v_i_825_);
if (lean_obj_tag(v_a_847_) == 0)
{
v_a_840_ = v_snd_834_;
goto v___jp_839_;
}
else
{
lean_object* v_val_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_val_848_ = lean_ctor_get(v_a_847_, 0);
v___x_849_ = l_Lean_LocalDecl_type(v_val_848_);
v___x_850_ = l_Lean_Meta_matchEq_x3f(v___x_849_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v___x_852_ = lean_box(0);
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_851_) == 1)
{
lean_object* v_val_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_921_; 
v_val_854_ = lean_ctor_get(v_a_851_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_851_);
if (v_isSharedCheck_921_ == 0)
{
v___x_856_ = v_a_851_;
v_isShared_857_ = v_isSharedCheck_921_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_val_854_);
lean_dec(v_a_851_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_921_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_snd_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_919_; 
v_snd_858_ = lean_ctor_get(v_val_854_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v_val_854_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v_val_854_, 0);
lean_dec(v_unused_920_);
v___x_860_ = v_val_854_;
v_isShared_861_ = v_isSharedCheck_919_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_snd_858_);
lean_dec(v_val_854_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_919_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_fst_862_; lean_object* v_snd_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_918_; 
v_fst_862_ = lean_ctor_get(v_snd_858_, 0);
v_snd_863_ = lean_ctor_get(v_snd_858_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_snd_858_);
if (v_isSharedCheck_918_ == 0)
{
v___x_865_ = v_snd_858_;
v_isShared_866_ = v_isSharedCheck_918_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_snd_863_);
lean_inc(v_fst_862_);
lean_dec(v_snd_858_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_918_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint8_t v___x_867_; 
v___x_867_ = l_Lean_Expr_isFVar(v_fst_862_);
if (v___x_867_ == 0)
{
lean_del_object(v___x_865_);
lean_dec(v_snd_863_);
lean_dec(v_fst_862_);
lean_del_object(v___x_860_);
lean_del_object(v___x_856_);
lean_dec(v_snd_834_);
v_a_840_ = v___x_853_;
goto v___jp_839_;
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = l_Lean_Expr_fvarId_x21(v_fst_862_);
lean_dec(v_fst_862_);
lean_inc(v___x_868_);
v___x_869_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_863_, v___x_868_, v___y_828_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; uint8_t v___x_871_; uint8_t v___x_872_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_869_, 1);
v___x_871_ = lean_unbox(v_a_870_);
lean_dec(v_a_870_);
v___x_872_ = lean_bool_not(v___x_871_);
if (v___x_872_ == 0)
{
lean_dec(v___x_868_);
lean_del_object(v___x_865_);
lean_del_object(v___x_860_);
lean_del_object(v___x_856_);
lean_dec(v_snd_834_);
v_a_840_ = v___x_853_;
goto v___jp_839_;
}
else
{
lean_object* v___x_873_; 
lean_inc(v_mvarId_822_);
v___x_873_ = l_Lean_Meta_subst_x3f(v_mvarId_822_, v___x_868_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_901_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_901_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_901_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_901_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
if (lean_obj_tag(v_a_874_) == 0)
{
lean_del_object(v___x_876_);
lean_del_object(v___x_865_);
lean_del_object(v___x_860_);
lean_del_object(v___x_856_);
lean_dec(v_snd_834_);
v_a_840_ = v___x_853_;
goto v___jp_839_;
}
else
{
lean_object* v_val_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_900_; 
lean_del_object(v___x_836_);
lean_dec(v_mvarId_822_);
v_val_878_ = lean_ctor_get(v_a_874_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_a_874_);
if (v_isSharedCheck_900_ == 0)
{
v___x_880_ = v_a_874_;
v_isShared_881_ = v_isSharedCheck_900_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_val_878_);
lean_dec(v_a_874_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_900_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = lean_mk_empty_array_with_capacity(v___x_882_);
v___x_884_ = lean_array_push(v___x_883_, v_val_878_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_884_);
v___x_886_ = v___x_880_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_899_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 1, v___x_852_);
lean_ctor_set(v___x_865_, 0, v___x_886_);
v___x_888_ = v___x_865_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_852_);
v___x_888_ = v_reuseFailAlloc_898_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_888_);
v___x_890_ = v___x_856_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_897_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_892_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v_snd_834_);
lean_ctor_set(v___x_860_, 0, v___x_890_);
v___x_892_ = v___x_860_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_snd_834_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_892_);
v___x_894_ = v___x_876_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
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
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_del_object(v___x_865_);
lean_del_object(v___x_860_);
lean_del_object(v___x_856_);
lean_del_object(v___x_836_);
lean_dec(v_snd_834_);
lean_dec(v_mvarId_822_);
v_a_902_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_873_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_873_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v___x_868_);
lean_del_object(v___x_865_);
lean_del_object(v___x_860_);
lean_del_object(v___x_856_);
lean_del_object(v___x_836_);
lean_dec(v_snd_834_);
lean_dec(v_mvarId_822_);
v_a_910_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_869_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_869_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
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
lean_dec(v_a_851_);
lean_dec(v_snd_834_);
v_a_840_ = v___x_853_;
goto v___jp_839_;
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_del_object(v___x_836_);
lean_dec(v_snd_834_);
lean_dec(v_mvarId_822_);
v_a_922_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_850_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_850_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
v___jp_839_:
{
lean_object* v___x_842_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_a_840_);
lean_ctor_set(v___x_836_, 0, v___x_838_);
v___x_842_ = v___x_836_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_a_840_);
v___x_842_ = v_reuseFailAlloc_846_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
size_t v___x_843_; size_t v___x_844_; 
v___x_843_ = ((size_t)1ULL);
v___x_844_ = lean_usize_add(v_i_825_, v___x_843_);
v_i_825_ = v___x_844_;
v_b_826_ = v___x_842_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___boxed(lean_object* v_mvarId_932_, lean_object* v_as_933_, lean_object* v_sz_934_, lean_object* v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
size_t v_sz_boxed_942_; size_t v_i_boxed_943_; lean_object* v_res_944_; 
v_sz_boxed_942_ = lean_unbox_usize(v_sz_934_);
lean_dec(v_sz_934_);
v_i_boxed_943_ = lean_unbox_usize(v_i_935_);
lean_dec(v_i_935_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_932_, v_as_933_, v_sz_boxed_942_, v_i_boxed_943_, v_b_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec_ref(v_as_933_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(lean_object* v_mvarId_945_, lean_object* v_as_946_, size_t v_sz_947_, size_t v_i_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec(v_mvarId_945_);
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v_b_949_);
return v___x_956_;
}
else
{
lean_object* v_snd_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_1053_; 
v_snd_957_ = lean_ctor_get(v_b_949_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_b_949_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v_b_949_, 0);
lean_dec(v_unused_1054_);
v___x_959_ = v_b_949_;
v_isShared_960_ = v_isSharedCheck_1053_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_snd_957_);
lean_dec(v_b_949_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_1053_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v_a_963_; lean_object* v_a_970_; 
v___x_961_ = lean_box(0);
v_a_970_ = lean_array_uget_borrowed(v_as_946_, v_i_948_);
if (lean_obj_tag(v_a_970_) == 0)
{
v_a_963_ = v_snd_957_;
goto v___jp_962_;
}
else
{
lean_object* v_val_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_val_971_ = lean_ctor_get(v_a_970_, 0);
v___x_972_ = l_Lean_LocalDecl_type(v_val_971_);
v___x_973_ = l_Lean_Meta_matchEq_x3f(v___x_972_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = lean_box(0);
v___x_976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_974_) == 1)
{
lean_object* v_val_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1044_; 
v_val_977_ = lean_ctor_get(v_a_974_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_a_974_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_979_ = v_a_974_;
v_isShared_980_ = v_isSharedCheck_1044_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_val_977_);
lean_dec(v_a_974_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1044_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_snd_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1042_; 
v_snd_981_ = lean_ctor_get(v_val_977_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_val_977_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v_val_977_, 0);
lean_dec(v_unused_1043_);
v___x_983_ = v_val_977_;
v_isShared_984_ = v_isSharedCheck_1042_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snd_981_);
lean_dec(v_val_977_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1042_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1041_; 
v_fst_985_ = lean_ctor_get(v_snd_981_, 0);
v_snd_986_ = lean_ctor_get(v_snd_981_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_snd_981_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_988_ = v_snd_981_;
v_isShared_989_ = v_isSharedCheck_1041_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snd_986_);
lean_inc(v_fst_985_);
lean_dec(v_snd_981_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1041_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___x_990_; 
v___x_990_ = l_Lean_Expr_isFVar(v_fst_985_);
if (v___x_990_ == 0)
{
lean_del_object(v___x_988_);
lean_dec(v_snd_986_);
lean_dec(v_fst_985_);
lean_del_object(v___x_983_);
lean_del_object(v___x_979_);
lean_dec(v_snd_957_);
v_a_963_ = v___x_976_;
goto v___jp_962_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = l_Lean_Expr_fvarId_x21(v_fst_985_);
lean_dec(v_fst_985_);
lean_inc(v___x_991_);
v___x_992_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_986_, v___x_991_, v___y_951_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; uint8_t v___x_994_; uint8_t v___x_995_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = lean_unbox(v_a_993_);
lean_dec(v_a_993_);
v___x_995_ = lean_bool_not(v___x_994_);
if (v___x_995_ == 0)
{
lean_dec(v___x_991_);
lean_del_object(v___x_988_);
lean_del_object(v___x_983_);
lean_del_object(v___x_979_);
lean_dec(v_snd_957_);
v_a_963_ = v___x_976_;
goto v___jp_962_;
}
else
{
lean_object* v___x_996_; 
lean_inc(v_mvarId_945_);
v___x_996_ = l_Lean_Meta_subst_x3f(v_mvarId_945_, v___x_991_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1024_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1024_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1024_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
if (lean_obj_tag(v_a_997_) == 0)
{
lean_del_object(v___x_999_);
lean_del_object(v___x_988_);
lean_del_object(v___x_983_);
lean_del_object(v___x_979_);
lean_dec(v_snd_957_);
v_a_963_ = v___x_976_;
goto v___jp_962_;
}
else
{
lean_object* v_val_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1023_; 
lean_del_object(v___x_959_);
lean_dec(v_mvarId_945_);
v_val_1001_ = lean_ctor_get(v_a_997_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_a_997_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1003_ = v_a_997_;
v_isShared_1004_ = v_isSharedCheck_1023_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_val_1001_);
lean_dec(v_a_997_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1023_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1005_ = lean_unsigned_to_nat(1u);
v___x_1006_ = lean_mk_empty_array_with_capacity(v___x_1005_);
v___x_1007_ = lean_array_push(v___x_1006_, v_val_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1007_);
v___x_1009_ = v___x_1003_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 1, v___x_975_);
lean_ctor_set(v___x_988_, 0, v___x_1009_);
v___x_1011_ = v___x_988_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_975_);
v___x_1011_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_1011_);
v___x_1013_ = v___x_979_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v_snd_957_);
lean_ctor_set(v___x_983_, 0, v___x_1013_);
v___x_1015_ = v___x_983_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_snd_957_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1015_);
v___x_1017_ = v___x_999_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
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
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_del_object(v___x_988_);
lean_del_object(v___x_983_);
lean_del_object(v___x_979_);
lean_del_object(v___x_959_);
lean_dec(v_snd_957_);
lean_dec(v_mvarId_945_);
v_a_1025_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_996_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_996_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v___x_991_);
lean_del_object(v___x_988_);
lean_del_object(v___x_983_);
lean_del_object(v___x_979_);
lean_del_object(v___x_959_);
lean_dec(v_snd_957_);
lean_dec(v_mvarId_945_);
v_a_1033_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_992_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_992_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
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
lean_dec(v_snd_957_);
v_a_963_ = v___x_976_;
goto v___jp_962_;
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_del_object(v___x_959_);
lean_dec(v_snd_957_);
lean_dec(v_mvarId_945_);
v_a_1045_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_973_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_973_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
v___jp_962_:
{
lean_object* v___x_965_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v_a_963_);
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_965_ = v___x_959_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_a_963_);
v___x_965_ = v_reuseFailAlloc_969_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((size_t)1ULL);
v___x_967_ = lean_usize_add(v_i_948_, v___x_966_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_945_, v_as_946_, v_sz_947_, v___x_967_, v___x_965_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
return v___x_968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2___boxed(lean_object* v_mvarId_1055_, lean_object* v_as_1056_, lean_object* v_sz_1057_, lean_object* v_i_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
size_t v_sz_boxed_1065_; size_t v_i_boxed_1066_; lean_object* v_res_1067_; 
v_sz_boxed_1065_ = lean_unbox_usize(v_sz_1057_);
lean_dec(v_sz_1057_);
v_i_boxed_1066_ = lean_unbox_usize(v_i_1058_);
lean_dec(v_i_1058_);
v_res_1067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1055_, v_as_1056_, v_sz_boxed_1065_, v_i_boxed_1066_, v_b_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v_as_1056_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(lean_object* v_mvarId_1068_, lean_object* v_t_1069_, lean_object* v_init_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_root_1076_; lean_object* v_tail_1077_; lean_object* v___x_1078_; 
v_root_1076_ = lean_ctor_get(v_t_1069_, 0);
v_tail_1077_ = lean_ctor_get(v_t_1069_, 1);
lean_inc(v_mvarId_1068_);
lean_inc_ref(v_init_1070_);
v___x_1078_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_1070_, v_mvarId_1068_, v_root_1076_, v_init_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec_ref(v_init_1070_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1115_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1115_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1115_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
if (lean_obj_tag(v_a_1079_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; 
lean_dec(v_mvarId_1068_);
v_a_1083_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v_a_1079_, 1);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v_a_1083_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; size_t v_sz_1090_; size_t v___x_1091_; lean_object* v___x_1092_; 
lean_del_object(v___x_1081_);
v_a_1087_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v_a_1079_, 1);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_a_1087_);
v_sz_1090_ = lean_array_size(v_tail_1077_);
v___x_1091_ = ((size_t)0ULL);
v___x_1092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1068_, v_tail_1077_, v_sz_1090_, v___x_1091_, v___x_1089_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1106_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1106_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_fst_1097_; 
v_fst_1097_ = lean_ctor_get(v_a_1093_, 0);
if (lean_obj_tag(v_fst_1097_) == 0)
{
lean_object* v_snd_1098_; lean_object* v___x_1100_; 
v_snd_1098_ = lean_ctor_get(v_a_1093_, 1);
lean_inc(v_snd_1098_);
lean_dec(v_a_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v_snd_1098_);
v___x_1100_ = v___x_1095_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_snd_1098_);
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
lean_object* v_val_1102_; lean_object* v___x_1104_; 
lean_inc_ref(v_fst_1097_);
lean_dec(v_a_1093_);
v_val_1102_ = lean_ctor_get(v_fst_1097_, 0);
lean_inc(v_val_1102_);
lean_dec_ref_known(v_fst_1097_, 1);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v_val_1102_);
v___x_1104_ = v___x_1095_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_val_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1092_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1092_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_mvarId_1068_);
v_a_1116_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1078_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1078_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1___boxed(lean_object* v_mvarId_1124_, lean_object* v_t_1125_, lean_object* v_init_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1124_, v_t_1125_, v_init_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec_ref(v_t_1125_);
return v_res_1132_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(lean_object* v_mvarId_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_lctx_1145_; lean_object* v_decls_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_lctx_1145_ = lean_ctor_get(v___y_1140_, 2);
v_decls_1146_ = lean_ctor_get(v_lctx_1145_, 1);
v___x_1147_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0));
v___x_1148_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1139_, v_decls_1146_, v___x_1147_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1160_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1160_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1160_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_fst_1153_; 
v_fst_1153_ = lean_ctor_get(v_a_1149_, 0);
lean_inc(v_fst_1153_);
lean_dec(v_a_1149_);
if (lean_obj_tag(v_fst_1153_) == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_del_object(v___x_1151_);
v___x_1154_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2);
v___x_1155_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1154_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v___x_1155_;
}
else
{
lean_object* v_val_1156_; lean_object* v___x_1158_; 
v_val_1156_ = lean_ctor_get(v_fst_1153_, 0);
lean_inc(v_val_1156_);
lean_dec_ref_known(v_fst_1153_, 1);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v_val_1156_);
v___x_1158_ = v___x_1151_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_val_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_a_1161_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1148_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1148_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed(lean_object* v_mvarId_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(v_mvarId_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(lean_object* v_mvarId_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v___f_1182_; lean_object* v___x_1183_; 
lean_inc(v_mvarId_1176_);
v___f_1182_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1182_, 0, v_mvarId_1176_);
v___x_1183_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_1176_, v___f_1182_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___boxed(lean_object* v_mvarId_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v_mvarId_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object* v_x_1198_){
_start:
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1200_ = lean_name_eq(v_x_1198_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object* v_x_1201_){
_start:
{
uint8_t v_res_1202_; lean_object* v_r_1203_; 
v_res_1202_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(v_x_1201_);
lean_dec(v_x_1201_);
v_r_1203_ = lean_box(v_res_1202_);
return v_r_1203_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object* v_e_1204_){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1206_ = l_Lean_Expr_isConstOf(v_e_1204_, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object* v_e_1207_){
_start:
{
uint8_t v_res_1208_; lean_object* v_r_1209_; 
v_res_1208_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(v_e_1207_);
lean_dec_ref(v_e_1207_);
v_r_1209_ = lean_box(v_res_1208_);
return v_r_1209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2));
v___x_1214_ = l_Lean_stringToMessageData(v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object* v_mvarId_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1221_; 
lean_inc(v_mvarId_1215_);
v___x_1221_ = l_Lean_MVarId_getType(v_mvarId_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___f_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___f_1223_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0));
v___f_1224_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1));
v___x_1225_ = lean_find_expr(v___f_1224_, v_a_1222_);
lean_dec(v_a_1222_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_mvarId_1215_);
v___x_1226_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3);
v___x_1227_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1226_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v___x_1236_; 
lean_dec_ref_known(v___x_1225_, 1);
v___x_1236_ = l_Lean_MVarId_deltaTarget(v_mvarId_1215_, v___f_1223_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
return v___x_1236_;
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_mvarId_1215_);
v_a_1237_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1221_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1221_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object* v_mvarId_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_mvarId_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
return v_res_1251_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = l_Lean_maxRecDepthErrorMessage;
v___x_1258_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3);
v___x_1260_ = l_Lean_MessageData_ofFormat(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4);
v___x_1262_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2));
v___x_1263_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(lean_object* v_ref_1264_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v_ref_1264_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___boxed(lean_object* v_ref_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1269_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object* v_00_u03b1_1272_, lean_object* v_ref_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1273_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object* v_00_u03b1_1280_, lean_object* v_ref_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v_00_u03b1_1280_, v_ref_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object* v_a_1288_, lean_object* v_____r_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_mk_empty_array_with_capacity(v___x_1295_);
v___x_1297_ = lean_array_push(v___x_1296_, v_a_1288_);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object* v_a_1299_, lean_object* v_____r_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1299_, v_____r_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1306_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1307_; double v___x_1308_; 
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_float_of_nat(v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object* v_cls_1312_, lean_object* v_msg_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_ref_1319_; lean_object* v___x_1320_; lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1365_; 
v_ref_1319_ = lean_ctor_get(v___y_1316_, 5);
v___x_1320_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1365_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1365_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v_traceState_1326_; lean_object* v_env_1327_; lean_object* v_nextMacroScope_1328_; lean_object* v_ngen_1329_; lean_object* v_auxDeclNGen_1330_; lean_object* v_cache_1331_; lean_object* v_messages_1332_; lean_object* v_infoState_1333_; lean_object* v_snapshotTasks_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1364_; 
v___x_1325_ = lean_st_ref_take(v___y_1317_);
v_traceState_1326_ = lean_ctor_get(v___x_1325_, 4);
v_env_1327_ = lean_ctor_get(v___x_1325_, 0);
v_nextMacroScope_1328_ = lean_ctor_get(v___x_1325_, 1);
v_ngen_1329_ = lean_ctor_get(v___x_1325_, 2);
v_auxDeclNGen_1330_ = lean_ctor_get(v___x_1325_, 3);
v_cache_1331_ = lean_ctor_get(v___x_1325_, 5);
v_messages_1332_ = lean_ctor_get(v___x_1325_, 6);
v_infoState_1333_ = lean_ctor_get(v___x_1325_, 7);
v_snapshotTasks_1334_ = lean_ctor_get(v___x_1325_, 8);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1336_ = v___x_1325_;
v_isShared_1337_ = v_isSharedCheck_1364_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_snapshotTasks_1334_);
lean_inc(v_infoState_1333_);
lean_inc(v_messages_1332_);
lean_inc(v_cache_1331_);
lean_inc(v_traceState_1326_);
lean_inc(v_auxDeclNGen_1330_);
lean_inc(v_ngen_1329_);
lean_inc(v_nextMacroScope_1328_);
lean_inc(v_env_1327_);
lean_dec(v___x_1325_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1364_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
uint64_t v_tid_1338_; lean_object* v_traces_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1363_; 
v_tid_1338_ = lean_ctor_get_uint64(v_traceState_1326_, sizeof(void*)*1);
v_traces_1339_ = lean_ctor_get(v_traceState_1326_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_traceState_1326_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1341_ = v_traceState_1326_;
v_isShared_1342_ = v_isSharedCheck_1363_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_traces_1339_);
lean_dec(v_traceState_1326_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1363_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; double v___x_1344_; uint8_t v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0);
v___x_1345_ = 0;
v___x_1346_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1));
v___x_1347_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1347_, 0, v_cls_1312_);
lean_ctor_set(v___x_1347_, 1, v___x_1343_);
lean_ctor_set(v___x_1347_, 2, v___x_1346_);
lean_ctor_set_float(v___x_1347_, sizeof(void*)*3, v___x_1344_);
lean_ctor_set_float(v___x_1347_, sizeof(void*)*3 + 8, v___x_1344_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*3 + 16, v___x_1345_);
v___x_1348_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2));
v___x_1349_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v_a_1321_);
lean_ctor_set(v___x_1349_, 2, v___x_1348_);
lean_inc(v_ref_1319_);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v_ref_1319_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = l_Lean_PersistentArray_push___redArg(v_traces_1339_, v___x_1350_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1351_);
v___x_1353_ = v___x_1341_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1351_);
lean_ctor_set_uint64(v_reuseFailAlloc_1362_, sizeof(void*)*1, v_tid_1338_);
v___x_1353_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1355_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 4, v___x_1353_);
v___x_1355_ = v___x_1336_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_env_1327_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_nextMacroScope_1328_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_ngen_1329_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_auxDeclNGen_1330_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1361_, 5, v_cache_1331_);
lean_ctor_set(v_reuseFailAlloc_1361_, 6, v_messages_1332_);
lean_ctor_set(v_reuseFailAlloc_1361_, 7, v_infoState_1333_);
lean_ctor_set(v_reuseFailAlloc_1361_, 8, v_snapshotTasks_1334_);
v___x_1355_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1356_ = lean_st_ref_set(v___y_1317_, v___x_1355_);
v___x_1357_ = lean_box(0);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1357_);
v___x_1359_ = v___x_1323_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object* v_cls_1366_, lean_object* v_msg_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1366_, v_msg_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
return v_res_1373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0));
v___x_1376_ = l_Lean_stringToMessageData(v___x_1375_);
return v___x_1376_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2));
v___x_1379_ = l_Lean_stringToMessageData(v___x_1378_);
return v___x_1379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4));
v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
return v___x_1382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
return v___x_1385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16(void){
_start:
{
lean_object* v_cls_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_cls_1399_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1400_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15));
v___x_1401_ = l_Lean_Name_append(v___x_1400_, v_cls_1399_);
return v___x_1401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17));
v___x_1404_ = l_Lean_stringToMessageData(v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1405_, lean_object* v_mvarId_1406_, lean_object* v_depth_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v_a_1418_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; uint8_t v___y_1480_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v_a_1504_; uint8_t v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; uint8_t v___y_1516_; uint8_t v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v_a_1558_; uint8_t v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; uint8_t v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; uint8_t v___y_1581_; uint8_t v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1613_; uint8_t v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; uint8_t v___y_1638_; uint8_t v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; uint8_t v___y_1663_; uint8_t v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; uint8_t v___y_1689_; uint8_t v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; uint8_t v___y_1718_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v_fileName_1769_; lean_object* v_fileMap_1770_; lean_object* v_options_1771_; lean_object* v_currRecDepth_1772_; lean_object* v_maxRecDepth_1773_; lean_object* v_ref_1774_; lean_object* v_currNamespace_1775_; lean_object* v_openDecls_1776_; lean_object* v_initHeartbeats_1777_; lean_object* v_maxHeartbeats_1778_; lean_object* v_quotContext_1779_; lean_object* v_currMacroScope_1780_; uint8_t v_diag_1781_; lean_object* v_cancelTk_x3f_1782_; uint8_t v_suppressElabErrors_1783_; lean_object* v_inheritedTraceOptions_1784_; lean_object* v_cls_1785_; uint8_t v___y_1787_; lean_object* v___x_1799_; uint8_t v___x_1800_; uint8_t v___x_1801_; 
v_fileName_1769_ = lean_ctor_get(v_a_1410_, 0);
v_fileMap_1770_ = lean_ctor_get(v_a_1410_, 1);
v_options_1771_ = lean_ctor_get(v_a_1410_, 2);
v_currRecDepth_1772_ = lean_ctor_get(v_a_1410_, 3);
v_maxRecDepth_1773_ = lean_ctor_get(v_a_1410_, 4);
v_ref_1774_ = lean_ctor_get(v_a_1410_, 5);
v_currNamespace_1775_ = lean_ctor_get(v_a_1410_, 6);
v_openDecls_1776_ = lean_ctor_get(v_a_1410_, 7);
v_initHeartbeats_1777_ = lean_ctor_get(v_a_1410_, 8);
v_maxHeartbeats_1778_ = lean_ctor_get(v_a_1410_, 9);
v_quotContext_1779_ = lean_ctor_get(v_a_1410_, 10);
v_currMacroScope_1780_ = lean_ctor_get(v_a_1410_, 11);
v_diag_1781_ = lean_ctor_get_uint8(v_a_1410_, sizeof(void*)*14);
v_cancelTk_x3f_1782_ = lean_ctor_get(v_a_1410_, 12);
v_suppressElabErrors_1783_ = lean_ctor_get_uint8(v_a_1410_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1784_ = lean_ctor_get(v_a_1410_, 13);
v_cls_1785_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = lean_nat_dec_eq(v_maxRecDepth_1773_, v___x_1799_);
v___x_1801_ = lean_bool_not(v___x_1800_);
if (v___x_1801_ == 0)
{
v___y_1787_ = v___x_1801_;
goto v___jp_1786_;
}
else
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_nat_dec_eq(v_currRecDepth_1772_, v_maxRecDepth_1773_);
v___y_1787_ = v___x_1802_;
goto v___jp_1786_;
}
v___jp_1413_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_array_get_size(v_a_1418_);
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_nat_dec_lt(v___x_1419_, v___x_1420_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; 
lean_dec_ref(v_a_1418_);
lean_dec_ref(v___y_1415_);
lean_dec(v_matchDeclName_1405_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
return v___x_1423_;
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_nat_dec_le(v___x_1420_, v___x_1420_);
if (v___x_1424_ == 0)
{
if (v___x_1422_ == 0)
{
lean_object* v___x_1425_; 
lean_dec_ref(v_a_1418_);
lean_dec_ref(v___y_1415_);
lean_dec(v_matchDeclName_1405_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1421_);
return v___x_1425_;
}
else
{
size_t v___x_1426_; size_t v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = lean_usize_of_nat(v___x_1420_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1407_, v_matchDeclName_1405_, v_a_1418_, v___x_1426_, v___x_1427_, v___x_1421_, v___y_1414_, v___y_1417_, v___y_1415_, v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec_ref(v_a_1418_);
return v___x_1428_;
}
}
else
{
size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = ((size_t)0ULL);
v___x_1430_ = lean_usize_of_nat(v___x_1420_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1407_, v_matchDeclName_1405_, v_a_1418_, v___x_1429_, v___x_1430_, v___x_1421_, v___y_1414_, v___y_1417_, v___y_1415_, v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec_ref(v_a_1418_);
return v___x_1431_;
}
}
}
v___jp_1432_:
{
if (lean_obj_tag(v___y_1437_) == 0)
{
lean_object* v_a_1438_; 
v_a_1438_ = lean_ctor_get(v___y_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___y_1437_, 1);
v___y_1414_ = v___y_1433_;
v___y_1415_ = v___y_1434_;
v___y_1416_ = v___y_1435_;
v___y_1417_ = v___y_1436_;
v_a_1418_ = v_a_1438_;
goto v___jp_1413_;
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v___y_1434_);
lean_dec(v_matchDeclName_1405_);
v_a_1439_ = lean_ctor_get(v___y_1437_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___y_1437_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___y_1437_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___y_1437_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
v___jp_1447_:
{
if (v___y_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_dec_ref(v___y_1451_);
v___x_1456_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1449_, v___y_1454_, v___y_1453_);
lean_dec_ref(v___y_1449_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1470_; 
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1456_, 0);
lean_dec(v_unused_1471_);
v___x_1458_ = v___x_1456_;
v_isShared_1459_ = v_isSharedCheck_1470_;
goto v_resetjp_1457_;
}
else
{
lean_dec(v___x_1456_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1470_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1460_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1405_);
v___x_1461_ = l_Lean_MessageData_ofName(v_matchDeclName_1405_);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set_tag(v___x_1458_, 1);
lean_ctor_set(v___x_1458_, 0, v___y_1448_);
v___x_1466_ = v___x_1458_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___y_1448_);
v___x_1466_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1464_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1467_, v___y_1450_, v___y_1454_, v___y_1452_, v___y_1453_);
v___y_1433_ = v___y_1450_;
v___y_1434_ = v___y_1452_;
v___y_1435_ = v___y_1453_;
v___y_1436_ = v___y_1454_;
v___y_1437_ = v___x_1468_;
goto v___jp_1432_;
}
}
}
else
{
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1448_);
lean_dec(v_matchDeclName_1405_);
return v___x_1456_;
}
}
else
{
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
v___y_1433_ = v___y_1450_;
v___y_1434_ = v___y_1452_;
v___y_1435_ = v___y_1453_;
v___y_1436_ = v___y_1454_;
v___y_1437_ = v___y_1451_;
goto v___jp_1432_;
}
}
v___jp_1472_:
{
if (v___y_1480_ == 0)
{
lean_object* v___x_1481_; 
lean_dec_ref(v___y_1477_);
v___x_1481_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1476_, v___y_1479_, v___y_1478_);
lean_dec_ref(v___y_1476_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v___x_1482_; 
lean_dec_ref_known(v___x_1481_, 1);
v___x_1482_ = l_Lean_Meta_saveState___redArg(v___y_1479_, v___y_1478_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1484_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1482_, 1);
lean_inc(v___y_1473_);
v___x_1484_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1473_, v___y_1474_, v___y_1479_, v___y_1475_, v___y_1478_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_dec(v_a_1483_);
lean_dec(v___y_1473_);
v___y_1433_ = v___y_1474_;
v___y_1434_ = v___y_1475_;
v___y_1435_ = v___y_1478_;
v___y_1436_ = v___y_1479_;
v___y_1437_ = v___x_1484_;
goto v___jp_1432_;
}
else
{
lean_object* v_a_1485_; uint8_t v___x_1486_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
v___x_1486_ = l_Lean_Exception_isInterrupt(v_a_1485_);
if (v___x_1486_ == 0)
{
uint8_t v___x_1487_; 
v___x_1487_ = l_Lean_Exception_isRuntime(v_a_1485_);
v___y_1448_ = v___y_1473_;
v___y_1449_ = v_a_1483_;
v___y_1450_ = v___y_1474_;
v___y_1451_ = v___x_1484_;
v___y_1452_ = v___y_1475_;
v___y_1453_ = v___y_1478_;
v___y_1454_ = v___y_1479_;
v___y_1455_ = v___x_1487_;
goto v___jp_1447_;
}
else
{
lean_dec(v_a_1485_);
v___y_1448_ = v___y_1473_;
v___y_1449_ = v_a_1483_;
v___y_1450_ = v___y_1474_;
v___y_1451_ = v___x_1484_;
v___y_1452_ = v___y_1475_;
v___y_1453_ = v___y_1478_;
v___y_1454_ = v___y_1479_;
v___y_1455_ = v___x_1486_;
goto v___jp_1447_;
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1473_);
lean_dec(v_matchDeclName_1405_);
v_a_1488_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1482_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1482_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1473_);
lean_dec(v_matchDeclName_1405_);
return v___x_1481_;
}
}
else
{
lean_object* v___x_1496_; 
lean_dec_ref(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1473_);
lean_dec(v_matchDeclName_1405_);
v___x_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1477_);
return v___x_1496_;
}
}
v___jp_1497_:
{
uint8_t v___x_1505_; 
v___x_1505_ = l_Lean_Exception_isInterrupt(v_a_1504_);
if (v___x_1505_ == 0)
{
uint8_t v___x_1506_; 
lean_inc_ref(v_a_1504_);
v___x_1506_ = l_Lean_Exception_isRuntime(v_a_1504_);
v___y_1473_ = v___y_1498_;
v___y_1474_ = v___y_1499_;
v___y_1475_ = v___y_1501_;
v___y_1476_ = v___y_1500_;
v___y_1477_ = v_a_1504_;
v___y_1478_ = v___y_1502_;
v___y_1479_ = v___y_1503_;
v___y_1480_ = v___x_1506_;
goto v___jp_1472_;
}
else
{
v___y_1473_ = v___y_1498_;
v___y_1474_ = v___y_1499_;
v___y_1475_ = v___y_1501_;
v___y_1476_ = v___y_1500_;
v___y_1477_ = v_a_1504_;
v___y_1478_ = v___y_1502_;
v___y_1479_ = v___y_1503_;
v___y_1480_ = v___x_1505_;
goto v___jp_1472_;
}
}
v___jp_1507_:
{
if (v___y_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_dec_ref(v___y_1511_);
v___x_1517_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1509_, v___y_1515_, v___y_1514_);
lean_dec_ref(v___y_1509_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v___x_1518_; 
lean_dec_ref_known(v___x_1517_, 1);
v___x_1518_ = l_Lean_Meta_saveState___redArg(v___y_1515_, v___y_1514_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = lean_box(0);
lean_inc(v___y_1510_);
v___x_1521_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1510_, v___x_1520_, v___y_1508_, v___y_1512_, v___y_1515_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
if (lean_obj_tag(v_a_1522_) == 1)
{
lean_object* v_val_1523_; lean_object* v_fst_1524_; lean_object* v_snd_1525_; lean_object* v_mvarId_1526_; lean_object* v_fvarId_1527_; lean_object* v___x_1528_; 
v_val_1523_ = lean_ctor_get(v_a_1522_, 0);
lean_inc(v_val_1523_);
lean_dec_ref_known(v_a_1522_, 1);
v_fst_1524_ = lean_ctor_get(v_val_1523_, 0);
lean_inc(v_fst_1524_);
v_snd_1525_ = lean_ctor_get(v_val_1523_, 1);
lean_inc(v_snd_1525_);
lean_dec(v_val_1523_);
v_mvarId_1526_ = lean_ctor_get(v_fst_1524_, 0);
lean_inc(v_mvarId_1526_);
v_fvarId_1527_ = lean_ctor_get(v_fst_1524_, 1);
lean_inc(v_fvarId_1527_);
lean_dec(v_fst_1524_);
v___x_1528_ = l_Lean_Meta_trySubst(v_mvarId_1526_, v_fvarId_1527_, v___y_1512_, v___y_1515_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v_mvarId_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v_a_1519_);
lean_dec(v___y_1510_);
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v_mvarId_1530_ = lean_ctor_get(v_snd_1525_, 0);
lean_inc(v_mvarId_1530_);
lean_dec(v_snd_1525_);
v___x_1531_ = lean_unsigned_to_nat(2u);
v___x_1532_ = lean_mk_empty_array_with_capacity(v___x_1531_);
v___x_1533_ = lean_array_push(v___x_1532_, v_a_1529_);
v___x_1534_ = lean_array_push(v___x_1533_, v_mvarId_1530_);
v___y_1414_ = v___y_1512_;
v___y_1415_ = v___y_1513_;
v___y_1416_ = v___y_1514_;
v___y_1417_ = v___y_1515_;
v_a_1418_ = v___x_1534_;
goto v___jp_1413_;
}
else
{
lean_object* v_a_1535_; 
lean_dec(v_snd_1525_);
v_a_1535_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1528_, 1);
v___y_1498_ = v___y_1510_;
v___y_1499_ = v___y_1512_;
v___y_1500_ = v_a_1519_;
v___y_1501_ = v___y_1513_;
v___y_1502_ = v___y_1514_;
v___y_1503_ = v___y_1515_;
v_a_1504_ = v_a_1535_;
goto v___jp_1497_;
}
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v_a_1522_);
v___x_1536_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1537_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1536_, v___y_1512_, v___y_1515_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; 
lean_dec(v_a_1519_);
lean_dec(v___y_1510_);
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v___y_1414_ = v___y_1512_;
v___y_1415_ = v___y_1513_;
v___y_1416_ = v___y_1514_;
v___y_1417_ = v___y_1515_;
v_a_1418_ = v_a_1538_;
goto v___jp_1413_;
}
else
{
lean_object* v_a_1539_; 
v_a_1539_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1537_, 1);
v___y_1498_ = v___y_1510_;
v___y_1499_ = v___y_1512_;
v___y_1500_ = v_a_1519_;
v___y_1501_ = v___y_1513_;
v___y_1502_ = v___y_1514_;
v___y_1503_ = v___y_1515_;
v_a_1504_ = v_a_1539_;
goto v___jp_1497_;
}
}
}
else
{
lean_object* v_a_1540_; 
v_a_1540_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1521_, 1);
v___y_1498_ = v___y_1510_;
v___y_1499_ = v___y_1512_;
v___y_1500_ = v_a_1519_;
v___y_1501_ = v___y_1513_;
v___y_1502_ = v___y_1514_;
v___y_1503_ = v___y_1515_;
v_a_1504_ = v_a_1540_;
goto v___jp_1497_;
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1510_);
lean_dec(v_matchDeclName_1405_);
v_a_1541_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1518_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1518_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1510_);
lean_dec(v_matchDeclName_1405_);
return v___x_1517_;
}
}
else
{
lean_object* v___x_1549_; 
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v_matchDeclName_1405_);
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___y_1511_);
return v___x_1549_;
}
}
v___jp_1550_:
{
uint8_t v___x_1559_; 
v___x_1559_ = l_Lean_Exception_isInterrupt(v_a_1558_);
if (v___x_1559_ == 0)
{
uint8_t v___x_1560_; 
lean_inc_ref(v_a_1558_);
v___x_1560_ = l_Lean_Exception_isRuntime(v_a_1558_);
v___y_1508_ = v___y_1551_;
v___y_1509_ = v___y_1552_;
v___y_1510_ = v___y_1553_;
v___y_1511_ = v_a_1558_;
v___y_1512_ = v___y_1554_;
v___y_1513_ = v___y_1555_;
v___y_1514_ = v___y_1556_;
v___y_1515_ = v___y_1557_;
v___y_1516_ = v___x_1560_;
goto v___jp_1507_;
}
else
{
v___y_1508_ = v___y_1551_;
v___y_1509_ = v___y_1552_;
v___y_1510_ = v___y_1553_;
v___y_1511_ = v_a_1558_;
v___y_1512_ = v___y_1554_;
v___y_1513_ = v___y_1555_;
v___y_1514_ = v___y_1556_;
v___y_1515_ = v___y_1557_;
v___y_1516_ = v___x_1559_;
goto v___jp_1507_;
}
}
v___jp_1561_:
{
if (lean_obj_tag(v___y_1569_) == 0)
{
lean_object* v_a_1570_; 
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
v_a_1570_ = lean_ctor_get(v___y_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___y_1569_, 1);
v___y_1414_ = v___y_1565_;
v___y_1415_ = v___y_1566_;
v___y_1416_ = v___y_1567_;
v___y_1417_ = v___y_1568_;
v_a_1418_ = v_a_1570_;
goto v___jp_1413_;
}
else
{
lean_object* v_a_1571_; 
v_a_1571_ = lean_ctor_get(v___y_1569_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___y_1569_, 1);
v___y_1551_ = v___y_1562_;
v___y_1552_ = v___y_1563_;
v___y_1553_ = v___y_1564_;
v___y_1554_ = v___y_1565_;
v___y_1555_ = v___y_1566_;
v___y_1556_ = v___y_1567_;
v___y_1557_ = v___y_1568_;
v_a_1558_ = v_a_1571_;
goto v___jp_1550_;
}
}
v___jp_1572_:
{
if (v___y_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref(v___y_1579_);
v___x_1582_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1576_, v___y_1580_, v___y_1578_);
lean_dec_ref(v___y_1576_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref_known(v___x_1582_, 1);
v___x_1583_ = l_Lean_Meta_saveState___redArg(v___y_1580_, v___y_1578_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
lean_inc(v___y_1574_);
v___x_1585_ = l_Lean_Meta_simpIfTarget(v___y_1574_, v___y_1573_, v___y_1573_, v___y_1575_, v___y_1580_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; uint8_t v___x_1587_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
v___x_1587_ = l_Lean_instBEqMVarId_beq(v_a_1586_, v___y_1574_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_box(0);
v___x_1589_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1586_, v___x_1588_, v___y_1575_, v___y_1580_, v___y_1577_, v___y_1578_);
v___y_1562_ = v___y_1573_;
v___y_1563_ = v_a_1584_;
v___y_1564_ = v___y_1574_;
v___y_1565_ = v___y_1575_;
v___y_1566_ = v___y_1577_;
v___y_1567_ = v___y_1578_;
v___y_1568_ = v___y_1580_;
v___y_1569_ = v___x_1589_;
goto v___jp_1561_;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1591_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1590_, v___y_1575_, v___y_1580_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1593_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v___x_1593_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1586_, v_a_1592_, v___y_1575_, v___y_1580_, v___y_1577_, v___y_1578_);
v___y_1562_ = v___y_1573_;
v___y_1563_ = v_a_1584_;
v___y_1564_ = v___y_1574_;
v___y_1565_ = v___y_1575_;
v___y_1566_ = v___y_1577_;
v___y_1567_ = v___y_1578_;
v___y_1568_ = v___y_1580_;
v___y_1569_ = v___x_1593_;
goto v___jp_1561_;
}
else
{
lean_object* v_a_1594_; 
lean_dec(v_a_1586_);
v_a_1594_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1591_, 1);
v___y_1551_ = v___y_1573_;
v___y_1552_ = v_a_1584_;
v___y_1553_ = v___y_1574_;
v___y_1554_ = v___y_1575_;
v___y_1555_ = v___y_1577_;
v___y_1556_ = v___y_1578_;
v___y_1557_ = v___y_1580_;
v_a_1558_ = v_a_1594_;
goto v___jp_1550_;
}
}
}
else
{
lean_object* v_a_1595_; 
v_a_1595_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1585_, 1);
v___y_1551_ = v___y_1573_;
v___y_1552_ = v_a_1584_;
v___y_1553_ = v___y_1574_;
v___y_1554_ = v___y_1575_;
v___y_1555_ = v___y_1577_;
v___y_1556_ = v___y_1578_;
v___y_1557_ = v___y_1580_;
v_a_1558_ = v_a_1595_;
goto v___jp_1550_;
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1574_);
lean_dec(v_matchDeclName_1405_);
v_a_1596_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1583_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1583_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1574_);
lean_dec(v_matchDeclName_1405_);
return v___x_1582_;
}
}
else
{
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1574_);
v___y_1433_ = v___y_1575_;
v___y_1434_ = v___y_1577_;
v___y_1435_ = v___y_1578_;
v___y_1436_ = v___y_1580_;
v___y_1437_ = v___y_1579_;
goto v___jp_1432_;
}
}
v___jp_1604_:
{
if (v___y_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_dec_ref(v___y_1606_);
v___x_1614_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1611_, v___y_1612_, v___y_1610_);
lean_dec_ref(v___y_1611_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v___x_1615_; 
lean_dec_ref_known(v___x_1614_, 1);
v___x_1615_ = l_Lean_Meta_saveState___redArg(v___y_1612_, v___y_1610_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
lean_inc(v___y_1607_);
v___x_1617_ = l_Lean_Meta_splitSparseCasesOn(v___y_1607_, v___y_1608_, v___y_1612_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_dec(v_a_1616_);
lean_dec(v___y_1607_);
v___y_1433_ = v___y_1608_;
v___y_1434_ = v___y_1609_;
v___y_1435_ = v___y_1610_;
v___y_1436_ = v___y_1612_;
v___y_1437_ = v___x_1617_;
goto v___jp_1432_;
}
else
{
lean_object* v_a_1618_; uint8_t v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
v___x_1619_ = l_Lean_Exception_isInterrupt(v_a_1618_);
if (v___x_1619_ == 0)
{
uint8_t v___x_1620_; 
v___x_1620_ = l_Lean_Exception_isRuntime(v_a_1618_);
v___y_1573_ = v___y_1605_;
v___y_1574_ = v___y_1607_;
v___y_1575_ = v___y_1608_;
v___y_1576_ = v_a_1616_;
v___y_1577_ = v___y_1609_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___x_1617_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___x_1620_;
goto v___jp_1572_;
}
else
{
lean_dec(v_a_1618_);
v___y_1573_ = v___y_1605_;
v___y_1574_ = v___y_1607_;
v___y_1575_ = v___y_1608_;
v___y_1576_ = v_a_1616_;
v___y_1577_ = v___y_1609_;
v___y_1578_ = v___y_1610_;
v___y_1579_ = v___x_1617_;
v___y_1580_ = v___y_1612_;
v___y_1581_ = v___x_1619_;
goto v___jp_1572_;
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1607_);
lean_dec(v_matchDeclName_1405_);
v_a_1621_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1615_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1615_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1607_);
lean_dec(v_matchDeclName_1405_);
return v___x_1614_;
}
}
else
{
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1607_);
v___y_1433_ = v___y_1608_;
v___y_1434_ = v___y_1609_;
v___y_1435_ = v___y_1610_;
v___y_1436_ = v___y_1612_;
v___y_1437_ = v___y_1606_;
goto v___jp_1432_;
}
}
v___jp_1629_:
{
if (v___y_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_dec_ref(v___y_1632_);
v___x_1639_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1636_, v___y_1637_, v___y_1635_);
lean_dec_ref(v___y_1636_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v___x_1640_; 
lean_dec_ref_known(v___x_1639_, 1);
v___x_1640_ = l_Lean_Meta_saveState___redArg(v___y_1637_, v___y_1635_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
lean_inc(v___y_1631_);
v___x_1642_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1631_, v___y_1633_, v___y_1637_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_dec(v_a_1641_);
lean_dec(v___y_1631_);
v___y_1433_ = v___y_1633_;
v___y_1434_ = v___y_1634_;
v___y_1435_ = v___y_1635_;
v___y_1436_ = v___y_1637_;
v___y_1437_ = v___x_1642_;
goto v___jp_1432_;
}
else
{
lean_object* v_a_1643_; uint8_t v___x_1644_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
v___x_1644_ = l_Lean_Exception_isInterrupt(v_a_1643_);
if (v___x_1644_ == 0)
{
uint8_t v___x_1645_; 
v___x_1645_ = l_Lean_Exception_isRuntime(v_a_1643_);
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___x_1642_;
v___y_1607_ = v___y_1631_;
v___y_1608_ = v___y_1633_;
v___y_1609_ = v___y_1634_;
v___y_1610_ = v___y_1635_;
v___y_1611_ = v_a_1641_;
v___y_1612_ = v___y_1637_;
v___y_1613_ = v___x_1645_;
goto v___jp_1604_;
}
else
{
lean_dec(v_a_1643_);
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___x_1642_;
v___y_1607_ = v___y_1631_;
v___y_1608_ = v___y_1633_;
v___y_1609_ = v___y_1634_;
v___y_1610_ = v___y_1635_;
v___y_1611_ = v_a_1641_;
v___y_1612_ = v___y_1637_;
v___y_1613_ = v___x_1644_;
goto v___jp_1604_;
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1631_);
lean_dec(v_matchDeclName_1405_);
v_a_1646_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1640_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1640_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1631_);
lean_dec(v_matchDeclName_1405_);
return v___x_1639_;
}
}
else
{
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1631_);
v___y_1433_ = v___y_1633_;
v___y_1434_ = v___y_1634_;
v___y_1435_ = v___y_1635_;
v___y_1436_ = v___y_1637_;
v___y_1437_ = v___y_1632_;
goto v___jp_1432_;
}
}
v___jp_1654_:
{
if (v___y_1663_ == 0)
{
lean_object* v___x_1664_; 
lean_dec_ref(v___y_1657_);
v___x_1664_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1660_, v___y_1662_, v___y_1661_);
lean_dec_ref(v___y_1660_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v___x_1665_; 
lean_dec_ref_known(v___x_1664_, 1);
v___x_1665_ = l_Lean_Meta_saveState___redArg(v___y_1662_, v___y_1661_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
lean_inc(v___y_1656_);
v___x_1667_ = l_Lean_Meta_casesOnStuckLHS(v___y_1656_, v___y_1658_, v___y_1662_, v___y_1659_, v___y_1661_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_dec(v_a_1666_);
lean_dec(v___y_1656_);
v___y_1433_ = v___y_1658_;
v___y_1434_ = v___y_1659_;
v___y_1435_ = v___y_1661_;
v___y_1436_ = v___y_1662_;
v___y_1437_ = v___x_1667_;
goto v___jp_1432_;
}
else
{
lean_object* v_a_1668_; uint8_t v___x_1669_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
v___x_1669_ = l_Lean_Exception_isInterrupt(v_a_1668_);
if (v___x_1669_ == 0)
{
uint8_t v___x_1670_; 
v___x_1670_ = l_Lean_Exception_isRuntime(v_a_1668_);
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___x_1667_;
v___y_1633_ = v___y_1658_;
v___y_1634_ = v___y_1659_;
v___y_1635_ = v___y_1661_;
v___y_1636_ = v_a_1666_;
v___y_1637_ = v___y_1662_;
v___y_1638_ = v___x_1670_;
goto v___jp_1629_;
}
else
{
lean_dec(v_a_1668_);
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___x_1667_;
v___y_1633_ = v___y_1658_;
v___y_1634_ = v___y_1659_;
v___y_1635_ = v___y_1661_;
v___y_1636_ = v_a_1666_;
v___y_1637_ = v___y_1662_;
v___y_1638_ = v___x_1669_;
goto v___jp_1629_;
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1656_);
lean_dec(v_matchDeclName_1405_);
v_a_1671_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1665_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1665_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1656_);
lean_dec(v_matchDeclName_1405_);
return v___x_1664_;
}
}
else
{
lean_object* v___x_1679_; 
lean_dec_ref(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1656_);
lean_dec(v_matchDeclName_1405_);
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v___y_1657_);
return v___x_1679_;
}
}
v___jp_1680_:
{
if (v___y_1689_ == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref(v___y_1682_);
v___x_1690_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1685_, v___y_1688_, v___y_1687_);
lean_dec_ref(v___y_1685_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; 
lean_dec_ref_known(v___x_1690_, 1);
v___x_1691_ = l_Lean_Meta_saveState___redArg(v___y_1688_, v___y_1687_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1693_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
lean_inc(v___y_1683_);
v___x_1693_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1683_, v___y_1684_, v___y_1688_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec(v_a_1692_);
lean_dec(v___y_1683_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1695_ = lean_unsigned_to_nat(1u);
v___x_1696_ = lean_mk_empty_array_with_capacity(v___x_1695_);
v___x_1697_ = lean_array_push(v___x_1696_, v_a_1694_);
v___y_1414_ = v___y_1684_;
v___y_1415_ = v___y_1686_;
v___y_1416_ = v___y_1687_;
v___y_1417_ = v___y_1688_;
v_a_1418_ = v___x_1697_;
goto v___jp_1413_;
}
else
{
lean_object* v_a_1698_; uint8_t v___x_1699_; 
v_a_1698_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1699_ = l_Lean_Exception_isInterrupt(v_a_1698_);
if (v___x_1699_ == 0)
{
uint8_t v___x_1700_; 
lean_inc(v_a_1698_);
v___x_1700_ = l_Lean_Exception_isRuntime(v_a_1698_);
v___y_1655_ = v___y_1681_;
v___y_1656_ = v___y_1683_;
v___y_1657_ = v_a_1698_;
v___y_1658_ = v___y_1684_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v_a_1692_;
v___y_1661_ = v___y_1687_;
v___y_1662_ = v___y_1688_;
v___y_1663_ = v___x_1700_;
goto v___jp_1654_;
}
else
{
v___y_1655_ = v___y_1681_;
v___y_1656_ = v___y_1683_;
v___y_1657_ = v_a_1698_;
v___y_1658_ = v___y_1684_;
v___y_1659_ = v___y_1686_;
v___y_1660_ = v_a_1692_;
v___y_1661_ = v___y_1687_;
v___y_1662_ = v___y_1688_;
v___y_1663_ = v___x_1699_;
goto v___jp_1654_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1683_);
lean_dec(v_matchDeclName_1405_);
v_a_1701_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1691_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1691_);
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
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1683_);
lean_dec(v_matchDeclName_1405_);
return v___x_1690_;
}
}
else
{
lean_dec_ref(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1683_);
lean_dec(v_matchDeclName_1405_);
return v___y_1682_;
}
}
v___jp_1709_:
{
if (v___y_1718_ == 0)
{
lean_object* v___x_1719_; 
lean_dec_ref(v___y_1713_);
v___x_1719_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1716_, v___y_1717_, v___y_1715_);
lean_dec_ref(v___y_1716_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec_ref_known(v___x_1719_, 1);
v___x_1720_ = lean_unsigned_to_nat(16u);
v___x_1721_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*1, v___y_1710_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*1 + 1, v___y_1710_);
lean_ctor_set_uint8(v___x_1721_, sizeof(void*)*1 + 2, v___y_1710_);
v___x_1722_ = l_Lean_Meta_saveState___redArg(v___y_1717_, v___y_1715_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
lean_inc(v___y_1711_);
v___x_1724_ = l_Lean_MVarId_contradiction(v___y_1711_, v___x_1721_, v___y_1712_, v___y_1717_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref_known(v___x_1724_, 1);
lean_dec(v_a_1723_);
lean_dec(v___y_1711_);
v___x_1725_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1414_ = v___y_1712_;
v___y_1415_ = v___y_1714_;
v___y_1416_ = v___y_1715_;
v___y_1417_ = v___y_1717_;
v_a_1418_ = v___x_1725_;
goto v___jp_1413_;
}
else
{
lean_object* v_a_1726_; uint8_t v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1726_);
v___x_1727_ = l_Lean_Exception_isInterrupt(v_a_1726_);
if (v___x_1727_ == 0)
{
uint8_t v___x_1728_; 
v___x_1728_ = l_Lean_Exception_isRuntime(v_a_1726_);
v___y_1681_ = v___y_1710_;
v___y_1682_ = v___x_1724_;
v___y_1683_ = v___y_1711_;
v___y_1684_ = v___y_1712_;
v___y_1685_ = v_a_1723_;
v___y_1686_ = v___y_1714_;
v___y_1687_ = v___y_1715_;
v___y_1688_ = v___y_1717_;
v___y_1689_ = v___x_1728_;
goto v___jp_1680_;
}
else
{
lean_dec(v_a_1726_);
v___y_1681_ = v___y_1710_;
v___y_1682_ = v___x_1724_;
v___y_1683_ = v___y_1711_;
v___y_1684_ = v___y_1712_;
v___y_1685_ = v_a_1723_;
v___y_1686_ = v___y_1714_;
v___y_1687_ = v___y_1715_;
v___y_1688_ = v___y_1717_;
v___y_1689_ = v___x_1727_;
goto v___jp_1680_;
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref_known(v___x_1721_, 1);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1711_);
lean_dec(v_matchDeclName_1405_);
v_a_1729_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1722_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1722_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1711_);
lean_dec(v_matchDeclName_1405_);
return v___x_1719_;
}
}
else
{
lean_dec_ref(v___y_1716_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1711_);
lean_dec(v_matchDeclName_1405_);
return v___y_1713_;
}
}
v___jp_1737_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1743_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1406_, v___x_1742_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1745_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v___x_1745_ = l_Lean_Meta_saveState___redArg(v___y_1739_, v___y_1741_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1747_ = 1;
lean_inc(v_a_1744_);
v___x_1748_ = l_Lean_MVarId_refl(v_a_1744_, v___x_1747_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v___x_1749_; 
lean_dec_ref_known(v___x_1748_, 1);
lean_dec(v_a_1746_);
lean_dec(v_a_1744_);
v___x_1749_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1414_ = v___y_1738_;
v___y_1415_ = v___y_1740_;
v___y_1416_ = v___y_1741_;
v___y_1417_ = v___y_1739_;
v_a_1418_ = v___x_1749_;
goto v___jp_1413_;
}
else
{
lean_object* v_a_1750_; uint8_t v___x_1751_; 
v_a_1750_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1750_);
v___x_1751_ = l_Lean_Exception_isInterrupt(v_a_1750_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; 
v___x_1752_ = l_Lean_Exception_isRuntime(v_a_1750_);
v___y_1710_ = v___x_1747_;
v___y_1711_ = v_a_1744_;
v___y_1712_ = v___y_1738_;
v___y_1713_ = v___x_1748_;
v___y_1714_ = v___y_1740_;
v___y_1715_ = v___y_1741_;
v___y_1716_ = v_a_1746_;
v___y_1717_ = v___y_1739_;
v___y_1718_ = v___x_1752_;
goto v___jp_1709_;
}
else
{
lean_dec(v_a_1750_);
v___y_1710_ = v___x_1747_;
v___y_1711_ = v_a_1744_;
v___y_1712_ = v___y_1738_;
v___y_1713_ = v___x_1748_;
v___y_1714_ = v___y_1740_;
v___y_1715_ = v___y_1741_;
v___y_1716_ = v_a_1746_;
v___y_1717_ = v___y_1739_;
v___y_1718_ = v___x_1751_;
goto v___jp_1709_;
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v_a_1744_);
lean_dec_ref(v___y_1740_);
lean_dec(v_matchDeclName_1405_);
v_a_1753_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1745_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1745_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v___y_1740_);
lean_dec(v_matchDeclName_1405_);
v_a_1761_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1743_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1743_);
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
v___jp_1786_:
{
if (v___y_1787_ == 0)
{
uint8_t v_hasTrace_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_hasTrace_1788_ = lean_ctor_get_uint8(v_options_1771_, sizeof(void*)*1);
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = lean_nat_add(v_currRecDepth_1772_, v___x_1789_);
lean_inc_ref(v_inheritedTraceOptions_1784_);
lean_inc(v_cancelTk_x3f_1782_);
lean_inc(v_currMacroScope_1780_);
lean_inc(v_quotContext_1779_);
lean_inc(v_maxHeartbeats_1778_);
lean_inc(v_initHeartbeats_1777_);
lean_inc(v_openDecls_1776_);
lean_inc(v_currNamespace_1775_);
lean_inc(v_ref_1774_);
lean_inc(v_maxRecDepth_1773_);
lean_inc_ref(v_options_1771_);
lean_inc_ref(v_fileMap_1770_);
lean_inc_ref(v_fileName_1769_);
v___x_1791_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1791_, 0, v_fileName_1769_);
lean_ctor_set(v___x_1791_, 1, v_fileMap_1770_);
lean_ctor_set(v___x_1791_, 2, v_options_1771_);
lean_ctor_set(v___x_1791_, 3, v___x_1790_);
lean_ctor_set(v___x_1791_, 4, v_maxRecDepth_1773_);
lean_ctor_set(v___x_1791_, 5, v_ref_1774_);
lean_ctor_set(v___x_1791_, 6, v_currNamespace_1775_);
lean_ctor_set(v___x_1791_, 7, v_openDecls_1776_);
lean_ctor_set(v___x_1791_, 8, v_initHeartbeats_1777_);
lean_ctor_set(v___x_1791_, 9, v_maxHeartbeats_1778_);
lean_ctor_set(v___x_1791_, 10, v_quotContext_1779_);
lean_ctor_set(v___x_1791_, 11, v_currMacroScope_1780_);
lean_ctor_set(v___x_1791_, 12, v_cancelTk_x3f_1782_);
lean_ctor_set(v___x_1791_, 13, v_inheritedTraceOptions_1784_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*14, v_diag_1781_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*14 + 1, v_suppressElabErrors_1783_);
if (v_hasTrace_1788_ == 0)
{
v___y_1738_ = v_a_1408_;
v___y_1739_ = v_a_1409_;
v___y_1740_ = v___x_1791_;
v___y_1741_ = v_a_1411_;
goto v___jp_1737_;
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1793_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1784_, v_options_1771_, v___x_1792_);
if (v___x_1793_ == 0)
{
v___y_1738_ = v_a_1408_;
v___y_1739_ = v_a_1409_;
v___y_1740_ = v___x_1791_;
v___y_1741_ = v_a_1411_;
goto v___jp_1737_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1406_);
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v_mvarId_1406_);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1794_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1785_, v___x_1796_, v_a_1408_, v_a_1409_, v___x_1791_, v_a_1411_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_dec_ref_known(v___x_1797_, 1);
v___y_1738_ = v_a_1408_;
v___y_1739_ = v_a_1409_;
v___y_1740_ = v___x_1791_;
v___y_1741_ = v_a_1411_;
goto v___jp_1737_;
}
else
{
lean_dec_ref_known(v___x_1791_, 14);
lean_dec(v_mvarId_1406_);
lean_dec(v_matchDeclName_1405_);
return v___x_1797_;
}
}
}
}
else
{
lean_object* v___x_1798_; 
lean_dec(v_mvarId_1406_);
lean_dec(v_matchDeclName_1405_);
lean_inc(v_ref_1774_);
v___x_1798_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1774_);
return v___x_1798_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1803_, lean_object* v_matchDeclName_1804_, lean_object* v_as_1805_, size_t v_i_1806_, size_t v_stop_1807_, lean_object* v_b_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
uint8_t v___x_1814_; 
v___x_1814_ = lean_usize_dec_eq(v_i_1806_, v_stop_1807_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1815_ = lean_array_uget_borrowed(v_as_1805_, v_i_1806_);
v___x_1816_ = lean_unsigned_to_nat(1u);
v___x_1817_ = lean_nat_add(v_depth_1803_, v___x_1816_);
lean_inc(v___x_1815_);
lean_inc(v_matchDeclName_1804_);
v___x_1818_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1804_, v___x_1815_, v___x_1817_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___x_1817_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; size_t v___x_1820_; size_t v___x_1821_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_add(v_i_1806_, v___x_1820_);
v_i_1806_ = v___x_1821_;
v_b_1808_ = v_a_1819_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1804_);
return v___x_1818_;
}
}
else
{
lean_object* v___x_1823_; 
lean_dec(v_matchDeclName_1804_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_b_1808_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1824_, lean_object* v_matchDeclName_1825_, lean_object* v_as_1826_, lean_object* v_i_1827_, lean_object* v_stop_1828_, lean_object* v_b_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
size_t v_i_boxed_1835_; size_t v_stop_boxed_1836_; lean_object* v_res_1837_; 
v_i_boxed_1835_ = lean_unbox_usize(v_i_1827_);
lean_dec(v_i_1827_);
v_stop_boxed_1836_ = lean_unbox_usize(v_stop_1828_);
lean_dec(v_stop_1828_);
v_res_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1824_, v_matchDeclName_1825_, v_as_1826_, v_i_boxed_1835_, v_stop_boxed_1836_, v_b_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec_ref(v_as_1826_);
lean_dec(v_depth_1824_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1838_, lean_object* v_mvarId_1839_, lean_object* v_depth_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1838_, v_mvarId_1839_, v_depth_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_depth_1840_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1847_, lean_object* v___y_1848_){
_start:
{
uint8_t v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = l_Lean_Expr_hasMVar(v_e_1847_);
v___x_1851_ = lean_bool_not(v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v_mctx_1853_; lean_object* v___x_1854_; lean_object* v_fst_1855_; lean_object* v_snd_1856_; lean_object* v___x_1857_; lean_object* v_cache_1858_; lean_object* v_zetaDeltaFVarIds_1859_; lean_object* v_postponed_1860_; lean_object* v_diag_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1870_; 
v___x_1852_ = lean_st_ref_get(v___y_1848_);
v_mctx_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc_ref(v_mctx_1853_);
lean_dec(v___x_1852_);
v___x_1854_ = l_Lean_instantiateMVarsCore(v_mctx_1853_, v_e_1847_);
v_fst_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_fst_1855_);
v_snd_1856_ = lean_ctor_get(v___x_1854_, 1);
lean_inc(v_snd_1856_);
lean_dec_ref(v___x_1854_);
v___x_1857_ = lean_st_ref_take(v___y_1848_);
v_cache_1858_ = lean_ctor_get(v___x_1857_, 1);
v_zetaDeltaFVarIds_1859_ = lean_ctor_get(v___x_1857_, 2);
v_postponed_1860_ = lean_ctor_get(v___x_1857_, 3);
v_diag_1861_ = lean_ctor_get(v___x_1857_, 4);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1870_ == 0)
{
lean_object* v_unused_1871_; 
v_unused_1871_ = lean_ctor_get(v___x_1857_, 0);
lean_dec(v_unused_1871_);
v___x_1863_ = v___x_1857_;
v_isShared_1864_ = v_isSharedCheck_1870_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_diag_1861_);
lean_inc(v_postponed_1860_);
lean_inc(v_zetaDeltaFVarIds_1859_);
lean_inc(v_cache_1858_);
lean_dec(v___x_1857_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1870_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v_snd_1856_);
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_snd_1856_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_cache_1858_);
lean_ctor_set(v_reuseFailAlloc_1869_, 2, v_zetaDeltaFVarIds_1859_);
lean_ctor_set(v_reuseFailAlloc_1869_, 3, v_postponed_1860_);
lean_ctor_set(v_reuseFailAlloc_1869_, 4, v_diag_1861_);
v___x_1866_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_st_ref_set(v___y_1848_, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_fst_1855_);
return v___x_1868_;
}
}
}
else
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_e_1847_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1873_, v___y_1874_);
lean_dec(v___y_1874_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1877_, v___y_1879_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1891_, lean_object* v_localInsts_1892_, lean_object* v_x_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1891_, v_localInsts_1892_, v_x_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_a_1908_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1899_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1899_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1916_, lean_object* v_localInsts_1917_, lean_object* v_x_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1916_, v_localInsts_1917_, v_x_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1925_, lean_object* v_lctx_1926_, lean_object* v_localInsts_1927_, lean_object* v_x_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1926_, v_localInsts_1927_, v_x_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1935_, lean_object* v_lctx_1936_, lean_object* v_localInsts_1937_, lean_object* v_x_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1935_, v_lctx_1936_, v_localInsts_1937_, v_x_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
return v_res_1944_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1945_, lean_object* v_x_1946_){
_start:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_name_eq(v_x_1946_, v_matchDeclName_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1948_, lean_object* v_x_1949_){
_start:
{
uint8_t v_res_1950_; lean_object* v_r_1951_; 
v_res_1950_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1948_, v_x_1949_);
lean_dec(v_x_1949_);
lean_dec(v_matchDeclName_1948_);
v_r_1951_ = lean_box(v_res_1950_);
return v_r_1951_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1952_, lean_object* v_a_1953_, lean_object* v_b_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
uint8_t v___x_1960_; 
v___x_1960_ = lean_nat_dec_lt(v_a_1953_, v_upperBound_1952_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_dec(v_a_1953_);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v_b_1954_);
return v___x_1961_;
}
else
{
uint8_t v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = 0;
v___x_1963_ = l_Lean_Meta_introSubstEq(v_b_1954_, v___x_1962_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v_snd_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v_snd_1965_ = lean_ctor_get(v_a_1964_, 1);
lean_inc(v_snd_1965_);
lean_dec(v_a_1964_);
v___x_1966_ = lean_unsigned_to_nat(1u);
v___x_1967_ = lean_nat_add(v_a_1953_, v___x_1966_);
lean_dec(v_a_1953_);
v_a_1953_ = v___x_1967_;
v_b_1954_ = v_snd_1965_;
goto _start;
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v_a_1953_);
v_a_1969_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1963_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1963_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1977_, lean_object* v_a_1978_, lean_object* v_b_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1977_, v_a_1978_, v_b_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v_upperBound_1977_);
return v_res_1985_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1988_ = l_Lean_stringToMessageData(v___x_1987_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1991_ = l_Lean_stringToMessageData(v___x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1992_, lean_object* v___f_1993_, lean_object* v_matchDeclName_1994_, lean_object* v___x_1995_, uint8_t v___x_1996_, lean_object* v_heqPos_1997_, lean_object* v_heqNum_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2155_; 
v___x_2004_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1992_, v___y_2000_);
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2155_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2155_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_box(0);
v___x_2010_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2005_, v___x_2009_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2154_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2154_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2154_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v_mvarId_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v_options_2079_; lean_object* v_inheritedTraceOptions_2080_; uint8_t v_hasTrace_2081_; lean_object* v___x_2082_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; 
v_options_2079_ = lean_ctor_get(v___y_2001_, 2);
v_inheritedTraceOptions_2080_ = lean_ctor_get(v___y_2001_, 13);
v_hasTrace_2081_ = lean_ctor_get_uint8(v_options_2079_, sizeof(void*)*1);
v___x_2082_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2081_ == 0)
{
v___y_2084_ = v___y_1999_;
v___y_2085_ = v___y_2000_;
v___y_2086_ = v___y_2001_;
v___y_2087_ = v___y_2002_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2139_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2140_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2080_, v_options_2079_, v___x_2139_);
if (v___x_2140_ == 0)
{
v___y_2084_ = v___y_1999_;
v___y_2085_ = v___y_2000_;
v___y_2086_ = v___y_2001_;
v___y_2087_ = v___y_2002_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2141_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2142_ = l_Lean_Expr_mvarId_x21(v_a_2011_);
v___x_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2141_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2082_, v___x_2144_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_dec_ref_known(v___x_2145_, 1);
v___y_2084_ = v___y_1999_;
v___y_2085_ = v___y_2000_;
v___y_2086_ = v___y_2001_;
v___y_2087_ = v___y_2002_;
goto v___jp_2083_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_del_object(v___x_2013_);
lean_dec(v_a_2011_);
lean_del_object(v___x_2007_);
lean_dec(v_heqPos_1997_);
lean_dec(v___x_1995_);
lean_dec(v_matchDeclName_1994_);
lean_dec_ref(v___f_1993_);
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
v___jp_2015_:
{
if (v___y_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_dec_ref(v___y_2021_);
lean_del_object(v___x_2013_);
v___x_2023_ = l_Lean_MVarId_deltaTarget(v___y_2019_, v___f_1993_, v___y_2017_, v___y_2020_, v___y_2016_, v___y_2018_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = l_Lean_MVarId_heqOfEq(v_a_2024_, v___y_2017_, v___y_2020_, v___y_2016_, v___y_2018_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1994_, v_a_2026_, v___x_1995_, v___y_2017_, v___y_2020_, v___y_2016_, v___y_2018_);
lean_dec(v___x_1995_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2028_; 
lean_dec_ref_known(v___x_2027_, 1);
v___x_2028_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2011_, v___y_2020_);
return v___x_2028_;
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_a_2011_);
v_a_2029_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2027_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2027_);
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
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_a_2011_);
lean_dec(v___x_1995_);
lean_dec(v_matchDeclName_1994_);
v_a_2037_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2025_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2025_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_2011_);
lean_dec(v___x_1995_);
lean_dec(v_matchDeclName_1994_);
v_a_2045_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2023_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2023_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v___x_2054_; 
lean_dec(v___y_2019_);
lean_dec(v_a_2011_);
lean_dec(v___x_1995_);
lean_dec(v_matchDeclName_1994_);
lean_dec_ref(v___f_1993_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 1);
lean_ctor_set(v___x_2013_, 0, v___y_2021_);
v___x_2054_ = v___x_2013_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___y_2021_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
v___jp_2056_:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_MVarId_intros(v_mvarId_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v_snd_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v_snd_2064_ = lean_ctor_get(v_a_2063_, 1);
lean_inc_n(v_snd_2064_, 2);
lean_dec(v_a_2063_);
v___x_2065_ = 1;
v___x_2066_ = l_Lean_MVarId_refl(v_snd_2064_, v___x_2065_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2067_; 
lean_dec_ref_known(v___x_2066_, 1);
lean_dec(v_snd_2064_);
lean_del_object(v___x_2013_);
lean_dec(v___x_1995_);
lean_dec(v_matchDeclName_1994_);
lean_dec_ref(v___f_1993_);
v___x_2067_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2011_, v___y_2059_);
return v___x_2067_;
}
else
{
lean_object* v_a_2068_; uint8_t v___x_2069_; 
v_a_2068_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2069_ = l_Lean_Exception_isInterrupt(v_a_2068_);
if (v___x_2069_ == 0)
{
uint8_t v___x_2070_; 
lean_inc(v_a_2068_);
v___x_2070_ = l_Lean_Exception_isRuntime(v_a_2068_);
v___y_2016_ = v___y_2060_;
v___y_2017_ = v___y_2058_;
v___y_2018_ = v___y_2061_;
v___y_2019_ = v_snd_2064_;
v___y_2020_ = v___y_2059_;
v___y_2021_ = v_a_2068_;
v___y_2022_ = v___x_2070_;
goto v___jp_2015_;
}
else
{
v___y_2016_ = v___y_2060_;
v___y_2017_ = v___y_2058_;
v___y_2018_ = v___y_2061_;
v___y_2019_ = v_snd_2064_;
v___y_2020_ = v___y_2059_;
v___y_2021_ = v_a_2068_;
v___y_2022_ = v___x_2069_;
goto v___jp_2015_;
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_del_object(v___x_2013_);
lean_dec(v_a_2011_);
lean_dec(v___x_1995_);
lean_dec(v_matchDeclName_1994_);
lean_dec_ref(v___f_1993_);
v_a_2071_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2062_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2062_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
v___jp_2083_:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Expr_mvarId_x21(v_a_2011_);
if (v___x_1996_ == 0)
{
lean_del_object(v___x_2007_);
lean_dec(v_heqPos_1997_);
v_mvarId_2057_ = v___x_2088_;
v___y_2058_ = v___y_2084_;
v___y_2059_ = v___y_2085_;
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2087_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = 0;
v___x_2091_ = l_Lean_Meta_introNCore(v___x_2088_, v_heqPos_1997_, v___x_2089_, v___x_2090_, v___x_2090_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v_snd_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2129_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v_snd_2093_ = lean_ctor_get(v_a_2092_, 1);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_a_2092_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; 
v_unused_2130_ = lean_ctor_get(v_a_2092_, 0);
lean_dec(v_unused_2130_);
v___x_2095_ = v_a_2092_;
v_isShared_2096_ = v_isSharedCheck_2129_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_snd_2093_);
lean_dec(v_a_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2129_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; 
lean_inc(v___x_1995_);
v___x_2097_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1998_, v___x_1995_, v_snd_2093_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_options_2098_; uint8_t v_hasTrace_2099_; 
v_options_2098_ = lean_ctor_get(v___y_2086_, 2);
v_hasTrace_2099_ = lean_ctor_get_uint8(v_options_2098_, sizeof(void*)*1);
if (v_hasTrace_2099_ == 0)
{
lean_object* v_a_2100_; 
lean_del_object(v___x_2095_);
lean_del_object(v___x_2007_);
v_a_2100_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2097_, 1);
v_mvarId_2057_ = v_a_2100_;
v___y_2058_ = v___y_2084_;
v___y_2059_ = v___y_2085_;
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2087_;
goto v___jp_2056_;
}
else
{
lean_object* v_a_2101_; lean_object* v_inheritedTraceOptions_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v_a_2101_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2097_, 1);
v_inheritedTraceOptions_2102_ = lean_ctor_get(v___y_2086_, 13);
v___x_2103_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2104_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2102_, v_options_2098_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_del_object(v___x_2095_);
lean_del_object(v___x_2007_);
v_mvarId_2057_ = v_a_2101_;
v___y_2058_ = v___y_2084_;
v___y_2059_ = v___y_2085_;
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2087_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2101_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set_tag(v___x_2007_, 1);
lean_ctor_set(v___x_2007_, 0, v_a_2101_);
v___x_2107_ = v___x_2007_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2101_);
v___x_2107_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 7);
lean_ctor_set(v___x_2095_, 1, v___x_2107_);
lean_ctor_set(v___x_2095_, 0, v___x_2105_);
v___x_2109_ = v___x_2095_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2082_, v___x_2109_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_dec_ref_known(v___x_2110_, 1);
v_mvarId_2057_ = v_a_2101_;
v___y_2058_ = v___y_2084_;
v___y_2059_ = v___y_2085_;
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2087_;
goto v___jp_2056_;
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_a_2101_);
lean_del_object(v___x_2013_);
lean_dec(v_a_2011_);
lean_dec(v___x_1995_);
lean_dec(v_matchDeclName_1994_);
lean_dec_ref(v___f_1993_);
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
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
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_del_object(v___x_2095_);
lean_del_object(v___x_2013_);
lean_dec(v_a_2011_);
lean_del_object(v___x_2007_);
lean_dec(v___x_1995_);
lean_dec(v_matchDeclName_1994_);
lean_dec_ref(v___f_1993_);
v_a_2121_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2097_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2097_);
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
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_del_object(v___x_2013_);
lean_dec(v_a_2011_);
lean_del_object(v___x_2007_);
lean_dec(v___x_1995_);
lean_dec(v_matchDeclName_1994_);
lean_dec_ref(v___f_1993_);
v_a_2131_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2091_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2091_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2007_);
lean_dec(v_heqPos_1997_);
lean_dec(v___x_1995_);
lean_dec(v_matchDeclName_1994_);
lean_dec_ref(v___f_1993_);
return v___x_2010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2156_, lean_object* v___f_2157_, lean_object* v_matchDeclName_2158_, lean_object* v___x_2159_, lean_object* v___x_2160_, lean_object* v_heqPos_2161_, lean_object* v_heqNum_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v___x_6053__boxed_2168_; lean_object* v_res_2169_; 
v___x_6053__boxed_2168_ = lean_unbox(v___x_2160_);
v_res_2169_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2156_, v___f_2157_, v_matchDeclName_2158_, v___x_2159_, v___x_6053__boxed_2168_, v_heqPos_2161_, v_heqNum_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v_heqNum_2162_);
return v_res_2169_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_unsigned_to_nat(32u);
v___x_2174_ = lean_mk_empty_array_with_capacity(v___x_2173_);
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2176_ = ((size_t)5ULL);
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = lean_unsigned_to_nat(32u);
v___x_2179_ = lean_mk_empty_array_with_capacity(v___x_2178_);
v___x_2180_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2181_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v___x_2179_);
lean_ctor_set(v___x_2181_, 2, v___x_2177_);
lean_ctor_set(v___x_2181_, 3, v___x_2177_);
lean_ctor_set_usize(v___x_2181_, 4, v___x_2176_);
return v___x_2181_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2182_ = lean_box(1);
v___x_2183_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2184_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v___x_2183_);
lean_ctor_set(v___x_2185_, 2, v___x_2182_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2188_, lean_object* v_type_2189_, lean_object* v_heqPos_2190_, lean_object* v_heqNum_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v___f_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; 
lean_inc(v_matchDeclName_2188_);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2197_, 0, v_matchDeclName_2188_);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2200_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2201_ = lean_nat_dec_lt(v___x_2198_, v_heqNum_2191_);
v___x_2202_ = lean_box(v___x_2201_);
v___f_2203_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2203_, 0, v_type_2189_);
lean_closure_set(v___f_2203_, 1, v___f_2197_);
lean_closure_set(v___f_2203_, 2, v_matchDeclName_2188_);
lean_closure_set(v___f_2203_, 3, v___x_2198_);
lean_closure_set(v___f_2203_, 4, v___x_2202_);
lean_closure_set(v___f_2203_, 5, v_heqPos_2190_);
lean_closure_set(v___f_2203_, 6, v_heqNum_2191_);
v___x_2204_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2199_, v___x_2200_, v___f_2203_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2205_, lean_object* v_type_2206_, lean_object* v_heqPos_2207_, lean_object* v_heqNum_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2205_, v_type_2206_, v_heqPos_2207_, v_heqNum_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2215_, lean_object* v_inst_2216_, lean_object* v_R_2217_, lean_object* v_a_2218_, lean_object* v_b_2219_, lean_object* v_c_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2215_, v_a_2218_, v_b_2219_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2227_, lean_object* v_inst_2228_, lean_object* v_R_2229_, lean_object* v_a_2230_, lean_object* v_b_2231_, lean_object* v_c_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2227_, v_inst_2228_, v_R_2229_, v_a_2230_, v_b_2231_, v_c_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v_upperBound_2227_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2239_, lean_object* v_b_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; 
lean_inc(v___y_2244_);
lean_inc_ref(v___y_2243_);
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
v___x_2246_ = lean_apply_6(v_k_2239_, v_b_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, lean_box(0));
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2247_, lean_object* v_b_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2247_, v_b_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2255_, uint8_t v_bi_2256_, lean_object* v_type_2257_, lean_object* v_k_2258_, uint8_t v_kind_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___f_2265_; lean_object* v___x_2266_; 
v___f_2265_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2265_, 0, v_k_2258_);
v___x_2266_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2255_, v_bi_2256_, v_type_2257_, v___f_2265_, v_kind_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_a_2275_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2266_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2266_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2283_, lean_object* v_bi_2284_, lean_object* v_type_2285_, lean_object* v_k_2286_, lean_object* v_kind_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
uint8_t v_bi_boxed_2293_; uint8_t v_kind_boxed_2294_; lean_object* v_res_2295_; 
v_bi_boxed_2293_ = lean_unbox(v_bi_2284_);
v_kind_boxed_2294_ = lean_unbox(v_kind_2287_);
v_res_2295_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2283_, v_bi_boxed_2293_, v_type_2285_, v_k_2286_, v_kind_boxed_2294_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2296_, lean_object* v_name_2297_, uint8_t v_bi_2298_, lean_object* v_type_2299_, lean_object* v_k_2300_, uint8_t v_kind_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2297_, v_bi_2298_, v_type_2299_, v_k_2300_, v_kind_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2308_, lean_object* v_name_2309_, lean_object* v_bi_2310_, lean_object* v_type_2311_, lean_object* v_k_2312_, lean_object* v_kind_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
uint8_t v_bi_boxed_2319_; uint8_t v_kind_boxed_2320_; lean_object* v_res_2321_; 
v_bi_boxed_2319_ = lean_unbox(v_bi_2310_);
v_kind_boxed_2320_ = lean_unbox(v_kind_2313_);
v_res_2321_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2308_, v_name_2309_, v_bi_boxed_2319_, v_type_2311_, v_k_2312_, v_kind_boxed_2320_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2322_, lean_object* v_altsNew_2323_, lean_object* v_discrs_2324_, lean_object* v_patterns_2325_, lean_object* v_alts_2326_, lean_object* v_k_2327_, lean_object* v_altNew_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2322_, v_altsNew_2323_, v_discrs_2324_, v_patterns_2325_, v_alts_2326_, v_k_2327_, v_altNew_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v_i_2322_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2335_, lean_object* v_patterns_2336_, lean_object* v_alts_2337_, lean_object* v_k_2338_, lean_object* v_i_2339_, lean_object* v_altsNew_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2346_ = lean_array_get_size(v_alts_2337_);
v___x_2347_ = lean_nat_dec_lt(v_i_2339_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec(v_i_2339_);
lean_dec_ref(v_alts_2337_);
lean_dec_ref(v_patterns_2336_);
lean_dec_ref(v_discrs_2335_);
lean_inc(v_a_2344_);
lean_inc_ref(v_a_2343_);
lean_inc(v_a_2342_);
lean_inc_ref(v_a_2341_);
v___x_2348_ = lean_apply_6(v_k_2338_, v_altsNew_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, lean_box(0));
return v___x_2348_;
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = lean_array_fget_borrowed(v_alts_2337_, v_i_2339_);
v___x_2350_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2349_, v_a_2341_, v_a_2343_, v_a_2344_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
lean_inc_ref(v_patterns_2336_);
lean_inc_ref(v_discrs_2335_);
v___f_2352_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2352_, 0, v_i_2339_);
lean_closure_set(v___f_2352_, 1, v_altsNew_2340_);
lean_closure_set(v___f_2352_, 2, v_discrs_2335_);
lean_closure_set(v___f_2352_, 3, v_patterns_2336_);
lean_closure_set(v___f_2352_, 4, v_alts_2337_);
lean_closure_set(v___f_2352_, 5, v_k_2338_);
v___x_2353_ = l_Lean_LocalDecl_type(v_a_2351_);
v___x_2354_ = l_Lean_Expr_replaceFVars(v___x_2353_, v_discrs_2335_, v_patterns_2336_);
lean_dec_ref(v_patterns_2336_);
lean_dec_ref(v_discrs_2335_);
lean_dec_ref(v___x_2353_);
v___x_2355_ = l_Lean_LocalDecl_userName(v_a_2351_);
v___x_2356_ = l_Lean_LocalDecl_binderInfo(v_a_2351_);
lean_dec(v_a_2351_);
v___x_2357_ = 0;
v___x_2358_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2355_, v___x_2356_, v___x_2354_, v___f_2352_, v___x_2357_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
return v___x_2358_;
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v_altsNew_2340_);
lean_dec(v_i_2339_);
lean_dec_ref(v_k_2338_);
lean_dec_ref(v_alts_2337_);
lean_dec_ref(v_patterns_2336_);
lean_dec_ref(v_discrs_2335_);
v_a_2359_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2350_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2350_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2367_, lean_object* v_altsNew_2368_, lean_object* v_discrs_2369_, lean_object* v_patterns_2370_, lean_object* v_alts_2371_, lean_object* v_k_2372_, lean_object* v_altNew_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2379_ = lean_unsigned_to_nat(1u);
v___x_2380_ = lean_nat_add(v_i_2367_, v___x_2379_);
v___x_2381_ = lean_array_push(v_altsNew_2368_, v_altNew_2373_);
v___x_2382_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2369_, v_patterns_2370_, v_alts_2371_, v_k_2372_, v___x_2380_, v___x_2381_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2383_, lean_object* v_patterns_2384_, lean_object* v_alts_2385_, lean_object* v_k_2386_, lean_object* v_i_2387_, lean_object* v_altsNew_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2383_, v_patterns_2384_, v_alts_2385_, v_k_2386_, v_i_2387_, v_altsNew_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2395_, lean_object* v_discrs_2396_, lean_object* v_patterns_2397_, lean_object* v_alts_2398_, lean_object* v_k_2399_, lean_object* v_i_2400_, lean_object* v_altsNew_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2396_, v_patterns_2397_, v_alts_2398_, v_k_2399_, v_i_2400_, v_altsNew_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2408_, lean_object* v_discrs_2409_, lean_object* v_patterns_2410_, lean_object* v_alts_2411_, lean_object* v_k_2412_, lean_object* v_i_2413_, lean_object* v_altsNew_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2408_, v_discrs_2409_, v_patterns_2410_, v_alts_2411_, v_k_2412_, v_i_2413_, v_altsNew_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2423_, lean_object* v_discrs_2424_, lean_object* v_patterns_2425_, lean_object* v_alts_2426_, lean_object* v_k_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2433_ = lean_unsigned_to_nat(0u);
v___x_2434_ = lean_nat_dec_eq(v_numDiscrEqs_2423_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2436_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2424_, v_patterns_2425_, v_alts_2426_, v_k_2427_, v___x_2433_, v___x_2435_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
return v___x_2436_;
}
else
{
lean_object* v___x_2437_; 
lean_dec_ref(v_patterns_2425_);
lean_dec_ref(v_discrs_2424_);
lean_inc(v_a_2431_);
lean_inc_ref(v_a_2430_);
lean_inc(v_a_2429_);
lean_inc_ref(v_a_2428_);
v___x_2437_ = lean_apply_6(v_k_2427_, v_alts_2426_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, lean_box(0));
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2438_, lean_object* v_discrs_2439_, lean_object* v_patterns_2440_, lean_object* v_alts_2441_, lean_object* v_k_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2438_, v_discrs_2439_, v_patterns_2440_, v_alts_2441_, v_k_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_numDiscrEqs_2438_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2449_, lean_object* v_numDiscrEqs_2450_, lean_object* v_discrs_2451_, lean_object* v_patterns_2452_, lean_object* v_alts_2453_, lean_object* v_k_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2450_, v_discrs_2451_, v_patterns_2452_, v_alts_2453_, v_k_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2461_, lean_object* v_numDiscrEqs_2462_, lean_object* v_discrs_2463_, lean_object* v_patterns_2464_, lean_object* v_alts_2465_, lean_object* v_k_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2461_, v_numDiscrEqs_2462_, v_discrs_2463_, v_patterns_2464_, v_alts_2465_, v_k_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_numDiscrEqs_2462_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(lean_object* v_declName_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; lean_object* v_env_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = lean_st_ref_get(v___y_2474_);
v_env_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_ref(v_env_2477_);
lean_dec(v___x_2476_);
v___x_2478_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2477_, v_declName_2473_);
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg___boxed(lean_object* v_declName_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2480_, v___y_2481_);
lean_dec(v___y_2481_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_declName_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2484_, v___y_2488_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___boxed(lean_object* v_declName_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v_declName_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___f_2505_; lean_object* v___x_14605__overap_2506_; lean_object* v___x_2507_; 
v___f_2505_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14605__overap_2506_ = lean_panic_fn_borrowed(v___f_2505_, v_msg_2499_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
v___x_2507_ = lean_apply_5(v___x_14605__overap_2506_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, lean_box(0));
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2515_, lean_object* v_b_2516_, lean_object* v_c_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; 
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2519_);
lean_inc_ref(v___y_2518_);
v___x_2523_ = lean_apply_7(v_k_2515_, v_b_2516_, v_c_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, lean_box(0));
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2524_, lean_object* v_b_2525_, lean_object* v_c_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2524_, v_b_2525_, v_c_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2533_, lean_object* v_k_2534_, uint8_t v_cleanupAnnotations_2535_, uint8_t v_whnfType_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___f_2542_; lean_object* v___x_2543_; 
v___f_2542_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2542_, 0, v_k_2534_);
v___x_2543_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2533_, v___f_2542_, v_cleanupAnnotations_2535_, v_whnfType_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
v_a_2552_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2543_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2543_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2560_, lean_object* v_k_2561_, lean_object* v_cleanupAnnotations_2562_, lean_object* v_whnfType_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2569_; uint8_t v_whnfType_boxed_2570_; lean_object* v_res_2571_; 
v_cleanupAnnotations_boxed_2569_ = lean_unbox(v_cleanupAnnotations_2562_);
v_whnfType_boxed_2570_ = lean_unbox(v_whnfType_2563_);
v_res_2571_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2560_, v_k_2561_, v_cleanupAnnotations_boxed_2569_, v_whnfType_boxed_2570_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2572_, lean_object* v_type_2573_, lean_object* v_k_2574_, uint8_t v_cleanupAnnotations_2575_, uint8_t v_whnfType_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2573_, v_k_2574_, v_cleanupAnnotations_2575_, v_whnfType_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2583_, lean_object* v_type_2584_, lean_object* v_k_2585_, lean_object* v_cleanupAnnotations_2586_, lean_object* v_whnfType_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2593_; uint8_t v_whnfType_boxed_2594_; lean_object* v_res_2595_; 
v_cleanupAnnotations_boxed_2593_ = lean_unbox(v_cleanupAnnotations_2586_);
v_whnfType_boxed_2594_ = lean_unbox(v_whnfType_2587_);
v_res_2595_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2583_, v_type_2584_, v_k_2585_, v_cleanupAnnotations_boxed_2593_, v_whnfType_boxed_2594_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2596_, lean_object* v_splitterName_2597_, lean_object* v_matcherInput_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_matchType_2604_; lean_object* v_discrInfos_2605_; lean_object* v_lhss_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2626_; 
v_matchType_2604_ = lean_ctor_get(v_matcherInput_2598_, 1);
v_discrInfos_2605_ = lean_ctor_get(v_matcherInput_2598_, 2);
v_lhss_2606_ = lean_ctor_get(v_matcherInput_2598_, 3);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_matcherInput_2598_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; lean_object* v_unused_2628_; 
v_unused_2627_ = lean_ctor_get(v_matcherInput_2598_, 4);
lean_dec(v_unused_2627_);
v_unused_2628_ = lean_ctor_get(v_matcherInput_2598_, 0);
lean_dec(v_unused_2628_);
v___x_2608_ = v_matcherInput_2598_;
v_isShared_2609_ = v_isSharedCheck_2626_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_lhss_2606_);
lean_inc(v_discrInfos_2605_);
lean_inc(v_matchType_2604_);
lean_dec(v_matcherInput_2598_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2626_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2610_, 0, v_overlaps_2596_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 4, v___x_2610_);
lean_ctor_set(v___x_2608_, 0, v_splitterName_2597_);
v___x_2612_ = v___x_2608_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_splitterName_2597_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_matchType_2604_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v_discrInfos_2605_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v_lhss_2606_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_Meta_Match_mkMatcher(v___x_2612_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v_addMatcher_2615_; lean_object* v___x_2616_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2613_, 1);
v_addMatcher_2615_ = lean_ctor_get(v_a_2614_, 3);
lean_inc_ref(v_addMatcher_2615_);
lean_dec(v_a_2614_);
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
v___x_2616_ = lean_apply_5(v_addMatcher_2615_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, lean_box(0));
return v___x_2616_;
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
v_a_2617_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2613_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2613_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2629_, lean_object* v_splitterName_2630_, lean_object* v_matcherInput_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2629_, v_splitterName_2630_, v_matcherInput_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
return v_res_2637_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2638_, lean_object* v_ys_2639_, lean_object* v_x_2640_){
_start:
{
lean_object* v_zero_2641_; uint8_t v_isZero_2642_; 
v_zero_2641_ = lean_unsigned_to_nat(0u);
v_isZero_2642_ = lean_nat_dec_eq(v_x_2640_, v_zero_2641_);
if (v_isZero_2642_ == 1)
{
lean_dec(v_x_2640_);
return v_isZero_2642_;
}
else
{
lean_object* v_one_2643_; lean_object* v_n_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v_one_2643_ = lean_unsigned_to_nat(1u);
v_n_2644_ = lean_nat_sub(v_x_2640_, v_one_2643_);
lean_dec(v_x_2640_);
v___x_2645_ = lean_array_fget_borrowed(v_xs_2638_, v_n_2644_);
v___x_2646_ = lean_array_fget_borrowed(v_ys_2639_, v_n_2644_);
v___x_2647_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_dec(v_n_2644_);
return v___x_2647_;
}
else
{
v_x_2640_ = v_n_2644_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2649_, lean_object* v_ys_2650_, lean_object* v_x_2651_){
_start:
{
uint8_t v_res_2652_; lean_object* v_r_2653_; 
v_res_2652_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2649_, v_ys_2650_, v_x_2651_);
lean_dec_ref(v_ys_2650_);
lean_dec_ref(v_xs_2649_);
v_r_2653_ = lean_box(v_res_2652_);
return v_r_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2654_, lean_object* v_b_2655_){
_start:
{
lean_object* v_array_2656_; lean_object* v_start_2657_; lean_object* v_stop_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2671_; 
v_array_2656_ = lean_ctor_get(v_a_2654_, 0);
v_start_2657_ = lean_ctor_get(v_a_2654_, 1);
v_stop_2658_ = lean_ctor_get(v_a_2654_, 2);
v_isSharedCheck_2671_ = !lean_is_exclusive(v_a_2654_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2660_ = v_a_2654_;
v_isShared_2661_ = v_isSharedCheck_2671_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_stop_2658_);
lean_inc(v_start_2657_);
lean_inc(v_array_2656_);
lean_dec(v_a_2654_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2671_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
uint8_t v___x_2662_; 
v___x_2662_ = lean_nat_dec_lt(v_start_2657_, v_stop_2658_);
if (v___x_2662_ == 0)
{
lean_del_object(v___x_2660_);
lean_dec(v_stop_2658_);
lean_dec(v_start_2657_);
lean_dec_ref(v_array_2656_);
return v_b_2655_;
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2663_ = lean_unsigned_to_nat(1u);
v___x_2664_ = lean_nat_add(v_start_2657_, v___x_2663_);
lean_inc_ref(v_array_2656_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___x_2664_);
v___x_2666_ = v___x_2660_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_array_2656_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_stop_2658_);
v___x_2666_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = lean_array_fget(v_array_2656_, v_start_2657_);
lean_dec(v_start_2657_);
lean_dec_ref(v_array_2656_);
v___x_2668_ = lean_array_push(v_b_2655_, v___x_2667_);
v_a_2654_ = v___x_2666_;
v_b_2655_ = v___x_2668_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2672_, size_t v_sz_2673_, size_t v_i_2674_, lean_object* v_b_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
uint8_t v___x_2681_; 
v___x_2681_ = lean_usize_dec_lt(v_i_2674_, v_sz_2673_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v_b_2675_);
return v___x_2682_;
}
else
{
lean_object* v_snd_2683_; lean_object* v_fst_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2736_; 
v_snd_2683_ = lean_ctor_get(v_b_2675_, 1);
v_fst_2684_ = lean_ctor_get(v_b_2675_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_b_2675_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2686_ = v_b_2675_;
v_isShared_2687_ = v_isSharedCheck_2736_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_snd_2683_);
lean_inc(v_fst_2684_);
lean_dec(v_b_2675_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2736_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_array_2688_; lean_object* v_start_2689_; lean_object* v_stop_2690_; uint8_t v___x_2691_; 
v_array_2688_ = lean_ctor_get(v_snd_2683_, 0);
v_start_2689_ = lean_ctor_get(v_snd_2683_, 1);
v_stop_2690_ = lean_ctor_get(v_snd_2683_, 2);
v___x_2691_ = lean_nat_dec_lt(v_start_2689_, v_stop_2690_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2693_; 
if (v_isShared_2687_ == 0)
{
v___x_2693_ = v___x_2686_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_fst_2684_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_snd_2683_);
v___x_2693_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
return v___x_2694_;
}
}
else
{
lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2732_; 
lean_inc(v_stop_2690_);
lean_inc(v_start_2689_);
lean_inc_ref(v_array_2688_);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_snd_2683_);
if (v_isSharedCheck_2732_ == 0)
{
lean_object* v_unused_2733_; lean_object* v_unused_2734_; lean_object* v_unused_2735_; 
v_unused_2733_ = lean_ctor_get(v_snd_2683_, 2);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_snd_2683_, 1);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_snd_2683_, 0);
lean_dec(v_unused_2735_);
v___x_2697_ = v_snd_2683_;
v_isShared_2698_ = v_isSharedCheck_2732_;
goto v_resetjp_2696_;
}
else
{
lean_dec(v_snd_2683_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2732_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v_a_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_a_2699_ = lean_array_uget_borrowed(v_as_2672_, v_i_2674_);
v___x_2700_ = lean_array_fget_borrowed(v_array_2688_, v_start_2689_);
lean_inc(v___x_2700_);
lean_inc(v_a_2699_);
v___x_2701_ = l_Lean_Meta_mkEqHEq(v_a_2699_, v___x_2700_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = l_Lean_mkArrow(v_a_2702_, v_fst_2684_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2705_ = lean_unsigned_to_nat(1u);
v___x_2706_ = lean_nat_add(v_start_2689_, v___x_2705_);
lean_dec(v_start_2689_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___x_2706_);
v___x_2708_ = v___x_2697_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_array_2688_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v_stop_2690_);
v___x_2708_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2710_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 1, v___x_2708_);
lean_ctor_set(v___x_2686_, 0, v_a_2704_);
v___x_2710_ = v___x_2686_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2704_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
size_t v___x_2711_; size_t v___x_2712_; 
v___x_2711_ = ((size_t)1ULL);
v___x_2712_ = lean_usize_add(v_i_2674_, v___x_2711_);
v_i_2674_ = v___x_2712_;
v_b_2675_ = v___x_2710_;
goto _start;
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_del_object(v___x_2697_);
lean_dec(v_stop_2690_);
lean_dec(v_start_2689_);
lean_dec_ref(v_array_2688_);
lean_del_object(v___x_2686_);
v_a_2716_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2703_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2703_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_del_object(v___x_2697_);
lean_dec(v_stop_2690_);
lean_dec(v_start_2689_);
lean_dec_ref(v_array_2688_);
lean_del_object(v___x_2686_);
lean_dec(v_fst_2684_);
v_a_2724_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2701_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2701_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2737_, lean_object* v_sz_2738_, lean_object* v_i_2739_, lean_object* v_b_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
size_t v_sz_boxed_2746_; size_t v_i_boxed_2747_; lean_object* v_res_2748_; 
v_sz_boxed_2746_ = lean_unbox_usize(v_sz_2738_);
lean_dec(v_sz_2738_);
v_i_boxed_2747_ = lean_unbox_usize(v_i_2739_);
lean_dec(v_i_2739_);
v_res_2748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2737_, v_sz_boxed_2746_, v_i_boxed_2747_, v_b_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec_ref(v_as_2737_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2749_, lean_object* v___x_2750_, lean_object* v_as_2751_, size_t v_sz_2752_, size_t v_i_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_usize_dec_lt(v_i_2753_, v_sz_2752_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2761_, 0, v_b_2754_);
return v___x_2761_;
}
else
{
lean_object* v___x_2762_; lean_object* v_a_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2762_ = l_Lean_instInhabitedExpr;
v_a_2763_ = lean_array_uget_borrowed(v_as_2751_, v_i_2753_);
v___x_2764_ = lean_array_get_borrowed(v___x_2762_, v___x_2749_, v_a_2763_);
lean_inc(v___x_2764_);
v___x_2765_ = l_Lean_Meta_instantiateForall(v___x_2764_, v___x_2750_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
v___x_2767_ = lean_array_get_size(v___x_2750_);
v___x_2768_ = l_Lean_Meta_Match_simpH_x3f(v_a_2766_, v___x_2767_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v_a_2771_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2768_, 1);
if (lean_obj_tag(v_a_2769_) == 1)
{
lean_object* v_val_2775_; lean_object* v___x_2776_; 
v_val_2775_ = lean_ctor_get(v_a_2769_, 0);
lean_inc(v_val_2775_);
lean_dec_ref_known(v_a_2769_, 1);
v___x_2776_ = lean_array_push(v_b_2754_, v_val_2775_);
v_a_2771_ = v___x_2776_;
goto v___jp_2770_;
}
else
{
lean_dec(v_a_2769_);
v_a_2771_ = v_b_2754_;
goto v___jp_2770_;
}
v___jp_2770_:
{
size_t v___x_2772_; size_t v___x_2773_; 
v___x_2772_ = ((size_t)1ULL);
v___x_2773_ = lean_usize_add(v_i_2753_, v___x_2772_);
v_i_2753_ = v___x_2773_;
v_b_2754_ = v_a_2771_;
goto _start;
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref(v_b_2754_);
v_a_2777_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2768_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2768_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec_ref(v_b_2754_);
v_a_2785_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2765_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2765_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2793_, lean_object* v___x_2794_, lean_object* v_as_2795_, lean_object* v_sz_2796_, lean_object* v_i_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
size_t v_sz_boxed_2804_; size_t v_i_boxed_2805_; lean_object* v_res_2806_; 
v_sz_boxed_2804_ = lean_unbox_usize(v_sz_2796_);
lean_dec(v_sz_2796_);
v_i_boxed_2805_ = lean_unbox_usize(v_i_2797_);
lean_dec(v_i_2797_);
v_res_2806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2793_, v___x_2794_, v_as_2795_, v_sz_boxed_2804_, v_i_boxed_2805_, v_b_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec_ref(v_as_2795_);
lean_dec_ref(v___x_2794_);
lean_dec_ref(v___x_2793_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v___x_2810_, lean_object* v___x_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v_rhsArgs_2815_, lean_object* v_a_2816_, lean_object* v_ys_2817_, uint8_t v___x_2818_, uint8_t v___x_2819_, uint8_t v___x_2820_, lean_object* v_matchDeclName_2821_, lean_object* v___x_2822_, lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v___x_2826_, lean_object* v_argMask_2827_, lean_object* v_a_2828_, lean_object* v_alts_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2835_ = lean_array_get_borrowed(v___x_2807_, v_alts_2829_, v_a_2808_);
v___x_2836_ = l_Lean_ConstantInfo_name(v_a_2809_);
v___x_2837_ = l_Lean_mkConst(v___x_2836_, v___x_2810_);
v___x_2838_ = l_Subarray_copy___redArg(v___x_2811_);
v___x_2839_ = lean_mk_empty_array_with_capacity(v___x_2812_);
v___x_2840_ = lean_array_push(v___x_2839_, v___x_2813_);
v___x_2841_ = l_Array_append___redArg(v___x_2838_, v___x_2840_);
lean_dec_ref(v___x_2840_);
lean_inc_ref(v___x_2841_);
v___x_2842_ = l_Array_append___redArg(v___x_2841_, v___x_2814_);
v___x_2843_ = l_Array_append___redArg(v___x_2842_, v_alts_2829_);
v___x_2844_ = l_Lean_mkAppN(v___x_2837_, v___x_2843_);
lean_dec_ref(v___x_2843_);
lean_inc(v___x_2835_);
v___x_2845_ = l_Lean_mkAppN(v___x_2835_, v_rhsArgs_2815_);
v___x_2846_ = l_Lean_Meta_mkEq(v___x_2844_, v___x_2845_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = l_Lean_mkArrowN(v_a_2816_, v_a_2847_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v___x_2850_ = l_Array_append___redArg(v___x_2841_, v_ys_2817_);
v___x_2851_ = l_Array_append___redArg(v___x_2850_, v_alts_2829_);
v___x_2852_ = l_Lean_Meta_mkForallFVars(v___x_2851_, v_a_2849_, v___x_2818_, v___x_2819_, v___x_2819_, v___x_2820_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
lean_dec_ref(v___x_2851_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2853_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc_n(v_a_2855_, 2);
lean_dec_ref_known(v___x_2854_, 1);
lean_inc(v___x_2822_);
v___x_2856_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2821_, v_a_2855_, v___x_2822_, v___x_2822_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2856_, 1);
lean_inc(v___x_2823_);
v___x_2858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2823_);
lean_ctor_set(v___x_2858_, 1, v___x_2824_);
lean_ctor_set(v___x_2858_, 2, v_a_2855_);
v___x_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2823_);
lean_ctor_set(v___x_2859_, 1, v___x_2825_);
v___x_2860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2858_);
lean_ctor_set(v___x_2860_, 1, v_a_2857_);
lean_ctor_set(v___x_2860_, 2, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
v___x_2862_ = l_Lean_addDecl(v___x_2861_, v___x_2818_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2871_; 
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; 
v_unused_2872_ = lean_ctor_get(v___x_2862_, 0);
lean_dec(v_unused_2872_);
v___x_2864_ = v___x_2862_;
v_isShared_2865_ = v_isSharedCheck_2871_;
goto v_resetjp_2863_;
}
else
{
lean_dec(v___x_2862_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2871_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2826_);
lean_ctor_set(v___x_2866_, 1, v_argMask_2827_);
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v_a_2828_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2867_);
v___x_2869_ = v___x_2864_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec_ref(v_a_2828_);
lean_dec_ref(v_argMask_2827_);
lean_dec_ref(v___x_2826_);
v_a_2873_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2862_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2862_);
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
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2828_);
lean_dec_ref(v_argMask_2827_);
lean_dec_ref(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v___x_2824_);
lean_dec(v___x_2823_);
v_a_2881_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2856_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2856_);
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
lean_dec_ref(v_a_2828_);
lean_dec_ref(v_argMask_2827_);
lean_dec_ref(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v___x_2824_);
lean_dec(v___x_2823_);
lean_dec(v___x_2822_);
lean_dec(v_matchDeclName_2821_);
v_a_2889_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2854_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2854_);
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
lean_dec_ref(v_a_2828_);
lean_dec_ref(v_argMask_2827_);
lean_dec_ref(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v___x_2824_);
lean_dec(v___x_2823_);
lean_dec(v___x_2822_);
lean_dec(v_matchDeclName_2821_);
v_a_2897_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2852_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2852_);
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
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec_ref(v___x_2841_);
lean_dec_ref(v_a_2828_);
lean_dec_ref(v_argMask_2827_);
lean_dec_ref(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v___x_2824_);
lean_dec(v___x_2823_);
lean_dec(v___x_2822_);
lean_dec(v_matchDeclName_2821_);
v_a_2905_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2848_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2848_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v___x_2841_);
lean_dec_ref(v_a_2828_);
lean_dec_ref(v_argMask_2827_);
lean_dec_ref(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v___x_2824_);
lean_dec(v___x_2823_);
lean_dec(v___x_2822_);
lean_dec(v_matchDeclName_2821_);
v_a_2913_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2846_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2846_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2921_ = _args[0];
lean_object* v_a_2922_ = _args[1];
lean_object* v_a_2923_ = _args[2];
lean_object* v___x_2924_ = _args[3];
lean_object* v___x_2925_ = _args[4];
lean_object* v___x_2926_ = _args[5];
lean_object* v___x_2927_ = _args[6];
lean_object* v___x_2928_ = _args[7];
lean_object* v_rhsArgs_2929_ = _args[8];
lean_object* v_a_2930_ = _args[9];
lean_object* v_ys_2931_ = _args[10];
lean_object* v___x_2932_ = _args[11];
lean_object* v___x_2933_ = _args[12];
lean_object* v___x_2934_ = _args[13];
lean_object* v_matchDeclName_2935_ = _args[14];
lean_object* v___x_2936_ = _args[15];
lean_object* v___x_2937_ = _args[16];
lean_object* v___x_2938_ = _args[17];
lean_object* v___x_2939_ = _args[18];
lean_object* v___x_2940_ = _args[19];
lean_object* v_argMask_2941_ = _args[20];
lean_object* v_a_2942_ = _args[21];
lean_object* v_alts_2943_ = _args[22];
lean_object* v___y_2944_ = _args[23];
lean_object* v___y_2945_ = _args[24];
lean_object* v___y_2946_ = _args[25];
lean_object* v___y_2947_ = _args[26];
lean_object* v___y_2948_ = _args[27];
_start:
{
uint8_t v___x_18839__boxed_2949_; uint8_t v___x_18840__boxed_2950_; uint8_t v___x_18841__boxed_2951_; lean_object* v_res_2952_; 
v___x_18839__boxed_2949_ = lean_unbox(v___x_2932_);
v___x_18840__boxed_2950_ = lean_unbox(v___x_2933_);
v___x_18841__boxed_2951_ = lean_unbox(v___x_2934_);
v_res_2952_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2921_, v_a_2922_, v_a_2923_, v___x_2924_, v___x_2925_, v___x_2926_, v___x_2927_, v___x_2928_, v_rhsArgs_2929_, v_a_2930_, v_ys_2931_, v___x_18839__boxed_2949_, v___x_18840__boxed_2950_, v___x_18841__boxed_2951_, v_matchDeclName_2935_, v___x_2936_, v___x_2937_, v___x_2938_, v___x_2939_, v___x_2940_, v_argMask_2941_, v_a_2942_, v_alts_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v_alts_2943_);
lean_dec_ref(v_ys_2931_);
lean_dec_ref(v_a_2930_);
lean_dec_ref(v_rhsArgs_2929_);
lean_dec_ref(v___x_2928_);
lean_dec(v___x_2926_);
lean_dec_ref(v_a_2923_);
lean_dec(v_a_2922_);
lean_dec_ref(v___x_2921_);
return v_res_2952_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2953_; lean_object* v_dummy_2954_; 
v___x_2953_ = lean_box(0);
v_dummy_2954_ = l_Lean_Expr_sort___override(v___x_2953_);
return v_dummy_2954_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = lean_box(0);
v___x_2959_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_2960_ = l_Lean_mkConst(v___x_2959_, v___x_2958_);
return v___x_2960_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_2963_ = l_Lean_stringToMessageData(v___x_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_2964_, lean_object* v_overlaps_2965_, lean_object* v_a_2966_, lean_object* v_fst_2967_, lean_object* v___x_2968_, lean_object* v___x_2969_, lean_object* v___x_2970_, uint8_t v___x_2971_, lean_object* v___x_2972_, lean_object* v_a_2973_, lean_object* v___x_2974_, lean_object* v___x_2975_, lean_object* v___x_2976_, lean_object* v_matchDeclName_2977_, lean_object* v___x_2978_, lean_object* v___x_2979_, lean_object* v___x_2980_, lean_object* v___x_2981_, lean_object* v___x_2982_, lean_object* v_ys_2983_, lean_object* v___eqs_2984_, lean_object* v_rhsArgs_2985_, lean_object* v_argMask_2986_, lean_object* v_altResultType_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_dummy_2993_; lean_object* v_nargs_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; size_t v_sz_2999_; size_t v___x_3000_; lean_object* v___x_3001_; 
v_dummy_2993_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_2994_ = l_Lean_Expr_getAppNumArgs(v_altResultType_2987_);
lean_inc(v_nargs_2994_);
v___x_2995_ = lean_mk_array(v_nargs_2994_, v_dummy_2993_);
v___x_2996_ = lean_nat_sub(v_nargs_2994_, v___x_2964_);
lean_dec(v_nargs_2994_);
v___x_2997_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_2987_, v___x_2995_, v___x_2996_);
v___x_2998_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_2965_, v_a_2966_);
v_sz_2999_ = lean_array_size(v___x_2998_);
v___x_3000_ = ((size_t)0ULL);
lean_inc_ref(v___x_2968_);
v___x_3001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_2967_, v___x_2997_, v___x_2998_, v_sz_2999_, v___x_3000_, v___x_2968_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec_ref(v___x_2998_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; uint8_t v___y_3008_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; uint8_t v___y_3056_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v_options_3067_; uint8_t v_hasTrace_3068_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v_options_3067_ = lean_ctor_get(v___y_2990_, 2);
v_hasTrace_3068_ = lean_ctor_get_uint8(v_options_3067_, sizeof(void*)*1);
if (v_hasTrace_3068_ == 0)
{
v___y_3059_ = v___y_2988_;
v___y_3060_ = v___y_2989_;
v___y_3061_ = v___y_2990_;
v___y_3062_ = v___y_2991_;
goto v___jp_3058_;
}
else
{
lean_object* v_inheritedTraceOptions_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; 
v_inheritedTraceOptions_3069_ = lean_ctor_get(v___y_2990_, 13);
v___x_3070_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3071_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_3072_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3069_, v_options_3067_, v___x_3071_);
if (v___x_3072_ == 0)
{
v___y_3059_ = v___y_2988_;
v___y_3060_ = v___y_2989_;
v___y_3061_ = v___y_2990_;
v___y_3062_ = v___y_2991_;
goto v___jp_3058_;
}
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3073_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_3002_);
v___x_3074_ = lean_array_to_list(v_a_3002_);
v___x_3075_ = lean_box(0);
v___x_3076_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3074_, v___x_3075_);
v___x_3077_ = l_Lean_MessageData_ofList(v___x_3076_);
v___x_3078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3073_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3070_, v___x_3078_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_dec_ref_known(v___x_3079_, 1);
v___y_3059_ = v___y_2988_;
v___y_3060_ = v___y_2989_;
v___y_3061_ = v___y_2990_;
v___y_3062_ = v___y_2991_;
goto v___jp_3058_;
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v_a_3002_);
lean_dec_ref(v___x_2997_);
lean_dec_ref(v_argMask_2986_);
lean_dec_ref(v_rhsArgs_2985_);
lean_dec_ref(v_ys_2983_);
lean_dec_ref(v___x_2981_);
lean_dec(v___x_2980_);
lean_dec(v___x_2979_);
lean_dec(v___x_2978_);
lean_dec(v_matchDeclName_2977_);
lean_dec_ref(v___x_2976_);
lean_dec_ref(v___x_2975_);
lean_dec(v___x_2974_);
lean_dec_ref(v_a_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec_ref(v___x_2968_);
lean_dec(v_a_2966_);
lean_dec(v___x_2964_);
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3079_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3079_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
v___jp_3003_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; size_t v_sz_3016_; lean_object* v___x_3017_; 
v___x_3009_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2997_);
v___x_3010_ = l_Array_reverse___redArg(v___x_2997_);
v___x_3011_ = lean_array_get_size(v___x_3010_);
lean_inc(v___x_2969_);
v___x_3012_ = l_Array_toSubarray___redArg(v___x_3010_, v___x_2969_, v___x_3011_);
lean_inc_ref(v___x_2970_);
v___x_3013_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2970_, v___x_2968_);
v___x_3014_ = l_Array_reverse___redArg(v___x_3013_);
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3009_);
lean_ctor_set(v___x_3015_, 1, v___x_3012_);
v_sz_3016_ = lean_array_size(v___x_3014_);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3014_, v_sz_3016_, v___x_3000_, v___x_3015_, v___y_3004_, v___y_3006_, v___y_3005_, v___y_3007_);
lean_dec_ref(v___x_3014_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v_fst_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; uint8_t v___x_3023_; lean_object* v___x_3024_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v_fst_3019_ = lean_ctor_get(v_a_3018_, 0);
lean_inc(v_fst_3019_);
lean_dec(v_a_3018_);
v___x_3020_ = l_Subarray_copy___redArg(v___x_2970_);
lean_inc_ref(v___x_3020_);
v___x_3021_ = l_Array_append___redArg(v___x_3020_, v_ys_2983_);
v___x_3022_ = 0;
v___x_3023_ = 1;
v___x_3024_ = l_Lean_Meta_mkForallFVars(v___x_3021_, v_fst_3019_, v___x_3022_, v___x_2971_, v___x_2971_, v___x_3023_, v___y_3004_, v___y_3006_, v___y_3005_, v___y_3007_);
lean_dec_ref(v___x_3021_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___f_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = lean_array_get_size(v_ys_2983_);
v___x_3027_ = lean_array_get_size(v_a_3002_);
v___x_3028_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3028_, 0, v___x_3026_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*2, v___y_3008_);
v___x_3029_ = lean_box(v___x_3022_);
v___x_3030_ = lean_box(v___x_2971_);
v___x_3031_ = lean_box(v___x_3023_);
lean_inc_ref(v___x_2997_);
v___f_3032_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_3032_, 0, v___x_2972_);
lean_closure_set(v___f_3032_, 1, v_a_2966_);
lean_closure_set(v___f_3032_, 2, v_a_2973_);
lean_closure_set(v___f_3032_, 3, v___x_2974_);
lean_closure_set(v___f_3032_, 4, v___x_2975_);
lean_closure_set(v___f_3032_, 5, v___x_2964_);
lean_closure_set(v___f_3032_, 6, v___x_2976_);
lean_closure_set(v___f_3032_, 7, v___x_2997_);
lean_closure_set(v___f_3032_, 8, v_rhsArgs_2985_);
lean_closure_set(v___f_3032_, 9, v_a_3002_);
lean_closure_set(v___f_3032_, 10, v_ys_2983_);
lean_closure_set(v___f_3032_, 11, v___x_3029_);
lean_closure_set(v___f_3032_, 12, v___x_3030_);
lean_closure_set(v___f_3032_, 13, v___x_3031_);
lean_closure_set(v___f_3032_, 14, v_matchDeclName_2977_);
lean_closure_set(v___f_3032_, 15, v___x_2969_);
lean_closure_set(v___f_3032_, 16, v___x_2978_);
lean_closure_set(v___f_3032_, 17, v___x_2979_);
lean_closure_set(v___f_3032_, 18, v___x_2980_);
lean_closure_set(v___f_3032_, 19, v___x_3028_);
lean_closure_set(v___f_3032_, 20, v_argMask_2986_);
lean_closure_set(v___f_3032_, 21, v_a_3025_);
v___x_3033_ = l_Subarray_copy___redArg(v___x_2981_);
v___x_3034_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2982_, v___x_3020_, v___x_2997_, v___x_3033_, v___f_3032_, v___y_3004_, v___y_3006_, v___y_3005_, v___y_3007_);
return v___x_3034_;
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec_ref(v___x_3020_);
lean_dec(v_a_3002_);
lean_dec_ref(v___x_2997_);
lean_dec_ref(v_argMask_2986_);
lean_dec_ref(v_rhsArgs_2985_);
lean_dec_ref(v_ys_2983_);
lean_dec_ref(v___x_2981_);
lean_dec(v___x_2980_);
lean_dec(v___x_2979_);
lean_dec(v___x_2978_);
lean_dec(v_matchDeclName_2977_);
lean_dec_ref(v___x_2976_);
lean_dec_ref(v___x_2975_);
lean_dec(v___x_2974_);
lean_dec_ref(v_a_2973_);
lean_dec_ref(v___x_2972_);
lean_dec(v___x_2969_);
lean_dec(v_a_2966_);
lean_dec(v___x_2964_);
v_a_3035_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3024_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3024_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v_a_3002_);
lean_dec_ref(v___x_2997_);
lean_dec_ref(v_argMask_2986_);
lean_dec_ref(v_rhsArgs_2985_);
lean_dec_ref(v_ys_2983_);
lean_dec_ref(v___x_2981_);
lean_dec(v___x_2980_);
lean_dec(v___x_2979_);
lean_dec(v___x_2978_);
lean_dec(v_matchDeclName_2977_);
lean_dec_ref(v___x_2976_);
lean_dec_ref(v___x_2975_);
lean_dec(v___x_2974_);
lean_dec_ref(v_a_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v_a_2966_);
lean_dec(v___x_2964_);
v_a_3043_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3017_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3017_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
v___jp_3051_:
{
if (v___y_3056_ == 0)
{
v___y_3004_ = v___y_3052_;
v___y_3005_ = v___y_3053_;
v___y_3006_ = v___y_3054_;
v___y_3007_ = v___y_3055_;
v___y_3008_ = v___y_3056_;
goto v___jp_3003_;
}
else
{
uint8_t v___x_3057_; 
v___x_3057_ = lean_nat_dec_eq(v___x_2982_, v___x_2969_);
v___y_3004_ = v___y_3052_;
v___y_3005_ = v___y_3053_;
v___y_3006_ = v___y_3054_;
v___y_3007_ = v___y_3055_;
v___y_3008_ = v___x_3057_;
goto v___jp_3003_;
}
}
v___jp_3058_:
{
lean_object* v___x_3063_; uint8_t v___x_3064_; 
v___x_3063_ = lean_array_get_size(v_ys_2983_);
v___x_3064_ = lean_nat_dec_eq(v___x_3063_, v___x_2969_);
if (v___x_3064_ == 0)
{
v___y_3052_ = v___y_3059_;
v___y_3053_ = v___y_3061_;
v___y_3054_ = v___y_3060_;
v___y_3055_ = v___y_3062_;
v___y_3056_ = v___x_3064_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3065_; uint8_t v___x_3066_; 
v___x_3065_ = lean_array_get_size(v_a_3002_);
v___x_3066_ = lean_nat_dec_eq(v___x_3065_, v___x_2969_);
v___y_3052_ = v___y_3059_;
v___y_3053_ = v___y_3061_;
v___y_3054_ = v___y_3060_;
v___y_3055_ = v___y_3062_;
v___y_3056_ = v___x_3066_;
goto v___jp_3051_;
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec_ref(v___x_2997_);
lean_dec_ref(v_argMask_2986_);
lean_dec_ref(v_rhsArgs_2985_);
lean_dec_ref(v_ys_2983_);
lean_dec_ref(v___x_2981_);
lean_dec(v___x_2980_);
lean_dec(v___x_2979_);
lean_dec(v___x_2978_);
lean_dec(v_matchDeclName_2977_);
lean_dec_ref(v___x_2976_);
lean_dec_ref(v___x_2975_);
lean_dec(v___x_2974_);
lean_dec_ref(v_a_2973_);
lean_dec_ref(v___x_2972_);
lean_dec_ref(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec_ref(v___x_2968_);
lean_dec(v_a_2966_);
lean_dec(v___x_2964_);
v_a_3088_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3001_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3001_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3096_ = _args[0];
lean_object* v_overlaps_3097_ = _args[1];
lean_object* v_a_3098_ = _args[2];
lean_object* v_fst_3099_ = _args[3];
lean_object* v___x_3100_ = _args[4];
lean_object* v___x_3101_ = _args[5];
lean_object* v___x_3102_ = _args[6];
lean_object* v___x_3103_ = _args[7];
lean_object* v___x_3104_ = _args[8];
lean_object* v_a_3105_ = _args[9];
lean_object* v___x_3106_ = _args[10];
lean_object* v___x_3107_ = _args[11];
lean_object* v___x_3108_ = _args[12];
lean_object* v_matchDeclName_3109_ = _args[13];
lean_object* v___x_3110_ = _args[14];
lean_object* v___x_3111_ = _args[15];
lean_object* v___x_3112_ = _args[16];
lean_object* v___x_3113_ = _args[17];
lean_object* v___x_3114_ = _args[18];
lean_object* v_ys_3115_ = _args[19];
lean_object* v___eqs_3116_ = _args[20];
lean_object* v_rhsArgs_3117_ = _args[21];
lean_object* v_argMask_3118_ = _args[22];
lean_object* v_altResultType_3119_ = _args[23];
lean_object* v___y_3120_ = _args[24];
lean_object* v___y_3121_ = _args[25];
lean_object* v___y_3122_ = _args[26];
lean_object* v___y_3123_ = _args[27];
lean_object* v___y_3124_ = _args[28];
_start:
{
uint8_t v___x_19107__boxed_3125_; lean_object* v_res_3126_; 
v___x_19107__boxed_3125_ = lean_unbox(v___x_3103_);
v_res_3126_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3096_, v_overlaps_3097_, v_a_3098_, v_fst_3099_, v___x_3100_, v___x_3101_, v___x_3102_, v___x_19107__boxed_3125_, v___x_3104_, v_a_3105_, v___x_3106_, v___x_3107_, v___x_3108_, v_matchDeclName_3109_, v___x_3110_, v___x_3111_, v___x_3112_, v___x_3113_, v___x_3114_, v_ys_3115_, v___eqs_3116_, v_rhsArgs_3117_, v_argMask_3118_, v_altResultType_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec_ref(v___eqs_3116_);
lean_dec(v___x_3114_);
lean_dec(v_fst_3099_);
lean_dec_ref(v_overlaps_3097_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3127_, lean_object* v_val_3128_, lean_object* v_baseName_3129_, lean_object* v___x_3130_, lean_object* v_a_3131_, lean_object* v___x_3132_, lean_object* v___x_3133_, lean_object* v___x_3134_, lean_object* v_matchDeclName_3135_, lean_object* v___x_3136_, lean_object* v___x_3137_, lean_object* v___x_3138_, lean_object* v_a_3139_, lean_object* v_b_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
uint8_t v___x_3146_; 
v___x_3146_ = lean_nat_dec_lt(v_a_3139_, v_upperBound_3127_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_dec(v_a_3139_);
lean_dec(v___x_3138_);
lean_dec_ref(v___x_3137_);
lean_dec(v___x_3136_);
lean_dec(v_matchDeclName_3135_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v___x_3133_);
lean_dec(v___x_3132_);
lean_dec_ref(v_a_3131_);
lean_dec_ref(v___x_3130_);
lean_dec(v_baseName_3129_);
lean_dec_ref(v_val_3128_);
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v_b_3140_);
return v___x_3147_;
}
else
{
lean_object* v_snd_3148_; lean_object* v_snd_3149_; lean_object* v_snd_3150_; lean_object* v_fst_3151_; lean_object* v_fst_3152_; lean_object* v_fst_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3236_; 
v_snd_3148_ = lean_ctor_get(v_b_3140_, 1);
lean_inc(v_snd_3148_);
v_snd_3149_ = lean_ctor_get(v_snd_3148_, 1);
lean_inc(v_snd_3149_);
v_snd_3150_ = lean_ctor_get(v_snd_3149_, 1);
lean_inc(v_snd_3150_);
v_fst_3151_ = lean_ctor_get(v_b_3140_, 0);
lean_inc(v_fst_3151_);
lean_dec_ref(v_b_3140_);
v_fst_3152_ = lean_ctor_get(v_snd_3148_, 0);
lean_inc(v_fst_3152_);
lean_dec(v_snd_3148_);
v_fst_3153_ = lean_ctor_get(v_snd_3149_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_snd_3149_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v_snd_3149_, 1);
lean_dec(v_unused_3237_);
v___x_3155_ = v_snd_3149_;
v_isShared_3156_ = v_isSharedCheck_3236_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_fst_3153_);
lean_dec(v_snd_3149_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3236_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_fst_3157_; lean_object* v_snd_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3235_; 
v_fst_3157_ = lean_ctor_get(v_snd_3150_, 0);
v_snd_3158_ = lean_ctor_get(v_snd_3150_, 1);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_snd_3150_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3160_ = v_snd_3150_;
v_isShared_3161_ = v_isSharedCheck_3235_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_snd_3158_);
lean_inc(v_fst_3157_);
lean_dec(v_snd_3150_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3235_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_altInfos_3162_; lean_object* v_overlaps_3163_; lean_object* v_start_3164_; lean_object* v_stop_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___f_3177_; lean_object* v___x_3178_; lean_object* v___y_3180_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v_altInfos_3162_ = lean_ctor_get(v_val_3128_, 2);
v_overlaps_3163_ = lean_ctor_get(v_val_3128_, 5);
v_start_3164_ = lean_ctor_get(v___x_3137_, 1);
v_stop_3165_ = lean_ctor_get(v___x_3137_, 2);
v___x_3166_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3167_ = l_Lean_instInhabitedExpr;
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3170_ = lean_box(0);
v___x_3171_ = lean_unsigned_to_nat(1u);
v___x_3172_ = lean_array_get_borrowed(v___x_3166_, v_altInfos_3162_, v_a_3139_);
v___x_3173_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3129_);
v___x_3174_ = l_Lean_Name_str___override(v_baseName_3129_, v___x_3173_);
lean_inc(v_fst_3153_);
v___x_3175_ = lean_name_append_index_after(v___x_3174_, v_fst_3153_);
v___x_3176_ = lean_box(v___x_3146_);
lean_inc(v___x_3138_);
lean_inc_ref(v___x_3137_);
lean_inc(v___x_3136_);
lean_inc(v___x_3175_);
lean_inc(v_matchDeclName_3135_);
lean_inc_ref(v___x_3134_);
lean_inc_ref(v___x_3133_);
lean_inc(v___x_3132_);
lean_inc_ref(v_a_3131_);
lean_inc_ref(v___x_3130_);
lean_inc(v_fst_3152_);
lean_inc(v_a_3139_);
lean_inc_ref(v_overlaps_3163_);
v___f_3177_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3177_, 0, v___x_3171_);
lean_closure_set(v___f_3177_, 1, v_overlaps_3163_);
lean_closure_set(v___f_3177_, 2, v_a_3139_);
lean_closure_set(v___f_3177_, 3, v_fst_3152_);
lean_closure_set(v___f_3177_, 4, v___x_3169_);
lean_closure_set(v___f_3177_, 5, v___x_3168_);
lean_closure_set(v___f_3177_, 6, v___x_3130_);
lean_closure_set(v___f_3177_, 7, v___x_3176_);
lean_closure_set(v___f_3177_, 8, v___x_3167_);
lean_closure_set(v___f_3177_, 9, v_a_3131_);
lean_closure_set(v___f_3177_, 10, v___x_3132_);
lean_closure_set(v___f_3177_, 11, v___x_3133_);
lean_closure_set(v___f_3177_, 12, v___x_3134_);
lean_closure_set(v___f_3177_, 13, v_matchDeclName_3135_);
lean_closure_set(v___f_3177_, 14, v___x_3175_);
lean_closure_set(v___f_3177_, 15, v___x_3136_);
lean_closure_set(v___f_3177_, 16, v___x_3170_);
lean_closure_set(v___f_3177_, 17, v___x_3137_);
lean_closure_set(v___f_3177_, 18, v___x_3138_);
v___x_3178_ = lean_array_push(v_fst_3151_, v___x_3175_);
v___x_3231_ = lean_nat_sub(v_stop_3165_, v_start_3164_);
v___x_3232_ = lean_nat_dec_lt(v_a_3139_, v___x_3231_);
lean_dec(v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; 
v___x_3233_ = l_outOfBounds___redArg(v___x_3167_);
v___y_3180_ = v___x_3233_;
goto v___jp_3179_;
}
else
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Subarray_get___redArg(v___x_3137_, v_a_3139_);
v___y_3180_ = v___x_3234_;
goto v___jp_3179_;
}
v___jp_3179_:
{
lean_object* v___x_3181_; 
lean_inc(v___y_3144_);
lean_inc_ref(v___y_3143_);
lean_inc(v___y_3142_);
lean_inc_ref(v___y_3141_);
v___x_3181_ = lean_infer_type(v___y_3180_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3183_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
lean_inc(v___x_3138_);
lean_inc(v___x_3172_);
v___x_3183_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3182_, v___x_3172_, v___x_3138_, v___f_3177_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v_snd_3185_; lean_object* v_fst_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3214_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
v_snd_3185_ = lean_ctor_get(v_a_3184_, 1);
v_fst_3186_ = lean_ctor_get(v_a_3184_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_a_3184_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3188_ = v_a_3184_;
v_isShared_3189_ = v_isSharedCheck_3214_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_snd_3185_);
lean_inc(v_fst_3186_);
lean_dec(v_a_3184_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3214_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v_fst_3190_; lean_object* v_snd_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3213_; 
v_fst_3190_ = lean_ctor_get(v_snd_3185_, 0);
v_snd_3191_ = lean_ctor_get(v_snd_3185_, 1);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_snd_3185_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3193_ = v_snd_3185_;
v_isShared_3194_ = v_isSharedCheck_3213_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_snd_3191_);
lean_inc(v_fst_3190_);
lean_dec(v_snd_3185_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3213_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3195_ = lean_array_push(v_fst_3152_, v_fst_3186_);
v___x_3196_ = lean_array_push(v_fst_3157_, v_fst_3190_);
v___x_3197_ = lean_array_push(v_snd_3158_, v_snd_3191_);
v___x_3198_ = lean_nat_add(v_fst_3153_, v___x_3171_);
lean_dec(v_fst_3153_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 1, v___x_3197_);
lean_ctor_set(v___x_3193_, 0, v___x_3196_);
v___x_3200_ = v___x_3193_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v___x_3197_);
v___x_3200_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 1, v___x_3200_);
lean_ctor_set(v___x_3188_, 0, v___x_3198_);
v___x_3202_ = v___x_3188_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3204_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v___x_3202_);
lean_ctor_set(v___x_3160_, 0, v___x_3195_);
v___x_3204_ = v___x_3160_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3206_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 1, v___x_3204_);
lean_ctor_set(v___x_3155_, 0, v___x_3178_);
v___x_3206_ = v___x_3155_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_nat_add(v_a_3139_, v___x_3171_);
lean_dec(v_a_3139_);
v_a_3139_ = v___x_3207_;
v_b_3140_ = v___x_3206_;
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
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v___x_3178_);
lean_del_object(v___x_3160_);
lean_dec(v_snd_3158_);
lean_dec(v_fst_3157_);
lean_del_object(v___x_3155_);
lean_dec(v_fst_3153_);
lean_dec(v_fst_3152_);
lean_dec(v_a_3139_);
lean_dec(v___x_3138_);
lean_dec_ref(v___x_3137_);
lean_dec(v___x_3136_);
lean_dec(v_matchDeclName_3135_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v___x_3133_);
lean_dec(v___x_3132_);
lean_dec_ref(v_a_3131_);
lean_dec_ref(v___x_3130_);
lean_dec(v_baseName_3129_);
lean_dec_ref(v_val_3128_);
v_a_3215_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3183_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3183_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref(v___x_3178_);
lean_dec_ref(v___f_3177_);
lean_del_object(v___x_3160_);
lean_dec(v_snd_3158_);
lean_dec(v_fst_3157_);
lean_del_object(v___x_3155_);
lean_dec(v_fst_3153_);
lean_dec(v_fst_3152_);
lean_dec(v_a_3139_);
lean_dec(v___x_3138_);
lean_dec_ref(v___x_3137_);
lean_dec(v___x_3136_);
lean_dec(v_matchDeclName_3135_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v___x_3133_);
lean_dec(v___x_3132_);
lean_dec_ref(v_a_3131_);
lean_dec_ref(v___x_3130_);
lean_dec(v_baseName_3129_);
lean_dec_ref(v_val_3128_);
v_a_3223_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3181_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3181_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
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
lean_object* v_upperBound_3238_ = _args[0];
lean_object* v_val_3239_ = _args[1];
lean_object* v_baseName_3240_ = _args[2];
lean_object* v___x_3241_ = _args[3];
lean_object* v_a_3242_ = _args[4];
lean_object* v___x_3243_ = _args[5];
lean_object* v___x_3244_ = _args[6];
lean_object* v___x_3245_ = _args[7];
lean_object* v_matchDeclName_3246_ = _args[8];
lean_object* v___x_3247_ = _args[9];
lean_object* v___x_3248_ = _args[10];
lean_object* v___x_3249_ = _args[11];
lean_object* v_a_3250_ = _args[12];
lean_object* v_b_3251_ = _args[13];
lean_object* v___y_3252_ = _args[14];
lean_object* v___y_3253_ = _args[15];
lean_object* v___y_3254_ = _args[16];
lean_object* v___y_3255_ = _args[17];
lean_object* v___y_3256_ = _args[18];
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3238_, v_val_3239_, v_baseName_3240_, v___x_3241_, v_a_3242_, v___x_3243_, v___x_3244_, v___x_3245_, v_matchDeclName_3246_, v___x_3247_, v___x_3248_, v___x_3249_, v_a_3250_, v_b_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v_upperBound_3238_);
return v_res_3257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3261_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3262_ = lean_unsigned_to_nat(6u);
v___x_3263_ = lean_unsigned_to_nat(233u);
v___x_3264_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3265_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3266_ = l_mkPanicMessageWithDecl(v___x_3265_, v___x_3264_, v___x_3263_, v___x_3262_, v___x_3261_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3279_, lean_object* v_matchDeclName_3280_, lean_object* v_altInfos_3281_, lean_object* v___x_3282_, lean_object* v___x_3283_, lean_object* v___x_3284_, lean_object* v_numParams_3285_, lean_object* v_val_3286_, lean_object* v___x_3287_, lean_object* v_numDiscrs_3288_, lean_object* v_baseName_3289_, lean_object* v_a_3290_, lean_object* v___x_3291_, lean_object* v_uElimPos_x3f_3292_, lean_object* v_discrInfos_3293_, lean_object* v_overlaps_3294_, lean_object* v___f_3295_, lean_object* v_xs_3296_, lean_object* v___matchResultType_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; uint8_t v___y_3312_; lean_object* v___x_3317_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; uint8_t v___y_3323_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v_lower_3344_; lean_object* v_upper_3345_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3317_ = lean_box(0);
v___x_3339_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3285_);
lean_inc_ref(v_xs_3296_);
v___x_3340_ = l_Array_toSubarray___redArg(v_xs_3296_, v___x_3339_, v_numParams_3285_);
v___x_3341_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3286_);
v___x_3342_ = lean_array_get(v___x_3287_, v_xs_3296_, v___x_3341_);
lean_dec(v___x_3341_);
v___x_3376_ = lean_array_get_size(v_xs_3296_);
v___x_3377_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3286_);
v___x_3378_ = lean_nat_sub(v___x_3376_, v___x_3377_);
lean_dec(v___x_3377_);
v___x_3379_ = lean_nat_dec_le(v___x_3378_, v___x_3339_);
if (v___x_3379_ == 0)
{
v_lower_3344_ = v___x_3378_;
v_upper_3345_ = v___x_3376_;
goto v___jp_3343_;
}
else
{
lean_dec(v___x_3378_);
v_lower_3344_ = v___x_3339_;
v_upper_3345_ = v___x_3376_;
goto v___jp_3343_;
}
v___jp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3306_, 0, v___y_3304_);
lean_ctor_set(v___x_3306_, 1, v_splitterName_3279_);
lean_ctor_set(v___x_3306_, 2, v___y_3305_);
v___x_3307_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3280_, v___x_3306_, v___y_3301_);
return v___x_3307_;
}
v___jp_3308_:
{
lean_object* v___x_3313_; 
lean_inc(v_matchDeclName_3280_);
v___x_3313_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3280_, v___y_3312_, v___y_3310_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_dec_ref_known(v___x_3313_, 1);
v___y_3304_ = v___y_3309_;
v___y_3305_ = v___y_3311_;
goto v___jp_3303_;
}
else
{
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3309_);
lean_dec(v_matchDeclName_3280_);
lean_dec(v_splitterName_3279_);
return v___x_3313_;
}
}
v___jp_3314_:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3316_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3315_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
return v___x_3316_;
}
v___jp_3318_:
{
if (v___y_3323_ == 0)
{
lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
lean_dec_ref(v___y_3320_);
v___x_3324_ = lean_array_get_size(v_altInfos_3281_);
v___x_3325_ = lean_array_get_size(v___y_3322_);
v___x_3326_ = lean_nat_dec_eq(v___x_3324_, v___x_3325_);
if (v___x_3326_ == 0)
{
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3319_);
lean_dec(v___x_3284_);
lean_dec_ref(v___x_3283_);
lean_dec(v___x_3282_);
lean_dec(v_matchDeclName_3280_);
lean_dec(v_splitterName_3279_);
goto v___jp_3314_;
}
else
{
uint8_t v___x_3327_; 
v___x_3327_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3281_, v___y_3322_, v___x_3324_);
lean_dec(v___y_3322_);
if (v___x_3327_ == 0)
{
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3319_);
lean_dec(v___x_3284_);
lean_dec_ref(v___x_3283_);
lean_dec(v___x_3282_);
lean_dec(v_matchDeclName_3280_);
lean_dec(v_splitterName_3279_);
goto v___jp_3314_;
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_inc_n(v_splitterName_3279_, 2);
v___x_3328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3328_, 0, v_splitterName_3279_);
lean_ctor_set(v___x_3328_, 1, v___x_3282_);
lean_ctor_set(v___x_3328_, 2, v___x_3283_);
lean_inc(v_matchDeclName_3280_);
v___x_3329_ = l_Lean_mkConst(v_matchDeclName_3280_, v___x_3284_);
v___x_3330_ = lean_box(1);
v___x_3331_ = 1;
v___x_3332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3332_, 0, v_splitterName_3279_);
lean_ctor_set(v___x_3332_, 1, v___x_3317_);
v___x_3333_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3333_, 0, v___x_3328_);
lean_ctor_set(v___x_3333_, 1, v___x_3329_);
lean_ctor_set(v___x_3333_, 2, v___x_3330_);
lean_ctor_set(v___x_3333_, 3, v___x_3332_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*4, v___x_3331_);
v___x_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
lean_inc_ref(v___x_3334_);
v___x_3335_ = l_Lean_addDecl(v___x_3334_, v___y_3323_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3335_) == 0)
{
uint8_t v___x_3336_; lean_object* v___x_3337_; 
lean_dec_ref_known(v___x_3335_, 1);
v___x_3336_ = 0;
lean_inc(v_splitterName_3279_);
v___x_3337_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3279_, v___x_3336_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v___x_3338_; 
lean_dec_ref_known(v___x_3337_, 1);
v___x_3338_ = l_Lean_compileDecl(v___x_3334_, v___y_3323_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_dec_ref_known(v___x_3338_, 1);
v___y_3304_ = v___y_3319_;
v___y_3305_ = v___y_3321_;
goto v___jp_3303_;
}
else
{
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3319_);
lean_dec(v_matchDeclName_3280_);
lean_dec(v_splitterName_3279_);
return v___x_3338_;
}
}
else
{
lean_dec_ref_known(v___x_3334_, 1);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3319_);
lean_dec(v_matchDeclName_3280_);
lean_dec(v_splitterName_3279_);
return v___x_3337_;
}
}
else
{
lean_dec_ref_known(v___x_3334_, 1);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3319_);
lean_dec(v_matchDeclName_3280_);
lean_dec(v_splitterName_3279_);
return v___x_3335_;
}
}
}
}
else
{
lean_dec(v___y_3322_);
lean_dec(v___x_3284_);
lean_dec_ref(v___x_3283_);
lean_dec(v___x_3282_);
v___y_3309_ = v___y_3319_;
v___y_3310_ = v___y_3320_;
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___y_3323_;
goto v___jp_3308_;
}
}
v___jp_3343_:
{
lean_object* v___x_3346_; lean_object* v_start_3347_; lean_object* v_stop_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_inc_ref(v_xs_3296_);
v___x_3346_ = l_Array_toSubarray___redArg(v_xs_3296_, v_lower_3344_, v_upper_3345_);
v_start_3347_ = lean_ctor_get(v___x_3346_, 1);
lean_inc(v_start_3347_);
v_stop_3348_ = lean_ctor_get(v___x_3346_, 2);
lean_inc(v_stop_3348_);
v___x_3349_ = lean_unsigned_to_nat(1u);
v___x_3350_ = lean_nat_add(v_numParams_3285_, v___x_3349_);
v___x_3351_ = lean_nat_add(v___x_3350_, v_numDiscrs_3288_);
v___x_3352_ = lean_nat_sub(v_stop_3348_, v_start_3347_);
lean_dec(v_start_3347_);
lean_dec(v_stop_3348_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3354_ = l_Array_toSubarray___redArg(v_xs_3296_, v___x_3350_, v___x_3351_);
lean_inc(v___x_3282_);
lean_inc(v_matchDeclName_3280_);
lean_inc(v___x_3284_);
v___x_3355_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3352_, v_val_3286_, v_baseName_3289_, v___x_3354_, v_a_3290_, v___x_3284_, v___x_3340_, v___x_3342_, v_matchDeclName_3280_, v___x_3282_, v___x_3346_, v___x_3291_, v___x_3339_, v___x_3353_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___x_3352_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v_snd_3357_; lean_object* v_snd_3358_; lean_object* v_snd_3359_; lean_object* v_fst_3360_; lean_object* v_fst_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; uint8_t v___x_3364_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
lean_dec_ref_known(v___x_3355_, 1);
v_snd_3357_ = lean_ctor_get(v_a_3356_, 1);
v_snd_3358_ = lean_ctor_get(v_snd_3357_, 1);
v_snd_3359_ = lean_ctor_get(v_snd_3358_, 1);
lean_inc(v_snd_3359_);
v_fst_3360_ = lean_ctor_get(v_a_3356_, 0);
lean_inc(v_fst_3360_);
lean_dec(v_a_3356_);
v_fst_3361_ = lean_ctor_get(v_snd_3359_, 0);
lean_inc_n(v_fst_3361_, 2);
lean_dec(v_snd_3359_);
lean_inc_ref(v_overlaps_3294_);
v___x_3362_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3362_, 0, v_numParams_3285_);
lean_ctor_set(v___x_3362_, 1, v_numDiscrs_3288_);
lean_ctor_set(v___x_3362_, 2, v_fst_3361_);
lean_ctor_set(v___x_3362_, 3, v_uElimPos_x3f_3292_);
lean_ctor_set(v___x_3362_, 4, v_discrInfos_3293_);
lean_ctor_set(v___x_3362_, 5, v_overlaps_3294_);
v___x_3363_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3294_);
lean_dec_ref(v_overlaps_3294_);
v___x_3364_ = lean_bool_not(v___x_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3366_ = lean_find_expr(v___x_3365_, v___x_3283_);
if (lean_obj_tag(v___x_3366_) == 0)
{
v___y_3319_ = v_fst_3360_;
v___y_3320_ = v___f_3295_;
v___y_3321_ = v___x_3362_;
v___y_3322_ = v_fst_3361_;
v___y_3323_ = v___x_3364_;
goto v___jp_3318_;
}
else
{
uint8_t v___x_3367_; 
lean_dec_ref_known(v___x_3366_, 1);
lean_dec(v_fst_3361_);
lean_dec(v___x_3284_);
lean_dec_ref(v___x_3283_);
lean_dec(v___x_3282_);
v___x_3367_ = 1;
v___y_3309_ = v_fst_3360_;
v___y_3310_ = v___f_3295_;
v___y_3311_ = v___x_3362_;
v___y_3312_ = v___x_3367_;
goto v___jp_3308_;
}
}
else
{
v___y_3319_ = v_fst_3360_;
v___y_3320_ = v___f_3295_;
v___y_3321_ = v___x_3362_;
v___y_3322_ = v_fst_3361_;
v___y_3323_ = v___x_3364_;
goto v___jp_3318_;
}
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec_ref(v___f_3295_);
lean_dec_ref(v_overlaps_3294_);
lean_dec_ref(v_discrInfos_3293_);
lean_dec(v_uElimPos_x3f_3292_);
lean_dec(v_numDiscrs_3288_);
lean_dec(v_numParams_3285_);
lean_dec(v___x_3284_);
lean_dec_ref(v___x_3283_);
lean_dec(v___x_3282_);
lean_dec(v_matchDeclName_3280_);
lean_dec(v_splitterName_3279_);
v_a_3368_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3355_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3355_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3380_ = _args[0];
lean_object* v_matchDeclName_3381_ = _args[1];
lean_object* v_altInfos_3382_ = _args[2];
lean_object* v___x_3383_ = _args[3];
lean_object* v___x_3384_ = _args[4];
lean_object* v___x_3385_ = _args[5];
lean_object* v_numParams_3386_ = _args[6];
lean_object* v_val_3387_ = _args[7];
lean_object* v___x_3388_ = _args[8];
lean_object* v_numDiscrs_3389_ = _args[9];
lean_object* v_baseName_3390_ = _args[10];
lean_object* v_a_3391_ = _args[11];
lean_object* v___x_3392_ = _args[12];
lean_object* v_uElimPos_x3f_3393_ = _args[13];
lean_object* v_discrInfos_3394_ = _args[14];
lean_object* v_overlaps_3395_ = _args[15];
lean_object* v___f_3396_ = _args[16];
lean_object* v_xs_3397_ = _args[17];
lean_object* v___matchResultType_3398_ = _args[18];
lean_object* v___y_3399_ = _args[19];
lean_object* v___y_3400_ = _args[20];
lean_object* v___y_3401_ = _args[21];
lean_object* v___y_3402_ = _args[22];
lean_object* v___y_3403_ = _args[23];
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3380_, v_matchDeclName_3381_, v_altInfos_3382_, v___x_3383_, v___x_3384_, v___x_3385_, v_numParams_3386_, v_val_3387_, v___x_3388_, v_numDiscrs_3389_, v_baseName_3390_, v_a_3391_, v___x_3392_, v_uElimPos_x3f_3393_, v_discrInfos_3394_, v_overlaps_3395_, v___f_3396_, v_xs_3397_, v___matchResultType_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec_ref(v___matchResultType_3398_);
lean_dec_ref(v___x_3388_);
lean_dec_ref(v_altInfos_3382_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
if (lean_obj_tag(v_a_3405_) == 0)
{
lean_object* v___x_3407_; 
v___x_3407_ = l_List_reverse___redArg(v_a_3406_);
return v___x_3407_;
}
else
{
lean_object* v_head_3408_; lean_object* v_tail_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3418_; 
v_head_3408_ = lean_ctor_get(v_a_3405_, 0);
v_tail_3409_ = lean_ctor_get(v_a_3405_, 1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_a_3405_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3411_ = v_a_3405_;
v_isShared_3412_ = v_isSharedCheck_3418_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_tail_3409_);
lean_inc(v_head_3408_);
lean_dec(v_a_3405_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3418_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3413_ = l_Lean_mkLevelParam(v_head_3408_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 1, v_a_3406_);
lean_ctor_set(v___x_3411_, 0, v___x_3413_);
v___x_3415_ = v___x_3411_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3413_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_a_3406_);
v___x_3415_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
v_a_3405_ = v_tail_3409_;
v_a_3406_ = v___x_3415_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
return v___x_3421_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
lean_ctor_set(v___x_3424_, 2, v___x_3423_);
lean_ctor_set(v___x_3424_, 3, v___x_3423_);
lean_ctor_set(v___x_3424_, 4, v___x_3422_);
lean_ctor_set(v___x_3424_, 5, v___x_3422_);
lean_ctor_set(v___x_3424_, 6, v___x_3422_);
lean_ctor_set(v___x_3424_, 7, v___x_3422_);
lean_ctor_set(v___x_3424_, 8, v___x_3422_);
lean_ctor_set(v___x_3424_, 9, v___x_3422_);
return v___x_3424_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3425_ = lean_box(1);
v___x_3426_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3427_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v___x_3426_);
lean_ctor_set(v___x_3428_, 2, v___x_3425_);
return v___x_3428_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
return v___x_3434_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_3437_ = l_Lean_stringToMessageData(v___x_3436_);
return v___x_3437_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_3440_ = l_Lean_stringToMessageData(v___x_3439_);
return v___x_3440_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_3443_ = l_Lean_stringToMessageData(v___x_3442_);
return v___x_3443_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_3446_ = l_Lean_stringToMessageData(v___x_3445_);
return v___x_3446_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_3449_ = l_Lean_stringToMessageData(v___x_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3450_, lean_object* v_declHint_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v___x_3454_; lean_object* v_env_3455_; uint8_t v___y_3457_; uint8_t v___x_3513_; uint8_t v___x_3514_; 
v___x_3454_ = lean_st_ref_get(v___y_3452_);
v_env_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc_ref(v_env_3455_);
lean_dec(v___x_3454_);
v___x_3513_ = l_Lean_Name_isAnonymous(v_declHint_3451_);
v___x_3514_ = lean_bool_not(v___x_3513_);
if (v___x_3514_ == 0)
{
v___y_3457_ = v___x_3514_;
goto v___jp_3456_;
}
else
{
uint8_t v_isExporting_3515_; 
v_isExporting_3515_ = lean_ctor_get_uint8(v_env_3455_, sizeof(void*)*8);
v___y_3457_ = v_isExporting_3515_;
goto v___jp_3456_;
}
v___jp_3456_:
{
if (v___y_3457_ == 0)
{
lean_object* v___x_3458_; 
lean_dec_ref(v_env_3455_);
lean_dec(v_declHint_3451_);
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v_msg_3450_);
return v___x_3458_;
}
else
{
uint8_t v___x_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3459_ = 0;
lean_inc_ref(v_env_3455_);
v___x_3460_ = l_Lean_Environment_setExporting(v_env_3455_, v___x_3459_);
lean_inc(v_declHint_3451_);
lean_inc_ref(v___x_3460_);
v___x_3461_ = l_Lean_Environment_contains(v___x_3460_, v_declHint_3451_, v___y_3457_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; 
lean_dec_ref(v___x_3460_);
lean_dec_ref(v_env_3455_);
lean_dec(v_declHint_3451_);
v___x_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3462_, 0, v_msg_3450_);
return v___x_3462_;
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v_c_3468_; lean_object* v___x_3469_; 
v___x_3463_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3464_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3465_ = l_Lean_Options_empty;
v___x_3466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3460_);
lean_ctor_set(v___x_3466_, 1, v___x_3463_);
lean_ctor_set(v___x_3466_, 2, v___x_3464_);
lean_ctor_set(v___x_3466_, 3, v___x_3465_);
lean_inc(v_declHint_3451_);
v___x_3467_ = l_Lean_MessageData_ofConstName(v_declHint_3451_, v___x_3459_);
v_c_3468_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3468_, 0, v___x_3466_);
lean_ctor_set(v_c_3468_, 1, v___x_3467_);
v___x_3469_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3455_, v_declHint_3451_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
lean_dec_ref(v_env_3455_);
lean_dec(v_declHint_3451_);
v___x_3470_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v_c_3468_);
v___x_3472_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Lean_MessageData_note(v___x_3473_);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v_msg_3450_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
return v___x_3476_;
}
else
{
lean_object* v_val_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3512_; 
v_val_3477_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3479_ = v___x_3469_;
v_isShared_3480_ = v_isSharedCheck_3512_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_val_3477_);
lean_dec(v___x_3469_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3512_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v_mod_3484_; uint8_t v___x_3485_; 
v___x_3481_ = lean_box(0);
v___x_3482_ = l_Lean_Environment_header(v_env_3455_);
lean_dec_ref(v_env_3455_);
v___x_3483_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3482_);
v_mod_3484_ = lean_array_get(v___x_3481_, v___x_3483_, v_val_3477_);
lean_dec(v_val_3477_);
lean_dec_ref(v___x_3483_);
v___x_3485_ = l_Lean_isPrivateName(v_declHint_3451_);
lean_dec(v_declHint_3451_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3486_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
lean_ctor_set(v___x_3487_, 1, v_c_3468_);
v___x_3488_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_3489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3487_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = l_Lean_MessageData_ofName(v_mod_3484_);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3491_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = l_Lean_MessageData_note(v___x_3493_);
v___x_3495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3495_, 0, v_msg_3450_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set_tag(v___x_3479_, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3495_);
v___x_3497_ = v___x_3479_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3499_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
lean_ctor_set(v___x_3500_, 1, v_c_3468_);
v___x_3501_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l_Lean_MessageData_ofName(v_mod_3484_);
v___x_3504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3502_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
v___x_3505_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_3506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3504_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = l_Lean_MessageData_note(v___x_3506_);
v___x_3508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3508_, 0, v_msg_3450_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set_tag(v___x_3479_, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3508_);
v___x_3510_ = v___x_3479_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3516_, lean_object* v_declHint_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3516_, v_declHint_3517_, v___y_3518_);
lean_dec(v___y_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3521_, lean_object* v_declHint_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3538_; 
v___x_3528_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3521_, v_declHint_3522_, v___y_3526_);
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3538_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3538_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3533_ = l_Lean_unknownIdentifierMessageTag;
v___x_3534_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
lean_ctor_set(v___x_3534_, 1, v_a_3529_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3534_);
v___x_3536_ = v___x_3531_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3539_, lean_object* v_declHint_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3539_, v_declHint_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3547_, lean_object* v_msg_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_fileName_3554_; lean_object* v_fileMap_3555_; lean_object* v_options_3556_; lean_object* v_currRecDepth_3557_; lean_object* v_maxRecDepth_3558_; lean_object* v_ref_3559_; lean_object* v_currNamespace_3560_; lean_object* v_openDecls_3561_; lean_object* v_initHeartbeats_3562_; lean_object* v_maxHeartbeats_3563_; lean_object* v_quotContext_3564_; lean_object* v_currMacroScope_3565_; uint8_t v_diag_3566_; lean_object* v_cancelTk_x3f_3567_; uint8_t v_suppressElabErrors_3568_; lean_object* v_inheritedTraceOptions_3569_; lean_object* v_ref_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v_fileName_3554_ = lean_ctor_get(v___y_3551_, 0);
v_fileMap_3555_ = lean_ctor_get(v___y_3551_, 1);
v_options_3556_ = lean_ctor_get(v___y_3551_, 2);
v_currRecDepth_3557_ = lean_ctor_get(v___y_3551_, 3);
v_maxRecDepth_3558_ = lean_ctor_get(v___y_3551_, 4);
v_ref_3559_ = lean_ctor_get(v___y_3551_, 5);
v_currNamespace_3560_ = lean_ctor_get(v___y_3551_, 6);
v_openDecls_3561_ = lean_ctor_get(v___y_3551_, 7);
v_initHeartbeats_3562_ = lean_ctor_get(v___y_3551_, 8);
v_maxHeartbeats_3563_ = lean_ctor_get(v___y_3551_, 9);
v_quotContext_3564_ = lean_ctor_get(v___y_3551_, 10);
v_currMacroScope_3565_ = lean_ctor_get(v___y_3551_, 11);
v_diag_3566_ = lean_ctor_get_uint8(v___y_3551_, sizeof(void*)*14);
v_cancelTk_x3f_3567_ = lean_ctor_get(v___y_3551_, 12);
v_suppressElabErrors_3568_ = lean_ctor_get_uint8(v___y_3551_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3569_ = lean_ctor_get(v___y_3551_, 13);
v_ref_3570_ = l_Lean_replaceRef(v_ref_3547_, v_ref_3559_);
lean_inc_ref(v_inheritedTraceOptions_3569_);
lean_inc(v_cancelTk_x3f_3567_);
lean_inc(v_currMacroScope_3565_);
lean_inc(v_quotContext_3564_);
lean_inc(v_maxHeartbeats_3563_);
lean_inc(v_initHeartbeats_3562_);
lean_inc(v_openDecls_3561_);
lean_inc(v_currNamespace_3560_);
lean_inc(v_maxRecDepth_3558_);
lean_inc(v_currRecDepth_3557_);
lean_inc_ref(v_options_3556_);
lean_inc_ref(v_fileMap_3555_);
lean_inc_ref(v_fileName_3554_);
v___x_3571_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3571_, 0, v_fileName_3554_);
lean_ctor_set(v___x_3571_, 1, v_fileMap_3555_);
lean_ctor_set(v___x_3571_, 2, v_options_3556_);
lean_ctor_set(v___x_3571_, 3, v_currRecDepth_3557_);
lean_ctor_set(v___x_3571_, 4, v_maxRecDepth_3558_);
lean_ctor_set(v___x_3571_, 5, v_ref_3570_);
lean_ctor_set(v___x_3571_, 6, v_currNamespace_3560_);
lean_ctor_set(v___x_3571_, 7, v_openDecls_3561_);
lean_ctor_set(v___x_3571_, 8, v_initHeartbeats_3562_);
lean_ctor_set(v___x_3571_, 9, v_maxHeartbeats_3563_);
lean_ctor_set(v___x_3571_, 10, v_quotContext_3564_);
lean_ctor_set(v___x_3571_, 11, v_currMacroScope_3565_);
lean_ctor_set(v___x_3571_, 12, v_cancelTk_x3f_3567_);
lean_ctor_set(v___x_3571_, 13, v_inheritedTraceOptions_3569_);
lean_ctor_set_uint8(v___x_3571_, sizeof(void*)*14, v_diag_3566_);
lean_ctor_set_uint8(v___x_3571_, sizeof(void*)*14 + 1, v_suppressElabErrors_3568_);
v___x_3572_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3548_, v___y_3549_, v___y_3550_, v___x_3571_, v___y_3552_);
lean_dec_ref_known(v___x_3571_, 14);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3573_, lean_object* v_msg_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3573_, v_msg_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v_ref_3573_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3581_, lean_object* v_msg_3582_, lean_object* v_declHint_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v___x_3589_; lean_object* v_a_3590_; lean_object* v___x_3591_; 
v___x_3589_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3582_, v_declHint_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref(v___x_3589_);
v___x_3591_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3581_, v_a_3590_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3592_, lean_object* v_msg_3593_, lean_object* v_declHint_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3592_, v_msg_3593_, v_declHint_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v_ref_3592_);
return v_res_3600_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3603_ = l_Lean_stringToMessageData(v___x_3602_);
return v___x_3603_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3606_ = l_Lean_stringToMessageData(v___x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3607_, lean_object* v_constName_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v___x_3614_; uint8_t v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3614_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3615_ = 0;
lean_inc(v_constName_3608_);
v___x_3616_ = l_Lean_MessageData_ofConstName(v_constName_3608_, v___x_3615_);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3614_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3607_, v___x_3619_, v_constName_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3621_, lean_object* v_constName_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3621_, v_constName_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v_ref_3621_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_ref_3635_; lean_object* v___x_3636_; 
v_ref_3635_ = lean_ctor_get(v___y_3632_, 5);
v___x_3636_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3635_, v_constName_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v___x_3650_; lean_object* v_env_3651_; uint8_t v___x_3652_; lean_object* v___x_3653_; 
v___x_3650_ = lean_st_ref_get(v___y_3648_);
v_env_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc_ref(v_env_3651_);
lean_dec(v___x_3650_);
v___x_3652_ = 0;
lean_inc(v_constName_3644_);
v___x_3653_ = l_Lean_Environment_find_x3f(v_env_3651_, v_constName_3644_, v___x_3652_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
return v___x_3654_;
}
else
{
lean_object* v_val_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_constName_3644_);
v_val_3655_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3653_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_val_3655_);
lean_dec(v___x_3653_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 0);
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_val_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
return v_res_3669_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3672_ = l_Lean_stringToMessageData(v___x_3671_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3673_, lean_object* v_baseName_3674_, lean_object* v_splitterName_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v___x_3681_; uint8_t v_foApprox_3682_; uint8_t v_ctxApprox_3683_; uint8_t v_quasiPatternApprox_3684_; uint8_t v_constApprox_3685_; uint8_t v_isDefEqStuckEx_3686_; uint8_t v_unificationHints_3687_; uint8_t v_proofIrrelevance_3688_; uint8_t v_assignSyntheticOpaque_3689_; uint8_t v_offsetCnstrs_3690_; uint8_t v_transparency_3691_; uint8_t v_univApprox_3692_; uint8_t v_iota_3693_; uint8_t v_beta_3694_; uint8_t v_proj_3695_; uint8_t v_zeta_3696_; uint8_t v_zetaDelta_3697_; uint8_t v_zetaUnused_3698_; uint8_t v_zetaHave_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3762_; 
v___x_3681_ = l_Lean_Meta_Context_config(v_a_3676_);
v_foApprox_3682_ = lean_ctor_get_uint8(v___x_3681_, 0);
v_ctxApprox_3683_ = lean_ctor_get_uint8(v___x_3681_, 1);
v_quasiPatternApprox_3684_ = lean_ctor_get_uint8(v___x_3681_, 2);
v_constApprox_3685_ = lean_ctor_get_uint8(v___x_3681_, 3);
v_isDefEqStuckEx_3686_ = lean_ctor_get_uint8(v___x_3681_, 4);
v_unificationHints_3687_ = lean_ctor_get_uint8(v___x_3681_, 5);
v_proofIrrelevance_3688_ = lean_ctor_get_uint8(v___x_3681_, 6);
v_assignSyntheticOpaque_3689_ = lean_ctor_get_uint8(v___x_3681_, 7);
v_offsetCnstrs_3690_ = lean_ctor_get_uint8(v___x_3681_, 8);
v_transparency_3691_ = lean_ctor_get_uint8(v___x_3681_, 9);
v_univApprox_3692_ = lean_ctor_get_uint8(v___x_3681_, 11);
v_iota_3693_ = lean_ctor_get_uint8(v___x_3681_, 12);
v_beta_3694_ = lean_ctor_get_uint8(v___x_3681_, 13);
v_proj_3695_ = lean_ctor_get_uint8(v___x_3681_, 14);
v_zeta_3696_ = lean_ctor_get_uint8(v___x_3681_, 15);
v_zetaDelta_3697_ = lean_ctor_get_uint8(v___x_3681_, 16);
v_zetaUnused_3698_ = lean_ctor_get_uint8(v___x_3681_, 17);
v_zetaHave_3699_ = lean_ctor_get_uint8(v___x_3681_, 18);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3701_ = v___x_3681_;
v_isShared_3702_ = v_isSharedCheck_3762_;
goto v_resetjp_3700_;
}
else
{
lean_dec(v___x_3681_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3762_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
uint8_t v_trackZetaDelta_3703_; lean_object* v_zetaDeltaSet_3704_; lean_object* v_lctx_3705_; lean_object* v_localInstances_3706_; lean_object* v_defEqCtx_x3f_3707_; lean_object* v_synthPendingDepth_3708_; lean_object* v_canUnfold_x3f_3709_; uint8_t v_univApprox_3710_; uint8_t v_inTypeClassResolution_3711_; uint8_t v_cacheInferType_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3760_; 
v_trackZetaDelta_3703_ = lean_ctor_get_uint8(v_a_3676_, sizeof(void*)*7);
v_zetaDeltaSet_3704_ = lean_ctor_get(v_a_3676_, 1);
v_lctx_3705_ = lean_ctor_get(v_a_3676_, 2);
v_localInstances_3706_ = lean_ctor_get(v_a_3676_, 3);
v_defEqCtx_x3f_3707_ = lean_ctor_get(v_a_3676_, 4);
v_synthPendingDepth_3708_ = lean_ctor_get(v_a_3676_, 5);
v_canUnfold_x3f_3709_ = lean_ctor_get(v_a_3676_, 6);
v_univApprox_3710_ = lean_ctor_get_uint8(v_a_3676_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3711_ = lean_ctor_get_uint8(v_a_3676_, sizeof(void*)*7 + 2);
v_cacheInferType_3712_ = lean_ctor_get_uint8(v_a_3676_, sizeof(void*)*7 + 3);
v_isSharedCheck_3760_ = !lean_is_exclusive(v_a_3676_);
if (v_isSharedCheck_3760_ == 0)
{
lean_object* v_unused_3761_; 
v_unused_3761_ = lean_ctor_get(v_a_3676_, 0);
lean_dec(v_unused_3761_);
v___x_3714_ = v_a_3676_;
v_isShared_3715_ = v_isSharedCheck_3760_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_canUnfold_x3f_3709_);
lean_inc(v_synthPendingDepth_3708_);
lean_inc(v_defEqCtx_x3f_3707_);
lean_inc(v_localInstances_3706_);
lean_inc(v_lctx_3705_);
lean_inc(v_zetaDeltaSet_3704_);
lean_dec(v_a_3676_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3760_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
uint8_t v___x_3716_; lean_object* v___x_3718_; 
v___x_3716_ = 2;
if (v_isShared_3702_ == 0)
{
v___x_3718_ = v___x_3701_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 0, v_foApprox_3682_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 1, v_ctxApprox_3683_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 2, v_quasiPatternApprox_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 3, v_constApprox_3685_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 4, v_isDefEqStuckEx_3686_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 5, v_unificationHints_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 6, v_proofIrrelevance_3688_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 7, v_assignSyntheticOpaque_3689_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 8, v_offsetCnstrs_3690_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 9, v_transparency_3691_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 11, v_univApprox_3692_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 12, v_iota_3693_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 13, v_beta_3694_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 14, v_proj_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 15, v_zeta_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 16, v_zetaDelta_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 17, v_zetaUnused_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3759_, 18, v_zetaHave_3699_);
v___x_3718_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
uint64_t v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3722_; 
lean_ctor_set_uint8(v___x_3718_, 10, v___x_3716_);
v___x_3719_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3718_);
v___x_3720_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3720_, 0, v___x_3718_);
lean_ctor_set_uint64(v___x_3720_, sizeof(void*)*1, v___x_3719_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v___x_3720_);
v___x_3722_ = v___x_3714_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_zetaDeltaSet_3704_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_lctx_3705_);
lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_localInstances_3706_);
lean_ctor_set(v_reuseFailAlloc_3758_, 4, v_defEqCtx_x3f_3707_);
lean_ctor_set(v_reuseFailAlloc_3758_, 5, v_synthPendingDepth_3708_);
lean_ctor_set(v_reuseFailAlloc_3758_, 6, v_canUnfold_x3f_3709_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, sizeof(void*)*7, v_trackZetaDelta_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, sizeof(void*)*7 + 1, v_univApprox_3710_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3711_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, sizeof(void*)*7 + 3, v_cacheInferType_3712_);
v___x_3722_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3723_; 
lean_inc(v_matchDeclName_3673_);
v___x_3723_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3673_, v___x_3722_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3725_; lean_object* v_a_3726_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref_known(v___x_3723_, 1);
lean_inc(v_matchDeclName_3673_);
v___x_3725_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_3673_, v_a_3679_);
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref(v___x_3725_);
if (lean_obj_tag(v_a_3726_) == 1)
{
lean_object* v_val_3727_; lean_object* v_numParams_3728_; lean_object* v_numDiscrs_3729_; lean_object* v_altInfos_3730_; lean_object* v_uElimPos_x3f_3731_; lean_object* v_discrInfos_3732_; lean_object* v_overlaps_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___f_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___f_3741_; uint8_t v___x_3742_; lean_object* v___x_3743_; 
v_val_3727_ = lean_ctor_get(v_a_3726_, 0);
lean_inc(v_val_3727_);
lean_dec_ref_known(v_a_3726_, 1);
v_numParams_3728_ = lean_ctor_get(v_val_3727_, 0);
lean_inc(v_numParams_3728_);
v_numDiscrs_3729_ = lean_ctor_get(v_val_3727_, 1);
lean_inc(v_numDiscrs_3729_);
v_altInfos_3730_ = lean_ctor_get(v_val_3727_, 2);
lean_inc_ref(v_altInfos_3730_);
v_uElimPos_x3f_3731_ = lean_ctor_get(v_val_3727_, 3);
lean_inc(v_uElimPos_x3f_3731_);
v_discrInfos_3732_ = lean_ctor_get(v_val_3727_, 4);
lean_inc_ref(v_discrInfos_3732_);
v_overlaps_3733_ = lean_ctor_get(v_val_3727_, 5);
lean_inc_ref_n(v_overlaps_3733_, 2);
v___x_3734_ = l_Lean_instInhabitedExpr;
v___x_3735_ = l_Lean_ConstantInfo_levelParams(v_a_3724_);
v___x_3736_ = lean_box(0);
lean_inc(v___x_3735_);
v___x_3737_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_3735_, v___x_3736_);
lean_inc(v_splitterName_3675_);
v___f_3738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3738_, 0, v_overlaps_3733_);
lean_closure_set(v___f_3738_, 1, v_splitterName_3675_);
v___x_3739_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3732_);
v___x_3740_ = l_Lean_ConstantInfo_type(v_a_3724_);
lean_inc_ref(v___x_3740_);
v___f_3741_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3741_, 0, v_splitterName_3675_);
lean_closure_set(v___f_3741_, 1, v_matchDeclName_3673_);
lean_closure_set(v___f_3741_, 2, v_altInfos_3730_);
lean_closure_set(v___f_3741_, 3, v___x_3735_);
lean_closure_set(v___f_3741_, 4, v___x_3740_);
lean_closure_set(v___f_3741_, 5, v___x_3737_);
lean_closure_set(v___f_3741_, 6, v_numParams_3728_);
lean_closure_set(v___f_3741_, 7, v_val_3727_);
lean_closure_set(v___f_3741_, 8, v___x_3734_);
lean_closure_set(v___f_3741_, 9, v_numDiscrs_3729_);
lean_closure_set(v___f_3741_, 10, v_baseName_3674_);
lean_closure_set(v___f_3741_, 11, v_a_3724_);
lean_closure_set(v___f_3741_, 12, v___x_3739_);
lean_closure_set(v___f_3741_, 13, v_uElimPos_x3f_3731_);
lean_closure_set(v___f_3741_, 14, v_discrInfos_3732_);
lean_closure_set(v___f_3741_, 15, v_overlaps_3733_);
lean_closure_set(v___f_3741_, 16, v___f_3738_);
v___x_3742_ = 0;
v___x_3743_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3740_, v___f_3741_, v___x_3742_, v___x_3742_, v___x_3722_, v_a_3677_, v_a_3678_, v_a_3679_);
lean_dec_ref(v___x_3722_);
return v___x_3743_;
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
lean_dec(v_a_3726_);
lean_dec(v_a_3724_);
lean_dec(v_splitterName_3675_);
lean_dec(v_baseName_3674_);
v___x_3744_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3745_ = l_Lean_MessageData_ofName(v_matchDeclName_3673_);
v___x_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3744_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3746_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3748_, v___x_3722_, v_a_3677_, v_a_3678_, v_a_3679_);
lean_dec_ref(v___x_3722_);
return v___x_3749_;
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec_ref(v___x_3722_);
lean_dec(v_splitterName_3675_);
lean_dec(v_baseName_3674_);
lean_dec(v_matchDeclName_3673_);
v_a_3750_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3723_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3723_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3763_, lean_object* v_baseName_3764_, lean_object* v_splitterName_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3763_, v_baseName_3764_, v_splitterName_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
return v_res_3771_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3772_, lean_object* v_ys_3773_, lean_object* v_hsz_3774_, lean_object* v_x_3775_, lean_object* v_x_3776_){
_start:
{
uint8_t v___x_3777_; 
v___x_3777_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3772_, v_ys_3773_, v_x_3775_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3778_, lean_object* v_ys_3779_, lean_object* v_hsz_3780_, lean_object* v_x_3781_, lean_object* v_x_3782_){
_start:
{
uint8_t v_res_3783_; lean_object* v_r_3784_; 
v_res_3783_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3778_, v_ys_3779_, v_hsz_3780_, v_x_3781_, v_x_3782_);
lean_dec_ref(v_ys_3779_);
lean_dec_ref(v_xs_3778_);
v_r_3784_ = lean_box(v_res_3783_);
return v_r_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3785_, lean_object* v_R_3786_, lean_object* v_a_3787_, lean_object* v_b_3788_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3787_, v_b_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3790_, lean_object* v_val_3791_, lean_object* v_baseName_3792_, lean_object* v___x_3793_, lean_object* v_a_3794_, lean_object* v___x_3795_, lean_object* v___x_3796_, lean_object* v___x_3797_, lean_object* v_matchDeclName_3798_, lean_object* v___x_3799_, lean_object* v___x_3800_, lean_object* v___x_3801_, lean_object* v_inst_3802_, lean_object* v_R_3803_, lean_object* v_a_3804_, lean_object* v_b_3805_, lean_object* v_c_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3790_, v_val_3791_, v_baseName_3792_, v___x_3793_, v_a_3794_, v___x_3795_, v___x_3796_, v___x_3797_, v_matchDeclName_3798_, v___x_3799_, v___x_3800_, v___x_3801_, v_a_3804_, v_b_3805_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3813_ = _args[0];
lean_object* v_val_3814_ = _args[1];
lean_object* v_baseName_3815_ = _args[2];
lean_object* v___x_3816_ = _args[3];
lean_object* v_a_3817_ = _args[4];
lean_object* v___x_3818_ = _args[5];
lean_object* v___x_3819_ = _args[6];
lean_object* v___x_3820_ = _args[7];
lean_object* v_matchDeclName_3821_ = _args[8];
lean_object* v___x_3822_ = _args[9];
lean_object* v___x_3823_ = _args[10];
lean_object* v___x_3824_ = _args[11];
lean_object* v_inst_3825_ = _args[12];
lean_object* v_R_3826_ = _args[13];
lean_object* v_a_3827_ = _args[14];
lean_object* v_b_3828_ = _args[15];
lean_object* v_c_3829_ = _args[16];
lean_object* v___y_3830_ = _args[17];
lean_object* v___y_3831_ = _args[18];
lean_object* v___y_3832_ = _args[19];
lean_object* v___y_3833_ = _args[20];
lean_object* v___y_3834_ = _args[21];
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3813_, v_val_3814_, v_baseName_3815_, v___x_3816_, v_a_3817_, v___x_3818_, v___x_3819_, v___x_3820_, v_matchDeclName_3821_, v___x_3822_, v___x_3823_, v___x_3824_, v_inst_3825_, v_R_3826_, v_a_3827_, v_b_3828_, v_c_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v_upperBound_3813_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3836_, lean_object* v_constName_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3844_, lean_object* v_constName_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3844_, v_constName_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3852_, lean_object* v_ref_3853_, lean_object* v_constName_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3853_, v_constName_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3861_, lean_object* v_ref_3862_, lean_object* v_constName_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3861_, v_ref_3862_, v_constName_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v_ref_3862_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3870_, lean_object* v_ref_3871_, lean_object* v_msg_3872_, lean_object* v_declHint_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3871_, v_msg_3872_, v_declHint_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3880_, lean_object* v_ref_3881_, lean_object* v_msg_3882_, lean_object* v_declHint_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3880_, v_ref_3881_, v_msg_3882_, v_declHint_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v_ref_3881_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3890_, lean_object* v_declHint_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3890_, v_declHint_3891_, v___y_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3898_, lean_object* v_declHint_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3898_, v_declHint_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3906_, lean_object* v_ref_3907_, lean_object* v_msg_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3907_, v_msg_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3915_, lean_object* v_ref_3916_, lean_object* v_msg_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3915_, v_ref_3916_, v_msg_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v_ref_3916_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3924_, lean_object* v_vals_3925_, lean_object* v_i_3926_, lean_object* v_k_3927_){
_start:
{
lean_object* v___x_3928_; uint8_t v___x_3929_; 
v___x_3928_ = lean_array_get_size(v_keys_3924_);
v___x_3929_ = lean_nat_dec_lt(v_i_3926_, v___x_3928_);
if (v___x_3929_ == 0)
{
lean_object* v___x_3930_; 
lean_dec(v_i_3926_);
v___x_3930_ = lean_box(0);
return v___x_3930_;
}
else
{
lean_object* v_k_x27_3931_; uint8_t v___x_3932_; 
v_k_x27_3931_ = lean_array_fget_borrowed(v_keys_3924_, v_i_3926_);
v___x_3932_ = lean_name_eq(v_k_3927_, v_k_x27_3931_);
if (v___x_3932_ == 0)
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_unsigned_to_nat(1u);
v___x_3934_ = lean_nat_add(v_i_3926_, v___x_3933_);
lean_dec(v_i_3926_);
v_i_3926_ = v___x_3934_;
goto _start;
}
else
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = lean_array_fget_borrowed(v_vals_3925_, v_i_3926_);
lean_dec(v_i_3926_);
lean_inc(v___x_3936_);
v___x_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
return v___x_3937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3938_, lean_object* v_vals_3939_, lean_object* v_i_3940_, lean_object* v_k_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3938_, v_vals_3939_, v_i_3940_, v_k_3941_);
lean_dec(v_k_3941_);
lean_dec_ref(v_vals_3939_);
lean_dec_ref(v_keys_3938_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3943_, size_t v_x_3944_, lean_object* v_x_3945_){
_start:
{
if (lean_obj_tag(v_x_3943_) == 0)
{
lean_object* v_es_3946_; lean_object* v___x_3947_; size_t v___x_3948_; size_t v___x_3949_; lean_object* v_j_3950_; lean_object* v___x_3951_; 
v_es_3946_ = lean_ctor_get(v_x_3943_, 0);
v___x_3947_ = lean_box(2);
v___x_3948_ = ((size_t)31ULL);
v___x_3949_ = lean_usize_land(v_x_3944_, v___x_3948_);
v_j_3950_ = lean_usize_to_nat(v___x_3949_);
v___x_3951_ = lean_array_get_borrowed(v___x_3947_, v_es_3946_, v_j_3950_);
lean_dec(v_j_3950_);
switch(lean_obj_tag(v___x_3951_))
{
case 0:
{
lean_object* v_key_3952_; lean_object* v_val_3953_; uint8_t v___x_3954_; 
v_key_3952_ = lean_ctor_get(v___x_3951_, 0);
v_val_3953_ = lean_ctor_get(v___x_3951_, 1);
v___x_3954_ = lean_name_eq(v_x_3945_, v_key_3952_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; 
v___x_3955_ = lean_box(0);
return v___x_3955_;
}
else
{
lean_object* v___x_3956_; 
lean_inc(v_val_3953_);
v___x_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_val_3953_);
return v___x_3956_;
}
}
case 1:
{
lean_object* v_node_3957_; size_t v___x_3958_; size_t v___x_3959_; 
v_node_3957_ = lean_ctor_get(v___x_3951_, 0);
v___x_3958_ = ((size_t)5ULL);
v___x_3959_ = lean_usize_shift_right(v_x_3944_, v___x_3958_);
v_x_3943_ = v_node_3957_;
v_x_3944_ = v___x_3959_;
goto _start;
}
default: 
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_box(0);
return v___x_3961_;
}
}
}
else
{
lean_object* v_ks_3962_; lean_object* v_vs_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_ks_3962_ = lean_ctor_get(v_x_3943_, 0);
v_vs_3963_ = lean_ctor_get(v_x_3943_, 1);
v___x_3964_ = lean_unsigned_to_nat(0u);
v___x_3965_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3962_, v_vs_3963_, v___x_3964_, v_x_3945_);
return v___x_3965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3966_, lean_object* v_x_3967_, lean_object* v_x_3968_){
_start:
{
size_t v_x_699__boxed_3969_; lean_object* v_res_3970_; 
v_x_699__boxed_3969_ = lean_unbox_usize(v_x_3967_);
lean_dec(v_x_3967_);
v_res_3970_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3966_, v_x_699__boxed_3969_, v_x_3968_);
lean_dec(v_x_3968_);
lean_dec_ref(v_x_3966_);
return v_res_3970_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3971_; uint64_t v___x_3972_; 
v___x_3971_ = lean_unsigned_to_nat(1723u);
v___x_3972_ = lean_uint64_of_nat(v___x_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3973_, lean_object* v_x_3974_){
_start:
{
uint64_t v___y_3976_; 
if (lean_obj_tag(v_x_3974_) == 0)
{
uint64_t v___x_3979_; 
v___x_3979_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0);
v___y_3976_ = v___x_3979_;
goto v___jp_3975_;
}
else
{
uint64_t v_hash_3980_; 
v_hash_3980_ = lean_ctor_get_uint64(v_x_3974_, sizeof(void*)*2);
v___y_3976_ = v_hash_3980_;
goto v___jp_3975_;
}
v___jp_3975_:
{
size_t v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = lean_uint64_to_usize(v___y_3976_);
v___x_3978_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3973_, v___x_3977_, v_x_3974_);
return v___x_3978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3981_, lean_object* v_x_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3981_, v_x_3982_);
lean_dec(v_x_3982_);
lean_dec_ref(v_x_3981_);
return v_res_3983_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3991_ = l_Lean_stringToMessageData(v___x_3990_);
return v___x_3991_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3993_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3994_ = l_Lean_stringToMessageData(v___x_3993_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v___x_4001_; lean_object* v_env_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4001_ = lean_st_ref_get(v_a_3999_);
v_env_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc_ref(v_env_4002_);
lean_dec(v___x_4001_);
lean_inc_n(v_matchDeclName_3995_, 3);
v___x_4003_ = l_Lean_mkPrivateName(v_env_4002_, v_matchDeclName_3995_);
lean_dec_ref(v_env_4002_);
v___x_4004_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_4003_);
v___x_4005_ = l_Lean_Name_append(v___x_4003_, v___x_4004_);
lean_inc_n(v___x_4005_, 2);
v___x_4006_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_4006_, 0, v_matchDeclName_3995_);
lean_closure_set(v___x_4006_, 1, v___x_4003_);
lean_closure_set(v___x_4006_, 2, v___x_4005_);
v___x_4007_ = l_Lean_Meta_realizeConst(v_matchDeclName_3995_, v___x_4005_, v___x_4006_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4036_; 
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4036_ == 0)
{
lean_object* v_unused_4037_; 
v_unused_4037_ = lean_ctor_get(v___x_4007_, 0);
lean_dec(v_unused_4037_);
v___x_4009_ = v___x_4007_;
v_isShared_4010_ = v_isSharedCheck_4036_;
goto v_resetjp_4008_;
}
else
{
lean_dec(v___x_4007_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4036_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; lean_object* v_env_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v_map_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4034_; 
v___x_4011_ = lean_st_ref_get(v_a_3999_);
v_env_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc_ref(v_env_4012_);
lean_dec(v___x_4011_);
v___x_4013_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_4014_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_4015_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_4016_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4013_, v___x_4014_, v_env_4012_, v___x_4015_, v___x_4005_);
v_map_4017_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; 
v_unused_4035_ = lean_ctor_get(v___x_4016_, 1);
lean_dec(v_unused_4035_);
v___x_4019_ = v___x_4016_;
v_isShared_4020_ = v_isSharedCheck_4034_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_map_4017_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4034_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; 
v___x_4021_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_4017_, v_matchDeclName_3995_);
lean_dec_ref(v_map_4017_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4025_; 
lean_del_object(v___x_4009_);
v___x_4022_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_4023_ = l_Lean_MessageData_ofName(v_matchDeclName_3995_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set_tag(v___x_4019_, 7);
lean_ctor_set(v___x_4019_, 1, v___x_4023_);
lean_ctor_set(v___x_4019_, 0, v___x_4022_);
v___x_4025_ = v___x_4019_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4022_);
lean_ctor_set(v_reuseFailAlloc_4029_, 1, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_4027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4025_);
lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_4027_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec(v_a_3997_);
lean_dec_ref(v_a_3996_);
return v___x_4028_;
}
}
else
{
lean_object* v_val_4030_; lean_object* v___x_4032_; 
lean_del_object(v___x_4019_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec(v_a_3997_);
lean_dec_ref(v_a_3996_);
lean_dec(v_matchDeclName_3995_);
v_val_4030_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_val_4030_);
lean_dec_ref_known(v___x_4021_, 1);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 0, v_val_4030_);
v___x_4032_ = v___x_4009_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_val_4030_);
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
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec(v___x_4005_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec(v_a_3997_);
lean_dec_ref(v_a_3996_);
lean_dec(v_matchDeclName_3995_);
v_a_4038_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4007_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4007_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = lean_get_match_equations_for(v_matchDeclName_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4053_, lean_object* v_x_4054_, lean_object* v_x_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4054_, v_x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4057_, lean_object* v_x_4058_, lean_object* v_x_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4057_, v_x_4058_, v_x_4059_);
lean_dec(v_x_4059_);
lean_dec_ref(v_x_4058_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4061_, lean_object* v_x_4062_, size_t v_x_4063_, lean_object* v_x_4064_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4062_, v_x_4063_, v_x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4066_, lean_object* v_x_4067_, lean_object* v_x_4068_, lean_object* v_x_4069_){
_start:
{
size_t v_x_897__boxed_4070_; lean_object* v_res_4071_; 
v_x_897__boxed_4070_ = lean_unbox_usize(v_x_4068_);
lean_dec(v_x_4068_);
v_res_4071_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4066_, v_x_4067_, v_x_897__boxed_4070_, v_x_4069_);
lean_dec(v_x_4069_);
lean_dec_ref(v_x_4067_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4072_, lean_object* v_keys_4073_, lean_object* v_vals_4074_, lean_object* v_heq_4075_, lean_object* v_i_4076_, lean_object* v_k_4077_){
_start:
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4073_, v_vals_4074_, v_i_4076_, v_k_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4079_, lean_object* v_keys_4080_, lean_object* v_vals_4081_, lean_object* v_heq_4082_, lean_object* v_i_4083_, lean_object* v_k_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4079_, v_keys_4080_, v_vals_4081_, v_heq_4082_, v_i_4083_, v_k_4084_);
lean_dec(v_k_4084_);
lean_dec_ref(v_vals_4081_);
lean_dec_ref(v_keys_4080_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4086_, lean_object* v_k_4087_, uint8_t v_cleanupAnnotations_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v___f_4094_; uint8_t v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___f_4094_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4094_, 0, v_k_4087_);
v___x_4095_ = 0;
v___x_4096_ = lean_box(0);
v___x_4097_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4095_, v___x_4096_, v_type_4086_, v___f_4094_, v_cleanupAnnotations_4088_, v___x_4095_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4097_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4097_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
else
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
v_a_4106_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v___x_4097_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4097_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4106_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4114_, lean_object* v_k_4115_, lean_object* v_cleanupAnnotations_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4122_; lean_object* v_res_4123_; 
v_cleanupAnnotations_boxed_4122_ = lean_unbox(v_cleanupAnnotations_4116_);
v_res_4123_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4114_, v_k_4115_, v_cleanupAnnotations_boxed_4122_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4124_, lean_object* v_type_4125_, lean_object* v_k_4126_, uint8_t v_cleanupAnnotations_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4125_, v_k_4126_, v_cleanupAnnotations_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4134_, lean_object* v_type_4135_, lean_object* v_k_4136_, lean_object* v_cleanupAnnotations_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4143_; lean_object* v_res_4144_; 
v_cleanupAnnotations_boxed_4143_ = lean_unbox(v_cleanupAnnotations_4137_);
v_res_4144_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4134_, v_type_4135_, v_k_4136_, v_cleanupAnnotations_boxed_4143_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v_msg_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v___f_4151_; lean_object* v___x_19933__overap_4152_; lean_object* v___x_4153_; 
v___f_4151_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_19933__overap_4152_ = lean_panic_fn_borrowed(v___f_4151_, v_msg_4145_);
lean_inc(v___y_4149_);
lean_inc_ref(v___y_4148_);
lean_inc(v___y_4147_);
lean_inc_ref(v___y_4146_);
v___x_4153_ = lean_apply_5(v___x_19933__overap_4152_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, lean_box(0));
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v_msg_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_msg_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4161_){
_start:
{
uint8_t v_foApprox_4162_; uint8_t v_ctxApprox_4163_; uint8_t v_quasiPatternApprox_4164_; uint8_t v_constApprox_4165_; uint8_t v_isDefEqStuckEx_4166_; uint8_t v_unificationHints_4167_; uint8_t v_proofIrrelevance_4168_; uint8_t v_assignSyntheticOpaque_4169_; uint8_t v_offsetCnstrs_4170_; uint8_t v_transparency_4171_; uint8_t v_univApprox_4172_; uint8_t v_iota_4173_; uint8_t v_beta_4174_; uint8_t v_proj_4175_; uint8_t v_zeta_4176_; uint8_t v_zetaDelta_4177_; uint8_t v_zetaUnused_4178_; uint8_t v_zetaHave_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4187_; 
v_foApprox_4162_ = lean_ctor_get_uint8(v_c_4161_, 0);
v_ctxApprox_4163_ = lean_ctor_get_uint8(v_c_4161_, 1);
v_quasiPatternApprox_4164_ = lean_ctor_get_uint8(v_c_4161_, 2);
v_constApprox_4165_ = lean_ctor_get_uint8(v_c_4161_, 3);
v_isDefEqStuckEx_4166_ = lean_ctor_get_uint8(v_c_4161_, 4);
v_unificationHints_4167_ = lean_ctor_get_uint8(v_c_4161_, 5);
v_proofIrrelevance_4168_ = lean_ctor_get_uint8(v_c_4161_, 6);
v_assignSyntheticOpaque_4169_ = lean_ctor_get_uint8(v_c_4161_, 7);
v_offsetCnstrs_4170_ = lean_ctor_get_uint8(v_c_4161_, 8);
v_transparency_4171_ = lean_ctor_get_uint8(v_c_4161_, 9);
v_univApprox_4172_ = lean_ctor_get_uint8(v_c_4161_, 11);
v_iota_4173_ = lean_ctor_get_uint8(v_c_4161_, 12);
v_beta_4174_ = lean_ctor_get_uint8(v_c_4161_, 13);
v_proj_4175_ = lean_ctor_get_uint8(v_c_4161_, 14);
v_zeta_4176_ = lean_ctor_get_uint8(v_c_4161_, 15);
v_zetaDelta_4177_ = lean_ctor_get_uint8(v_c_4161_, 16);
v_zetaUnused_4178_ = lean_ctor_get_uint8(v_c_4161_, 17);
v_zetaHave_4179_ = lean_ctor_get_uint8(v_c_4161_, 18);
v_isSharedCheck_4187_ = !lean_is_exclusive(v_c_4161_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4181_ = v_c_4161_;
v_isShared_4182_ = v_isSharedCheck_4187_;
goto v_resetjp_4180_;
}
else
{
lean_dec(v_c_4161_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4187_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
uint8_t v___x_4183_; lean_object* v___x_4185_; 
v___x_4183_ = 2;
if (v_isShared_4182_ == 0)
{
v___x_4185_ = v___x_4181_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 0, v_foApprox_4162_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 1, v_ctxApprox_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 2, v_quasiPatternApprox_4164_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 3, v_constApprox_4165_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 4, v_isDefEqStuckEx_4166_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 5, v_unificationHints_4167_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 6, v_proofIrrelevance_4168_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 7, v_assignSyntheticOpaque_4169_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 8, v_offsetCnstrs_4170_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 9, v_transparency_4171_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 11, v_univApprox_4172_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 12, v_iota_4173_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 13, v_beta_4174_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 14, v_proj_4175_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 15, v_zeta_4176_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 16, v_zetaDelta_4177_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 17, v_zetaUnused_4178_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, 18, v_zetaHave_4179_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
lean_ctor_set_uint8(v___x_4185_, 10, v___x_4183_);
return v___x_4185_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4188_, lean_object* v_t_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_dummy_4195_; lean_object* v_nargs_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v_dummy_4195_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4196_ = l_Lean_Expr_getAppNumArgs(v_t_4189_);
lean_inc(v_nargs_4196_);
v___x_4197_ = lean_mk_array(v_nargs_4196_, v_dummy_4195_);
v___x_4198_ = lean_unsigned_to_nat(1u);
v___x_4199_ = lean_nat_sub(v_nargs_4196_, v___x_4198_);
lean_dec(v_nargs_4196_);
v___x_4200_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4189_, v___x_4197_, v___x_4199_);
v___x_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4202_, lean_object* v_t_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4202_, v_t_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v_x_4202_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4210_, lean_object* v_x_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4217_, 0, v_snd_4210_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4218_, lean_object* v_x_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4218_, v_x_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec_ref(v_x_4219_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4226_, size_t v_i_4227_, lean_object* v_bs_4228_){
_start:
{
uint8_t v___x_4229_; 
v___x_4229_ = lean_usize_dec_lt(v_i_4227_, v_sz_4226_);
if (v___x_4229_ == 0)
{
return v_bs_4228_;
}
else
{
lean_object* v_v_4230_; lean_object* v_fst_4231_; lean_object* v_snd_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4246_; 
v_v_4230_ = lean_array_uget(v_bs_4228_, v_i_4227_);
v_fst_4231_ = lean_ctor_get(v_v_4230_, 0);
v_snd_4232_ = lean_ctor_get(v_v_4230_, 1);
v_isSharedCheck_4246_ = !lean_is_exclusive(v_v_4230_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4234_ = v_v_4230_;
v_isShared_4235_ = v_isSharedCheck_4246_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_snd_4232_);
lean_inc(v_fst_4231_);
lean_dec(v_v_4230_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4246_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4236_; lean_object* v_bs_x27_4237_; lean_object* v___f_4238_; lean_object* v___x_4240_; 
v___x_4236_ = lean_unsigned_to_nat(0u);
v_bs_x27_4237_ = lean_array_uset(v_bs_4228_, v_i_4227_, v___x_4236_);
v___f_4238_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4238_, 0, v_snd_4232_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 1, v___f_4238_);
v___x_4240_ = v___x_4234_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_fst_4231_);
lean_ctor_set(v_reuseFailAlloc_4245_, 1, v___f_4238_);
v___x_4240_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
size_t v___x_4241_; size_t v___x_4242_; lean_object* v___x_4243_; 
v___x_4241_ = ((size_t)1ULL);
v___x_4242_ = lean_usize_add(v_i_4227_, v___x_4241_);
v___x_4243_ = lean_array_uset(v_bs_x27_4237_, v_i_4227_, v___x_4240_);
v_i_4227_ = v___x_4242_;
v_bs_4228_ = v___x_4243_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4247_, lean_object* v_i_4248_, lean_object* v_bs_4249_){
_start:
{
size_t v_sz_boxed_4250_; size_t v_i_boxed_4251_; lean_object* v_res_4252_; 
v_sz_boxed_4250_ = lean_unbox_usize(v_sz_4247_);
lean_dec(v_sz_4247_);
v_i_boxed_4251_ = lean_unbox_usize(v_i_4248_);
lean_dec(v_i_4248_);
v_res_4252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4250_, v_i_boxed_4251_, v_bs_4249_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4253_, size_t v_i_4254_, lean_object* v_bs_4255_){
_start:
{
uint8_t v___x_4256_; 
v___x_4256_ = lean_usize_dec_lt(v_i_4254_, v_sz_4253_);
if (v___x_4256_ == 0)
{
return v_bs_4255_;
}
else
{
lean_object* v_v_4257_; lean_object* v_fst_4258_; lean_object* v_snd_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4275_; 
v_v_4257_ = lean_array_uget(v_bs_4255_, v_i_4254_);
v_fst_4258_ = lean_ctor_get(v_v_4257_, 0);
v_snd_4259_ = lean_ctor_get(v_v_4257_, 1);
v_isSharedCheck_4275_ = !lean_is_exclusive(v_v_4257_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4261_ = v_v_4257_;
v_isShared_4262_ = v_isSharedCheck_4275_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_snd_4259_);
lean_inc(v_fst_4258_);
lean_dec(v_v_4257_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4275_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4263_; lean_object* v_bs_x27_4264_; uint8_t v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4268_; 
v___x_4263_ = lean_unsigned_to_nat(0u);
v_bs_x27_4264_ = lean_array_uset(v_bs_4255_, v_i_4254_, v___x_4263_);
v___x_4265_ = 0;
v___x_4266_ = lean_box(v___x_4265_);
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 0, v___x_4266_);
v___x_4268_ = v___x_4261_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4266_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v_snd_4259_);
v___x_4268_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
lean_object* v___x_4269_; size_t v___x_4270_; size_t v___x_4271_; lean_object* v___x_4272_; 
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v_fst_4258_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = ((size_t)1ULL);
v___x_4271_ = lean_usize_add(v_i_4254_, v___x_4270_);
v___x_4272_ = lean_array_uset(v_bs_x27_4264_, v_i_4254_, v___x_4269_);
v_i_4254_ = v___x_4271_;
v_bs_4255_ = v___x_4272_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4276_, lean_object* v_i_4277_, lean_object* v_bs_4278_){
_start:
{
size_t v_sz_boxed_4279_; size_t v_i_boxed_4280_; lean_object* v_res_4281_; 
v_sz_boxed_4279_ = lean_unbox_usize(v_sz_4276_);
lean_dec(v_sz_4276_);
v_i_boxed_4280_ = lean_unbox_usize(v_i_4277_);
lean_dec(v_i_4277_);
v_res_4281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4279_, v_i_boxed_4280_, v_bs_4278_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4282_, lean_object* v_a_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_21855__overap_4290_; lean_object* v___x_4291_; 
v___x_4289_ = l_Lean_instInhabitedExpr;
v___x_21855__overap_4290_ = l_instInhabitedOfMonad___redArg(v___x_4282_, v___x_4289_);
lean_inc(v___y_4287_);
lean_inc_ref(v___y_4286_);
lean_inc(v___y_4285_);
lean_inc_ref(v___y_4284_);
v___x_4291_ = lean_apply_5(v___x_21855__overap_4290_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, lean_box(0));
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4292_, lean_object* v_a_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4292_, v_a_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec_ref(v_a_4293_);
return v_res_4299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l_instMonadEIO(lean_box(0));
return v___x_4300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4301_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4302_ = l_StateRefT_x27_instMonad___redArg(v___x_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4307_, lean_object* v_declInfos_4308_, lean_object* v_k_4309_, lean_object* v_kind_4310_, lean_object* v_x_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
uint8_t v_kind_boxed_4317_; lean_object* v_res_4318_; 
v_kind_boxed_4317_ = lean_unbox(v_kind_4310_);
v_res_4318_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4307_, v_declInfos_4308_, v_k_4309_, v_kind_boxed_4317_, v_x_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4319_, lean_object* v_k_4320_, uint8_t v_kind_4321_, lean_object* v_acc_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v___x_4328_; lean_object* v_toApplicative_4329_; lean_object* v_toFunctor_4330_; lean_object* v_toSeq_4331_; lean_object* v_toSeqLeft_4332_; lean_object* v_toSeqRight_4333_; lean_object* v___f_4334_; lean_object* v___f_4335_; lean_object* v___f_4336_; lean_object* v___f_4337_; lean_object* v___x_4338_; lean_object* v___f_4339_; lean_object* v___f_4340_; lean_object* v___f_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v_toApplicative_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4394_; 
v___x_4328_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4329_ = lean_ctor_get(v___x_4328_, 0);
v_toFunctor_4330_ = lean_ctor_get(v_toApplicative_4329_, 0);
v_toSeq_4331_ = lean_ctor_get(v_toApplicative_4329_, 2);
v_toSeqLeft_4332_ = lean_ctor_get(v_toApplicative_4329_, 3);
v_toSeqRight_4333_ = lean_ctor_get(v_toApplicative_4329_, 4);
v___f_4334_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4335_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4330_, 2);
v___f_4336_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4336_, 0, v_toFunctor_4330_);
v___f_4337_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4337_, 0, v_toFunctor_4330_);
v___x_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___f_4336_);
lean_ctor_set(v___x_4338_, 1, v___f_4337_);
lean_inc(v_toSeqRight_4333_);
v___f_4339_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4339_, 0, v_toSeqRight_4333_);
lean_inc(v_toSeqLeft_4332_);
v___f_4340_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4340_, 0, v_toSeqLeft_4332_);
lean_inc(v_toSeq_4331_);
v___f_4341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4341_, 0, v_toSeq_4331_);
v___x_4342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4338_);
lean_ctor_set(v___x_4342_, 1, v___f_4334_);
lean_ctor_set(v___x_4342_, 2, v___f_4341_);
lean_ctor_set(v___x_4342_, 3, v___f_4340_);
lean_ctor_set(v___x_4342_, 4, v___f_4339_);
v___x_4343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
lean_ctor_set(v___x_4343_, 1, v___f_4335_);
v___x_4344_ = l_StateRefT_x27_instMonad___redArg(v___x_4343_);
v_toApplicative_4345_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4394_ == 0)
{
lean_object* v_unused_4395_; 
v_unused_4395_ = lean_ctor_get(v___x_4344_, 1);
lean_dec(v_unused_4395_);
v___x_4347_ = v___x_4344_;
v_isShared_4348_ = v_isSharedCheck_4394_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_toApplicative_4345_);
lean_dec(v___x_4344_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4394_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v_toFunctor_4349_; lean_object* v_toSeq_4350_; lean_object* v_toSeqLeft_4351_; lean_object* v_toSeqRight_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4392_; 
v_toFunctor_4349_ = lean_ctor_get(v_toApplicative_4345_, 0);
v_toSeq_4350_ = lean_ctor_get(v_toApplicative_4345_, 2);
v_toSeqLeft_4351_ = lean_ctor_get(v_toApplicative_4345_, 3);
v_toSeqRight_4352_ = lean_ctor_get(v_toApplicative_4345_, 4);
v_isSharedCheck_4392_ = !lean_is_exclusive(v_toApplicative_4345_);
if (v_isSharedCheck_4392_ == 0)
{
lean_object* v_unused_4393_; 
v_unused_4393_ = lean_ctor_get(v_toApplicative_4345_, 1);
lean_dec(v_unused_4393_);
v___x_4354_ = v_toApplicative_4345_;
v_isShared_4355_ = v_isSharedCheck_4392_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_toSeqRight_4352_);
lean_inc(v_toSeqLeft_4351_);
lean_inc(v_toSeq_4350_);
lean_inc(v_toFunctor_4349_);
lean_dec(v_toApplicative_4345_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4392_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___f_4356_; lean_object* v___f_4357_; lean_object* v___f_4358_; lean_object* v___f_4359_; lean_object* v___x_4360_; lean_object* v___f_4361_; lean_object* v___f_4362_; lean_object* v___f_4363_; lean_object* v___x_4365_; 
v___f_4356_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4357_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4349_);
v___f_4358_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4358_, 0, v_toFunctor_4349_);
v___f_4359_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4359_, 0, v_toFunctor_4349_);
v___x_4360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___f_4358_);
lean_ctor_set(v___x_4360_, 1, v___f_4359_);
v___f_4361_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4361_, 0, v_toSeqRight_4352_);
v___f_4362_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4362_, 0, v_toSeqLeft_4351_);
v___f_4363_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4363_, 0, v_toSeq_4350_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 4, v___f_4361_);
lean_ctor_set(v___x_4354_, 3, v___f_4362_);
lean_ctor_set(v___x_4354_, 2, v___f_4363_);
lean_ctor_set(v___x_4354_, 1, v___f_4356_);
lean_ctor_set(v___x_4354_, 0, v___x_4360_);
v___x_4365_ = v___x_4354_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4360_);
lean_ctor_set(v_reuseFailAlloc_4391_, 1, v___f_4356_);
lean_ctor_set(v_reuseFailAlloc_4391_, 2, v___f_4363_);
lean_ctor_set(v_reuseFailAlloc_4391_, 3, v___f_4362_);
lean_ctor_set(v_reuseFailAlloc_4391_, 4, v___f_4361_);
v___x_4365_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4367_; 
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 1, v___f_4357_);
lean_ctor_set(v___x_4347_, 0, v___x_4365_);
v___x_4367_ = v___x_4347_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4365_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v___f_4357_);
v___x_4367_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; uint8_t v___x_4370_; 
v___x_4368_ = lean_array_get_size(v_acc_4322_);
v___x_4369_ = lean_array_get_size(v_declInfos_4319_);
v___x_4370_ = lean_nat_dec_lt(v___x_4368_, v___x_4369_);
if (v___x_4370_ == 0)
{
lean_object* v___x_4371_; 
lean_dec_ref(v___x_4367_);
lean_dec_ref(v_declInfos_4319_);
lean_inc(v___y_4326_);
lean_inc_ref(v___y_4325_);
lean_inc(v___y_4324_);
lean_inc_ref(v___y_4323_);
v___x_4371_ = lean_apply_6(v_k_4320_, v_acc_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, lean_box(0));
return v___x_4371_;
}
else
{
lean_object* v___f_4372_; lean_object* v___x_4373_; uint8_t v___x_4374_; lean_object* v___f_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v_snd_4380_; lean_object* v_fst_4381_; lean_object* v_fst_4382_; lean_object* v_snd_4383_; lean_object* v___x_4384_; 
v___f_4372_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4372_, 0, v___x_4367_);
v___x_4373_ = lean_box(0);
v___x_4374_ = 0;
v___f_4375_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4375_, 0, v___f_4372_);
v___x_4376_ = lean_box(v___x_4374_);
v___x_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
lean_ctor_set(v___x_4377_, 1, v___f_4375_);
v___x_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4373_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
v___x_4379_ = lean_array_get(v___x_4378_, v_declInfos_4319_, v___x_4368_);
lean_dec_ref_known(v___x_4378_, 2);
v_snd_4380_ = lean_ctor_get(v___x_4379_, 1);
lean_inc(v_snd_4380_);
v_fst_4381_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_fst_4381_);
lean_dec(v___x_4379_);
v_fst_4382_ = lean_ctor_get(v_snd_4380_, 0);
lean_inc(v_fst_4382_);
v_snd_4383_ = lean_ctor_get(v_snd_4380_, 1);
lean_inc(v_snd_4383_);
lean_dec(v_snd_4380_);
lean_inc(v___y_4326_);
lean_inc_ref(v___y_4325_);
lean_inc(v___y_4324_);
lean_inc_ref(v___y_4323_);
lean_inc_ref(v_acc_4322_);
v___x_4384_ = lean_apply_6(v_snd_4383_, v_acc_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, lean_box(0));
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; lean_object* v___f_4387_; uint8_t v___x_4388_; lean_object* v___x_4389_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = lean_box(v_kind_4321_);
v___f_4387_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4387_, 0, v_acc_4322_);
lean_closure_set(v___f_4387_, 1, v_declInfos_4319_);
lean_closure_set(v___f_4387_, 2, v_k_4320_);
lean_closure_set(v___f_4387_, 3, v___x_4386_);
v___x_4388_ = lean_unbox(v_fst_4382_);
lean_dec(v_fst_4382_);
v___x_4389_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4381_, v___x_4388_, v_a_4385_, v___f_4387_, v_kind_4321_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
return v___x_4389_;
}
else
{
lean_dec(v_fst_4382_);
lean_dec(v_fst_4381_);
lean_dec_ref(v_acc_4322_);
lean_dec_ref(v_k_4320_);
lean_dec_ref(v_declInfos_4319_);
return v___x_4384_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4396_, lean_object* v_declInfos_4397_, lean_object* v_k_4398_, uint8_t v_kind_4399_, lean_object* v_x_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4406_ = lean_array_push(v_acc_4396_, v_x_4400_);
v___x_4407_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4397_, v_k_4398_, v_kind_4399_, v___x_4406_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4408_, lean_object* v_k_4409_, lean_object* v_kind_4410_, lean_object* v_acc_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
uint8_t v_kind_boxed_4417_; lean_object* v_res_4418_; 
v_kind_boxed_4417_ = lean_unbox(v_kind_4410_);
v_res_4418_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4408_, v_k_4409_, v_kind_boxed_4417_, v_acc_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4419_, lean_object* v_k_4420_, uint8_t v_kind_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4428_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4419_, v_k_4420_, v_kind_4421_, v___x_4427_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4429_, lean_object* v_k_4430_, lean_object* v_kind_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
uint8_t v_kind_boxed_4437_; lean_object* v_res_4438_; 
v_kind_boxed_4437_ = lean_unbox(v_kind_4431_);
v_res_4438_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4429_, v_k_4430_, v_kind_boxed_4437_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4439_, lean_object* v_k_4440_, uint8_t v_kind_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
size_t v_sz_4447_; size_t v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v_sz_4447_ = lean_array_size(v_declInfos_4439_);
v___x_4448_ = ((size_t)0ULL);
v___x_4449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4447_, v___x_4448_, v_declInfos_4439_);
v___x_4450_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4449_, v_k_4440_, v_kind_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
return v___x_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4451_, lean_object* v_k_4452_, lean_object* v_kind_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
uint8_t v_kind_boxed_4459_; lean_object* v_res_4460_; 
v_kind_boxed_4459_ = lean_unbox(v_kind_4453_);
v_res_4460_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4451_, v_k_4452_, v_kind_boxed_4459_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4461_, lean_object* v_k_4462_, uint8_t v_kind_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_){
_start:
{
size_t v_sz_4469_; size_t v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v_sz_4469_ = lean_array_size(v_declInfos_4461_);
v___x_4470_ = ((size_t)0ULL);
v___x_4471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4469_, v___x_4470_, v_declInfos_4461_);
v___x_4472_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4471_, v_k_4462_, v_kind_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4473_, lean_object* v_k_4474_, lean_object* v_kind_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
uint8_t v_kind_boxed_4481_; lean_object* v_res_4482_; 
v_kind_boxed_4481_ = lean_unbox(v_kind_4475_);
v_res_4482_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4473_, v_k_4474_, v_kind_boxed_4481_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(lean_object* v_a_4486_, lean_object* v_b_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_array_4493_; lean_object* v_start_4494_; lean_object* v_stop_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4553_; 
v_array_4493_ = lean_ctor_get(v_a_4486_, 0);
v_start_4494_ = lean_ctor_get(v_a_4486_, 1);
v_stop_4495_ = lean_ctor_get(v_a_4486_, 2);
v_isSharedCheck_4553_ = !lean_is_exclusive(v_a_4486_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4497_ = v_a_4486_;
v_isShared_4498_ = v_isSharedCheck_4553_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_stop_4495_);
lean_inc(v_start_4494_);
lean_inc(v_array_4493_);
lean_dec(v_a_4486_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4553_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
uint8_t v___x_4499_; 
v___x_4499_ = lean_nat_dec_lt(v_start_4494_, v_stop_4495_);
if (v___x_4499_ == 0)
{
lean_object* v___x_4500_; 
lean_del_object(v___x_4497_);
lean_dec(v_stop_4495_);
lean_dec(v_start_4494_);
lean_dec_ref(v_array_4493_);
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v_b_4487_);
return v___x_4500_;
}
else
{
lean_object* v_snd_4501_; lean_object* v_fst_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4552_; 
v_snd_4501_ = lean_ctor_get(v_b_4487_, 1);
v_fst_4502_ = lean_ctor_get(v_b_4487_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v_b_4487_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4504_ = v_b_4487_;
v_isShared_4505_ = v_isSharedCheck_4552_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_snd_4501_);
lean_inc(v_fst_4502_);
lean_dec(v_b_4487_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4552_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v_array_4506_; lean_object* v_start_4507_; lean_object* v_stop_4508_; uint8_t v___x_4509_; 
v_array_4506_ = lean_ctor_get(v_snd_4501_, 0);
v_start_4507_ = lean_ctor_get(v_snd_4501_, 1);
v_stop_4508_ = lean_ctor_get(v_snd_4501_, 2);
v___x_4509_ = lean_nat_dec_lt(v_start_4507_, v_stop_4508_);
if (v___x_4509_ == 0)
{
lean_object* v___x_4511_; 
lean_del_object(v___x_4497_);
lean_dec(v_stop_4495_);
lean_dec(v_start_4494_);
lean_dec_ref(v_array_4493_);
if (v_isShared_4505_ == 0)
{
v___x_4511_ = v___x_4504_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_fst_4502_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_snd_4501_);
v___x_4511_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
lean_object* v___x_4512_; 
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
return v___x_4512_;
}
}
else
{
lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4548_; 
lean_inc(v_stop_4508_);
lean_inc(v_start_4507_);
lean_inc_ref(v_array_4506_);
v_isSharedCheck_4548_ = !lean_is_exclusive(v_snd_4501_);
if (v_isSharedCheck_4548_ == 0)
{
lean_object* v_unused_4549_; lean_object* v_unused_4550_; lean_object* v_unused_4551_; 
v_unused_4549_ = lean_ctor_get(v_snd_4501_, 2);
lean_dec(v_unused_4549_);
v_unused_4550_ = lean_ctor_get(v_snd_4501_, 1);
lean_dec(v_unused_4550_);
v_unused_4551_ = lean_ctor_get(v_snd_4501_, 0);
lean_dec(v_unused_4551_);
v___x_4515_ = v_snd_4501_;
v_isShared_4516_ = v_isSharedCheck_4548_;
goto v_resetjp_4514_;
}
else
{
lean_dec(v_snd_4501_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4548_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4517_ = lean_array_fget_borrowed(v_array_4493_, v_start_4494_);
v___x_4518_ = lean_array_fget_borrowed(v_array_4506_, v_start_4507_);
lean_inc(v___x_4518_);
lean_inc(v___x_4517_);
v___x_4519_ = l_Lean_Meta_mkEqHEq(v___x_4517_, v___x_4518_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4524_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4520_);
lean_dec_ref_known(v___x_4519_, 1);
v___x_4521_ = lean_unsigned_to_nat(1u);
v___x_4522_ = lean_nat_add(v_start_4494_, v___x_4521_);
lean_dec(v_start_4494_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 2, v_stop_4495_);
lean_ctor_set(v___x_4515_, 1, v___x_4522_);
lean_ctor_set(v___x_4515_, 0, v_array_4493_);
v___x_4524_ = v___x_4515_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_array_4493_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v___x_4522_);
lean_ctor_set(v_reuseFailAlloc_4539_, 2, v_stop_4495_);
v___x_4524_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
lean_object* v___x_4525_; lean_object* v___x_4527_; 
v___x_4525_ = lean_nat_add(v_start_4507_, v___x_4521_);
lean_dec(v_start_4507_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 2, v_stop_4508_);
lean_ctor_set(v___x_4497_, 1, v___x_4525_);
lean_ctor_set(v___x_4497_, 0, v_array_4506_);
v___x_4527_ = v___x_4497_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_array_4506_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v___x_4525_);
lean_ctor_set(v_reuseFailAlloc_4538_, 2, v_stop_4508_);
v___x_4527_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4533_; 
v___x_4528_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__1));
v___x_4529_ = lean_array_get_size(v_fst_4502_);
v___x_4530_ = lean_nat_add(v___x_4529_, v___x_4521_);
v___x_4531_ = lean_name_append_index_after(v___x_4528_, v___x_4530_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 1, v_a_4520_);
lean_ctor_set(v___x_4504_, 0, v___x_4531_);
v___x_4533_ = v___x_4504_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4531_);
lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_a_4520_);
v___x_4533_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
v___x_4534_ = lean_array_push(v_fst_4502_, v___x_4533_);
v___x_4535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4535_, 0, v___x_4534_);
lean_ctor_set(v___x_4535_, 1, v___x_4527_);
v_a_4486_ = v___x_4524_;
v_b_4487_ = v___x_4535_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_del_object(v___x_4515_);
lean_dec(v_stop_4508_);
lean_dec(v_start_4507_);
lean_dec_ref(v_array_4506_);
lean_del_object(v___x_4504_);
lean_dec(v_fst_4502_);
lean_del_object(v___x_4497_);
lean_dec(v_stop_4495_);
lean_dec(v_start_4494_);
lean_dec_ref(v_array_4493_);
v_a_4540_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4519_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4519_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___boxed(lean_object* v_a_4554_, lean_object* v_b_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_4554_, v_b_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v___x_4562_, lean_object* v_a_4563_, lean_object* v___x_4564_, lean_object* v_as_4565_, size_t v_sz_4566_, size_t v_i_4567_, lean_object* v_b_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
uint8_t v___x_4574_; 
v___x_4574_ = lean_usize_dec_lt(v_i_4567_, v_sz_4566_);
if (v___x_4574_ == 0)
{
lean_object* v___x_4575_; 
lean_dec(v___x_4564_);
v___x_4575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4575_, 0, v_b_4568_);
return v___x_4575_;
}
else
{
lean_object* v___x_4576_; lean_object* v_a_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4576_ = l_Lean_instInhabitedExpr;
v_a_4577_ = lean_array_uget_borrowed(v_as_4565_, v_i_4567_);
v___x_4578_ = lean_array_get_borrowed(v___x_4576_, v___x_4562_, v_a_4577_);
lean_inc(v___x_4578_);
v___x_4579_ = l_Lean_Meta_instantiateForall(v___x_4578_, v_a_4563_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v___x_4581_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref_known(v___x_4579_, 1);
lean_inc(v___x_4564_);
v___x_4581_ = l_Lean_Meta_Match_simpH_x3f(v_a_4580_, v___x_4564_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v_a_4584_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc(v_a_4582_);
lean_dec_ref_known(v___x_4581_, 1);
if (lean_obj_tag(v_a_4582_) == 1)
{
lean_object* v_val_4588_; lean_object* v___x_4589_; 
v_val_4588_ = lean_ctor_get(v_a_4582_, 0);
lean_inc(v_val_4588_);
lean_dec_ref_known(v_a_4582_, 1);
v___x_4589_ = lean_array_push(v_b_4568_, v_val_4588_);
v_a_4584_ = v___x_4589_;
goto v___jp_4583_;
}
else
{
lean_dec(v_a_4582_);
v_a_4584_ = v_b_4568_;
goto v___jp_4583_;
}
v___jp_4583_:
{
size_t v___x_4585_; size_t v___x_4586_; 
v___x_4585_ = ((size_t)1ULL);
v___x_4586_ = lean_usize_add(v_i_4567_, v___x_4585_);
v_i_4567_ = v___x_4586_;
v_b_4568_ = v_a_4584_;
goto _start;
}
}
else
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4597_; 
lean_dec_ref(v_b_4568_);
lean_dec(v___x_4564_);
v_a_4590_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4592_ = v___x_4581_;
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4581_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4597_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v___x_4595_; 
if (v_isShared_4593_ == 0)
{
v___x_4595_ = v___x_4592_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4605_; 
lean_dec_ref(v_b_4568_);
lean_dec(v___x_4564_);
v_a_4598_ = lean_ctor_get(v___x_4579_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4600_ = v___x_4579_;
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4579_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4603_; 
if (v_isShared_4601_ == 0)
{
v___x_4603_ = v___x_4600_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4598_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v___x_4606_, lean_object* v_a_4607_, lean_object* v___x_4608_, lean_object* v_as_4609_, lean_object* v_sz_4610_, lean_object* v_i_4611_, lean_object* v_b_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
size_t v_sz_boxed_4618_; size_t v_i_boxed_4619_; lean_object* v_res_4620_; 
v_sz_boxed_4618_ = lean_unbox_usize(v_sz_4610_);
lean_dec(v_sz_4610_);
v_i_boxed_4619_ = lean_unbox_usize(v_i_4611_);
lean_dec(v_i_4611_);
v_res_4620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v___x_4606_, v_a_4607_, v___x_4608_, v_as_4609_, v_sz_boxed_4618_, v_i_boxed_4619_, v_b_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec_ref(v_as_4609_);
lean_dec_ref(v_a_4607_);
lean_dec_ref(v___x_4606_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4621_, lean_object* v_args_4622_, lean_object* v___x_4623_, lean_object* v_overlaps_4624_, lean_object* v_a_4625_, lean_object* v_fst_4626_, lean_object* v_a_4627_, lean_object* v___x_4628_, lean_object* v___x_4629_, lean_object* v___x_4630_, lean_object* v___x_4631_, lean_object* v_altVars_4632_, uint8_t v___x_4633_, uint8_t v___x_4634_, lean_object* v_a_4635_, lean_object* v___x_4636_, lean_object* v___x_4637_, lean_object* v___x_4638_, lean_object* v___x_4639_, lean_object* v___x_4640_, lean_object* v___x_4641_, lean_object* v___x_4642_, lean_object* v_matchDeclName_4643_, lean_object* v___x_4644_, lean_object* v___x_4645_, lean_object* v___x_4646_, lean_object* v_heqs_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4653_ = l_Lean_mkAppN(v___y_4621_, v_args_4622_);
lean_inc_ref(v_heqs_4647_);
v___x_4654_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4653_, v_heqs_4647_, v___x_4623_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
if (lean_obj_tag(v___x_4654_) == 0)
{
lean_object* v_a_4655_; lean_object* v___x_4656_; size_t v_sz_4657_; size_t v___x_4658_; lean_object* v___x_4659_; 
v_a_4655_ = lean_ctor_get(v___x_4654_, 0);
lean_inc(v_a_4655_);
lean_dec_ref_known(v___x_4654_, 1);
v___x_4656_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4624_, v_a_4625_);
v_sz_4657_ = lean_array_size(v___x_4656_);
v___x_4658_ = ((size_t)0ULL);
lean_inc_ref(v___x_4629_);
v___x_4659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_fst_4626_, v_a_4627_, v___x_4628_, v___x_4656_, v_sz_4657_, v___x_4658_, v___x_4629_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
lean_dec_ref(v___x_4656_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v_options_4772_; uint8_t v_hasTrace_4773_; 
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
lean_inc(v_a_4660_);
lean_dec_ref_known(v___x_4659_, 1);
v_options_4772_ = lean_ctor_get(v___y_4650_, 2);
v_hasTrace_4773_ = lean_ctor_get_uint8(v_options_4772_, sizeof(void*)*1);
if (v_hasTrace_4773_ == 0)
{
v___y_4662_ = v___y_4648_;
v___y_4663_ = v___y_4649_;
v___y_4664_ = v___y_4650_;
v___y_4665_ = v___y_4651_;
goto v___jp_4661_;
}
else
{
lean_object* v_inheritedTraceOptions_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; uint8_t v___x_4777_; 
v_inheritedTraceOptions_4774_ = lean_ctor_get(v___y_4650_, 13);
v___x_4775_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4776_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4774_, v_options_4772_, v___x_4776_);
if (v___x_4777_ == 0)
{
v___y_4662_ = v___y_4648_;
v___y_4663_ = v___y_4649_;
v___y_4664_ = v___y_4650_;
v___y_4665_ = v___y_4651_;
goto v___jp_4661_;
}
else
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4778_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4660_);
v___x_4779_ = lean_array_to_list(v_a_4660_);
v___x_4780_ = lean_box(0);
v___x_4781_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4779_, v___x_4780_);
v___x_4782_ = l_Lean_MessageData_ofList(v___x_4781_);
v___x_4783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4778_);
lean_ctor_set(v___x_4783_, 1, v___x_4782_);
v___x_4784_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4775_, v___x_4783_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_dec_ref_known(v___x_4784_, 1);
v___y_4662_ = v___y_4648_;
v___y_4663_ = v___y_4649_;
v___y_4664_ = v___y_4650_;
v___y_4665_ = v___y_4651_;
goto v___jp_4661_;
}
else
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4792_; 
lean_dec(v_a_4660_);
lean_dec(v_a_4655_);
lean_dec_ref(v_heqs_4647_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
lean_dec(v_matchDeclName_4643_);
lean_dec_ref(v___x_4640_);
lean_dec_ref(v___x_4639_);
lean_dec_ref(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec(v___x_4630_);
lean_dec_ref(v___x_4629_);
lean_dec_ref(v_a_4627_);
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4787_ = v___x_4784_;
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4784_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4790_; 
if (v_isShared_4788_ == 0)
{
v___x_4790_ = v___x_4787_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4785_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
}
v___jp_4661_:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; size_t v_sz_4673_; lean_object* v___x_4674_; 
v___x_4666_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4667_ = l_Array_reverse___redArg(v_a_4627_);
v___x_4668_ = lean_array_get_size(v___x_4667_);
v___x_4669_ = l_Array_toSubarray___redArg(v___x_4667_, v___x_4630_, v___x_4668_);
lean_inc_ref(v___x_4631_);
v___x_4670_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4631_, v___x_4629_);
v___x_4671_ = l_Array_reverse___redArg(v___x_4670_);
v___x_4672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4666_);
lean_ctor_set(v___x_4672_, 1, v___x_4669_);
v_sz_4673_ = lean_array_size(v___x_4671_);
v___x_4674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4671_, v_sz_4673_, v___x_4658_, v___x_4672_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
lean_dec_ref(v___x_4671_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v_fst_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4762_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v___x_4674_, 1);
v_fst_4676_ = lean_ctor_get(v_a_4675_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v_a_4675_);
if (v_isSharedCheck_4762_ == 0)
{
lean_object* v_unused_4763_; 
v_unused_4763_ = lean_ctor_get(v_a_4675_, 1);
lean_dec(v_unused_4763_);
v___x_4678_ = v_a_4675_;
v_isShared_4679_ = v_isSharedCheck_4762_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_fst_4676_);
lean_dec(v_a_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4762_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4680_; lean_object* v___x_4681_; uint8_t v___x_4682_; lean_object* v___x_4683_; 
v___x_4680_ = l_Subarray_copy___redArg(v___x_4631_);
lean_inc_ref(v___x_4680_);
v___x_4681_ = l_Array_append___redArg(v___x_4680_, v_altVars_4632_);
v___x_4682_ = 1;
v___x_4683_ = l_Lean_Meta_mkForallFVars(v___x_4681_, v_fst_4676_, v___x_4633_, v___x_4634_, v___x_4634_, v___x_4682_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
lean_dec_ref(v___x_4681_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc(v_a_4684_);
lean_dec_ref_known(v___x_4683_, 1);
v___x_4685_ = l_Lean_ConstantInfo_name(v_a_4635_);
v___x_4686_ = l_Lean_mkConst(v___x_4685_, v___x_4636_);
lean_inc_ref(v___x_4637_);
v___x_4687_ = l_Subarray_copy___redArg(v___x_4637_);
v___x_4688_ = lean_mk_empty_array_with_capacity(v___x_4638_);
v___x_4689_ = lean_array_push(v___x_4688_, v___x_4639_);
v___x_4690_ = l_Array_append___redArg(v___x_4687_, v___x_4689_);
lean_dec_ref(v___x_4689_);
v___x_4691_ = l_Array_append___redArg(v___x_4690_, v___x_4680_);
lean_dec_ref(v___x_4680_);
v___x_4692_ = l_Subarray_copy___redArg(v___x_4640_);
v___x_4693_ = l_Array_append___redArg(v___x_4691_, v___x_4692_);
lean_dec_ref(v___x_4692_);
v___x_4694_ = l_Lean_mkAppN(v___x_4686_, v___x_4693_);
v___x_4695_ = l_Lean_Meta_mkHEq(v___x_4694_, v_a_4655_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; lean_object* v___x_4697_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref_known(v___x_4695_, 1);
v___x_4697_ = l_Lean_mkArrowN(v_a_4660_, v_a_4696_, v___y_4664_, v___y_4665_);
lean_dec(v_a_4660_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4698_);
lean_dec_ref_known(v___x_4697_, 1);
v___x_4699_ = l_Array_append___redArg(v___x_4693_, v_altVars_4632_);
v___x_4700_ = l_Array_append___redArg(v___x_4699_, v_heqs_4647_);
v___x_4701_ = l_Lean_Meta_mkForallFVars(v___x_4700_, v_a_4698_, v___x_4633_, v___x_4634_, v___x_4634_, v___x_4682_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
lean_dec_ref(v___x_4700_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; lean_object* v___x_4703_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4701_, 1);
v___x_4703_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4702_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4761_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4706_ = v___x_4703_;
v_isShared_4707_ = v_isSharedCheck_4761_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4703_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4761_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v_start_4708_; lean_object* v_stop_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4759_; 
v_start_4708_ = lean_ctor_get(v___x_4637_, 1);
v_stop_4709_ = lean_ctor_get(v___x_4637_, 2);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4759_ == 0)
{
lean_object* v_unused_4760_; 
v_unused_4760_ = lean_ctor_get(v___x_4637_, 0);
lean_dec(v_unused_4760_);
v___x_4711_ = v___x_4637_;
v_isShared_4712_ = v_isSharedCheck_4759_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_stop_4709_);
lean_inc(v_start_4708_);
lean_dec(v___x_4637_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4759_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4713_ = lean_nat_sub(v_stop_4709_, v_start_4708_);
lean_dec(v_start_4708_);
lean_dec(v_stop_4709_);
v___x_4714_ = lean_nat_add(v___x_4713_, v___x_4638_);
lean_dec(v___x_4713_);
v___x_4715_ = lean_nat_add(v___x_4714_, v___x_4641_);
lean_dec(v___x_4714_);
v___x_4716_ = lean_nat_add(v___x_4715_, v___x_4642_);
lean_dec(v___x_4715_);
v___x_4717_ = lean_array_get_size(v_altVars_4632_);
v___x_4718_ = lean_nat_add(v___x_4716_, v___x_4717_);
lean_dec(v___x_4716_);
v___x_4719_ = lean_array_get_size(v_heqs_4647_);
lean_dec_ref(v_heqs_4647_);
lean_inc(v_a_4704_);
v___x_4720_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4643_, v_a_4704_, v___x_4718_, v___x_4719_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4758_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4723_ = v___x_4720_;
v_isShared_4724_ = v_isSharedCheck_4758_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4720_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4758_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4725_; lean_object* v_env_4726_; uint8_t v___x_4727_; 
v___x_4725_ = lean_st_ref_get(v___y_4665_);
v_env_4726_ = lean_ctor_get(v___x_4725_, 0);
lean_inc_ref(v_env_4726_);
lean_dec(v___x_4725_);
lean_inc(v___x_4644_);
v___x_4727_ = l_Lean_Environment_contains(v_env_4726_, v___x_4644_, v___x_4634_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4729_; 
lean_del_object(v___x_4723_);
lean_inc(v___x_4644_);
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 2, v_a_4704_);
lean_ctor_set(v___x_4711_, 1, v___x_4645_);
lean_ctor_set(v___x_4711_, 0, v___x_4644_);
v___x_4729_ = v___x_4711_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4644_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v___x_4645_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_a_4704_);
v___x_4729_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
lean_object* v___x_4731_; 
if (v_isShared_4679_ == 0)
{
lean_ctor_set_tag(v___x_4678_, 1);
lean_ctor_set(v___x_4678_, 1, v___x_4646_);
lean_ctor_set(v___x_4678_, 0, v___x_4644_);
v___x_4731_ = v___x_4678_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4644_);
lean_ctor_set(v_reuseFailAlloc_4753_, 1, v___x_4646_);
v___x_4731_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
lean_object* v___x_4732_; lean_object* v___x_4734_; 
v___x_4732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4729_);
lean_ctor_set(v___x_4732_, 1, v_a_4721_);
lean_ctor_set(v___x_4732_, 2, v___x_4731_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set_tag(v___x_4706_, 2);
lean_ctor_set(v___x_4706_, 0, v___x_4732_);
v___x_4734_ = v___x_4706_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4732_);
v___x_4734_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
lean_object* v___x_4735_; 
v___x_4735_ = l_Lean_addDecl(v___x_4734_, v___x_4633_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4742_ == 0)
{
lean_object* v_unused_4743_; 
v_unused_4743_ = lean_ctor_get(v___x_4735_, 0);
lean_dec(v_unused_4743_);
v___x_4737_ = v___x_4735_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_dec(v___x_4735_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
lean_ctor_set(v___x_4737_, 0, v_a_4684_);
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4684_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec(v_a_4684_);
v_a_4744_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4735_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4735_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4756_; 
lean_dec(v_a_4721_);
lean_del_object(v___x_4711_);
lean_del_object(v___x_4706_);
lean_dec(v_a_4704_);
lean_del_object(v___x_4678_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
if (v_isShared_4724_ == 0)
{
lean_ctor_set(v___x_4723_, 0, v_a_4684_);
v___x_4756_ = v___x_4723_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4684_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
}
else
{
lean_del_object(v___x_4711_);
lean_del_object(v___x_4706_);
lean_dec(v_a_4704_);
lean_dec(v_a_4684_);
lean_del_object(v___x_4678_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
return v___x_4720_;
}
}
}
}
else
{
lean_dec(v_a_4684_);
lean_del_object(v___x_4678_);
lean_dec_ref(v_heqs_4647_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
lean_dec(v_matchDeclName_4643_);
lean_dec_ref(v___x_4637_);
return v___x_4703_;
}
}
else
{
lean_dec(v_a_4684_);
lean_del_object(v___x_4678_);
lean_dec_ref(v_heqs_4647_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
lean_dec(v_matchDeclName_4643_);
lean_dec_ref(v___x_4637_);
return v___x_4701_;
}
}
else
{
lean_dec_ref(v___x_4693_);
lean_dec(v_a_4684_);
lean_del_object(v___x_4678_);
lean_dec_ref(v_heqs_4647_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
lean_dec(v_matchDeclName_4643_);
lean_dec_ref(v___x_4637_);
return v___x_4697_;
}
}
else
{
lean_dec_ref(v___x_4693_);
lean_dec(v_a_4684_);
lean_del_object(v___x_4678_);
lean_dec(v_a_4660_);
lean_dec_ref(v_heqs_4647_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
lean_dec(v_matchDeclName_4643_);
lean_dec_ref(v___x_4637_);
return v___x_4695_;
}
}
else
{
lean_dec_ref(v___x_4680_);
lean_del_object(v___x_4678_);
lean_dec(v_a_4660_);
lean_dec(v_a_4655_);
lean_dec_ref(v_heqs_4647_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
lean_dec(v_matchDeclName_4643_);
lean_dec_ref(v___x_4640_);
lean_dec_ref(v___x_4639_);
lean_dec_ref(v___x_4637_);
lean_dec(v___x_4636_);
return v___x_4683_;
}
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
lean_dec(v_a_4660_);
lean_dec(v_a_4655_);
lean_dec_ref(v_heqs_4647_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
lean_dec(v_matchDeclName_4643_);
lean_dec_ref(v___x_4640_);
lean_dec_ref(v___x_4639_);
lean_dec_ref(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec_ref(v___x_4631_);
v_a_4764_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4674_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4674_);
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
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
lean_dec(v_a_4655_);
lean_dec_ref(v_heqs_4647_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
lean_dec(v_matchDeclName_4643_);
lean_dec_ref(v___x_4640_);
lean_dec_ref(v___x_4639_);
lean_dec_ref(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec(v___x_4630_);
lean_dec_ref(v___x_4629_);
lean_dec_ref(v_a_4627_);
v_a_4793_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4659_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4659_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4647_);
lean_dec(v___x_4646_);
lean_dec(v___x_4645_);
lean_dec(v___x_4644_);
lean_dec(v_matchDeclName_4643_);
lean_dec_ref(v___x_4640_);
lean_dec_ref(v___x_4639_);
lean_dec_ref(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec_ref(v___x_4631_);
lean_dec(v___x_4630_);
lean_dec_ref(v___x_4629_);
lean_dec(v___x_4628_);
lean_dec_ref(v_a_4627_);
return v___x_4654_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4801_ = _args[0];
lean_object* v_args_4802_ = _args[1];
lean_object* v___x_4803_ = _args[2];
lean_object* v_overlaps_4804_ = _args[3];
lean_object* v_a_4805_ = _args[4];
lean_object* v_fst_4806_ = _args[5];
lean_object* v_a_4807_ = _args[6];
lean_object* v___x_4808_ = _args[7];
lean_object* v___x_4809_ = _args[8];
lean_object* v___x_4810_ = _args[9];
lean_object* v___x_4811_ = _args[10];
lean_object* v_altVars_4812_ = _args[11];
lean_object* v___x_4813_ = _args[12];
lean_object* v___x_4814_ = _args[13];
lean_object* v_a_4815_ = _args[14];
lean_object* v___x_4816_ = _args[15];
lean_object* v___x_4817_ = _args[16];
lean_object* v___x_4818_ = _args[17];
lean_object* v___x_4819_ = _args[18];
lean_object* v___x_4820_ = _args[19];
lean_object* v___x_4821_ = _args[20];
lean_object* v___x_4822_ = _args[21];
lean_object* v_matchDeclName_4823_ = _args[22];
lean_object* v___x_4824_ = _args[23];
lean_object* v___x_4825_ = _args[24];
lean_object* v___x_4826_ = _args[25];
lean_object* v_heqs_4827_ = _args[26];
lean_object* v___y_4828_ = _args[27];
lean_object* v___y_4829_ = _args[28];
lean_object* v___y_4830_ = _args[29];
lean_object* v___y_4831_ = _args[30];
lean_object* v___y_4832_ = _args[31];
_start:
{
uint8_t v___x_22595__boxed_4833_; uint8_t v___x_22596__boxed_4834_; lean_object* v_res_4835_; 
v___x_22595__boxed_4833_ = lean_unbox(v___x_4813_);
v___x_22596__boxed_4834_ = lean_unbox(v___x_4814_);
v_res_4835_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4801_, v_args_4802_, v___x_4803_, v_overlaps_4804_, v_a_4805_, v_fst_4806_, v_a_4807_, v___x_4808_, v___x_4809_, v___x_4810_, v___x_4811_, v_altVars_4812_, v___x_22595__boxed_4833_, v___x_22596__boxed_4834_, v_a_4815_, v___x_4816_, v___x_4817_, v___x_4818_, v___x_4819_, v___x_4820_, v___x_4821_, v___x_4822_, v_matchDeclName_4823_, v___x_4824_, v___x_4825_, v___x_4826_, v_heqs_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___x_4822_);
lean_dec(v___x_4821_);
lean_dec(v___x_4818_);
lean_dec_ref(v_a_4815_);
lean_dec_ref(v_altVars_4812_);
lean_dec(v_fst_4806_);
lean_dec(v_a_4805_);
lean_dec_ref(v_overlaps_4804_);
lean_dec_ref(v_args_4802_);
return v_res_4835_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4838_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4839_ = lean_unsigned_to_nat(8u);
v___x_4840_ = lean_unsigned_to_nat(295u);
v___x_4841_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4842_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4843_ = l_mkPanicMessageWithDecl(v___x_4842_, v___x_4841_, v___x_4840_, v___x_4839_, v___x_4838_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4844_, lean_object* v___x_4845_, lean_object* v___x_4846_, lean_object* v___y_4847_, lean_object* v___x_4848_, lean_object* v_overlaps_4849_, lean_object* v_a_4850_, lean_object* v_fst_4851_, lean_object* v___x_4852_, lean_object* v_a_4853_, lean_object* v___x_4854_, lean_object* v___x_4855_, lean_object* v___x_4856_, lean_object* v___x_4857_, lean_object* v___x_4858_, lean_object* v___x_4859_, lean_object* v_matchDeclName_4860_, lean_object* v___x_4861_, lean_object* v___x_4862_, lean_object* v___x_4863_, lean_object* v_altVars_4864_, lean_object* v_args_4865_, lean_object* v___mask_4866_, lean_object* v_altResultType_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_){
_start:
{
uint8_t v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = 0;
v___x_4874_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4867_, v___f_4844_, v___x_4873_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v_start_4876_; lean_object* v_stop_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; uint8_t v___x_4880_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref_known(v___x_4874_, 1);
v_start_4876_ = lean_ctor_get(v___x_4845_, 1);
v_stop_4877_ = lean_ctor_get(v___x_4845_, 2);
v___x_4878_ = lean_array_get_size(v_a_4875_);
v___x_4879_ = lean_nat_sub(v_stop_4877_, v_start_4876_);
v___x_4880_ = lean_nat_dec_eq(v___x_4878_, v___x_4879_);
if (v___x_4880_ == 0)
{
lean_object* v___x_4881_; lean_object* v___x_4882_; 
lean_dec(v___x_4879_);
lean_dec(v_a_4875_);
lean_dec_ref(v_args_4865_);
lean_dec_ref(v_altVars_4864_);
lean_dec(v___x_4863_);
lean_dec(v___x_4862_);
lean_dec(v___x_4861_);
lean_dec(v_matchDeclName_4860_);
lean_dec(v___x_4859_);
lean_dec_ref(v___x_4858_);
lean_dec_ref(v___x_4857_);
lean_dec(v___x_4856_);
lean_dec_ref(v___x_4855_);
lean_dec(v___x_4854_);
lean_dec_ref(v_a_4853_);
lean_dec_ref(v___x_4852_);
lean_dec(v_fst_4851_);
lean_dec(v_a_4850_);
lean_dec_ref(v_overlaps_4849_);
lean_dec(v___x_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___x_4846_);
lean_dec_ref(v___x_4845_);
v___x_4881_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4882_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4881_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
return v___x_4882_;
}
else
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4883_ = lean_mk_empty_array_with_capacity(v___x_4846_);
lean_inc(v___x_4846_);
lean_inc(v_a_4875_);
v___x_4884_ = l_Array_toSubarray___redArg(v_a_4875_, v___x_4846_, v___x_4878_);
v___x_4885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4883_);
lean_ctor_set(v___x_4885_, 1, v___x_4884_);
lean_inc_ref(v___x_4845_);
v___x_4886_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v___x_4845_, v___x_4885_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v_fst_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___f_4891_; uint8_t v___x_4892_; lean_object* v___x_4893_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4887_);
lean_dec_ref_known(v___x_4886_, 1);
v_fst_4888_ = lean_ctor_get(v_a_4887_, 0);
lean_inc(v_fst_4888_);
lean_dec(v_a_4887_);
v___x_4889_ = lean_box(v___x_4873_);
v___x_4890_ = lean_box(v___x_4880_);
v___f_4891_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4891_, 0, v___y_4847_);
lean_closure_set(v___f_4891_, 1, v_args_4865_);
lean_closure_set(v___f_4891_, 2, v___x_4848_);
lean_closure_set(v___f_4891_, 3, v_overlaps_4849_);
lean_closure_set(v___f_4891_, 4, v_a_4850_);
lean_closure_set(v___f_4891_, 5, v_fst_4851_);
lean_closure_set(v___f_4891_, 6, v_a_4875_);
lean_closure_set(v___f_4891_, 7, v___x_4878_);
lean_closure_set(v___f_4891_, 8, v___x_4852_);
lean_closure_set(v___f_4891_, 9, v___x_4846_);
lean_closure_set(v___f_4891_, 10, v___x_4845_);
lean_closure_set(v___f_4891_, 11, v_altVars_4864_);
lean_closure_set(v___f_4891_, 12, v___x_4889_);
lean_closure_set(v___f_4891_, 13, v___x_4890_);
lean_closure_set(v___f_4891_, 14, v_a_4853_);
lean_closure_set(v___f_4891_, 15, v___x_4854_);
lean_closure_set(v___f_4891_, 16, v___x_4855_);
lean_closure_set(v___f_4891_, 17, v___x_4856_);
lean_closure_set(v___f_4891_, 18, v___x_4857_);
lean_closure_set(v___f_4891_, 19, v___x_4858_);
lean_closure_set(v___f_4891_, 20, v___x_4879_);
lean_closure_set(v___f_4891_, 21, v___x_4859_);
lean_closure_set(v___f_4891_, 22, v_matchDeclName_4860_);
lean_closure_set(v___f_4891_, 23, v___x_4861_);
lean_closure_set(v___f_4891_, 24, v___x_4862_);
lean_closure_set(v___f_4891_, 25, v___x_4863_);
v___x_4892_ = 0;
v___x_4893_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4888_, v___f_4891_, v___x_4892_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
return v___x_4893_;
}
else
{
lean_object* v_a_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4901_; 
lean_dec(v___x_4879_);
lean_dec(v_a_4875_);
lean_dec_ref(v_args_4865_);
lean_dec_ref(v_altVars_4864_);
lean_dec(v___x_4863_);
lean_dec(v___x_4862_);
lean_dec(v___x_4861_);
lean_dec(v_matchDeclName_4860_);
lean_dec(v___x_4859_);
lean_dec_ref(v___x_4858_);
lean_dec_ref(v___x_4857_);
lean_dec(v___x_4856_);
lean_dec_ref(v___x_4855_);
lean_dec(v___x_4854_);
lean_dec_ref(v_a_4853_);
lean_dec_ref(v___x_4852_);
lean_dec(v_fst_4851_);
lean_dec(v_a_4850_);
lean_dec_ref(v_overlaps_4849_);
lean_dec(v___x_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___x_4846_);
lean_dec_ref(v___x_4845_);
v_a_4894_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4896_ = v___x_4886_;
v_isShared_4897_ = v_isSharedCheck_4901_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_a_4894_);
lean_dec(v___x_4886_);
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
}
else
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4909_; 
lean_dec_ref(v_args_4865_);
lean_dec_ref(v_altVars_4864_);
lean_dec(v___x_4863_);
lean_dec(v___x_4862_);
lean_dec(v___x_4861_);
lean_dec(v_matchDeclName_4860_);
lean_dec(v___x_4859_);
lean_dec_ref(v___x_4858_);
lean_dec_ref(v___x_4857_);
lean_dec(v___x_4856_);
lean_dec_ref(v___x_4855_);
lean_dec(v___x_4854_);
lean_dec_ref(v_a_4853_);
lean_dec_ref(v___x_4852_);
lean_dec(v_fst_4851_);
lean_dec(v_a_4850_);
lean_dec_ref(v_overlaps_4849_);
lean_dec(v___x_4848_);
lean_dec_ref(v___y_4847_);
lean_dec(v___x_4846_);
lean_dec_ref(v___x_4845_);
v_a_4902_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4904_ = v___x_4874_;
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4874_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4910_ = _args[0];
lean_object* v___x_4911_ = _args[1];
lean_object* v___x_4912_ = _args[2];
lean_object* v___y_4913_ = _args[3];
lean_object* v___x_4914_ = _args[4];
lean_object* v_overlaps_4915_ = _args[5];
lean_object* v_a_4916_ = _args[6];
lean_object* v_fst_4917_ = _args[7];
lean_object* v___x_4918_ = _args[8];
lean_object* v_a_4919_ = _args[9];
lean_object* v___x_4920_ = _args[10];
lean_object* v___x_4921_ = _args[11];
lean_object* v___x_4922_ = _args[12];
lean_object* v___x_4923_ = _args[13];
lean_object* v___x_4924_ = _args[14];
lean_object* v___x_4925_ = _args[15];
lean_object* v_matchDeclName_4926_ = _args[16];
lean_object* v___x_4927_ = _args[17];
lean_object* v___x_4928_ = _args[18];
lean_object* v___x_4929_ = _args[19];
lean_object* v_altVars_4930_ = _args[20];
lean_object* v_args_4931_ = _args[21];
lean_object* v___mask_4932_ = _args[22];
lean_object* v_altResultType_4933_ = _args[23];
lean_object* v___y_4934_ = _args[24];
lean_object* v___y_4935_ = _args[25];
lean_object* v___y_4936_ = _args[26];
lean_object* v___y_4937_ = _args[27];
lean_object* v___y_4938_ = _args[28];
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4910_, v___x_4911_, v___x_4912_, v___y_4913_, v___x_4914_, v_overlaps_4915_, v_a_4916_, v_fst_4917_, v___x_4918_, v_a_4919_, v___x_4920_, v___x_4921_, v___x_4922_, v___x_4923_, v___x_4924_, v___x_4925_, v_matchDeclName_4926_, v___x_4927_, v___x_4928_, v___x_4929_, v_altVars_4930_, v_args_4931_, v___mask_4932_, v_altResultType_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
lean_dec(v___y_4937_);
lean_dec_ref(v___y_4936_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec_ref(v___mask_4932_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4941_, lean_object* v_val_4942_, lean_object* v_matchDeclName_4943_, lean_object* v___x_4944_, lean_object* v___x_4945_, lean_object* v_a_4946_, lean_object* v___x_4947_, lean_object* v___x_4948_, lean_object* v___x_4949_, lean_object* v___x_4950_, lean_object* v___x_4951_, lean_object* v___x_4952_, lean_object* v_a_4953_, lean_object* v_b_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_){
_start:
{
uint8_t v___x_4960_; 
v___x_4960_ = lean_nat_dec_lt(v_a_4953_, v_upperBound_4941_);
if (v___x_4960_ == 0)
{
lean_object* v___x_4961_; 
lean_dec(v_a_4953_);
lean_dec(v___x_4952_);
lean_dec(v___x_4951_);
lean_dec_ref(v___x_4950_);
lean_dec_ref(v___x_4949_);
lean_dec_ref(v___x_4948_);
lean_dec(v___x_4947_);
lean_dec_ref(v_a_4946_);
lean_dec(v___x_4945_);
lean_dec_ref(v___x_4944_);
lean_dec(v_matchDeclName_4943_);
lean_dec_ref(v_val_4942_);
v___x_4961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4961_, 0, v_b_4954_);
return v___x_4961_;
}
else
{
lean_object* v_snd_4962_; lean_object* v_fst_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_5026_; 
v_snd_4962_ = lean_ctor_get(v_b_4954_, 1);
v_fst_4963_ = lean_ctor_get(v_b_4954_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v_b_4954_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_4965_ = v_b_4954_;
v_isShared_4966_ = v_isSharedCheck_5026_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_snd_4962_);
lean_inc(v_fst_4963_);
lean_dec(v_b_4954_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_5026_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v_fst_4967_; lean_object* v_snd_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_5025_; 
v_fst_4967_ = lean_ctor_get(v_snd_4962_, 0);
v_snd_4968_ = lean_ctor_get(v_snd_4962_, 1);
v_isSharedCheck_5025_ = !lean_is_exclusive(v_snd_4962_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_4970_ = v_snd_4962_;
v_isShared_4971_ = v_isSharedCheck_5025_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_snd_4968_);
lean_inc(v_fst_4967_);
lean_dec(v_snd_4962_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_5025_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v_altInfos_4972_; lean_object* v_overlaps_4973_; lean_object* v_start_4974_; lean_object* v_stop_4975_; lean_object* v___f_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___y_4988_; lean_object* v___x_5020_; uint8_t v___x_5021_; 
v_altInfos_4972_ = lean_ctor_get(v_val_4942_, 2);
v_overlaps_4973_ = lean_ctor_get(v_val_4942_, 5);
v_start_4974_ = lean_ctor_get(v___x_4950_, 1);
v_stop_4975_ = lean_ctor_get(v___x_4950_, 2);
v___f_4976_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4977_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4978_ = lean_unsigned_to_nat(0u);
v___x_4979_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4980_ = lean_unsigned_to_nat(1u);
v___x_4981_ = lean_box(0);
v___x_4982_ = lean_array_get_borrowed(v___x_4977_, v_altInfos_4972_, v_a_4953_);
v___x_4983_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4943_);
v___x_4984_ = l_Lean_Name_str___override(v_matchDeclName_4943_, v___x_4983_);
lean_inc(v_snd_4968_);
v___x_4985_ = lean_name_append_index_after(v___x_4984_, v_snd_4968_);
lean_inc(v___x_4985_);
v___x_4986_ = lean_array_push(v_fst_4963_, v___x_4985_);
v___x_5020_ = lean_nat_sub(v_stop_4975_, v_start_4974_);
v___x_5021_ = lean_nat_dec_lt(v_a_4953_, v___x_5020_);
lean_dec(v___x_5020_);
if (v___x_5021_ == 0)
{
lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___x_5022_ = l_Lean_instInhabitedExpr;
v___x_5023_ = l_outOfBounds___redArg(v___x_5022_);
v___y_4988_ = v___x_5023_;
goto v___jp_4987_;
}
else
{
lean_object* v___x_5024_; 
v___x_5024_ = l_Subarray_get___redArg(v___x_4950_, v_a_4953_);
v___y_4988_ = v___x_5024_;
goto v___jp_4987_;
}
v___jp_4987_:
{
lean_object* v___x_4989_; 
lean_inc(v___y_4958_);
lean_inc_ref(v___y_4957_);
lean_inc(v___y_4956_);
lean_inc_ref(v___y_4955_);
lean_inc_ref(v___y_4988_);
v___x_4989_ = lean_infer_type(v___y_4988_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v_a_4990_; lean_object* v___f_4991_; lean_object* v___x_4992_; 
v_a_4990_ = lean_ctor_get(v___x_4989_, 0);
lean_inc(v_a_4990_);
lean_dec_ref_known(v___x_4989_, 1);
lean_inc(v___x_4952_);
lean_inc(v_matchDeclName_4943_);
lean_inc(v___x_4951_);
lean_inc_ref(v___x_4950_);
lean_inc_ref(v___x_4949_);
lean_inc_ref(v___x_4948_);
lean_inc(v___x_4947_);
lean_inc_ref(v_a_4946_);
lean_inc(v_fst_4967_);
lean_inc(v_a_4953_);
lean_inc_ref(v_overlaps_4973_);
lean_inc(v___x_4945_);
lean_inc_ref(v___x_4944_);
v___f_4991_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 29, 20);
lean_closure_set(v___f_4991_, 0, v___f_4976_);
lean_closure_set(v___f_4991_, 1, v___x_4944_);
lean_closure_set(v___f_4991_, 2, v___x_4978_);
lean_closure_set(v___f_4991_, 3, v___y_4988_);
lean_closure_set(v___f_4991_, 4, v___x_4945_);
lean_closure_set(v___f_4991_, 5, v_overlaps_4973_);
lean_closure_set(v___f_4991_, 6, v_a_4953_);
lean_closure_set(v___f_4991_, 7, v_fst_4967_);
lean_closure_set(v___f_4991_, 8, v___x_4979_);
lean_closure_set(v___f_4991_, 9, v_a_4946_);
lean_closure_set(v___f_4991_, 10, v___x_4947_);
lean_closure_set(v___f_4991_, 11, v___x_4948_);
lean_closure_set(v___f_4991_, 12, v___x_4980_);
lean_closure_set(v___f_4991_, 13, v___x_4949_);
lean_closure_set(v___f_4991_, 14, v___x_4950_);
lean_closure_set(v___f_4991_, 15, v___x_4951_);
lean_closure_set(v___f_4991_, 16, v_matchDeclName_4943_);
lean_closure_set(v___f_4991_, 17, v___x_4985_);
lean_closure_set(v___f_4991_, 18, v___x_4952_);
lean_closure_set(v___f_4991_, 19, v___x_4981_);
lean_inc(v___x_4982_);
v___x_4992_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4990_, v___x_4982_, v___f_4991_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v_a_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4997_; 
v_a_4993_ = lean_ctor_get(v___x_4992_, 0);
lean_inc(v_a_4993_);
lean_dec_ref_known(v___x_4992_, 1);
v___x_4994_ = lean_array_push(v_fst_4967_, v_a_4993_);
v___x_4995_ = lean_nat_add(v_snd_4968_, v___x_4980_);
lean_dec(v_snd_4968_);
if (v_isShared_4971_ == 0)
{
lean_ctor_set(v___x_4970_, 1, v___x_4995_);
lean_ctor_set(v___x_4970_, 0, v___x_4994_);
v___x_4997_ = v___x_4970_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v___x_4994_);
lean_ctor_set(v_reuseFailAlloc_5003_, 1, v___x_4995_);
v___x_4997_ = v_reuseFailAlloc_5003_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
lean_object* v___x_4999_; 
if (v_isShared_4966_ == 0)
{
lean_ctor_set(v___x_4965_, 1, v___x_4997_);
lean_ctor_set(v___x_4965_, 0, v___x_4986_);
v___x_4999_ = v___x_4965_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v___x_4986_);
lean_ctor_set(v_reuseFailAlloc_5002_, 1, v___x_4997_);
v___x_4999_ = v_reuseFailAlloc_5002_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
lean_object* v___x_5000_; 
v___x_5000_ = lean_nat_add(v_a_4953_, v___x_4980_);
lean_dec(v_a_4953_);
v_a_4953_ = v___x_5000_;
v_b_4954_ = v___x_4999_;
goto _start;
}
}
}
else
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
lean_dec_ref(v___x_4986_);
lean_del_object(v___x_4970_);
lean_dec(v_snd_4968_);
lean_dec(v_fst_4967_);
lean_del_object(v___x_4965_);
lean_dec(v_a_4953_);
lean_dec(v___x_4952_);
lean_dec(v___x_4951_);
lean_dec_ref(v___x_4950_);
lean_dec_ref(v___x_4949_);
lean_dec_ref(v___x_4948_);
lean_dec(v___x_4947_);
lean_dec_ref(v_a_4946_);
lean_dec(v___x_4945_);
lean_dec_ref(v___x_4944_);
lean_dec(v_matchDeclName_4943_);
lean_dec_ref(v_val_4942_);
v_a_5004_ = lean_ctor_get(v___x_4992_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4992_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_4992_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_4992_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
}
else
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
lean_dec_ref(v___y_4988_);
lean_dec_ref(v___x_4986_);
lean_dec(v___x_4985_);
lean_del_object(v___x_4970_);
lean_dec(v_snd_4968_);
lean_dec(v_fst_4967_);
lean_del_object(v___x_4965_);
lean_dec(v_a_4953_);
lean_dec(v___x_4952_);
lean_dec(v___x_4951_);
lean_dec_ref(v___x_4950_);
lean_dec_ref(v___x_4949_);
lean_dec_ref(v___x_4948_);
lean_dec(v___x_4947_);
lean_dec_ref(v_a_4946_);
lean_dec(v___x_4945_);
lean_dec_ref(v___x_4944_);
lean_dec(v_matchDeclName_4943_);
lean_dec_ref(v_val_4942_);
v_a_5012_ = lean_ctor_get(v___x_4989_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_4989_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5014_ = v___x_4989_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_4989_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5012_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
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
lean_object* v_upperBound_5027_ = _args[0];
lean_object* v_val_5028_ = _args[1];
lean_object* v_matchDeclName_5029_ = _args[2];
lean_object* v___x_5030_ = _args[3];
lean_object* v___x_5031_ = _args[4];
lean_object* v_a_5032_ = _args[5];
lean_object* v___x_5033_ = _args[6];
lean_object* v___x_5034_ = _args[7];
lean_object* v___x_5035_ = _args[8];
lean_object* v___x_5036_ = _args[9];
lean_object* v___x_5037_ = _args[10];
lean_object* v___x_5038_ = _args[11];
lean_object* v_a_5039_ = _args[12];
lean_object* v_b_5040_ = _args[13];
lean_object* v___y_5041_ = _args[14];
lean_object* v___y_5042_ = _args[15];
lean_object* v___y_5043_ = _args[16];
lean_object* v___y_5044_ = _args[17];
lean_object* v___y_5045_ = _args[18];
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5027_, v_val_5028_, v_matchDeclName_5029_, v___x_5030_, v___x_5031_, v_a_5032_, v___x_5033_, v___x_5034_, v___x_5035_, v___x_5036_, v___x_5037_, v___x_5038_, v_a_5039_, v_b_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec(v_upperBound_5027_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5053_, lean_object* v___x_5054_, lean_object* v_matchDeclName_5055_, lean_object* v___x_5056_, lean_object* v_a_5057_, lean_object* v___x_5058_, lean_object* v___x_5059_, lean_object* v_xs_5060_, lean_object* v___matchResultType_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v_numParams_5067_; lean_object* v_numDiscrs_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v_lower_5074_; lean_object* v_upper_5075_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; uint8_t v___x_5106_; 
v_numParams_5067_ = lean_ctor_get(v_val_5053_, 0);
v_numDiscrs_5068_ = lean_ctor_get(v_val_5053_, 1);
v___x_5069_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5067_);
lean_inc_ref(v_xs_5060_);
v___x_5070_ = l_Array_toSubarray___redArg(v_xs_5060_, v___x_5069_, v_numParams_5067_);
v___x_5071_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5053_);
v___x_5072_ = lean_array_get(v___x_5054_, v_xs_5060_, v___x_5071_);
lean_dec(v___x_5071_);
v___x_5103_ = lean_array_get_size(v_xs_5060_);
v___x_5104_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5053_);
v___x_5105_ = lean_nat_sub(v___x_5103_, v___x_5104_);
lean_dec(v___x_5104_);
v___x_5106_ = lean_nat_dec_le(v___x_5105_, v___x_5069_);
if (v___x_5106_ == 0)
{
v_lower_5074_ = v___x_5105_;
v_upper_5075_ = v___x_5103_;
goto v___jp_5073_;
}
else
{
lean_dec(v___x_5105_);
v_lower_5074_ = v___x_5069_;
v_upper_5075_ = v___x_5103_;
goto v___jp_5073_;
}
v___jp_5073_:
{
lean_object* v___x_5076_; lean_object* v_start_5077_; lean_object* v_stop_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
lean_inc_ref(v_xs_5060_);
v___x_5076_ = l_Array_toSubarray___redArg(v_xs_5060_, v_lower_5074_, v_upper_5075_);
v_start_5077_ = lean_ctor_get(v___x_5076_, 1);
lean_inc(v_start_5077_);
v_stop_5078_ = lean_ctor_get(v___x_5076_, 2);
lean_inc(v_stop_5078_);
v___x_5079_ = lean_unsigned_to_nat(1u);
v___x_5080_ = lean_nat_add(v_numParams_5067_, v___x_5079_);
v___x_5081_ = lean_nat_add(v___x_5080_, v_numDiscrs_5068_);
v___x_5082_ = lean_nat_sub(v_stop_5078_, v_start_5077_);
lean_dec(v_start_5077_);
lean_dec(v_stop_5078_);
v___x_5083_ = l_Array_toSubarray___redArg(v_xs_5060_, v___x_5080_, v___x_5081_);
v___x_5084_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5082_);
v___x_5085_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5082_, v_val_5053_, v_matchDeclName_5055_, v___x_5083_, v___x_5056_, v_a_5057_, v___x_5058_, v___x_5070_, v___x_5072_, v___x_5076_, v___x_5082_, v___x_5059_, v___x_5069_, v___x_5084_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
lean_dec(v___x_5082_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5093_; 
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5093_ == 0)
{
lean_object* v_unused_5094_; 
v_unused_5094_ = lean_ctor_get(v___x_5085_, 0);
lean_dec(v_unused_5094_);
v___x_5087_ = v___x_5085_;
v_isShared_5088_ = v_isSharedCheck_5093_;
goto v_resetjp_5086_;
}
else
{
lean_dec(v___x_5085_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5093_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5089_; lean_object* v___x_5091_; 
v___x_5089_ = lean_box(0);
if (v_isShared_5088_ == 0)
{
lean_ctor_set(v___x_5087_, 0, v___x_5089_);
v___x_5091_ = v___x_5087_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v___x_5089_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
else
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
v_a_5095_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_5085_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5085_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5107_, lean_object* v___x_5108_, lean_object* v_matchDeclName_5109_, lean_object* v___x_5110_, lean_object* v_a_5111_, lean_object* v___x_5112_, lean_object* v___x_5113_, lean_object* v_xs_5114_, lean_object* v___matchResultType_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5107_, v___x_5108_, v_matchDeclName_5109_, v___x_5110_, v_a_5111_, v___x_5112_, v___x_5113_, v_xs_5114_, v___matchResultType_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
lean_dec(v___y_5119_);
lean_dec_ref(v___y_5118_);
lean_dec(v___y_5117_);
lean_dec_ref(v___y_5116_);
lean_dec_ref(v___matchResultType_5115_);
lean_dec_ref(v___x_5108_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_){
_start:
{
uint8_t v_trackZetaDelta_5128_; lean_object* v_zetaDeltaSet_5129_; lean_object* v_lctx_5130_; lean_object* v_localInstances_5131_; lean_object* v_defEqCtx_x3f_5132_; lean_object* v_synthPendingDepth_5133_; lean_object* v_canUnfold_x3f_5134_; uint8_t v_univApprox_5135_; uint8_t v_inTypeClassResolution_5136_; uint8_t v_cacheInferType_5137_; lean_object* v___x_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5181_; 
v_trackZetaDelta_5128_ = lean_ctor_get_uint8(v_a_5123_, sizeof(void*)*7);
v_zetaDeltaSet_5129_ = lean_ctor_get(v_a_5123_, 1);
lean_inc(v_zetaDeltaSet_5129_);
v_lctx_5130_ = lean_ctor_get(v_a_5123_, 2);
lean_inc_ref(v_lctx_5130_);
v_localInstances_5131_ = lean_ctor_get(v_a_5123_, 3);
lean_inc_ref(v_localInstances_5131_);
v_defEqCtx_x3f_5132_ = lean_ctor_get(v_a_5123_, 4);
lean_inc(v_defEqCtx_x3f_5132_);
v_synthPendingDepth_5133_ = lean_ctor_get(v_a_5123_, 5);
lean_inc(v_synthPendingDepth_5133_);
v_canUnfold_x3f_5134_ = lean_ctor_get(v_a_5123_, 6);
lean_inc(v_canUnfold_x3f_5134_);
v_univApprox_5135_ = lean_ctor_get_uint8(v_a_5123_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5136_ = lean_ctor_get_uint8(v_a_5123_, sizeof(void*)*7 + 2);
v_cacheInferType_5137_ = lean_ctor_get_uint8(v_a_5123_, sizeof(void*)*7 + 3);
v___x_5138_ = l_Lean_Meta_Context_config(v_a_5123_);
v_isSharedCheck_5181_ = !lean_is_exclusive(v_a_5123_);
if (v_isSharedCheck_5181_ == 0)
{
lean_object* v_unused_5182_; lean_object* v_unused_5183_; lean_object* v_unused_5184_; lean_object* v_unused_5185_; lean_object* v_unused_5186_; lean_object* v_unused_5187_; lean_object* v_unused_5188_; 
v_unused_5182_ = lean_ctor_get(v_a_5123_, 6);
lean_dec(v_unused_5182_);
v_unused_5183_ = lean_ctor_get(v_a_5123_, 5);
lean_dec(v_unused_5183_);
v_unused_5184_ = lean_ctor_get(v_a_5123_, 4);
lean_dec(v_unused_5184_);
v_unused_5185_ = lean_ctor_get(v_a_5123_, 3);
lean_dec(v_unused_5185_);
v_unused_5186_ = lean_ctor_get(v_a_5123_, 2);
lean_dec(v_unused_5186_);
v_unused_5187_ = lean_ctor_get(v_a_5123_, 1);
lean_dec(v_unused_5187_);
v_unused_5188_ = lean_ctor_get(v_a_5123_, 0);
lean_dec(v_unused_5188_);
v___x_5140_ = v_a_5123_;
v_isShared_5141_ = v_isSharedCheck_5181_;
goto v_resetjp_5139_;
}
else
{
lean_dec(v_a_5123_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5181_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5142_; uint64_t v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5146_; 
v___x_5142_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5138_);
v___x_5143_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5142_);
v___x_5144_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5144_, 0, v___x_5142_);
lean_ctor_set_uint64(v___x_5144_, sizeof(void*)*1, v___x_5143_);
lean_inc(v_canUnfold_x3f_5134_);
lean_inc(v_synthPendingDepth_5133_);
lean_inc(v_defEqCtx_x3f_5132_);
lean_inc_ref(v_localInstances_5131_);
lean_inc_ref(v_lctx_5130_);
lean_inc(v_zetaDeltaSet_5129_);
if (v_isShared_5141_ == 0)
{
lean_ctor_set(v___x_5140_, 0, v___x_5144_);
v___x_5146_ = v___x_5140_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v___x_5144_);
lean_ctor_set(v_reuseFailAlloc_5180_, 1, v_zetaDeltaSet_5129_);
lean_ctor_set(v_reuseFailAlloc_5180_, 2, v_lctx_5130_);
lean_ctor_set(v_reuseFailAlloc_5180_, 3, v_localInstances_5131_);
lean_ctor_set(v_reuseFailAlloc_5180_, 4, v_defEqCtx_x3f_5132_);
lean_ctor_set(v_reuseFailAlloc_5180_, 5, v_synthPendingDepth_5133_);
lean_ctor_set(v_reuseFailAlloc_5180_, 6, v_canUnfold_x3f_5134_);
lean_ctor_set_uint8(v_reuseFailAlloc_5180_, sizeof(void*)*7, v_trackZetaDelta_5128_);
lean_ctor_set_uint8(v_reuseFailAlloc_5180_, sizeof(void*)*7 + 1, v_univApprox_5135_);
lean_ctor_set_uint8(v_reuseFailAlloc_5180_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5136_);
lean_ctor_set_uint8(v_reuseFailAlloc_5180_, sizeof(void*)*7 + 3, v_cacheInferType_5137_);
v___x_5146_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; uint64_t v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5147_ = l_Lean_Meta_Context_config(v___x_5146_);
lean_dec_ref(v___x_5146_);
v___x_5148_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5147_);
v___x_5149_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5148_);
v___x_5150_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5150_, 0, v___x_5148_);
lean_ctor_set_uint64(v___x_5150_, sizeof(void*)*1, v___x_5149_);
v___x_5151_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5151_, 0, v___x_5150_);
lean_ctor_set(v___x_5151_, 1, v_zetaDeltaSet_5129_);
lean_ctor_set(v___x_5151_, 2, v_lctx_5130_);
lean_ctor_set(v___x_5151_, 3, v_localInstances_5131_);
lean_ctor_set(v___x_5151_, 4, v_defEqCtx_x3f_5132_);
lean_ctor_set(v___x_5151_, 5, v_synthPendingDepth_5133_);
lean_ctor_set(v___x_5151_, 6, v_canUnfold_x3f_5134_);
lean_ctor_set_uint8(v___x_5151_, sizeof(void*)*7, v_trackZetaDelta_5128_);
lean_ctor_set_uint8(v___x_5151_, sizeof(void*)*7 + 1, v_univApprox_5135_);
lean_ctor_set_uint8(v___x_5151_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5136_);
lean_ctor_set_uint8(v___x_5151_, sizeof(void*)*7 + 3, v_cacheInferType_5137_);
lean_inc(v_matchDeclName_5122_);
v___x_5152_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5122_, v___x_5151_, v_a_5124_, v_a_5125_, v_a_5126_);
if (lean_obj_tag(v___x_5152_) == 0)
{
lean_object* v_a_5153_; lean_object* v___x_5154_; lean_object* v_a_5155_; 
v_a_5153_ = lean_ctor_get(v___x_5152_, 0);
lean_inc(v_a_5153_);
lean_dec_ref_known(v___x_5152_, 1);
lean_inc(v_matchDeclName_5122_);
v___x_5154_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5122_, v_a_5126_);
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_a_5155_);
lean_dec_ref(v___x_5154_);
if (lean_obj_tag(v_a_5155_) == 1)
{
lean_object* v_val_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___f_5162_; lean_object* v___x_5163_; uint8_t v___x_5164_; lean_object* v___x_5165_; 
v_val_5156_ = lean_ctor_get(v_a_5155_, 0);
lean_inc(v_val_5156_);
lean_dec_ref_known(v_a_5155_, 1);
v___x_5157_ = l_Lean_instInhabitedExpr;
v___x_5158_ = l_Lean_ConstantInfo_levelParams(v_a_5153_);
v___x_5159_ = lean_box(0);
lean_inc(v___x_5158_);
v___x_5160_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_5158_, v___x_5159_);
v___x_5161_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5156_);
lean_inc(v_a_5153_);
v___f_5162_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5162_, 0, v_val_5156_);
lean_closure_set(v___f_5162_, 1, v___x_5157_);
lean_closure_set(v___f_5162_, 2, v_matchDeclName_5122_);
lean_closure_set(v___f_5162_, 3, v___x_5161_);
lean_closure_set(v___f_5162_, 4, v_a_5153_);
lean_closure_set(v___f_5162_, 5, v___x_5160_);
lean_closure_set(v___f_5162_, 6, v___x_5158_);
v___x_5163_ = l_Lean_ConstantInfo_type(v_a_5153_);
lean_dec(v_a_5153_);
v___x_5164_ = 0;
v___x_5165_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5163_, v___f_5162_, v___x_5164_, v___x_5164_, v___x_5151_, v_a_5124_, v_a_5125_, v_a_5126_);
lean_dec_ref_known(v___x_5151_, 7);
return v___x_5165_;
}
else
{
lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; 
lean_dec(v_a_5155_);
lean_dec(v_a_5153_);
v___x_5166_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5167_ = l_Lean_MessageData_ofName(v_matchDeclName_5122_);
v___x_5168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5166_);
lean_ctor_set(v___x_5168_, 1, v___x_5167_);
v___x_5169_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5170_, 0, v___x_5168_);
lean_ctor_set(v___x_5170_, 1, v___x_5169_);
v___x_5171_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5170_, v___x_5151_, v_a_5124_, v_a_5125_, v_a_5126_);
lean_dec_ref_known(v___x_5151_, 7);
return v___x_5171_;
}
}
else
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5179_; 
lean_dec_ref_known(v___x_5151_, 7);
lean_dec(v_matchDeclName_5122_);
v_a_5172_ = lean_ctor_get(v___x_5152_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5152_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5174_ = v___x_5152_;
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5152_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5177_; 
if (v_isShared_5175_ == 0)
{
v___x_5177_ = v___x_5174_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_){
_start:
{
lean_object* v_res_5195_; 
v_res_5195_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_);
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec(v_a_5191_);
return v_res_5195_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_inst_5196_, lean_object* v_R_5197_, lean_object* v_a_5198_, lean_object* v_b_5199_, lean_object* v_c_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_){
_start:
{
lean_object* v___x_5206_; 
v___x_5206_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_5198_, v_b_5199_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
return v___x_5206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_inst_5207_, lean_object* v_R_5208_, lean_object* v_a_5209_, lean_object* v_b_5210_, lean_object* v_c_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_inst_5207_, v_R_5208_, v_a_5209_, v_b_5210_, v_c_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5218_, lean_object* v_val_5219_, lean_object* v_matchDeclName_5220_, lean_object* v___x_5221_, lean_object* v___x_5222_, lean_object* v_a_5223_, lean_object* v___x_5224_, lean_object* v___x_5225_, lean_object* v___x_5226_, lean_object* v___x_5227_, lean_object* v___x_5228_, lean_object* v___x_5229_, lean_object* v_inst_5230_, lean_object* v_R_5231_, lean_object* v_a_5232_, lean_object* v_b_5233_, lean_object* v_c_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_){
_start:
{
lean_object* v___x_5240_; 
v___x_5240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5218_, v_val_5219_, v_matchDeclName_5220_, v___x_5221_, v___x_5222_, v_a_5223_, v___x_5224_, v___x_5225_, v___x_5226_, v___x_5227_, v___x_5228_, v___x_5229_, v_a_5232_, v_b_5233_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_);
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5241_ = _args[0];
lean_object* v_val_5242_ = _args[1];
lean_object* v_matchDeclName_5243_ = _args[2];
lean_object* v___x_5244_ = _args[3];
lean_object* v___x_5245_ = _args[4];
lean_object* v_a_5246_ = _args[5];
lean_object* v___x_5247_ = _args[6];
lean_object* v___x_5248_ = _args[7];
lean_object* v___x_5249_ = _args[8];
lean_object* v___x_5250_ = _args[9];
lean_object* v___x_5251_ = _args[10];
lean_object* v___x_5252_ = _args[11];
lean_object* v_inst_5253_ = _args[12];
lean_object* v_R_5254_ = _args[13];
lean_object* v_a_5255_ = _args[14];
lean_object* v_b_5256_ = _args[15];
lean_object* v_c_5257_ = _args[16];
lean_object* v___y_5258_ = _args[17];
lean_object* v___y_5259_ = _args[18];
lean_object* v___y_5260_ = _args[19];
lean_object* v___y_5261_ = _args[20];
lean_object* v___y_5262_ = _args[21];
_start:
{
lean_object* v_res_5263_; 
v_res_5263_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5241_, v_val_5242_, v_matchDeclName_5243_, v___x_5244_, v___x_5245_, v_a_5246_, v___x_5247_, v___x_5248_, v___x_5249_, v___x_5250_, v___x_5251_, v___x_5252_, v_inst_5253_, v_R_5254_, v_a_5255_, v_b_5256_, v_c_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
lean_dec(v___y_5259_);
lean_dec_ref(v___y_5258_);
lean_dec(v_upperBound_5241_);
return v_res_5263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5264_, lean_object* v_matchDeclName_5265_, lean_object* v_a_5266_, lean_object* v_b_5267_){
_start:
{
uint8_t v___x_5269_; 
v___x_5269_ = lean_nat_dec_lt(v_a_5266_, v_upperBound_5264_);
if (v___x_5269_ == 0)
{
lean_object* v___x_5270_; 
lean_dec(v_a_5266_);
lean_dec(v_matchDeclName_5265_);
v___x_5270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5270_, 0, v_b_5267_);
return v___x_5270_;
}
else
{
lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; 
v___x_5271_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5265_);
v___x_5272_ = l_Lean_Name_str___override(v_matchDeclName_5265_, v___x_5271_);
v___x_5273_ = lean_unsigned_to_nat(1u);
v___x_5274_ = lean_nat_add(v_a_5266_, v___x_5273_);
lean_dec(v_a_5266_);
lean_inc(v___x_5274_);
v___x_5275_ = lean_name_append_index_after(v___x_5272_, v___x_5274_);
v___x_5276_ = lean_array_push(v_b_5267_, v___x_5275_);
v_a_5266_ = v___x_5274_;
v_b_5267_ = v___x_5276_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5278_, lean_object* v_matchDeclName_5279_, lean_object* v_a_5280_, lean_object* v_b_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v_res_5283_; 
v_res_5283_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5278_, v_matchDeclName_5279_, v_a_5280_, v_b_5281_);
lean_dec(v_upperBound_5278_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_){
_start:
{
lean_object* v___x_5290_; lean_object* v_firstEqnName_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v___x_5290_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5284_, 3);
v_firstEqnName_5291_ = l_Lean_Name_str___override(v_matchDeclName_5284_, v___x_5290_);
v___x_5292_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5292_, 0, v_matchDeclName_5284_);
v___x_5293_ = l_Lean_Meta_realizeConst(v_matchDeclName_5284_, v_firstEqnName_5291_, v___x_5292_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_);
if (lean_obj_tag(v___x_5293_) == 0)
{
lean_object* v___x_5294_; lean_object* v_a_5295_; 
lean_dec_ref_known(v___x_5293_, 1);
lean_inc(v_matchDeclName_5284_);
v___x_5294_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5284_, v_a_5288_);
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
lean_inc(v_a_5295_);
lean_dec_ref(v___x_5294_);
if (lean_obj_tag(v_a_5295_) == 1)
{
lean_object* v_val_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; 
lean_dec(v_a_5288_);
lean_dec_ref(v_a_5287_);
lean_dec(v_a_5286_);
lean_dec_ref(v_a_5285_);
v_val_5296_ = lean_ctor_get(v_a_5295_, 0);
lean_inc(v_val_5296_);
lean_dec_ref_known(v_a_5295_, 1);
v___x_5297_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5296_);
lean_dec(v_val_5296_);
v___x_5298_ = lean_unsigned_to_nat(0u);
v___x_5299_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5300_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5297_, v_matchDeclName_5284_, v___x_5298_, v___x_5299_);
lean_dec(v___x_5297_);
return v___x_5300_;
}
else
{
lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; 
lean_dec(v_a_5295_);
v___x_5301_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5302_ = l_Lean_MessageData_ofName(v_matchDeclName_5284_);
v___x_5303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5303_, 0, v___x_5301_);
lean_ctor_set(v___x_5303_, 1, v___x_5302_);
v___x_5304_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5303_);
lean_ctor_set(v___x_5305_, 1, v___x_5304_);
v___x_5306_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5305_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_);
lean_dec(v_a_5288_);
lean_dec_ref(v_a_5287_);
lean_dec(v_a_5286_);
lean_dec_ref(v_a_5285_);
return v___x_5306_;
}
}
else
{
lean_object* v_a_5307_; lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5314_; 
lean_dec(v_a_5288_);
lean_dec_ref(v_a_5287_);
lean_dec(v_a_5286_);
lean_dec_ref(v_a_5285_);
lean_dec(v_matchDeclName_5284_);
v_a_5307_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5314_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5314_ == 0)
{
v___x_5309_ = v___x_5293_;
v_isShared_5310_ = v_isSharedCheck_5314_;
goto v_resetjp_5308_;
}
else
{
lean_inc(v_a_5307_);
lean_dec(v___x_5293_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5314_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
lean_object* v___x_5312_; 
if (v_isShared_5310_ == 0)
{
v___x_5312_ = v___x_5309_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5313_; 
v_reuseFailAlloc_5313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5313_, 0, v_a_5307_);
v___x_5312_ = v_reuseFailAlloc_5313_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
return v___x_5312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_){
_start:
{
lean_object* v_res_5321_; 
v_res_5321_ = lean_get_congr_match_equations_for(v_matchDeclName_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_);
return v_res_5321_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5322_, lean_object* v_matchDeclName_5323_, lean_object* v_inst_5324_, lean_object* v_R_5325_, lean_object* v_a_5326_, lean_object* v_b_5327_, lean_object* v_c_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v___x_5334_; 
v___x_5334_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5322_, v_matchDeclName_5323_, v_a_5326_, v_b_5327_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5335_, lean_object* v_matchDeclName_5336_, lean_object* v_inst_5337_, lean_object* v_R_5338_, lean_object* v_a_5339_, lean_object* v_b_5340_, lean_object* v_c_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5335_, v_matchDeclName_5336_, v_inst_5337_, v_R_5338_, v_a_5339_, v_b_5340_, v_c_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_);
lean_dec(v___y_5345_);
lean_dec_ref(v___y_5344_);
lean_dec(v___y_5343_);
lean_dec_ref(v___y_5342_);
lean_dec(v_upperBound_5335_);
return v_res_5347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5398_ = lean_unsigned_to_nat(3248161880u);
v___x_5399_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5400_ = l_Lean_Name_num___override(v___x_5399_, v___x_5398_);
return v___x_5400_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5402_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5403_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5404_ = l_Lean_Name_str___override(v___x_5403_, v___x_5402_);
return v___x_5404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; 
v___x_5406_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5407_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5408_ = l_Lean_Name_str___override(v___x_5407_, v___x_5406_);
return v___x_5408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
v___x_5409_ = lean_unsigned_to_nat(2u);
v___x_5410_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5411_ = l_Lean_Name_num___override(v___x_5410_, v___x_5409_);
return v___x_5411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5413_; uint8_t v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; 
v___x_5413_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5414_ = 0;
v___x_5415_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5416_ = l_Lean_registerTraceClass(v___x_5413_, v___x_5414_, v___x_5415_);
return v___x_5416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5417_){
_start:
{
lean_object* v_res_5418_; 
v_res_5418_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5419_, lean_object* v_n_5420_){
_start:
{
if (lean_obj_tag(v_n_5420_) == 1)
{
lean_object* v_pre_5421_; lean_object* v_str_5422_; uint8_t v___y_5424_; uint8_t v___x_5430_; 
v_pre_5421_ = lean_ctor_get(v_n_5420_, 0);
lean_inc(v_pre_5421_);
v_str_5422_ = lean_ctor_get(v_n_5420_, 1);
lean_inc_ref_n(v_str_5422_, 2);
lean_dec_ref_known(v_n_5420_, 2);
v___x_5430_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5422_);
if (v___x_5430_ == 0)
{
lean_object* v___x_5431_; uint8_t v___x_5432_; 
v___x_5431_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5432_ = lean_string_dec_eq(v_str_5422_, v___x_5431_);
lean_dec_ref(v_str_5422_);
v___y_5424_ = v___x_5432_;
goto v___jp_5423_;
}
else
{
lean_dec_ref(v_str_5422_);
v___y_5424_ = v___x_5430_;
goto v___jp_5423_;
}
v___jp_5423_:
{
if (v___y_5424_ == 0)
{
lean_object* v___x_5425_; 
lean_dec(v_pre_5421_);
lean_dec_ref(v_env_5419_);
v___x_5425_ = lean_box(0);
return v___x_5425_;
}
else
{
lean_object* v___x_5426_; 
v___x_5426_ = l_Lean_privateToUserName_x3f(v_pre_5421_);
if (lean_obj_tag(v___x_5426_) == 0)
{
lean_dec_ref(v_env_5419_);
return v___x_5426_;
}
else
{
lean_object* v_val_5427_; uint8_t v___x_5428_; 
v_val_5427_ = lean_ctor_get(v___x_5426_, 0);
lean_inc(v_val_5427_);
v___x_5428_ = l_Lean_Meta_isMatcherCore(v_env_5419_, v_val_5427_);
if (v___x_5428_ == 0)
{
lean_object* v___x_5429_; 
lean_dec_ref_known(v___x_5426_, 1);
v___x_5429_ = lean_box(0);
return v___x_5429_;
}
else
{
return v___x_5426_;
}
}
}
}
}
else
{
lean_object* v___x_5433_; 
lean_dec(v_n_5420_);
lean_dec_ref(v_env_5419_);
v___x_5433_ = lean_box(0);
return v___x_5433_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5434_, lean_object* v_x2_5435_){
_start:
{
lean_object* v___x_5436_; 
v___x_5436_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5434_, v_x2_5435_);
if (lean_obj_tag(v___x_5436_) == 0)
{
uint8_t v___x_5437_; 
v___x_5437_ = 0;
return v___x_5437_;
}
else
{
uint8_t v___x_5438_; 
lean_dec_ref_known(v___x_5436_, 1);
v___x_5438_ = 1;
return v___x_5438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5439_, lean_object* v_x2_5440_){
_start:
{
uint8_t v_res_5441_; lean_object* v_r_5442_; 
v_res_5441_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5439_, v_x2_5440_);
v_r_5442_ = lean_box(v_res_5441_);
return v_r_5442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5445_; lean_object* v___x_5446_; 
v___f_5445_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5446_ = l_Lean_registerReservedNamePredicate(v___f_5445_);
return v___x_5446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5447_){
_start:
{
lean_object* v_res_5448_; 
v_res_5448_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5448_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5455_; uint64_t v___x_5456_; 
v___x_5455_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5456_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5455_);
return v___x_5456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; 
v___x_5457_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5458_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5459_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5459_, 0, v___x_5458_);
lean_ctor_set_uint64(v___x_5459_, sizeof(void*)*1, v___x_5457_);
return v___x_5459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; 
v___x_5462_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5463_ = lean_unsigned_to_nat(0u);
v___x_5464_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5464_, 0, v___x_5463_);
lean_ctor_set(v___x_5464_, 1, v___x_5463_);
lean_ctor_set(v___x_5464_, 2, v___x_5463_);
lean_ctor_set(v___x_5464_, 3, v___x_5463_);
lean_ctor_set(v___x_5464_, 4, v___x_5462_);
lean_ctor_set(v___x_5464_, 5, v___x_5462_);
lean_ctor_set(v___x_5464_, 6, v___x_5462_);
lean_ctor_set(v___x_5464_, 7, v___x_5462_);
lean_ctor_set(v___x_5464_, 8, v___x_5462_);
lean_ctor_set(v___x_5464_, 9, v___x_5462_);
return v___x_5464_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5465_; lean_object* v___x_5466_; 
v___x_5465_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5466_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5466_, 0, v___x_5465_);
lean_ctor_set(v___x_5466_, 1, v___x_5465_);
lean_ctor_set(v___x_5466_, 2, v___x_5465_);
lean_ctor_set(v___x_5466_, 3, v___x_5465_);
lean_ctor_set(v___x_5466_, 4, v___x_5465_);
lean_ctor_set(v___x_5466_, 5, v___x_5465_);
return v___x_5466_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5467_; lean_object* v___x_5468_; 
v___x_5467_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5468_, 0, v___x_5467_);
lean_ctor_set(v___x_5468_, 1, v___x_5467_);
lean_ctor_set(v___x_5468_, 2, v___x_5467_);
lean_ctor_set(v___x_5468_, 3, v___x_5467_);
lean_ctor_set(v___x_5468_, 4, v___x_5467_);
return v___x_5468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5469_, lean_object* v_name_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_){
_start:
{
lean_object* v___x_5474_; lean_object* v_env_5475_; lean_object* v___x_5476_; 
v___x_5474_ = lean_st_ref_get(v___y_5472_);
v_env_5475_ = lean_ctor_get(v___x_5474_, 0);
lean_inc_ref(v_env_5475_);
lean_dec(v___x_5474_);
v___x_5476_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5475_, v_name_5470_);
if (lean_obj_tag(v___x_5476_) == 1)
{
lean_object* v_val_5477_; uint8_t v___x_5478_; uint8_t v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
v_val_5477_ = lean_ctor_get(v___x_5476_, 0);
lean_inc(v_val_5477_);
lean_dec_ref_known(v___x_5476_, 1);
v___x_5478_ = 0;
v___x_5479_ = 1;
v___x_5480_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5481_ = lean_unsigned_to_nat(0u);
v___x_5482_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5483_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5484_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5485_ = lean_box(0);
lean_inc(v___x_5469_);
v___x_5486_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5486_, 0, v___x_5480_);
lean_ctor_set(v___x_5486_, 1, v___x_5469_);
lean_ctor_set(v___x_5486_, 2, v___x_5483_);
lean_ctor_set(v___x_5486_, 3, v___x_5484_);
lean_ctor_set(v___x_5486_, 4, v___x_5485_);
lean_ctor_set(v___x_5486_, 5, v___x_5481_);
lean_ctor_set(v___x_5486_, 6, v___x_5485_);
lean_ctor_set_uint8(v___x_5486_, sizeof(void*)*7, v___x_5478_);
lean_ctor_set_uint8(v___x_5486_, sizeof(void*)*7 + 1, v___x_5478_);
lean_ctor_set_uint8(v___x_5486_, sizeof(void*)*7 + 2, v___x_5478_);
lean_ctor_set_uint8(v___x_5486_, sizeof(void*)*7 + 3, v___x_5479_);
v___x_5487_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5488_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5489_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5490_, 0, v___x_5487_);
lean_ctor_set(v___x_5490_, 1, v___x_5488_);
lean_ctor_set(v___x_5490_, 2, v___x_5469_);
lean_ctor_set(v___x_5490_, 3, v___x_5482_);
lean_ctor_set(v___x_5490_, 4, v___x_5489_);
v___x_5491_ = lean_st_mk_ref(v___x_5490_);
lean_inc(v___y_5472_);
lean_inc_ref(v___y_5471_);
lean_inc(v___x_5491_);
v___x_5492_ = lean_get_match_equations_for(v_val_5477_, v___x_5486_, v___x_5491_, v___y_5471_, v___y_5472_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5501_; 
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5501_ == 0)
{
lean_object* v_unused_5502_; 
v_unused_5502_ = lean_ctor_get(v___x_5492_, 0);
lean_dec(v_unused_5502_);
v___x_5494_ = v___x_5492_;
v_isShared_5495_ = v_isSharedCheck_5501_;
goto v_resetjp_5493_;
}
else
{
lean_dec(v___x_5492_);
v___x_5494_ = lean_box(0);
v_isShared_5495_ = v_isSharedCheck_5501_;
goto v_resetjp_5493_;
}
v_resetjp_5493_:
{
lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5499_; 
v___x_5496_ = lean_st_ref_get(v___x_5491_);
lean_dec(v___x_5491_);
lean_dec(v___x_5496_);
v___x_5497_ = lean_box(v___x_5479_);
if (v_isShared_5495_ == 0)
{
lean_ctor_set(v___x_5494_, 0, v___x_5497_);
v___x_5499_ = v___x_5494_;
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
lean_dec(v___x_5491_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5510_; 
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5510_ == 0)
{
lean_object* v_unused_5511_; 
v_unused_5511_ = lean_ctor_get(v___x_5492_, 0);
lean_dec(v_unused_5511_);
v___x_5504_ = v___x_5492_;
v_isShared_5505_ = v_isSharedCheck_5510_;
goto v_resetjp_5503_;
}
else
{
lean_dec(v___x_5492_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5510_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5506_; lean_object* v___x_5508_; 
v___x_5506_ = lean_box(v___x_5479_);
if (v_isShared_5505_ == 0)
{
lean_ctor_set_tag(v___x_5504_, 0);
lean_ctor_set(v___x_5504_, 0, v___x_5506_);
v___x_5508_ = v___x_5504_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v___x_5506_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
}
}
}
else
{
lean_object* v_a_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5519_; 
v_a_5512_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5519_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5519_ == 0)
{
v___x_5514_ = v___x_5492_;
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_a_5512_);
lean_dec(v___x_5492_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5517_; 
if (v_isShared_5515_ == 0)
{
v___x_5517_ = v___x_5514_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5512_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
}
}
}
else
{
uint8_t v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; 
lean_dec(v___x_5476_);
lean_dec(v___x_5469_);
v___x_5520_ = 0;
v___x_5521_ = lean_box(v___x_5520_);
v___x_5522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5522_, 0, v___x_5521_);
return v___x_5522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5523_, lean_object* v_name_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_){
_start:
{
lean_object* v_res_5528_; 
v_res_5528_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5523_, v_name_5524_, v___y_5525_, v___y_5526_);
lean_dec(v___y_5526_);
lean_dec_ref(v___y_5525_);
return v_res_5528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5532_; lean_object* v___x_5533_; 
v___f_5532_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5533_ = l_Lean_registerReservedNameAction(v___f_5532_);
return v___x_5533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5534_){
_start:
{
lean_object* v_res_5535_; 
v_res_5535_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5536_, lean_object* v_n_5537_){
_start:
{
if (lean_obj_tag(v_n_5537_) == 1)
{
lean_object* v_pre_5538_; lean_object* v_str_5539_; uint8_t v___x_5540_; 
v_pre_5538_ = lean_ctor_get(v_n_5537_, 0);
lean_inc(v_pre_5538_);
v_str_5539_ = lean_ctor_get(v_n_5537_, 1);
lean_inc_ref(v_str_5539_);
lean_dec_ref_known(v_n_5537_, 2);
v___x_5540_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5539_);
if (v___x_5540_ == 0)
{
lean_object* v___x_5541_; 
lean_dec(v_pre_5538_);
lean_dec_ref(v_env_5536_);
v___x_5541_ = lean_box(0);
return v___x_5541_;
}
else
{
uint8_t v___x_5542_; 
lean_inc(v_pre_5538_);
v___x_5542_ = l_Lean_Meta_isMatcherCore(v_env_5536_, v_pre_5538_);
if (v___x_5542_ == 0)
{
lean_object* v___x_5543_; 
lean_dec(v_pre_5538_);
v___x_5543_ = lean_box(0);
return v___x_5543_;
}
else
{
lean_object* v___x_5544_; 
v___x_5544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5544_, 0, v_pre_5538_);
return v___x_5544_;
}
}
}
else
{
lean_object* v___x_5545_; 
lean_dec(v_n_5537_);
lean_dec_ref(v_env_5536_);
v___x_5545_ = lean_box(0);
return v___x_5545_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5546_, lean_object* v_x2_5547_){
_start:
{
lean_object* v___x_5548_; 
v___x_5548_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5546_, v_x2_5547_);
if (lean_obj_tag(v___x_5548_) == 0)
{
uint8_t v___x_5549_; 
v___x_5549_ = 0;
return v___x_5549_;
}
else
{
uint8_t v___x_5550_; 
lean_dec_ref_known(v___x_5548_, 1);
v___x_5550_ = 1;
return v___x_5550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5551_, lean_object* v_x2_5552_){
_start:
{
uint8_t v_res_5553_; lean_object* v_r_5554_; 
v_res_5553_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5551_, v_x2_5552_);
v_r_5554_ = lean_box(v_res_5553_);
return v_r_5554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5557_; lean_object* v___x_5558_; 
v___f_5557_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5558_ = l_Lean_registerReservedNamePredicate(v___f_5557_);
return v___x_5558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5559_){
_start:
{
lean_object* v_res_5560_; 
v_res_5560_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5561_, lean_object* v_name_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_){
_start:
{
lean_object* v___x_5566_; lean_object* v_env_5567_; lean_object* v___x_5568_; 
v___x_5566_ = lean_st_ref_get(v___y_5564_);
v_env_5567_ = lean_ctor_get(v___x_5566_, 0);
lean_inc_ref(v_env_5567_);
lean_dec(v___x_5566_);
v___x_5568_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5567_, v_name_5562_);
if (lean_obj_tag(v___x_5568_) == 1)
{
lean_object* v_val_5569_; uint8_t v___x_5570_; uint8_t v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; 
v_val_5569_ = lean_ctor_get(v___x_5568_, 0);
lean_inc(v_val_5569_);
lean_dec_ref_known(v___x_5568_, 1);
v___x_5570_ = 0;
v___x_5571_ = 1;
v___x_5572_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5573_ = lean_unsigned_to_nat(32u);
v___x_5574_ = lean_mk_empty_array_with_capacity(v___x_5573_);
lean_dec_ref(v___x_5574_);
v___x_5575_ = lean_unsigned_to_nat(0u);
v___x_5576_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5577_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5578_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5579_ = lean_box(0);
lean_inc(v___x_5561_);
v___x_5580_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5580_, 0, v___x_5572_);
lean_ctor_set(v___x_5580_, 1, v___x_5561_);
lean_ctor_set(v___x_5580_, 2, v___x_5577_);
lean_ctor_set(v___x_5580_, 3, v___x_5578_);
lean_ctor_set(v___x_5580_, 4, v___x_5579_);
lean_ctor_set(v___x_5580_, 5, v___x_5575_);
lean_ctor_set(v___x_5580_, 6, v___x_5579_);
lean_ctor_set_uint8(v___x_5580_, sizeof(void*)*7, v___x_5570_);
lean_ctor_set_uint8(v___x_5580_, sizeof(void*)*7 + 1, v___x_5570_);
lean_ctor_set_uint8(v___x_5580_, sizeof(void*)*7 + 2, v___x_5570_);
lean_ctor_set_uint8(v___x_5580_, sizeof(void*)*7 + 3, v___x_5571_);
v___x_5581_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5582_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5583_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5581_);
lean_ctor_set(v___x_5584_, 1, v___x_5582_);
lean_ctor_set(v___x_5584_, 2, v___x_5561_);
lean_ctor_set(v___x_5584_, 3, v___x_5576_);
lean_ctor_set(v___x_5584_, 4, v___x_5583_);
v___x_5585_ = lean_st_mk_ref(v___x_5584_);
lean_inc(v___y_5564_);
lean_inc_ref(v___y_5563_);
lean_inc(v___x_5585_);
v___x_5586_ = lean_get_congr_match_equations_for(v_val_5569_, v___x_5580_, v___x_5585_, v___y_5563_, v___y_5564_);
if (lean_obj_tag(v___x_5586_) == 0)
{
lean_object* v___x_5588_; uint8_t v_isShared_5589_; uint8_t v_isSharedCheck_5595_; 
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5586_);
if (v_isSharedCheck_5595_ == 0)
{
lean_object* v_unused_5596_; 
v_unused_5596_ = lean_ctor_get(v___x_5586_, 0);
lean_dec(v_unused_5596_);
v___x_5588_ = v___x_5586_;
v_isShared_5589_ = v_isSharedCheck_5595_;
goto v_resetjp_5587_;
}
else
{
lean_dec(v___x_5586_);
v___x_5588_ = lean_box(0);
v_isShared_5589_ = v_isSharedCheck_5595_;
goto v_resetjp_5587_;
}
v_resetjp_5587_:
{
lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5593_; 
v___x_5590_ = lean_st_ref_get(v___x_5585_);
lean_dec(v___x_5585_);
lean_dec(v___x_5590_);
v___x_5591_ = lean_box(v___x_5571_);
if (v_isShared_5589_ == 0)
{
lean_ctor_set(v___x_5588_, 0, v___x_5591_);
v___x_5593_ = v___x_5588_;
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
lean_dec(v___x_5585_);
if (lean_obj_tag(v___x_5586_) == 0)
{
lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5604_; 
v_isSharedCheck_5604_ = !lean_is_exclusive(v___x_5586_);
if (v_isSharedCheck_5604_ == 0)
{
lean_object* v_unused_5605_; 
v_unused_5605_ = lean_ctor_get(v___x_5586_, 0);
lean_dec(v_unused_5605_);
v___x_5598_ = v___x_5586_;
v_isShared_5599_ = v_isSharedCheck_5604_;
goto v_resetjp_5597_;
}
else
{
lean_dec(v___x_5586_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5604_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v___x_5600_; lean_object* v___x_5602_; 
v___x_5600_ = lean_box(v___x_5571_);
if (v_isShared_5599_ == 0)
{
lean_ctor_set_tag(v___x_5598_, 0);
lean_ctor_set(v___x_5598_, 0, v___x_5600_);
v___x_5602_ = v___x_5598_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v___x_5600_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
else
{
lean_object* v_a_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5613_; 
v_a_5606_ = lean_ctor_get(v___x_5586_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5586_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5608_ = v___x_5586_;
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_a_5606_);
lean_dec(v___x_5586_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5611_; 
if (v_isShared_5609_ == 0)
{
v___x_5611_ = v___x_5608_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
v___x_5611_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
return v___x_5611_;
}
}
}
}
}
else
{
uint8_t v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; 
lean_dec(v___x_5568_);
lean_dec(v___x_5561_);
v___x_5614_ = 0;
v___x_5615_ = lean_box(v___x_5614_);
v___x_5616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5615_);
return v___x_5616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5617_, lean_object* v_name_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_){
_start:
{
lean_object* v_res_5622_; 
v_res_5622_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5617_, v_name_5618_, v___y_5619_, v___y_5620_);
lean_dec(v___y_5620_);
lean_dec_ref(v___y_5619_);
return v_res_5622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5626_; lean_object* v___x_5627_; 
v___f_5626_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5627_ = l_Lean_registerReservedNameAction(v___f_5626_);
return v___x_5627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5628_){
_start:
{
lean_object* v_res_5629_; 
v_res_5629_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5629_;
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
