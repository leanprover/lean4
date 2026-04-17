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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
uint8_t lean_is_matcher(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_private_to_user_name(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimOffset"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(15, 200, 217, 88, 39, 250, 32, 250)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "goal's target does not contain `Nat.elimOffset`"};
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1;
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
lean_dec_ref(v_ty_83_);
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
lean_dec_ref(v_fst_103_);
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
lean_dec_ref(v___x_168_);
lean_inc_ref(v_binderType_149_);
v___x_170_ = l_Lean_Meta_isExprDefEq(v_a_169_, v_binderType_149_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
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
lean_dec_ref(v___x_272_);
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
lean_dec_ref(v___x_338_);
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
lean_dec_ref(v___x_448_);
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
lean_dec_ref(v___x_467_);
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
lean_dec_ref(v___x_577_);
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
lean_dec_ref(v___x_596_);
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
lean_dec_ref(v_fst_694_);
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
lean_dec_ref(v_fst_723_);
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
lean_dec_ref(v_a_761_);
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
lean_dec_ref(v___x_846_);
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
lean_dec_ref(v___x_865_);
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
lean_dec_ref(v___x_968_);
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
lean_dec_ref(v___x_987_);
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
lean_dec_ref(v_a_1073_);
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
lean_dec_ref(v_a_1073_);
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
lean_dec_ref(v_fst_1091_);
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
lean_dec_ref(v_fst_1147_);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object* v_x_1190_){
_start:
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2));
v___x_1192_ = lean_name_eq(v_x_1190_, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object* v_x_1193_){
_start:
{
uint8_t v_res_1194_; lean_object* v_r_1195_; 
v_res_1194_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(v_x_1193_);
lean_dec(v_x_1193_);
v_r_1195_ = lean_box(v_res_1194_);
return v_r_1195_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object* v_e_1196_){
_start:
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2));
v___x_1198_ = l_Lean_Expr_isConstOf(v_e_1196_, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object* v_e_1199_){
_start:
{
uint8_t v_res_1200_; lean_object* v_r_1201_; 
v_res_1200_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(v_e_1199_);
lean_dec_ref(v_e_1199_);
v_r_1201_ = lean_box(v_res_1200_);
return v_r_1201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2));
v___x_1206_ = l_Lean_stringToMessageData(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object* v_mvarId_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; 
lean_inc(v_mvarId_1207_);
v___x_1213_ = l_Lean_MVarId_getType(v_mvarId_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___f_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref(v___x_1213_);
v___f_1215_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0));
v___f_1216_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1));
v___x_1217_ = lean_find_expr(v___f_1216_, v_a_1214_);
lean_dec(v_a_1214_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_mvarId_1207_);
v___x_1218_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3);
v___x_1219_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1218_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_object* v___x_1228_; 
lean_dec_ref(v___x_1217_);
v___x_1228_ = l_Lean_MVarId_deltaTarget(v_mvarId_1207_, v___f_1215_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
return v___x_1228_;
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_mvarId_1207_);
v_a_1229_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1213_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1213_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object* v_mvarId_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_mvarId_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
return v_res_1243_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = l_Lean_maxRecDepthErrorMessage;
v___x_1250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3);
v___x_1252_ = l_Lean_MessageData_ofFormat(v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4);
v___x_1254_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2));
v___x_1255_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v___x_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(lean_object* v_ref_1256_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_ref_1256_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___boxed(lean_object* v_ref_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object* v_00_u03b1_1264_, lean_object* v_ref_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1265_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object* v_00_u03b1_1272_, lean_object* v_ref_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v_00_u03b1_1272_, v_ref_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object* v_a_1280_, lean_object* v_____r_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_mk_empty_array_with_capacity(v___x_1287_);
v___x_1289_ = lean_array_push(v___x_1288_, v_a_1280_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object* v_a_1291_, lean_object* v_____r_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1291_, v_____r_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
return v_res_1298_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1299_; double v___x_1300_; 
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lean_float_of_nat(v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object* v_cls_1304_, lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_ref_1311_; lean_object* v___x_1312_; lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1357_; 
v_ref_1311_ = lean_ctor_get(v___y_1308_, 5);
v___x_1312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1357_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1357_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v_traceState_1318_; lean_object* v_env_1319_; lean_object* v_nextMacroScope_1320_; lean_object* v_ngen_1321_; lean_object* v_auxDeclNGen_1322_; lean_object* v_cache_1323_; lean_object* v_messages_1324_; lean_object* v_infoState_1325_; lean_object* v_snapshotTasks_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1356_; 
v___x_1317_ = lean_st_ref_take(v___y_1309_);
v_traceState_1318_ = lean_ctor_get(v___x_1317_, 4);
v_env_1319_ = lean_ctor_get(v___x_1317_, 0);
v_nextMacroScope_1320_ = lean_ctor_get(v___x_1317_, 1);
v_ngen_1321_ = lean_ctor_get(v___x_1317_, 2);
v_auxDeclNGen_1322_ = lean_ctor_get(v___x_1317_, 3);
v_cache_1323_ = lean_ctor_get(v___x_1317_, 5);
v_messages_1324_ = lean_ctor_get(v___x_1317_, 6);
v_infoState_1325_ = lean_ctor_get(v___x_1317_, 7);
v_snapshotTasks_1326_ = lean_ctor_get(v___x_1317_, 8);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1328_ = v___x_1317_;
v_isShared_1329_ = v_isSharedCheck_1356_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_snapshotTasks_1326_);
lean_inc(v_infoState_1325_);
lean_inc(v_messages_1324_);
lean_inc(v_cache_1323_);
lean_inc(v_traceState_1318_);
lean_inc(v_auxDeclNGen_1322_);
lean_inc(v_ngen_1321_);
lean_inc(v_nextMacroScope_1320_);
lean_inc(v_env_1319_);
lean_dec(v___x_1317_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1356_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
uint64_t v_tid_1330_; lean_object* v_traces_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1355_; 
v_tid_1330_ = lean_ctor_get_uint64(v_traceState_1318_, sizeof(void*)*1);
v_traces_1331_ = lean_ctor_get(v_traceState_1318_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_traceState_1318_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1333_ = v_traceState_1318_;
v_isShared_1334_ = v_isSharedCheck_1355_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_traces_1331_);
lean_dec(v_traceState_1318_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1355_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; double v___x_1336_; uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1335_ = lean_box(0);
v___x_1336_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0);
v___x_1337_ = 0;
v___x_1338_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1));
v___x_1339_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1339_, 0, v_cls_1304_);
lean_ctor_set(v___x_1339_, 1, v___x_1335_);
lean_ctor_set(v___x_1339_, 2, v___x_1338_);
lean_ctor_set_float(v___x_1339_, sizeof(void*)*3, v___x_1336_);
lean_ctor_set_float(v___x_1339_, sizeof(void*)*3 + 8, v___x_1336_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*3 + 16, v___x_1337_);
v___x_1340_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2));
v___x_1341_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set(v___x_1341_, 1, v_a_1313_);
lean_ctor_set(v___x_1341_, 2, v___x_1340_);
lean_inc(v_ref_1311_);
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v_ref_1311_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_PersistentArray_push___redArg(v_traces_1331_, v___x_1342_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1343_);
v___x_1345_ = v___x_1333_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1343_);
lean_ctor_set_uint64(v_reuseFailAlloc_1354_, sizeof(void*)*1, v_tid_1330_);
v___x_1345_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 4, v___x_1345_);
v___x_1347_ = v___x_1328_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_env_1319_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_nextMacroScope_1320_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_ngen_1321_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v_auxDeclNGen_1322_);
lean_ctor_set(v_reuseFailAlloc_1353_, 4, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1353_, 5, v_cache_1323_);
lean_ctor_set(v_reuseFailAlloc_1353_, 6, v_messages_1324_);
lean_ctor_set(v_reuseFailAlloc_1353_, 7, v_infoState_1325_);
lean_ctor_set(v_reuseFailAlloc_1353_, 8, v_snapshotTasks_1326_);
v___x_1347_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1348_ = lean_st_ref_set(v___y_1309_, v___x_1347_);
v___x_1349_ = lean_box(0);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1349_);
v___x_1351_ = v___x_1315_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object* v_cls_1358_, lean_object* v_msg_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1358_, v_msg_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1365_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0));
v___x_1368_ = l_Lean_stringToMessageData(v___x_1367_);
return v___x_1368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3(void){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2));
v___x_1371_ = l_Lean_stringToMessageData(v___x_1370_);
return v___x_1371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4));
v___x_1374_ = l_Lean_stringToMessageData(v___x_1373_);
return v___x_1374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16(void){
_start:
{
lean_object* v_cls_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_cls_1391_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1392_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15));
v___x_1393_ = l_Lean_Name_append(v___x_1392_, v_cls_1391_);
return v___x_1393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17));
v___x_1396_ = l_Lean_stringToMessageData(v___x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1397_, lean_object* v_mvarId_1398_, lean_object* v_depth_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v_a_1410_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; uint8_t v___y_1447_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; uint8_t v___y_1472_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v_a_1496_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; uint8_t v___y_1507_; uint8_t v___y_1508_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; uint8_t v___y_1549_; lean_object* v_a_1550_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; uint8_t v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; uint8_t v___y_1572_; uint8_t v___y_1573_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; uint8_t v___y_1604_; uint8_t v___y_1605_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; uint8_t v___y_1628_; lean_object* v___y_1629_; uint8_t v___y_1630_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; uint8_t v___y_1653_; lean_object* v___y_1654_; uint8_t v___y_1655_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; uint8_t v___y_1680_; uint8_t v___y_1681_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___y_1709_; uint8_t v___y_1710_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v_fileName_1761_; lean_object* v_fileMap_1762_; lean_object* v_options_1763_; lean_object* v_currRecDepth_1764_; lean_object* v_maxRecDepth_1765_; lean_object* v_ref_1766_; lean_object* v_currNamespace_1767_; lean_object* v_openDecls_1768_; lean_object* v_initHeartbeats_1769_; lean_object* v_maxHeartbeats_1770_; lean_object* v_quotContext_1771_; lean_object* v_currMacroScope_1772_; uint8_t v_diag_1773_; lean_object* v_cancelTk_x3f_1774_; uint8_t v_suppressElabErrors_1775_; lean_object* v_inheritedTraceOptions_1776_; lean_object* v_cls_1777_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_fileName_1761_ = lean_ctor_get(v_a_1402_, 0);
v_fileMap_1762_ = lean_ctor_get(v_a_1402_, 1);
v_options_1763_ = lean_ctor_get(v_a_1402_, 2);
v_currRecDepth_1764_ = lean_ctor_get(v_a_1402_, 3);
v_maxRecDepth_1765_ = lean_ctor_get(v_a_1402_, 4);
v_ref_1766_ = lean_ctor_get(v_a_1402_, 5);
v_currNamespace_1767_ = lean_ctor_get(v_a_1402_, 6);
v_openDecls_1768_ = lean_ctor_get(v_a_1402_, 7);
v_initHeartbeats_1769_ = lean_ctor_get(v_a_1402_, 8);
v_maxHeartbeats_1770_ = lean_ctor_get(v_a_1402_, 9);
v_quotContext_1771_ = lean_ctor_get(v_a_1402_, 10);
v_currMacroScope_1772_ = lean_ctor_get(v_a_1402_, 11);
v_diag_1773_ = lean_ctor_get_uint8(v_a_1402_, sizeof(void*)*14);
v_cancelTk_x3f_1774_ = lean_ctor_get(v_a_1402_, 12);
v_suppressElabErrors_1775_ = lean_ctor_get_uint8(v_a_1402_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1776_ = lean_ctor_get(v_a_1402_, 13);
v_cls_1777_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_nat_dec_eq(v_maxRecDepth_1765_, v___x_1789_);
if (v___x_1790_ == 0)
{
uint8_t v___x_1791_; 
v___x_1791_ = lean_nat_dec_eq(v_currRecDepth_1764_, v_maxRecDepth_1765_);
if (v___x_1791_ == 0)
{
goto v___jp_1778_;
}
else
{
lean_object* v___x_1792_; 
lean_dec(v_mvarId_1398_);
lean_dec(v_matchDeclName_1397_);
lean_inc(v_ref_1766_);
v___x_1792_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1766_);
return v___x_1792_;
}
}
else
{
goto v___jp_1778_;
}
v___jp_1405_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = lean_array_get_size(v_a_1410_);
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_nat_dec_lt(v___x_1411_, v___x_1412_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
lean_dec_ref(v_a_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v_matchDeclName_1397_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
return v___x_1415_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_le(v___x_1412_, v___x_1412_);
if (v___x_1416_ == 0)
{
if (v___x_1414_ == 0)
{
lean_object* v___x_1417_; 
lean_dec_ref(v_a_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v_matchDeclName_1397_);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1413_);
return v___x_1417_;
}
else
{
size_t v___x_1418_; size_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = ((size_t)0ULL);
v___x_1419_ = lean_usize_of_nat(v___x_1412_);
v___x_1420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1399_, v_matchDeclName_1397_, v_a_1410_, v___x_1418_, v___x_1419_, v___x_1413_, v___y_1408_, v___y_1406_, v___y_1409_, v___y_1407_);
lean_dec_ref(v___y_1409_);
lean_dec_ref(v_a_1410_);
return v___x_1420_;
}
}
else
{
size_t v___x_1421_; size_t v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = ((size_t)0ULL);
v___x_1422_ = lean_usize_of_nat(v___x_1412_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1399_, v_matchDeclName_1397_, v_a_1410_, v___x_1421_, v___x_1422_, v___x_1413_, v___y_1408_, v___y_1406_, v___y_1409_, v___y_1407_);
lean_dec_ref(v___y_1409_);
lean_dec_ref(v_a_1410_);
return v___x_1423_;
}
}
}
v___jp_1424_:
{
if (lean_obj_tag(v___y_1429_) == 0)
{
lean_object* v_a_1430_; 
v_a_1430_ = lean_ctor_get(v___y_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref(v___y_1429_);
v___y_1406_ = v___y_1425_;
v___y_1407_ = v___y_1427_;
v___y_1408_ = v___y_1426_;
v___y_1409_ = v___y_1428_;
v_a_1410_ = v_a_1430_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v___y_1428_);
lean_dec(v_matchDeclName_1397_);
v_a_1431_ = lean_ctor_get(v___y_1429_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___y_1429_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___y_1429_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___y_1429_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
v___jp_1439_:
{
if (v___y_1447_ == 0)
{
lean_object* v___x_1448_; 
lean_dec_ref(v___y_1443_);
v___x_1448_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1442_, v___y_1440_, v___y_1445_);
lean_dec_ref(v___y_1442_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1462_; 
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v___x_1448_, 0);
lean_dec(v_unused_1463_);
v___x_1450_ = v___x_1448_;
v_isShared_1451_ = v_isSharedCheck_1462_;
goto v_resetjp_1449_;
}
else
{
lean_dec(v___x_1448_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1462_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1452_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1397_);
v___x_1453_ = l_Lean_MessageData_ofName(v_matchDeclName_1397_);
v___x_1454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1452_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
v___x_1455_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set_tag(v___x_1450_, 1);
lean_ctor_set(v___x_1450_, 0, v___y_1441_);
v___x_1458_ = v___x_1450_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___y_1441_);
v___x_1458_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1456_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1459_, v___y_1444_, v___y_1440_, v___y_1446_, v___y_1445_);
v___y_1425_ = v___y_1440_;
v___y_1426_ = v___y_1444_;
v___y_1427_ = v___y_1445_;
v___y_1428_ = v___y_1446_;
v___y_1429_ = v___x_1460_;
goto v___jp_1424_;
}
}
}
else
{
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1441_);
lean_dec(v_matchDeclName_1397_);
return v___x_1448_;
}
}
else
{
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
v___y_1425_ = v___y_1440_;
v___y_1426_ = v___y_1444_;
v___y_1427_ = v___y_1445_;
v___y_1428_ = v___y_1446_;
v___y_1429_ = v___y_1443_;
goto v___jp_1424_;
}
}
v___jp_1464_:
{
if (v___y_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_dec_ref(v___y_1468_);
v___x_1473_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1466_, v___y_1465_, v___y_1470_);
lean_dec_ref(v___y_1466_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v___x_1474_; 
lean_dec_ref(v___x_1473_);
v___x_1474_ = l_Lean_Meta_saveState___redArg(v___y_1465_, v___y_1470_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref(v___x_1474_);
lean_inc(v___y_1467_);
v___x_1476_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1467_, v___y_1469_, v___y_1465_, v___y_1471_, v___y_1470_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_dec(v_a_1475_);
lean_dec(v___y_1467_);
v___y_1425_ = v___y_1465_;
v___y_1426_ = v___y_1469_;
v___y_1427_ = v___y_1470_;
v___y_1428_ = v___y_1471_;
v___y_1429_ = v___x_1476_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1477_; uint8_t v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
v___x_1478_ = l_Lean_Exception_isInterrupt(v_a_1477_);
if (v___x_1478_ == 0)
{
uint8_t v___x_1479_; 
v___x_1479_ = l_Lean_Exception_isRuntime(v_a_1477_);
v___y_1440_ = v___y_1465_;
v___y_1441_ = v___y_1467_;
v___y_1442_ = v_a_1475_;
v___y_1443_ = v___x_1476_;
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___y_1470_;
v___y_1446_ = v___y_1471_;
v___y_1447_ = v___x_1479_;
goto v___jp_1439_;
}
else
{
lean_dec(v_a_1477_);
v___y_1440_ = v___y_1465_;
v___y_1441_ = v___y_1467_;
v___y_1442_ = v_a_1475_;
v___y_1443_ = v___x_1476_;
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___y_1470_;
v___y_1446_ = v___y_1471_;
v___y_1447_ = v___x_1478_;
goto v___jp_1439_;
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1467_);
lean_dec(v_matchDeclName_1397_);
v_a_1480_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1474_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1474_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
else
{
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1467_);
lean_dec(v_matchDeclName_1397_);
return v___x_1473_;
}
}
else
{
lean_object* v___x_1488_; 
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v_matchDeclName_1397_);
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___y_1468_);
return v___x_1488_;
}
}
v___jp_1489_:
{
uint8_t v___x_1497_; 
v___x_1497_ = l_Lean_Exception_isInterrupt(v_a_1496_);
if (v___x_1497_ == 0)
{
uint8_t v___x_1498_; 
lean_inc_ref(v_a_1496_);
v___x_1498_ = l_Lean_Exception_isRuntime(v_a_1496_);
v___y_1465_ = v___y_1490_;
v___y_1466_ = v___y_1491_;
v___y_1467_ = v___y_1492_;
v___y_1468_ = v_a_1496_;
v___y_1469_ = v___y_1494_;
v___y_1470_ = v___y_1493_;
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___x_1498_;
goto v___jp_1464_;
}
else
{
v___y_1465_ = v___y_1490_;
v___y_1466_ = v___y_1491_;
v___y_1467_ = v___y_1492_;
v___y_1468_ = v_a_1496_;
v___y_1469_ = v___y_1494_;
v___y_1470_ = v___y_1493_;
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___x_1497_;
goto v___jp_1464_;
}
}
v___jp_1499_:
{
if (v___y_1508_ == 0)
{
lean_object* v___x_1509_; 
lean_dec_ref(v___y_1501_);
v___x_1509_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1503_, v___y_1500_, v___y_1505_);
lean_dec_ref(v___y_1503_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v___x_1510_; 
lean_dec_ref(v___x_1509_);
v___x_1510_ = l_Lean_Meta_saveState___redArg(v___y_1500_, v___y_1505_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref(v___x_1510_);
v___x_1512_ = lean_box(0);
lean_inc(v___y_1502_);
v___x_1513_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1502_, v___x_1512_, v___y_1507_, v___y_1504_, v___y_1500_, v___y_1506_, v___y_1505_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref(v___x_1513_);
if (lean_obj_tag(v_a_1514_) == 1)
{
lean_object* v_val_1515_; lean_object* v_fst_1516_; lean_object* v_snd_1517_; lean_object* v_mvarId_1518_; lean_object* v_fvarId_1519_; lean_object* v___x_1520_; 
v_val_1515_ = lean_ctor_get(v_a_1514_, 0);
lean_inc(v_val_1515_);
lean_dec_ref(v_a_1514_);
v_fst_1516_ = lean_ctor_get(v_val_1515_, 0);
lean_inc(v_fst_1516_);
v_snd_1517_ = lean_ctor_get(v_val_1515_, 1);
lean_inc(v_snd_1517_);
lean_dec(v_val_1515_);
v_mvarId_1518_ = lean_ctor_get(v_fst_1516_, 0);
lean_inc(v_mvarId_1518_);
v_fvarId_1519_ = lean_ctor_get(v_fst_1516_, 1);
lean_inc(v_fvarId_1519_);
lean_dec(v_fst_1516_);
v___x_1520_ = l_Lean_Meta_trySubst(v_mvarId_1518_, v_fvarId_1519_, v___y_1504_, v___y_1500_, v___y_1506_, v___y_1505_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_mvarId_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec(v_a_1511_);
lean_dec(v___y_1502_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref(v___x_1520_);
v_mvarId_1522_ = lean_ctor_get(v_snd_1517_, 0);
lean_inc(v_mvarId_1522_);
lean_dec(v_snd_1517_);
v___x_1523_ = lean_unsigned_to_nat(2u);
v___x_1524_ = lean_mk_empty_array_with_capacity(v___x_1523_);
v___x_1525_ = lean_array_push(v___x_1524_, v_a_1521_);
v___x_1526_ = lean_array_push(v___x_1525_, v_mvarId_1522_);
v___y_1406_ = v___y_1500_;
v___y_1407_ = v___y_1505_;
v___y_1408_ = v___y_1504_;
v___y_1409_ = v___y_1506_;
v_a_1410_ = v___x_1526_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1527_; 
lean_dec(v_snd_1517_);
v_a_1527_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1520_);
v___y_1490_ = v___y_1500_;
v___y_1491_ = v_a_1511_;
v___y_1492_ = v___y_1502_;
v___y_1493_ = v___y_1505_;
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1506_;
v_a_1496_ = v_a_1527_;
goto v___jp_1489_;
}
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec(v_a_1514_);
v___x_1528_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1529_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1528_, v___y_1504_, v___y_1500_, v___y_1506_, v___y_1505_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; 
lean_dec(v_a_1511_);
lean_dec(v___y_1502_);
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v___y_1406_ = v___y_1500_;
v___y_1407_ = v___y_1505_;
v___y_1408_ = v___y_1504_;
v___y_1409_ = v___y_1506_;
v_a_1410_ = v_a_1530_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1531_; 
v_a_1531_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1531_);
lean_dec_ref(v___x_1529_);
v___y_1490_ = v___y_1500_;
v___y_1491_ = v_a_1511_;
v___y_1492_ = v___y_1502_;
v___y_1493_ = v___y_1505_;
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1506_;
v_a_1496_ = v_a_1531_;
goto v___jp_1489_;
}
}
}
else
{
lean_object* v_a_1532_; 
v_a_1532_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1532_);
lean_dec_ref(v___x_1513_);
v___y_1490_ = v___y_1500_;
v___y_1491_ = v_a_1511_;
v___y_1492_ = v___y_1502_;
v___y_1493_ = v___y_1505_;
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1506_;
v_a_1496_ = v_a_1532_;
goto v___jp_1489_;
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1502_);
lean_dec(v_matchDeclName_1397_);
v_a_1533_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1510_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1510_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1502_);
lean_dec(v_matchDeclName_1397_);
return v___x_1509_;
}
}
else
{
lean_object* v___x_1541_; 
lean_dec_ref(v___y_1506_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec(v_matchDeclName_1397_);
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___y_1501_);
return v___x_1541_;
}
}
v___jp_1542_:
{
uint8_t v___x_1551_; 
v___x_1551_ = l_Lean_Exception_isInterrupt(v_a_1550_);
if (v___x_1551_ == 0)
{
uint8_t v___x_1552_; 
lean_inc_ref(v_a_1550_);
v___x_1552_ = l_Lean_Exception_isRuntime(v_a_1550_);
v___y_1500_ = v___y_1543_;
v___y_1501_ = v_a_1550_;
v___y_1502_ = v___y_1544_;
v___y_1503_ = v___y_1545_;
v___y_1504_ = v___y_1547_;
v___y_1505_ = v___y_1546_;
v___y_1506_ = v___y_1548_;
v___y_1507_ = v___y_1549_;
v___y_1508_ = v___x_1552_;
goto v___jp_1499_;
}
else
{
v___y_1500_ = v___y_1543_;
v___y_1501_ = v_a_1550_;
v___y_1502_ = v___y_1544_;
v___y_1503_ = v___y_1545_;
v___y_1504_ = v___y_1547_;
v___y_1505_ = v___y_1546_;
v___y_1506_ = v___y_1548_;
v___y_1507_ = v___y_1549_;
v___y_1508_ = v___x_1551_;
goto v___jp_1499_;
}
}
v___jp_1553_:
{
if (lean_obj_tag(v___y_1561_) == 0)
{
lean_object* v_a_1562_; 
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
v_a_1562_ = lean_ctor_get(v___y_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___y_1561_);
v___y_1406_ = v___y_1554_;
v___y_1407_ = v___y_1558_;
v___y_1408_ = v___y_1557_;
v___y_1409_ = v___y_1559_;
v_a_1410_ = v_a_1562_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1563_; 
v_a_1563_ = lean_ctor_get(v___y_1561_, 0);
lean_inc(v_a_1563_);
lean_dec_ref(v___y_1561_);
v___y_1543_ = v___y_1554_;
v___y_1544_ = v___y_1555_;
v___y_1545_ = v___y_1556_;
v___y_1546_ = v___y_1558_;
v___y_1547_ = v___y_1557_;
v___y_1548_ = v___y_1559_;
v___y_1549_ = v___y_1560_;
v_a_1550_ = v_a_1563_;
goto v___jp_1542_;
}
}
v___jp_1564_:
{
if (v___y_1573_ == 0)
{
lean_object* v___x_1574_; 
lean_dec_ref(v___y_1567_);
v___x_1574_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1565_, v___y_1566_, v___y_1570_);
lean_dec_ref(v___y_1565_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref(v___x_1574_);
v___x_1575_ = l_Lean_Meta_saveState___redArg(v___y_1566_, v___y_1570_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1575_);
lean_inc(v___y_1568_);
v___x_1577_ = l_Lean_Meta_simpIfTarget(v___y_1568_, v___y_1572_, v___y_1572_, v___y_1569_, v___y_1566_, v___y_1571_, v___y_1570_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; uint8_t v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = l_Lean_instBEqMVarId_beq(v_a_1578_, v___y_1568_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1578_, v___x_1580_, v___y_1569_, v___y_1566_, v___y_1571_, v___y_1570_);
v___y_1554_ = v___y_1566_;
v___y_1555_ = v___y_1568_;
v___y_1556_ = v_a_1576_;
v___y_1557_ = v___y_1569_;
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___y_1571_;
v___y_1560_ = v___y_1572_;
v___y_1561_ = v___x_1581_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1583_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1582_, v___y_1569_, v___y_1566_, v___y_1571_, v___y_1570_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref(v___x_1583_);
v___x_1585_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1578_, v_a_1584_, v___y_1569_, v___y_1566_, v___y_1571_, v___y_1570_);
v___y_1554_ = v___y_1566_;
v___y_1555_ = v___y_1568_;
v___y_1556_ = v_a_1576_;
v___y_1557_ = v___y_1569_;
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___y_1571_;
v___y_1560_ = v___y_1572_;
v___y_1561_ = v___x_1585_;
goto v___jp_1553_;
}
else
{
lean_object* v_a_1586_; 
lean_dec(v_a_1578_);
v_a_1586_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1583_);
v___y_1543_ = v___y_1566_;
v___y_1544_ = v___y_1568_;
v___y_1545_ = v_a_1576_;
v___y_1546_ = v___y_1570_;
v___y_1547_ = v___y_1569_;
v___y_1548_ = v___y_1571_;
v___y_1549_ = v___y_1572_;
v_a_1550_ = v_a_1586_;
goto v___jp_1542_;
}
}
}
else
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1577_);
v___y_1543_ = v___y_1566_;
v___y_1544_ = v___y_1568_;
v___y_1545_ = v_a_1576_;
v___y_1546_ = v___y_1570_;
v___y_1547_ = v___y_1569_;
v___y_1548_ = v___y_1571_;
v___y_1549_ = v___y_1572_;
v_a_1550_ = v_a_1587_;
goto v___jp_1542_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1568_);
lean_dec(v_matchDeclName_1397_);
v_a_1588_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1575_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1575_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1568_);
lean_dec(v_matchDeclName_1397_);
return v___x_1574_;
}
}
else
{
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1565_);
v___y_1425_ = v___y_1566_;
v___y_1426_ = v___y_1569_;
v___y_1427_ = v___y_1570_;
v___y_1428_ = v___y_1571_;
v___y_1429_ = v___y_1567_;
goto v___jp_1424_;
}
}
v___jp_1596_:
{
if (v___y_1605_ == 0)
{
lean_object* v___x_1606_; 
lean_dec_ref(v___y_1600_);
v___x_1606_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1598_, v___y_1597_, v___y_1602_);
lean_dec_ref(v___y_1598_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1607_; 
lean_dec_ref(v___x_1606_);
v___x_1607_ = l_Lean_Meta_saveState___redArg(v___y_1597_, v___y_1602_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1609_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref(v___x_1607_);
lean_inc(v___y_1599_);
v___x_1609_ = l_Lean_Meta_splitSparseCasesOn(v___y_1599_, v___y_1601_, v___y_1597_, v___y_1603_, v___y_1602_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_dec(v_a_1608_);
lean_dec(v___y_1599_);
v___y_1425_ = v___y_1597_;
v___y_1426_ = v___y_1601_;
v___y_1427_ = v___y_1602_;
v___y_1428_ = v___y_1603_;
v___y_1429_ = v___x_1609_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1610_; uint8_t v___x_1611_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
v___x_1611_ = l_Lean_Exception_isInterrupt(v_a_1610_);
if (v___x_1611_ == 0)
{
uint8_t v___x_1612_; 
v___x_1612_ = l_Lean_Exception_isRuntime(v_a_1610_);
v___y_1565_ = v_a_1608_;
v___y_1566_ = v___y_1597_;
v___y_1567_ = v___x_1609_;
v___y_1568_ = v___y_1599_;
v___y_1569_ = v___y_1601_;
v___y_1570_ = v___y_1602_;
v___y_1571_ = v___y_1603_;
v___y_1572_ = v___y_1604_;
v___y_1573_ = v___x_1612_;
goto v___jp_1564_;
}
else
{
lean_dec(v_a_1610_);
v___y_1565_ = v_a_1608_;
v___y_1566_ = v___y_1597_;
v___y_1567_ = v___x_1609_;
v___y_1568_ = v___y_1599_;
v___y_1569_ = v___y_1601_;
v___y_1570_ = v___y_1602_;
v___y_1571_ = v___y_1603_;
v___y_1572_ = v___y_1604_;
v___y_1573_ = v___x_1611_;
goto v___jp_1564_;
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1599_);
lean_dec(v_matchDeclName_1397_);
v_a_1613_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1607_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1607_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1599_);
lean_dec(v_matchDeclName_1397_);
return v___x_1606_;
}
}
else
{
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
v___y_1425_ = v___y_1597_;
v___y_1426_ = v___y_1601_;
v___y_1427_ = v___y_1602_;
v___y_1428_ = v___y_1603_;
v___y_1429_ = v___y_1600_;
goto v___jp_1424_;
}
}
v___jp_1621_:
{
if (v___y_1630_ == 0)
{
lean_object* v___x_1631_; 
lean_dec_ref(v___y_1622_);
v___x_1631_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1629_, v___y_1623_, v___y_1626_);
lean_dec_ref(v___y_1629_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref(v___x_1631_);
v___x_1632_ = l_Lean_Meta_saveState___redArg(v___y_1623_, v___y_1626_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref(v___x_1632_);
lean_inc(v___y_1624_);
v___x_1634_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1624_, v___y_1625_, v___y_1623_, v___y_1627_, v___y_1626_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec(v_a_1633_);
lean_dec(v___y_1624_);
v___y_1425_ = v___y_1623_;
v___y_1426_ = v___y_1625_;
v___y_1427_ = v___y_1626_;
v___y_1428_ = v___y_1627_;
v___y_1429_ = v___x_1634_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1635_; uint8_t v___x_1636_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
v___x_1636_ = l_Lean_Exception_isInterrupt(v_a_1635_);
if (v___x_1636_ == 0)
{
uint8_t v___x_1637_; 
v___x_1637_ = l_Lean_Exception_isRuntime(v_a_1635_);
v___y_1597_ = v___y_1623_;
v___y_1598_ = v_a_1633_;
v___y_1599_ = v___y_1624_;
v___y_1600_ = v___x_1634_;
v___y_1601_ = v___y_1625_;
v___y_1602_ = v___y_1626_;
v___y_1603_ = v___y_1627_;
v___y_1604_ = v___y_1628_;
v___y_1605_ = v___x_1637_;
goto v___jp_1596_;
}
else
{
lean_dec(v_a_1635_);
v___y_1597_ = v___y_1623_;
v___y_1598_ = v_a_1633_;
v___y_1599_ = v___y_1624_;
v___y_1600_ = v___x_1634_;
v___y_1601_ = v___y_1625_;
v___y_1602_ = v___y_1626_;
v___y_1603_ = v___y_1627_;
v___y_1604_ = v___y_1628_;
v___y_1605_ = v___x_1636_;
goto v___jp_1596_;
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1624_);
lean_dec(v_matchDeclName_1397_);
v_a_1638_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1632_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1632_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1624_);
lean_dec(v_matchDeclName_1397_);
return v___x_1631_;
}
}
else
{
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1624_);
v___y_1425_ = v___y_1623_;
v___y_1426_ = v___y_1625_;
v___y_1427_ = v___y_1626_;
v___y_1428_ = v___y_1627_;
v___y_1429_ = v___y_1622_;
goto v___jp_1424_;
}
}
v___jp_1646_:
{
if (v___y_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_dec_ref(v___y_1647_);
v___x_1656_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1654_, v___y_1648_, v___y_1651_);
lean_dec_ref(v___y_1654_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v___x_1657_; 
lean_dec_ref(v___x_1656_);
v___x_1657_ = l_Lean_Meta_saveState___redArg(v___y_1648_, v___y_1651_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1659_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref(v___x_1657_);
lean_inc(v___y_1649_);
v___x_1659_ = l_Lean_Meta_casesOnStuckLHS(v___y_1649_, v___y_1650_, v___y_1648_, v___y_1652_, v___y_1651_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_dec(v_a_1658_);
lean_dec(v___y_1649_);
v___y_1425_ = v___y_1648_;
v___y_1426_ = v___y_1650_;
v___y_1427_ = v___y_1651_;
v___y_1428_ = v___y_1652_;
v___y_1429_ = v___x_1659_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1660_; uint8_t v___x_1661_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
v___x_1661_ = l_Lean_Exception_isInterrupt(v_a_1660_);
if (v___x_1661_ == 0)
{
uint8_t v___x_1662_; 
v___x_1662_ = l_Lean_Exception_isRuntime(v_a_1660_);
v___y_1622_ = v___x_1659_;
v___y_1623_ = v___y_1648_;
v___y_1624_ = v___y_1649_;
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1653_;
v___y_1629_ = v_a_1658_;
v___y_1630_ = v___x_1662_;
goto v___jp_1621_;
}
else
{
lean_dec(v_a_1660_);
v___y_1622_ = v___x_1659_;
v___y_1623_ = v___y_1648_;
v___y_1624_ = v___y_1649_;
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1653_;
v___y_1629_ = v_a_1658_;
v___y_1630_ = v___x_1661_;
goto v___jp_1621_;
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1649_);
lean_dec(v_matchDeclName_1397_);
v_a_1663_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1657_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1657_);
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
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1649_);
lean_dec(v_matchDeclName_1397_);
return v___x_1656_;
}
}
else
{
lean_object* v___x_1671_; 
lean_dec_ref(v___y_1654_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1649_);
lean_dec(v_matchDeclName_1397_);
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___y_1647_);
return v___x_1671_;
}
}
v___jp_1672_:
{
if (v___y_1681_ == 0)
{
lean_object* v___x_1682_; 
lean_dec_ref(v___y_1674_);
v___x_1682_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1673_, v___y_1675_, v___y_1678_);
lean_dec_ref(v___y_1673_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v___x_1683_; 
lean_dec_ref(v___x_1682_);
v___x_1683_ = l_Lean_Meta_saveState___redArg(v___y_1675_, v___y_1678_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
lean_inc(v___y_1676_);
v___x_1685_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1676_, v___y_1677_, v___y_1675_, v___y_1679_, v___y_1678_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_dec(v_a_1684_);
lean_dec(v___y_1676_);
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = lean_mk_empty_array_with_capacity(v___x_1687_);
v___x_1689_ = lean_array_push(v___x_1688_, v_a_1686_);
v___y_1406_ = v___y_1675_;
v___y_1407_ = v___y_1678_;
v___y_1408_ = v___y_1677_;
v___y_1409_ = v___y_1679_;
v_a_1410_ = v___x_1689_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1690_; uint8_t v___x_1691_; 
v_a_1690_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1685_);
v___x_1691_ = l_Lean_Exception_isInterrupt(v_a_1690_);
if (v___x_1691_ == 0)
{
uint8_t v___x_1692_; 
lean_inc(v_a_1690_);
v___x_1692_ = l_Lean_Exception_isRuntime(v_a_1690_);
v___y_1647_ = v_a_1690_;
v___y_1648_ = v___y_1675_;
v___y_1649_ = v___y_1676_;
v___y_1650_ = v___y_1677_;
v___y_1651_ = v___y_1678_;
v___y_1652_ = v___y_1679_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v_a_1684_;
v___y_1655_ = v___x_1692_;
goto v___jp_1646_;
}
else
{
v___y_1647_ = v_a_1690_;
v___y_1648_ = v___y_1675_;
v___y_1649_ = v___y_1676_;
v___y_1650_ = v___y_1677_;
v___y_1651_ = v___y_1678_;
v___y_1652_ = v___y_1679_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v_a_1684_;
v___y_1655_ = v___x_1691_;
goto v___jp_1646_;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1676_);
lean_dec(v_matchDeclName_1397_);
v_a_1693_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1683_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1683_);
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
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1676_);
lean_dec(v_matchDeclName_1397_);
return v___x_1682_;
}
}
else
{
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1673_);
lean_dec(v_matchDeclName_1397_);
return v___y_1674_;
}
}
v___jp_1701_:
{
if (v___y_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec_ref(v___y_1705_);
v___x_1711_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1703_, v___y_1702_, v___y_1707_);
lean_dec_ref(v___y_1703_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref(v___x_1711_);
v___x_1712_ = lean_unsigned_to_nat(16u);
v___x_1713_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set_uint8(v___x_1713_, sizeof(void*)*1, v___y_1709_);
lean_ctor_set_uint8(v___x_1713_, sizeof(void*)*1 + 1, v___y_1709_);
lean_ctor_set_uint8(v___x_1713_, sizeof(void*)*1 + 2, v___y_1709_);
v___x_1714_ = l_Lean_Meta_saveState___redArg(v___y_1702_, v___y_1707_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1716_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref(v___x_1714_);
lean_inc(v___y_1704_);
v___x_1716_ = l_Lean_MVarId_contradiction(v___y_1704_, v___x_1713_, v___y_1706_, v___y_1702_, v___y_1708_, v___y_1707_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref(v___x_1716_);
lean_dec(v_a_1715_);
lean_dec(v___y_1704_);
v___x_1717_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1406_ = v___y_1702_;
v___y_1407_ = v___y_1707_;
v___y_1408_ = v___y_1706_;
v___y_1409_ = v___y_1708_;
v_a_1410_ = v___x_1717_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1718_; uint8_t v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1718_);
v___x_1719_ = l_Lean_Exception_isInterrupt(v_a_1718_);
if (v___x_1719_ == 0)
{
uint8_t v___x_1720_; 
v___x_1720_ = l_Lean_Exception_isRuntime(v_a_1718_);
v___y_1673_ = v_a_1715_;
v___y_1674_ = v___x_1716_;
v___y_1675_ = v___y_1702_;
v___y_1676_ = v___y_1704_;
v___y_1677_ = v___y_1706_;
v___y_1678_ = v___y_1707_;
v___y_1679_ = v___y_1708_;
v___y_1680_ = v___y_1709_;
v___y_1681_ = v___x_1720_;
goto v___jp_1672_;
}
else
{
lean_dec(v_a_1718_);
v___y_1673_ = v_a_1715_;
v___y_1674_ = v___x_1716_;
v___y_1675_ = v___y_1702_;
v___y_1676_ = v___y_1704_;
v___y_1677_ = v___y_1706_;
v___y_1678_ = v___y_1707_;
v___y_1679_ = v___y_1708_;
v___y_1680_ = v___y_1709_;
v___y_1681_ = v___x_1719_;
goto v___jp_1672_;
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1704_);
lean_dec(v_matchDeclName_1397_);
v_a_1721_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1714_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1714_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
else
{
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1704_);
lean_dec(v_matchDeclName_1397_);
return v___x_1711_;
}
}
else
{
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v_matchDeclName_1397_);
return v___y_1705_;
}
}
v___jp_1729_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1735_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1398_, v___x_1734_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = l_Lean_Meta_saveState___redArg(v___y_1731_, v___y_1733_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref(v___x_1737_);
v___x_1739_ = 1;
lean_inc(v_a_1736_);
v___x_1740_ = l_Lean_MVarId_refl(v_a_1736_, v___x_1739_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref(v___x_1740_);
lean_dec(v_a_1738_);
lean_dec(v_a_1736_);
v___x_1741_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1406_ = v___y_1731_;
v___y_1407_ = v___y_1733_;
v___y_1408_ = v___y_1730_;
v___y_1409_ = v___y_1732_;
v_a_1410_ = v___x_1741_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1742_; uint8_t v___x_1743_; 
v_a_1742_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1742_);
v___x_1743_ = l_Lean_Exception_isInterrupt(v_a_1742_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; 
v___x_1744_ = l_Lean_Exception_isRuntime(v_a_1742_);
v___y_1702_ = v___y_1731_;
v___y_1703_ = v_a_1738_;
v___y_1704_ = v_a_1736_;
v___y_1705_ = v___x_1740_;
v___y_1706_ = v___y_1730_;
v___y_1707_ = v___y_1733_;
v___y_1708_ = v___y_1732_;
v___y_1709_ = v___x_1739_;
v___y_1710_ = v___x_1744_;
goto v___jp_1701_;
}
else
{
lean_dec(v_a_1742_);
v___y_1702_ = v___y_1731_;
v___y_1703_ = v_a_1738_;
v___y_1704_ = v_a_1736_;
v___y_1705_ = v___x_1740_;
v___y_1706_ = v___y_1730_;
v___y_1707_ = v___y_1733_;
v___y_1708_ = v___y_1732_;
v___y_1709_ = v___x_1739_;
v___y_1710_ = v___x_1743_;
goto v___jp_1701_;
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec(v_a_1736_);
lean_dec_ref(v___y_1732_);
lean_dec(v_matchDeclName_1397_);
v_a_1745_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1737_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1737_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v___y_1732_);
lean_dec(v_matchDeclName_1397_);
v_a_1753_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1735_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1735_);
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
v___jp_1778_:
{
uint8_t v_hasTrace_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_hasTrace_1779_ = lean_ctor_get_uint8(v_options_1763_, sizeof(void*)*1);
v___x_1780_ = lean_unsigned_to_nat(1u);
v___x_1781_ = lean_nat_add(v_currRecDepth_1764_, v___x_1780_);
lean_inc_ref(v_inheritedTraceOptions_1776_);
lean_inc(v_cancelTk_x3f_1774_);
lean_inc(v_currMacroScope_1772_);
lean_inc(v_quotContext_1771_);
lean_inc(v_maxHeartbeats_1770_);
lean_inc(v_initHeartbeats_1769_);
lean_inc(v_openDecls_1768_);
lean_inc(v_currNamespace_1767_);
lean_inc(v_ref_1766_);
lean_inc(v_maxRecDepth_1765_);
lean_inc_ref(v_options_1763_);
lean_inc_ref(v_fileMap_1762_);
lean_inc_ref(v_fileName_1761_);
v___x_1782_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1782_, 0, v_fileName_1761_);
lean_ctor_set(v___x_1782_, 1, v_fileMap_1762_);
lean_ctor_set(v___x_1782_, 2, v_options_1763_);
lean_ctor_set(v___x_1782_, 3, v___x_1781_);
lean_ctor_set(v___x_1782_, 4, v_maxRecDepth_1765_);
lean_ctor_set(v___x_1782_, 5, v_ref_1766_);
lean_ctor_set(v___x_1782_, 6, v_currNamespace_1767_);
lean_ctor_set(v___x_1782_, 7, v_openDecls_1768_);
lean_ctor_set(v___x_1782_, 8, v_initHeartbeats_1769_);
lean_ctor_set(v___x_1782_, 9, v_maxHeartbeats_1770_);
lean_ctor_set(v___x_1782_, 10, v_quotContext_1771_);
lean_ctor_set(v___x_1782_, 11, v_currMacroScope_1772_);
lean_ctor_set(v___x_1782_, 12, v_cancelTk_x3f_1774_);
lean_ctor_set(v___x_1782_, 13, v_inheritedTraceOptions_1776_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*14, v_diag_1773_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*14 + 1, v_suppressElabErrors_1775_);
if (v_hasTrace_1779_ == 0)
{
v___y_1730_ = v_a_1400_;
v___y_1731_ = v_a_1401_;
v___y_1732_ = v___x_1782_;
v___y_1733_ = v_a_1403_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1784_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1776_, v_options_1763_, v___x_1783_);
if (v___x_1784_ == 0)
{
v___y_1730_ = v_a_1400_;
v___y_1731_ = v_a_1401_;
v___y_1732_ = v___x_1782_;
v___y_1733_ = v_a_1403_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1785_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1398_);
v___x_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_mvarId_1398_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1777_, v___x_1787_, v_a_1400_, v_a_1401_, v___x_1782_, v_a_1403_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_dec_ref(v___x_1788_);
v___y_1730_ = v_a_1400_;
v___y_1731_ = v_a_1401_;
v___y_1732_ = v___x_1782_;
v___y_1733_ = v_a_1403_;
goto v___jp_1729_;
}
else
{
lean_dec_ref(v___x_1782_);
lean_dec(v_mvarId_1398_);
lean_dec(v_matchDeclName_1397_);
return v___x_1788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1793_, lean_object* v_matchDeclName_1794_, lean_object* v_as_1795_, size_t v_i_1796_, size_t v_stop_1797_, lean_object* v_b_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_usize_dec_eq(v_i_1796_, v_stop_1797_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = lean_array_uget_borrowed(v_as_1795_, v_i_1796_);
v___x_1806_ = lean_unsigned_to_nat(1u);
v___x_1807_ = lean_nat_add(v_depth_1793_, v___x_1806_);
lean_inc(v___x_1805_);
lean_inc(v_matchDeclName_1794_);
v___x_1808_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1794_, v___x_1805_, v___x_1807_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___x_1807_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; size_t v___x_1810_; size_t v___x_1811_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref(v___x_1808_);
v___x_1810_ = ((size_t)1ULL);
v___x_1811_ = lean_usize_add(v_i_1796_, v___x_1810_);
v_i_1796_ = v___x_1811_;
v_b_1798_ = v_a_1809_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1794_);
return v___x_1808_;
}
}
else
{
lean_object* v___x_1813_; 
lean_dec(v_matchDeclName_1794_);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_b_1798_);
return v___x_1813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1814_, lean_object* v_matchDeclName_1815_, lean_object* v_as_1816_, lean_object* v_i_1817_, lean_object* v_stop_1818_, lean_object* v_b_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
size_t v_i_boxed_1825_; size_t v_stop_boxed_1826_; lean_object* v_res_1827_; 
v_i_boxed_1825_ = lean_unbox_usize(v_i_1817_);
lean_dec(v_i_1817_);
v_stop_boxed_1826_ = lean_unbox_usize(v_stop_1818_);
lean_dec(v_stop_1818_);
v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1814_, v_matchDeclName_1815_, v_as_1816_, v_i_boxed_1825_, v_stop_boxed_1826_, v_b_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v_as_1816_);
lean_dec(v_depth_1814_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1828_, lean_object* v_mvarId_1829_, lean_object* v_depth_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1828_, v_mvarId_1829_, v_depth_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_depth_1830_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1837_, lean_object* v___y_1838_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = l_Lean_Expr_hasMVar(v_e_1837_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_e_1837_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; lean_object* v_mctx_1843_; lean_object* v___x_1844_; lean_object* v_fst_1845_; lean_object* v_snd_1846_; lean_object* v___x_1847_; lean_object* v_cache_1848_; lean_object* v_zetaDeltaFVarIds_1849_; lean_object* v_postponed_1850_; lean_object* v_diag_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1860_; 
v___x_1842_ = lean_st_ref_get(v___y_1838_);
v_mctx_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc_ref(v_mctx_1843_);
lean_dec(v___x_1842_);
v___x_1844_ = l_Lean_instantiateMVarsCore(v_mctx_1843_, v_e_1837_);
v_fst_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_fst_1845_);
v_snd_1846_ = lean_ctor_get(v___x_1844_, 1);
lean_inc(v_snd_1846_);
lean_dec_ref(v___x_1844_);
v___x_1847_ = lean_st_ref_take(v___y_1838_);
v_cache_1848_ = lean_ctor_get(v___x_1847_, 1);
v_zetaDeltaFVarIds_1849_ = lean_ctor_get(v___x_1847_, 2);
v_postponed_1850_ = lean_ctor_get(v___x_1847_, 3);
v_diag_1851_ = lean_ctor_get(v___x_1847_, 4);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v___x_1847_, 0);
lean_dec(v_unused_1861_);
v___x_1853_ = v___x_1847_;
v_isShared_1854_ = v_isSharedCheck_1860_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_diag_1851_);
lean_inc(v_postponed_1850_);
lean_inc(v_zetaDeltaFVarIds_1849_);
lean_inc(v_cache_1848_);
lean_dec(v___x_1847_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1860_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v_snd_1846_);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_snd_1846_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_cache_1848_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_zetaDeltaFVarIds_1849_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_postponed_1850_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_diag_1851_);
v___x_1856_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_st_ref_set(v___y_1838_, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_fst_1845_);
return v___x_1858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1862_, v___y_1863_);
lean_dec(v___y_1863_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1866_, v___y_1868_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1880_, lean_object* v_localInsts_1881_, lean_object* v_x_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1880_, v_localInsts_1881_, v_x_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_a_1897_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1888_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1888_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1905_, lean_object* v_localInsts_1906_, lean_object* v_x_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1905_, v_localInsts_1906_, v_x_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1914_, lean_object* v_lctx_1915_, lean_object* v_localInsts_1916_, lean_object* v_x_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1915_, v_localInsts_1916_, v_x_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1924_, lean_object* v_lctx_1925_, lean_object* v_localInsts_1926_, lean_object* v_x_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1924_, v_lctx_1925_, v_localInsts_1926_, v_x_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
return v_res_1933_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1934_, lean_object* v_x_1935_){
_start:
{
uint8_t v___x_1936_; 
v___x_1936_ = lean_name_eq(v_x_1935_, v_matchDeclName_1934_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1937_, lean_object* v_x_1938_){
_start:
{
uint8_t v_res_1939_; lean_object* v_r_1940_; 
v_res_1939_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1937_, v_x_1938_);
lean_dec(v_x_1938_);
lean_dec(v_matchDeclName_1937_);
v_r_1940_ = lean_box(v_res_1939_);
return v_r_1940_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1941_, lean_object* v_a_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
uint8_t v___x_1949_; 
v___x_1949_ = lean_nat_dec_lt(v_a_1942_, v_upperBound_1941_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_dec(v_a_1942_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_b_1943_);
return v___x_1950_;
}
else
{
uint8_t v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = 0;
v___x_1952_ = l_Lean_Meta_introSubstEq(v_b_1943_, v___x_1951_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v_snd_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
v_snd_1954_ = lean_ctor_get(v_a_1953_, 1);
lean_inc(v_snd_1954_);
lean_dec(v_a_1953_);
v___x_1955_ = lean_unsigned_to_nat(1u);
v___x_1956_ = lean_nat_add(v_a_1942_, v___x_1955_);
lean_dec(v_a_1942_);
v_a_1942_ = v___x_1956_;
v_b_1943_ = v_snd_1954_;
goto _start;
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_a_1942_);
v_a_1958_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1952_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1952_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1966_, lean_object* v_a_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1966_, v_a_1967_, v_b_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_upperBound_1966_);
return v_res_1974_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1977_ = l_Lean_stringToMessageData(v___x_1976_);
return v___x_1977_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1980_ = l_Lean_stringToMessageData(v___x_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1981_, lean_object* v___f_1982_, lean_object* v_matchDeclName_1983_, lean_object* v___x_1984_, uint8_t v___x_1985_, lean_object* v_heqPos_1986_, lean_object* v_heqNum_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v___x_1993_; lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2144_; 
v___x_1993_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1981_, v___y_1989_);
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2144_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2144_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_box(0);
v___x_1999_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1994_, v___x_1998_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2143_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2002_ = v___x_1999_;
v_isShared_2003_ = v_isSharedCheck_2143_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2143_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; uint8_t v___y_2011_; lean_object* v_mvarId_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v_options_2068_; lean_object* v_inheritedTraceOptions_2069_; uint8_t v_hasTrace_2070_; lean_object* v___x_2071_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; 
v_options_2068_ = lean_ctor_get(v___y_1990_, 2);
v_inheritedTraceOptions_2069_ = lean_ctor_get(v___y_1990_, 13);
v_hasTrace_2070_ = lean_ctor_get_uint8(v_options_2068_, sizeof(void*)*1);
v___x_2071_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2070_ == 0)
{
v___y_2073_ = v___y_1988_;
v___y_2074_ = v___y_1989_;
v___y_2075_ = v___y_1990_;
v___y_2076_ = v___y_1991_;
goto v___jp_2072_;
}
else
{
lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2128_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2129_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2069_, v_options_2068_, v___x_2128_);
if (v___x_2129_ == 0)
{
v___y_2073_ = v___y_1988_;
v___y_2074_ = v___y_1989_;
v___y_2075_ = v___y_1990_;
v___y_2076_ = v___y_1991_;
goto v___jp_2072_;
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2130_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2131_ = l_Lean_Expr_mvarId_x21(v_a_2000_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2130_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2071_, v___x_2133_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_dec_ref(v___x_2134_);
v___y_2073_ = v___y_1988_;
v___y_2074_ = v___y_1989_;
v___y_2075_ = v___y_1990_;
v___y_2076_ = v___y_1991_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_2002_);
lean_dec(v_a_2000_);
lean_del_object(v___x_1996_);
lean_dec(v_heqPos_1986_);
lean_dec(v___x_1984_);
lean_dec(v_matchDeclName_1983_);
lean_dec_ref(v___f_1982_);
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
v___jp_2004_:
{
if (v___y_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_dec_ref(v___y_2005_);
lean_del_object(v___x_2002_);
v___x_2012_ = l_Lean_MVarId_deltaTarget(v___y_2010_, v___f_1982_, v___y_2009_, v___y_2008_, v___y_2007_, v___y_2006_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref(v___x_2012_);
v___x_2014_ = l_Lean_MVarId_heqOfEq(v_a_2013_, v___y_2009_, v___y_2008_, v___y_2007_, v___y_2006_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1983_, v_a_2015_, v___x_1984_, v___y_2009_, v___y_2008_, v___y_2007_, v___y_2006_);
lean_dec(v___x_1984_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; 
lean_dec_ref(v___x_2016_);
v___x_2017_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2000_, v___y_2008_);
return v___x_2017_;
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_a_2000_);
v_a_2018_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2016_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2016_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_a_2000_);
lean_dec(v___x_1984_);
lean_dec(v_matchDeclName_1983_);
v_a_2026_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2014_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2014_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v_a_2000_);
lean_dec(v___x_1984_);
lean_dec(v_matchDeclName_1983_);
v_a_2034_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2012_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2012_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_object* v___x_2043_; 
lean_dec(v___y_2010_);
lean_dec(v_a_2000_);
lean_dec(v___x_1984_);
lean_dec(v_matchDeclName_1983_);
lean_dec_ref(v___f_1982_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 1);
lean_ctor_set(v___x_2002_, 0, v___y_2005_);
v___x_2043_ = v___x_2002_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___y_2005_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
v___jp_2045_:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_MVarId_intros(v_mvarId_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v_snd_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
v_snd_2053_ = lean_ctor_get(v_a_2052_, 1);
lean_inc_n(v_snd_2053_, 2);
lean_dec(v_a_2052_);
v___x_2054_ = 1;
v___x_2055_ = l_Lean_MVarId_refl(v_snd_2053_, v___x_2054_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2056_; 
lean_dec_ref(v___x_2055_);
lean_dec(v_snd_2053_);
lean_del_object(v___x_2002_);
lean_dec(v___x_1984_);
lean_dec(v_matchDeclName_1983_);
lean_dec_ref(v___f_1982_);
v___x_2056_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2000_, v___y_2048_);
return v___x_2056_;
}
else
{
lean_object* v_a_2057_; uint8_t v___x_2058_; 
v_a_2057_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2057_);
lean_dec_ref(v___x_2055_);
v___x_2058_ = l_Lean_Exception_isInterrupt(v_a_2057_);
if (v___x_2058_ == 0)
{
uint8_t v___x_2059_; 
lean_inc(v_a_2057_);
v___x_2059_ = l_Lean_Exception_isRuntime(v_a_2057_);
v___y_2005_ = v_a_2057_;
v___y_2006_ = v___y_2050_;
v___y_2007_ = v___y_2049_;
v___y_2008_ = v___y_2048_;
v___y_2009_ = v___y_2047_;
v___y_2010_ = v_snd_2053_;
v___y_2011_ = v___x_2059_;
goto v___jp_2004_;
}
else
{
v___y_2005_ = v_a_2057_;
v___y_2006_ = v___y_2050_;
v___y_2007_ = v___y_2049_;
v___y_2008_ = v___y_2048_;
v___y_2009_ = v___y_2047_;
v___y_2010_ = v_snd_2053_;
v___y_2011_ = v___x_2058_;
goto v___jp_2004_;
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_del_object(v___x_2002_);
lean_dec(v_a_2000_);
lean_dec(v___x_1984_);
lean_dec(v_matchDeclName_1983_);
lean_dec_ref(v___f_1982_);
v_a_2060_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2051_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2051_);
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
v___jp_2072_:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Expr_mvarId_x21(v_a_2000_);
if (v___x_1985_ == 0)
{
lean_del_object(v___x_1996_);
lean_dec(v_heqPos_1986_);
v_mvarId_2046_ = v___x_2077_;
v___y_2047_ = v___y_2073_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
goto v___jp_2045_;
}
else
{
lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_box(0);
v___x_2079_ = 0;
v___x_2080_ = l_Lean_Meta_introNCore(v___x_2077_, v_heqPos_1986_, v___x_2078_, v___x_2079_, v___x_2079_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v_snd_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2118_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref(v___x_2080_);
v_snd_2082_ = lean_ctor_get(v_a_2081_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_a_2081_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v_a_2081_, 0);
lean_dec(v_unused_2119_);
v___x_2084_ = v_a_2081_;
v_isShared_2085_ = v_isSharedCheck_2118_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_snd_2082_);
lean_dec(v_a_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2118_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; 
lean_inc(v___x_1984_);
v___x_2086_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1987_, v___x_1984_, v_snd_2082_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_options_2087_; uint8_t v_hasTrace_2088_; 
v_options_2087_ = lean_ctor_get(v___y_2075_, 2);
v_hasTrace_2088_ = lean_ctor_get_uint8(v_options_2087_, sizeof(void*)*1);
if (v_hasTrace_2088_ == 0)
{
lean_object* v_a_2089_; 
lean_del_object(v___x_2084_);
lean_del_object(v___x_1996_);
v_a_2089_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2089_);
lean_dec_ref(v___x_2086_);
v_mvarId_2046_ = v_a_2089_;
v___y_2047_ = v___y_2073_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2090_; lean_object* v_inheritedTraceOptions_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_a_2090_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v___x_2086_);
v_inheritedTraceOptions_2091_ = lean_ctor_get(v___y_2075_, 13);
v___x_2092_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2093_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2091_, v_options_2087_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_del_object(v___x_2084_);
lean_del_object(v___x_1996_);
v_mvarId_2046_ = v_a_2090_;
v___y_2047_ = v___y_2073_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
goto v___jp_2045_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2090_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 1);
lean_ctor_set(v___x_1996_, 0, v_a_2090_);
v___x_2096_ = v___x_1996_;
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
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 7);
lean_ctor_set(v___x_2084_, 1, v___x_2096_);
lean_ctor_set(v___x_2084_, 0, v___x_2094_);
v___x_2098_ = v___x_2084_;
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
v___x_2099_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2071_, v___x_2098_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_dec_ref(v___x_2099_);
v_mvarId_2046_ = v_a_2090_;
v___y_2047_ = v___y_2073_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
goto v___jp_2045_;
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_a_2090_);
lean_del_object(v___x_2002_);
lean_dec(v_a_2000_);
lean_dec(v___x_1984_);
lean_dec(v_matchDeclName_1983_);
lean_dec_ref(v___f_1982_);
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
lean_del_object(v___x_2084_);
lean_del_object(v___x_2002_);
lean_dec(v_a_2000_);
lean_del_object(v___x_1996_);
lean_dec(v___x_1984_);
lean_dec(v_matchDeclName_1983_);
lean_dec_ref(v___f_1982_);
v_a_2110_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2086_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2086_);
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
lean_del_object(v___x_2002_);
lean_dec(v_a_2000_);
lean_del_object(v___x_1996_);
lean_dec(v___x_1984_);
lean_dec(v_matchDeclName_1983_);
lean_dec_ref(v___f_1982_);
v_a_2120_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2080_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2080_);
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
lean_del_object(v___x_1996_);
lean_dec(v_heqPos_1986_);
lean_dec(v___x_1984_);
lean_dec(v_matchDeclName_1983_);
lean_dec_ref(v___f_1982_);
return v___x_1999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2145_, lean_object* v___f_2146_, lean_object* v_matchDeclName_2147_, lean_object* v___x_2148_, lean_object* v___x_2149_, lean_object* v_heqPos_2150_, lean_object* v_heqNum_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v___x_6046__boxed_2157_; lean_object* v_res_2158_; 
v___x_6046__boxed_2157_ = lean_unbox(v___x_2149_);
v_res_2158_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2145_, v___f_2146_, v_matchDeclName_2147_, v___x_2148_, v___x_6046__boxed_2157_, v_heqPos_2150_, v_heqNum_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v_heqNum_2151_);
return v_res_2158_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = lean_unsigned_to_nat(32u);
v___x_2163_ = lean_mk_empty_array_with_capacity(v___x_2162_);
v___x_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
return v___x_2164_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2165_ = ((size_t)5ULL);
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = lean_unsigned_to_nat(32u);
v___x_2168_ = lean_mk_empty_array_with_capacity(v___x_2167_);
v___x_2169_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2170_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2168_);
lean_ctor_set(v___x_2170_, 2, v___x_2166_);
lean_ctor_set(v___x_2170_, 3, v___x_2166_);
lean_ctor_set_usize(v___x_2170_, 4, v___x_2165_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2171_ = lean_box(1);
v___x_2172_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2173_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v___x_2172_);
lean_ctor_set(v___x_2174_, 2, v___x_2171_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2177_, lean_object* v_type_2178_, lean_object* v_heqPos_2179_, lean_object* v_heqNum_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v___f_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; lean_object* v___f_2192_; lean_object* v___x_2193_; 
lean_inc(v_matchDeclName_2177_);
v___f_2186_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2186_, 0, v_matchDeclName_2177_);
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2189_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2190_ = lean_nat_dec_lt(v___x_2187_, v_heqNum_2180_);
v___x_2191_ = lean_box(v___x_2190_);
v___f_2192_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2192_, 0, v_type_2178_);
lean_closure_set(v___f_2192_, 1, v___f_2186_);
lean_closure_set(v___f_2192_, 2, v_matchDeclName_2177_);
lean_closure_set(v___f_2192_, 3, v___x_2187_);
lean_closure_set(v___f_2192_, 4, v___x_2191_);
lean_closure_set(v___f_2192_, 5, v_heqPos_2179_);
lean_closure_set(v___f_2192_, 6, v_heqNum_2180_);
v___x_2193_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2188_, v___x_2189_, v___f_2192_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2194_, lean_object* v_type_2195_, lean_object* v_heqPos_2196_, lean_object* v_heqNum_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2194_, v_type_2195_, v_heqPos_2196_, v_heqNum_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2204_, lean_object* v_inst_2205_, lean_object* v_R_2206_, lean_object* v_a_2207_, lean_object* v_b_2208_, lean_object* v_c_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2204_, v_a_2207_, v_b_2208_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2216_, lean_object* v_inst_2217_, lean_object* v_R_2218_, lean_object* v_a_2219_, lean_object* v_b_2220_, lean_object* v_c_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2216_, v_inst_2217_, v_R_2218_, v_a_2219_, v_b_2220_, v_c_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v_upperBound_2216_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2228_, lean_object* v_b_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; 
lean_inc(v___y_2233_);
lean_inc_ref(v___y_2232_);
lean_inc(v___y_2231_);
lean_inc_ref(v___y_2230_);
v___x_2235_ = lean_apply_6(v_k_2228_, v_b_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, lean_box(0));
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2236_, lean_object* v_b_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2236_, v_b_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2244_, uint8_t v_bi_2245_, lean_object* v_type_2246_, lean_object* v_k_2247_, uint8_t v_kind_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___f_2254_; lean_object* v___x_2255_; 
v___f_2254_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2254_, 0, v_k_2247_);
v___x_2255_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2244_, v_bi_2245_, v_type_2246_, v___f_2254_, v_kind_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
v_a_2264_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2255_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2255_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2272_, lean_object* v_bi_2273_, lean_object* v_type_2274_, lean_object* v_k_2275_, lean_object* v_kind_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v_bi_boxed_2282_; uint8_t v_kind_boxed_2283_; lean_object* v_res_2284_; 
v_bi_boxed_2282_ = lean_unbox(v_bi_2273_);
v_kind_boxed_2283_ = lean_unbox(v_kind_2276_);
v_res_2284_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2272_, v_bi_boxed_2282_, v_type_2274_, v_k_2275_, v_kind_boxed_2283_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2285_, lean_object* v_name_2286_, uint8_t v_bi_2287_, lean_object* v_type_2288_, lean_object* v_k_2289_, uint8_t v_kind_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2286_, v_bi_2287_, v_type_2288_, v_k_2289_, v_kind_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2297_, lean_object* v_name_2298_, lean_object* v_bi_2299_, lean_object* v_type_2300_, lean_object* v_k_2301_, lean_object* v_kind_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
uint8_t v_bi_boxed_2308_; uint8_t v_kind_boxed_2309_; lean_object* v_res_2310_; 
v_bi_boxed_2308_ = lean_unbox(v_bi_2299_);
v_kind_boxed_2309_ = lean_unbox(v_kind_2302_);
v_res_2310_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2297_, v_name_2298_, v_bi_boxed_2308_, v_type_2300_, v_k_2301_, v_kind_boxed_2309_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2311_, lean_object* v_altsNew_2312_, lean_object* v_discrs_2313_, lean_object* v_patterns_2314_, lean_object* v_alts_2315_, lean_object* v_k_2316_, lean_object* v_altNew_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2311_, v_altsNew_2312_, v_discrs_2313_, v_patterns_2314_, v_alts_2315_, v_k_2316_, v_altNew_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v_i_2311_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2324_, lean_object* v_patterns_2325_, lean_object* v_alts_2326_, lean_object* v_k_2327_, lean_object* v_i_2328_, lean_object* v_altsNew_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v___x_2335_; uint8_t v___x_2336_; 
v___x_2335_ = lean_array_get_size(v_alts_2326_);
v___x_2336_ = lean_nat_dec_lt(v_i_2328_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; 
lean_dec(v_i_2328_);
lean_dec_ref(v_alts_2326_);
lean_dec_ref(v_patterns_2325_);
lean_dec_ref(v_discrs_2324_);
lean_inc(v_a_2333_);
lean_inc_ref(v_a_2332_);
lean_inc(v_a_2331_);
lean_inc_ref(v_a_2330_);
v___x_2337_ = lean_apply_6(v_k_2327_, v_altsNew_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, lean_box(0));
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_array_fget_borrowed(v_alts_2326_, v_i_2328_);
v___x_2339_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2338_, v_a_2330_, v_a_2332_, v_a_2333_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___f_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
lean_inc_ref(v_patterns_2325_);
lean_inc_ref(v_discrs_2324_);
v___f_2341_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2341_, 0, v_i_2328_);
lean_closure_set(v___f_2341_, 1, v_altsNew_2329_);
lean_closure_set(v___f_2341_, 2, v_discrs_2324_);
lean_closure_set(v___f_2341_, 3, v_patterns_2325_);
lean_closure_set(v___f_2341_, 4, v_alts_2326_);
lean_closure_set(v___f_2341_, 5, v_k_2327_);
v___x_2342_ = l_Lean_LocalDecl_type(v_a_2340_);
v___x_2343_ = l_Lean_Expr_replaceFVars(v___x_2342_, v_discrs_2324_, v_patterns_2325_);
lean_dec_ref(v_patterns_2325_);
lean_dec_ref(v_discrs_2324_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = l_Lean_LocalDecl_userName(v_a_2340_);
v___x_2345_ = l_Lean_LocalDecl_binderInfo(v_a_2340_);
lean_dec(v_a_2340_);
v___x_2346_ = 0;
v___x_2347_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2344_, v___x_2345_, v___x_2343_, v___f_2341_, v___x_2346_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
return v___x_2347_;
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec_ref(v_altsNew_2329_);
lean_dec(v_i_2328_);
lean_dec_ref(v_k_2327_);
lean_dec_ref(v_alts_2326_);
lean_dec_ref(v_patterns_2325_);
lean_dec_ref(v_discrs_2324_);
v_a_2348_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2339_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2339_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2356_, lean_object* v_altsNew_2357_, lean_object* v_discrs_2358_, lean_object* v_patterns_2359_, lean_object* v_alts_2360_, lean_object* v_k_2361_, lean_object* v_altNew_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = lean_nat_add(v_i_2356_, v___x_2368_);
v___x_2370_ = lean_array_push(v_altsNew_2357_, v_altNew_2362_);
v___x_2371_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2358_, v_patterns_2359_, v_alts_2360_, v_k_2361_, v___x_2369_, v___x_2370_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2372_, lean_object* v_patterns_2373_, lean_object* v_alts_2374_, lean_object* v_k_2375_, lean_object* v_i_2376_, lean_object* v_altsNew_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2372_, v_patterns_2373_, v_alts_2374_, v_k_2375_, v_i_2376_, v_altsNew_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2384_, lean_object* v_discrs_2385_, lean_object* v_patterns_2386_, lean_object* v_alts_2387_, lean_object* v_k_2388_, lean_object* v_i_2389_, lean_object* v_altsNew_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2385_, v_patterns_2386_, v_alts_2387_, v_k_2388_, v_i_2389_, v_altsNew_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2397_, lean_object* v_discrs_2398_, lean_object* v_patterns_2399_, lean_object* v_alts_2400_, lean_object* v_k_2401_, lean_object* v_i_2402_, lean_object* v_altsNew_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2397_, v_discrs_2398_, v_patterns_2399_, v_alts_2400_, v_k_2401_, v_i_2402_, v_altsNew_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2412_, lean_object* v_discrs_2413_, lean_object* v_patterns_2414_, lean_object* v_alts_2415_, lean_object* v_k_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2423_ = lean_nat_dec_eq(v_numDiscrEqs_2412_, v___x_2422_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2425_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2413_, v_patterns_2414_, v_alts_2415_, v_k_2416_, v___x_2422_, v___x_2424_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; 
lean_dec_ref(v_patterns_2414_);
lean_dec_ref(v_discrs_2413_);
lean_inc(v_a_2420_);
lean_inc_ref(v_a_2419_);
lean_inc(v_a_2418_);
lean_inc_ref(v_a_2417_);
v___x_2426_ = lean_apply_6(v_k_2416_, v_alts_2415_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, lean_box(0));
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2427_, lean_object* v_discrs_2428_, lean_object* v_patterns_2429_, lean_object* v_alts_2430_, lean_object* v_k_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2427_, v_discrs_2428_, v_patterns_2429_, v_alts_2430_, v_k_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_numDiscrEqs_2427_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2438_, lean_object* v_numDiscrEqs_2439_, lean_object* v_discrs_2440_, lean_object* v_patterns_2441_, lean_object* v_alts_2442_, lean_object* v_k_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2439_, v_discrs_2440_, v_patterns_2441_, v_alts_2442_, v_k_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2450_, lean_object* v_numDiscrEqs_2451_, lean_object* v_discrs_2452_, lean_object* v_patterns_2453_, lean_object* v_alts_2454_, lean_object* v_k_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2450_, v_numDiscrEqs_2451_, v_discrs_2452_, v_patterns_2453_, v_alts_2454_, v_k_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_numDiscrEqs_2451_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(lean_object* v_declName_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___x_2465_; lean_object* v_env_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2465_ = lean_st_ref_get(v___y_2463_);
v_env_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc_ref(v_env_2466_);
lean_dec(v___x_2465_);
v___x_2467_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2466_, v_declName_2462_);
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg___boxed(lean_object* v_declName_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2469_, v___y_2470_);
lean_dec(v___y_2470_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_declName_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2473_, v___y_2477_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___boxed(lean_object* v_declName_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v_declName_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___f_2494_; lean_object* v___x_14707__overap_2495_; lean_object* v___x_2496_; 
v___f_2494_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14707__overap_2495_ = lean_panic_fn_borrowed(v___f_2494_, v_msg_2488_);
lean_inc(v___y_2492_);
lean_inc_ref(v___y_2491_);
lean_inc(v___y_2490_);
lean_inc_ref(v___y_2489_);
v___x_2496_ = lean_apply_5(v___x_14707__overap_2495_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, lean_box(0));
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2504_, lean_object* v_b_2505_, lean_object* v_c_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2512_; 
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
v___x_2512_ = lean_apply_7(v_k_2504_, v_b_2505_, v_c_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, lean_box(0));
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2513_, lean_object* v_b_2514_, lean_object* v_c_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2513_, v_b_2514_, v_c_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2522_, lean_object* v_k_2523_, uint8_t v_cleanupAnnotations_2524_, uint8_t v_whnfType_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___f_2531_; lean_object* v___x_2532_; 
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2531_, 0, v_k_2523_);
v___x_2532_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2522_, v___f_2531_, v_cleanupAnnotations_2524_, v_whnfType_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
v_a_2541_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2532_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2532_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2549_, lean_object* v_k_2550_, lean_object* v_cleanupAnnotations_2551_, lean_object* v_whnfType_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2558_; uint8_t v_whnfType_boxed_2559_; lean_object* v_res_2560_; 
v_cleanupAnnotations_boxed_2558_ = lean_unbox(v_cleanupAnnotations_2551_);
v_whnfType_boxed_2559_ = lean_unbox(v_whnfType_2552_);
v_res_2560_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2549_, v_k_2550_, v_cleanupAnnotations_boxed_2558_, v_whnfType_boxed_2559_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2561_, lean_object* v_type_2562_, lean_object* v_k_2563_, uint8_t v_cleanupAnnotations_2564_, uint8_t v_whnfType_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2562_, v_k_2563_, v_cleanupAnnotations_2564_, v_whnfType_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2572_, lean_object* v_type_2573_, lean_object* v_k_2574_, lean_object* v_cleanupAnnotations_2575_, lean_object* v_whnfType_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2582_; uint8_t v_whnfType_boxed_2583_; lean_object* v_res_2584_; 
v_cleanupAnnotations_boxed_2582_ = lean_unbox(v_cleanupAnnotations_2575_);
v_whnfType_boxed_2583_ = lean_unbox(v_whnfType_2576_);
v_res_2584_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2572_, v_type_2573_, v_k_2574_, v_cleanupAnnotations_boxed_2582_, v_whnfType_boxed_2583_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2585_, lean_object* v_splitterName_2586_, lean_object* v_matcherInput_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_matchType_2593_; lean_object* v_discrInfos_2594_; lean_object* v_lhss_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2615_; 
v_matchType_2593_ = lean_ctor_get(v_matcherInput_2587_, 1);
v_discrInfos_2594_ = lean_ctor_get(v_matcherInput_2587_, 2);
v_lhss_2595_ = lean_ctor_get(v_matcherInput_2587_, 3);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_matcherInput_2587_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; lean_object* v_unused_2617_; 
v_unused_2616_ = lean_ctor_get(v_matcherInput_2587_, 4);
lean_dec(v_unused_2616_);
v_unused_2617_ = lean_ctor_get(v_matcherInput_2587_, 0);
lean_dec(v_unused_2617_);
v___x_2597_ = v_matcherInput_2587_;
v_isShared_2598_ = v_isSharedCheck_2615_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_lhss_2595_);
lean_inc(v_discrInfos_2594_);
lean_inc(v_matchType_2593_);
lean_dec(v_matcherInput_2587_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2615_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_overlaps_2585_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 4, v___x_2599_);
lean_ctor_set(v___x_2597_, 0, v_splitterName_2586_);
v___x_2601_ = v___x_2597_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_splitterName_2586_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_matchType_2593_);
lean_ctor_set(v_reuseFailAlloc_2614_, 2, v_discrInfos_2594_);
lean_ctor_set(v_reuseFailAlloc_2614_, 3, v_lhss_2595_);
lean_ctor_set(v_reuseFailAlloc_2614_, 4, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_Meta_Match_mkMatcher(v___x_2601_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v_addMatcher_2604_; lean_object* v___x_2605_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref(v___x_2602_);
v_addMatcher_2604_ = lean_ctor_get(v_a_2603_, 3);
lean_inc_ref(v_addMatcher_2604_);
lean_dec(v_a_2603_);
lean_inc(v___y_2591_);
lean_inc_ref(v___y_2590_);
lean_inc(v___y_2589_);
lean_inc_ref(v___y_2588_);
v___x_2605_ = lean_apply_5(v_addMatcher_2604_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, lean_box(0));
return v___x_2605_;
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
v_a_2606_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2602_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2602_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2618_, lean_object* v_splitterName_2619_, lean_object* v_matcherInput_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2618_, v_splitterName_2619_, v_matcherInput_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
return v_res_2626_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2627_, lean_object* v_ys_2628_, lean_object* v_x_2629_){
_start:
{
lean_object* v_zero_2630_; uint8_t v_isZero_2631_; 
v_zero_2630_ = lean_unsigned_to_nat(0u);
v_isZero_2631_ = lean_nat_dec_eq(v_x_2629_, v_zero_2630_);
if (v_isZero_2631_ == 1)
{
lean_dec(v_x_2629_);
return v_isZero_2631_;
}
else
{
lean_object* v_one_2632_; lean_object* v_n_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v_one_2632_ = lean_unsigned_to_nat(1u);
v_n_2633_ = lean_nat_sub(v_x_2629_, v_one_2632_);
lean_dec(v_x_2629_);
v___x_2634_ = lean_array_fget_borrowed(v_xs_2627_, v_n_2633_);
v___x_2635_ = lean_array_fget_borrowed(v_ys_2628_, v_n_2633_);
v___x_2636_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2634_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_dec(v_n_2633_);
return v___x_2636_;
}
else
{
v_x_2629_ = v_n_2633_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2638_, lean_object* v_ys_2639_, lean_object* v_x_2640_){
_start:
{
uint8_t v_res_2641_; lean_object* v_r_2642_; 
v_res_2641_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2638_, v_ys_2639_, v_x_2640_);
lean_dec_ref(v_ys_2639_);
lean_dec_ref(v_xs_2638_);
v_r_2642_ = lean_box(v_res_2641_);
return v_r_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2643_, lean_object* v_b_2644_){
_start:
{
lean_object* v_array_2645_; lean_object* v_start_2646_; lean_object* v_stop_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2660_; 
v_array_2645_ = lean_ctor_get(v_a_2643_, 0);
v_start_2646_ = lean_ctor_get(v_a_2643_, 1);
v_stop_2647_ = lean_ctor_get(v_a_2643_, 2);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_a_2643_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2649_ = v_a_2643_;
v_isShared_2650_ = v_isSharedCheck_2660_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_stop_2647_);
lean_inc(v_start_2646_);
lean_inc(v_array_2645_);
lean_dec(v_a_2643_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2660_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
uint8_t v___x_2651_; 
v___x_2651_ = lean_nat_dec_lt(v_start_2646_, v_stop_2647_);
if (v___x_2651_ == 0)
{
lean_del_object(v___x_2649_);
lean_dec(v_stop_2647_);
lean_dec(v_start_2646_);
lean_dec_ref(v_array_2645_);
return v_b_2644_;
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2652_ = lean_unsigned_to_nat(1u);
v___x_2653_ = lean_nat_add(v_start_2646_, v___x_2652_);
lean_inc_ref(v_array_2645_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 1, v___x_2653_);
v___x_2655_ = v___x_2649_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_array_2645_);
lean_ctor_set(v_reuseFailAlloc_2659_, 1, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2659_, 2, v_stop_2647_);
v___x_2655_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = lean_array_fget(v_array_2645_, v_start_2646_);
lean_dec(v_start_2646_);
lean_dec_ref(v_array_2645_);
v___x_2657_ = lean_array_push(v_b_2644_, v___x_2656_);
v_a_2643_ = v___x_2655_;
v_b_2644_ = v___x_2657_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2661_, size_t v_sz_2662_, size_t v_i_2663_, lean_object* v_b_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v___x_2670_; 
v___x_2670_ = lean_usize_dec_lt(v_i_2663_, v_sz_2662_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v_b_2664_);
return v___x_2671_;
}
else
{
lean_object* v_snd_2672_; lean_object* v_fst_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2725_; 
v_snd_2672_ = lean_ctor_get(v_b_2664_, 1);
v_fst_2673_ = lean_ctor_get(v_b_2664_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_b_2664_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2675_ = v_b_2664_;
v_isShared_2676_ = v_isSharedCheck_2725_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_snd_2672_);
lean_inc(v_fst_2673_);
lean_dec(v_b_2664_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2725_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_array_2677_; lean_object* v_start_2678_; lean_object* v_stop_2679_; uint8_t v___x_2680_; 
v_array_2677_ = lean_ctor_get(v_snd_2672_, 0);
v_start_2678_ = lean_ctor_get(v_snd_2672_, 1);
v_stop_2679_ = lean_ctor_get(v_snd_2672_, 2);
v___x_2680_ = lean_nat_dec_lt(v_start_2678_, v_stop_2679_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2682_; 
if (v_isShared_2676_ == 0)
{
v___x_2682_ = v___x_2675_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_fst_2673_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_snd_2672_);
v___x_2682_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
return v___x_2683_;
}
}
else
{
lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2721_; 
lean_inc(v_stop_2679_);
lean_inc(v_start_2678_);
lean_inc_ref(v_array_2677_);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_snd_2672_);
if (v_isSharedCheck_2721_ == 0)
{
lean_object* v_unused_2722_; lean_object* v_unused_2723_; lean_object* v_unused_2724_; 
v_unused_2722_ = lean_ctor_get(v_snd_2672_, 2);
lean_dec(v_unused_2722_);
v_unused_2723_ = lean_ctor_get(v_snd_2672_, 1);
lean_dec(v_unused_2723_);
v_unused_2724_ = lean_ctor_get(v_snd_2672_, 0);
lean_dec(v_unused_2724_);
v___x_2686_ = v_snd_2672_;
v_isShared_2687_ = v_isSharedCheck_2721_;
goto v_resetjp_2685_;
}
else
{
lean_dec(v_snd_2672_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2721_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_a_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_a_2688_ = lean_array_uget_borrowed(v_as_2661_, v_i_2663_);
v___x_2689_ = lean_array_fget_borrowed(v_array_2677_, v_start_2678_);
lean_inc(v___x_2689_);
lean_inc(v_a_2688_);
v___x_2690_ = l_Lean_Meta_mkEqHEq(v_a_2688_, v___x_2689_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref(v___x_2690_);
v___x_2692_ = l_Lean_mkArrow(v_a_2691_, v_fst_2673_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref(v___x_2692_);
v___x_2694_ = lean_unsigned_to_nat(1u);
v___x_2695_ = lean_nat_add(v_start_2678_, v___x_2694_);
lean_dec(v_start_2678_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 1, v___x_2695_);
v___x_2697_ = v___x_2686_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_array_2677_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_stop_2679_);
v___x_2697_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2699_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 1, v___x_2697_);
lean_ctor_set(v___x_2675_, 0, v_a_2693_);
v___x_2699_ = v___x_2675_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2693_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
size_t v___x_2700_; size_t v___x_2701_; 
v___x_2700_ = ((size_t)1ULL);
v___x_2701_ = lean_usize_add(v_i_2663_, v___x_2700_);
v_i_2663_ = v___x_2701_;
v_b_2664_ = v___x_2699_;
goto _start;
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_del_object(v___x_2686_);
lean_dec(v_stop_2679_);
lean_dec(v_start_2678_);
lean_dec_ref(v_array_2677_);
lean_del_object(v___x_2675_);
v_a_2705_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2692_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2692_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_del_object(v___x_2686_);
lean_dec(v_stop_2679_);
lean_dec(v_start_2678_);
lean_dec_ref(v_array_2677_);
lean_del_object(v___x_2675_);
lean_dec(v_fst_2673_);
v_a_2713_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2690_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2690_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2726_, lean_object* v_sz_2727_, lean_object* v_i_2728_, lean_object* v_b_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
size_t v_sz_boxed_2735_; size_t v_i_boxed_2736_; lean_object* v_res_2737_; 
v_sz_boxed_2735_ = lean_unbox_usize(v_sz_2727_);
lean_dec(v_sz_2727_);
v_i_boxed_2736_ = lean_unbox_usize(v_i_2728_);
lean_dec(v_i_2728_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2726_, v_sz_boxed_2735_, v_i_boxed_2736_, v_b_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec_ref(v_as_2726_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2738_, lean_object* v___x_2739_, lean_object* v_as_2740_, size_t v_sz_2741_, size_t v_i_2742_, lean_object* v_b_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
uint8_t v___x_2749_; 
v___x_2749_ = lean_usize_dec_lt(v_i_2742_, v_sz_2741_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v_b_2743_);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; lean_object* v_a_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2751_ = l_Lean_instInhabitedExpr;
v_a_2752_ = lean_array_uget_borrowed(v_as_2740_, v_i_2742_);
v___x_2753_ = lean_array_get_borrowed(v___x_2751_, v___x_2738_, v_a_2752_);
lean_inc(v___x_2753_);
v___x_2754_ = l_Lean_Meta_instantiateForall(v___x_2753_, v___x_2739_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref(v___x_2754_);
v___x_2756_ = lean_array_get_size(v___x_2739_);
v___x_2757_ = l_Lean_Meta_Match_simpH_x3f(v_a_2755_, v___x_2756_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v_a_2760_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref(v___x_2757_);
if (lean_obj_tag(v_a_2758_) == 1)
{
lean_object* v_val_2764_; lean_object* v___x_2765_; 
v_val_2764_ = lean_ctor_get(v_a_2758_, 0);
lean_inc(v_val_2764_);
lean_dec_ref(v_a_2758_);
v___x_2765_ = lean_array_push(v_b_2743_, v_val_2764_);
v_a_2760_ = v___x_2765_;
goto v___jp_2759_;
}
else
{
lean_dec(v_a_2758_);
v_a_2760_ = v_b_2743_;
goto v___jp_2759_;
}
v___jp_2759_:
{
size_t v___x_2761_; size_t v___x_2762_; 
v___x_2761_ = ((size_t)1ULL);
v___x_2762_ = lean_usize_add(v_i_2742_, v___x_2761_);
v_i_2742_ = v___x_2762_;
v_b_2743_ = v_a_2760_;
goto _start;
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec_ref(v_b_2743_);
v_a_2766_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2757_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2757_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec_ref(v_b_2743_);
v_a_2774_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2754_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2754_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2782_, lean_object* v___x_2783_, lean_object* v_as_2784_, lean_object* v_sz_2785_, lean_object* v_i_2786_, lean_object* v_b_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
size_t v_sz_boxed_2793_; size_t v_i_boxed_2794_; lean_object* v_res_2795_; 
v_sz_boxed_2793_ = lean_unbox_usize(v_sz_2785_);
lean_dec(v_sz_2785_);
v_i_boxed_2794_ = lean_unbox_usize(v_i_2786_);
lean_dec(v_i_2786_);
v_res_2795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2782_, v___x_2783_, v_as_2784_, v_sz_boxed_2793_, v_i_boxed_2794_, v_b_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec_ref(v_as_2784_);
lean_dec_ref(v___x_2783_);
lean_dec_ref(v___x_2782_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v___x_2799_, lean_object* v___x_2800_, lean_object* v___x_2801_, lean_object* v___x_2802_, lean_object* v___x_2803_, lean_object* v_rhsArgs_2804_, lean_object* v_a_2805_, lean_object* v_ys_2806_, uint8_t v___x_2807_, uint8_t v___x_2808_, uint8_t v___x_2809_, lean_object* v_matchDeclName_2810_, lean_object* v___x_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v_argMask_2816_, lean_object* v_a_2817_, lean_object* v_alts_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2824_ = lean_array_get_borrowed(v___x_2796_, v_alts_2818_, v_a_2797_);
v___x_2825_ = l_Lean_ConstantInfo_name(v_a_2798_);
v___x_2826_ = l_Lean_mkConst(v___x_2825_, v___x_2799_);
v___x_2827_ = l_Subarray_copy___redArg(v___x_2800_);
v___x_2828_ = lean_mk_empty_array_with_capacity(v___x_2801_);
v___x_2829_ = lean_array_push(v___x_2828_, v___x_2802_);
v___x_2830_ = l_Array_append___redArg(v___x_2827_, v___x_2829_);
lean_dec_ref(v___x_2829_);
lean_inc_ref(v___x_2830_);
v___x_2831_ = l_Array_append___redArg(v___x_2830_, v___x_2803_);
v___x_2832_ = l_Array_append___redArg(v___x_2831_, v_alts_2818_);
v___x_2833_ = l_Lean_mkAppN(v___x_2826_, v___x_2832_);
lean_dec_ref(v___x_2832_);
lean_inc(v___x_2824_);
v___x_2834_ = l_Lean_mkAppN(v___x_2824_, v_rhsArgs_2804_);
v___x_2835_ = l_Lean_Meta_mkEq(v___x_2833_, v___x_2834_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2837_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = l_Lean_mkArrowN(v_a_2805_, v_a_2836_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref(v___x_2837_);
v___x_2839_ = l_Array_append___redArg(v___x_2830_, v_ys_2806_);
v___x_2840_ = l_Array_append___redArg(v___x_2839_, v_alts_2818_);
v___x_2841_ = l_Lean_Meta_mkForallFVars(v___x_2840_, v_a_2838_, v___x_2807_, v___x_2808_, v___x_2808_, v___x_2809_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec_ref(v___x_2840_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2843_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2842_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc_n(v_a_2844_, 2);
lean_dec_ref(v___x_2843_);
lean_inc(v___x_2811_);
v___x_2845_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2810_, v_a_2844_, v___x_2811_, v___x_2811_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref(v___x_2845_);
lean_inc(v___x_2812_);
v___x_2847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2812_);
lean_ctor_set(v___x_2847_, 1, v___x_2813_);
lean_ctor_set(v___x_2847_, 2, v_a_2844_);
v___x_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2812_);
lean_ctor_set(v___x_2848_, 1, v___x_2814_);
v___x_2849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v_a_2846_);
lean_ctor_set(v___x_2849_, 2, v___x_2848_);
v___x_2850_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
v___x_2851_ = l_Lean_addDecl(v___x_2850_, v___x_2807_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2860_; 
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2860_ == 0)
{
lean_object* v_unused_2861_; 
v_unused_2861_ = lean_ctor_get(v___x_2851_, 0);
lean_dec(v_unused_2861_);
v___x_2853_ = v___x_2851_;
v_isShared_2854_ = v_isSharedCheck_2860_;
goto v_resetjp_2852_;
}
else
{
lean_dec(v___x_2851_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2860_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2858_; 
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2815_);
lean_ctor_set(v___x_2855_, 1, v_argMask_2816_);
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_a_2817_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2856_);
v___x_2858_ = v___x_2853_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref(v_a_2817_);
lean_dec_ref(v_argMask_2816_);
lean_dec_ref(v___x_2815_);
v_a_2862_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2851_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2851_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2817_);
lean_dec_ref(v_argMask_2816_);
lean_dec_ref(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v___x_2812_);
v_a_2870_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2845_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2845_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec_ref(v_a_2817_);
lean_dec_ref(v_argMask_2816_);
lean_dec_ref(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v___x_2812_);
lean_dec(v___x_2811_);
lean_dec(v_matchDeclName_2810_);
v_a_2878_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2843_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2843_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec_ref(v_a_2817_);
lean_dec_ref(v_argMask_2816_);
lean_dec_ref(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v___x_2812_);
lean_dec(v___x_2811_);
lean_dec(v_matchDeclName_2810_);
v_a_2886_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2841_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2841_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec_ref(v___x_2830_);
lean_dec_ref(v_a_2817_);
lean_dec_ref(v_argMask_2816_);
lean_dec_ref(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v___x_2812_);
lean_dec(v___x_2811_);
lean_dec(v_matchDeclName_2810_);
v_a_2894_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2837_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2837_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec_ref(v___x_2830_);
lean_dec_ref(v_a_2817_);
lean_dec_ref(v_argMask_2816_);
lean_dec_ref(v___x_2815_);
lean_dec(v___x_2814_);
lean_dec(v___x_2813_);
lean_dec(v___x_2812_);
lean_dec(v___x_2811_);
lean_dec(v_matchDeclName_2810_);
v_a_2902_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2835_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2835_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2910_ = _args[0];
lean_object* v_a_2911_ = _args[1];
lean_object* v_a_2912_ = _args[2];
lean_object* v___x_2913_ = _args[3];
lean_object* v___x_2914_ = _args[4];
lean_object* v___x_2915_ = _args[5];
lean_object* v___x_2916_ = _args[6];
lean_object* v___x_2917_ = _args[7];
lean_object* v_rhsArgs_2918_ = _args[8];
lean_object* v_a_2919_ = _args[9];
lean_object* v_ys_2920_ = _args[10];
lean_object* v___x_2921_ = _args[11];
lean_object* v___x_2922_ = _args[12];
lean_object* v___x_2923_ = _args[13];
lean_object* v_matchDeclName_2924_ = _args[14];
lean_object* v___x_2925_ = _args[15];
lean_object* v___x_2926_ = _args[16];
lean_object* v___x_2927_ = _args[17];
lean_object* v___x_2928_ = _args[18];
lean_object* v___x_2929_ = _args[19];
lean_object* v_argMask_2930_ = _args[20];
lean_object* v_a_2931_ = _args[21];
lean_object* v_alts_2932_ = _args[22];
lean_object* v___y_2933_ = _args[23];
lean_object* v___y_2934_ = _args[24];
lean_object* v___y_2935_ = _args[25];
lean_object* v___y_2936_ = _args[26];
lean_object* v___y_2937_ = _args[27];
_start:
{
uint8_t v___x_18941__boxed_2938_; uint8_t v___x_18942__boxed_2939_; uint8_t v___x_18943__boxed_2940_; lean_object* v_res_2941_; 
v___x_18941__boxed_2938_ = lean_unbox(v___x_2921_);
v___x_18942__boxed_2939_ = lean_unbox(v___x_2922_);
v___x_18943__boxed_2940_ = lean_unbox(v___x_2923_);
v_res_2941_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2910_, v_a_2911_, v_a_2912_, v___x_2913_, v___x_2914_, v___x_2915_, v___x_2916_, v___x_2917_, v_rhsArgs_2918_, v_a_2919_, v_ys_2920_, v___x_18941__boxed_2938_, v___x_18942__boxed_2939_, v___x_18943__boxed_2940_, v_matchDeclName_2924_, v___x_2925_, v___x_2926_, v___x_2927_, v___x_2928_, v___x_2929_, v_argMask_2930_, v_a_2931_, v_alts_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec_ref(v_alts_2932_);
lean_dec_ref(v_ys_2920_);
lean_dec_ref(v_a_2919_);
lean_dec_ref(v_rhsArgs_2918_);
lean_dec_ref(v___x_2917_);
lean_dec(v___x_2915_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v___x_2910_);
return v_res_2941_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2942_; lean_object* v_dummy_2943_; 
v___x_2942_ = lean_box(0);
v_dummy_2943_ = l_Lean_Expr_sort___override(v___x_2942_);
return v_dummy_2943_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = lean_box(0);
v___x_2948_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_2949_ = l_Lean_mkConst(v___x_2948_, v___x_2947_);
return v___x_2949_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_2952_ = l_Lean_stringToMessageData(v___x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_2953_, lean_object* v_overlaps_2954_, lean_object* v_a_2955_, lean_object* v_fst_2956_, lean_object* v___x_2957_, lean_object* v___x_2958_, lean_object* v___x_2959_, uint8_t v___x_2960_, lean_object* v___x_2961_, lean_object* v_a_2962_, lean_object* v___x_2963_, lean_object* v___x_2964_, lean_object* v___x_2965_, lean_object* v_matchDeclName_2966_, lean_object* v___x_2967_, lean_object* v___x_2968_, lean_object* v___x_2969_, lean_object* v___x_2970_, lean_object* v___x_2971_, lean_object* v_ys_2972_, lean_object* v___eqs_2973_, lean_object* v_rhsArgs_2974_, lean_object* v_argMask_2975_, lean_object* v_altResultType_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_dummy_2982_; lean_object* v_nargs_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; size_t v_sz_2988_; size_t v___x_2989_; lean_object* v___x_2990_; 
v_dummy_2982_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_2983_ = l_Lean_Expr_getAppNumArgs(v_altResultType_2976_);
lean_inc(v_nargs_2983_);
v___x_2984_ = lean_mk_array(v_nargs_2983_, v_dummy_2982_);
v___x_2985_ = lean_nat_sub(v_nargs_2983_, v___x_2953_);
lean_dec(v_nargs_2983_);
v___x_2986_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_2976_, v___x_2984_, v___x_2985_);
v___x_2987_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_2954_, v_a_2955_);
v_sz_2988_ = lean_array_size(v___x_2987_);
v___x_2989_ = ((size_t)0ULL);
lean_inc_ref(v___x_2957_);
v___x_2990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_2956_, v___x_2986_, v___x_2987_, v_sz_2988_, v___x_2989_, v___x_2957_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec_ref(v___x_2987_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; uint8_t v___y_2997_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; uint8_t v___y_3045_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v_options_3056_; uint8_t v_hasTrace_3057_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref(v___x_2990_);
v_options_3056_ = lean_ctor_get(v___y_2979_, 2);
v_hasTrace_3057_ = lean_ctor_get_uint8(v_options_3056_, sizeof(void*)*1);
if (v_hasTrace_3057_ == 0)
{
v___y_3048_ = v___y_2977_;
v___y_3049_ = v___y_2978_;
v___y_3050_ = v___y_2979_;
v___y_3051_ = v___y_2980_;
goto v___jp_3047_;
}
else
{
lean_object* v_inheritedTraceOptions_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v_inheritedTraceOptions_3058_ = lean_ctor_get(v___y_2979_, 13);
v___x_3059_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3060_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_3061_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3058_, v_options_3056_, v___x_3060_);
if (v___x_3061_ == 0)
{
v___y_3048_ = v___y_2977_;
v___y_3049_ = v___y_2978_;
v___y_3050_ = v___y_2979_;
v___y_3051_ = v___y_2980_;
goto v___jp_3047_;
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3062_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_2991_);
v___x_3063_ = lean_array_to_list(v_a_2991_);
v___x_3064_ = lean_box(0);
v___x_3065_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3063_, v___x_3064_);
v___x_3066_ = l_Lean_MessageData_ofList(v___x_3065_);
v___x_3067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3062_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3059_, v___x_3067_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_dec_ref(v___x_3068_);
v___y_3048_ = v___y_2977_;
v___y_3049_ = v___y_2978_;
v___y_3050_ = v___y_2979_;
v___y_3051_ = v___y_2980_;
goto v___jp_3047_;
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_a_2991_);
lean_dec_ref(v___x_2986_);
lean_dec_ref(v_argMask_2975_);
lean_dec_ref(v_rhsArgs_2974_);
lean_dec_ref(v_ys_2972_);
lean_dec_ref(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v___x_2968_);
lean_dec(v___x_2967_);
lean_dec(v_matchDeclName_2966_);
lean_dec_ref(v___x_2965_);
lean_dec_ref(v___x_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_a_2962_);
lean_dec_ref(v___x_2961_);
lean_dec_ref(v___x_2959_);
lean_dec(v___x_2958_);
lean_dec_ref(v___x_2957_);
lean_dec(v_a_2955_);
lean_dec(v___x_2953_);
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
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
v___jp_2992_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; size_t v_sz_3005_; lean_object* v___x_3006_; 
v___x_2998_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2986_);
v___x_2999_ = l_Array_reverse___redArg(v___x_2986_);
v___x_3000_ = lean_array_get_size(v___x_2999_);
lean_inc(v___x_2958_);
v___x_3001_ = l_Array_toSubarray___redArg(v___x_2999_, v___x_2958_, v___x_3000_);
lean_inc_ref(v___x_2959_);
v___x_3002_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2959_, v___x_2957_);
v___x_3003_ = l_Array_reverse___redArg(v___x_3002_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_2998_);
lean_ctor_set(v___x_3004_, 1, v___x_3001_);
v_sz_3005_ = lean_array_size(v___x_3003_);
v___x_3006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3003_, v_sz_3005_, v___x_2989_, v___x_3004_, v___y_2995_, v___y_2993_, v___y_2996_, v___y_2994_);
lean_dec_ref(v___x_3003_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v_fst_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_3006_);
v_fst_3008_ = lean_ctor_get(v_a_3007_, 0);
lean_inc(v_fst_3008_);
lean_dec(v_a_3007_);
v___x_3009_ = l_Subarray_copy___redArg(v___x_2959_);
lean_inc_ref(v___x_3009_);
v___x_3010_ = l_Array_append___redArg(v___x_3009_, v_ys_2972_);
v___x_3011_ = 0;
v___x_3012_ = 1;
v___x_3013_ = l_Lean_Meta_mkForallFVars(v___x_3010_, v_fst_3008_, v___x_3011_, v___x_2960_, v___x_2960_, v___x_3012_, v___y_2995_, v___y_2993_, v___y_2996_, v___y_2994_);
lean_dec_ref(v___x_3010_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___f_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_3013_);
v___x_3015_ = lean_array_get_size(v_ys_2972_);
v___x_3016_ = lean_array_get_size(v_a_2991_);
v___x_3017_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*2, v___y_2997_);
v___x_3018_ = lean_box(v___x_3011_);
v___x_3019_ = lean_box(v___x_2960_);
v___x_3020_ = lean_box(v___x_3012_);
lean_inc_ref(v___x_2986_);
v___f_3021_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_3021_, 0, v___x_2961_);
lean_closure_set(v___f_3021_, 1, v_a_2955_);
lean_closure_set(v___f_3021_, 2, v_a_2962_);
lean_closure_set(v___f_3021_, 3, v___x_2963_);
lean_closure_set(v___f_3021_, 4, v___x_2964_);
lean_closure_set(v___f_3021_, 5, v___x_2953_);
lean_closure_set(v___f_3021_, 6, v___x_2965_);
lean_closure_set(v___f_3021_, 7, v___x_2986_);
lean_closure_set(v___f_3021_, 8, v_rhsArgs_2974_);
lean_closure_set(v___f_3021_, 9, v_a_2991_);
lean_closure_set(v___f_3021_, 10, v_ys_2972_);
lean_closure_set(v___f_3021_, 11, v___x_3018_);
lean_closure_set(v___f_3021_, 12, v___x_3019_);
lean_closure_set(v___f_3021_, 13, v___x_3020_);
lean_closure_set(v___f_3021_, 14, v_matchDeclName_2966_);
lean_closure_set(v___f_3021_, 15, v___x_2958_);
lean_closure_set(v___f_3021_, 16, v___x_2967_);
lean_closure_set(v___f_3021_, 17, v___x_2968_);
lean_closure_set(v___f_3021_, 18, v___x_2969_);
lean_closure_set(v___f_3021_, 19, v___x_3017_);
lean_closure_set(v___f_3021_, 20, v_argMask_2975_);
lean_closure_set(v___f_3021_, 21, v_a_3014_);
v___x_3022_ = l_Subarray_copy___redArg(v___x_2970_);
v___x_3023_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2971_, v___x_3009_, v___x_2986_, v___x_3022_, v___f_3021_, v___y_2995_, v___y_2993_, v___y_2996_, v___y_2994_);
return v___x_3023_;
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec_ref(v___x_3009_);
lean_dec(v_a_2991_);
lean_dec_ref(v___x_2986_);
lean_dec_ref(v_argMask_2975_);
lean_dec_ref(v_rhsArgs_2974_);
lean_dec_ref(v_ys_2972_);
lean_dec_ref(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v___x_2968_);
lean_dec(v___x_2967_);
lean_dec(v_matchDeclName_2966_);
lean_dec_ref(v___x_2965_);
lean_dec_ref(v___x_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_a_2962_);
lean_dec_ref(v___x_2961_);
lean_dec(v___x_2958_);
lean_dec(v_a_2955_);
lean_dec(v___x_2953_);
v_a_3024_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3013_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3013_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec(v_a_2991_);
lean_dec_ref(v___x_2986_);
lean_dec_ref(v_argMask_2975_);
lean_dec_ref(v_rhsArgs_2974_);
lean_dec_ref(v_ys_2972_);
lean_dec_ref(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v___x_2968_);
lean_dec(v___x_2967_);
lean_dec(v_matchDeclName_2966_);
lean_dec_ref(v___x_2965_);
lean_dec_ref(v___x_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_a_2962_);
lean_dec_ref(v___x_2961_);
lean_dec_ref(v___x_2959_);
lean_dec(v___x_2958_);
lean_dec(v_a_2955_);
lean_dec(v___x_2953_);
v_a_3032_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3006_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3006_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
v___jp_3040_:
{
if (v___y_3045_ == 0)
{
v___y_2993_ = v___y_3041_;
v___y_2994_ = v___y_3042_;
v___y_2995_ = v___y_3043_;
v___y_2996_ = v___y_3044_;
v___y_2997_ = v___y_3045_;
goto v___jp_2992_;
}
else
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_nat_dec_eq(v___x_2971_, v___x_2958_);
v___y_2993_ = v___y_3041_;
v___y_2994_ = v___y_3042_;
v___y_2995_ = v___y_3043_;
v___y_2996_ = v___y_3044_;
v___y_2997_ = v___x_3046_;
goto v___jp_2992_;
}
}
v___jp_3047_:
{
lean_object* v___x_3052_; uint8_t v___x_3053_; 
v___x_3052_ = lean_array_get_size(v_ys_2972_);
v___x_3053_ = lean_nat_dec_eq(v___x_3052_, v___x_2958_);
if (v___x_3053_ == 0)
{
v___y_3041_ = v___y_3049_;
v___y_3042_ = v___y_3051_;
v___y_3043_ = v___y_3048_;
v___y_3044_ = v___y_3050_;
v___y_3045_ = v___x_3053_;
goto v___jp_3040_;
}
else
{
lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = lean_array_get_size(v_a_2991_);
v___x_3055_ = lean_nat_dec_eq(v___x_3054_, v___x_2958_);
v___y_3041_ = v___y_3049_;
v___y_3042_ = v___y_3051_;
v___y_3043_ = v___y_3048_;
v___y_3044_ = v___y_3050_;
v___y_3045_ = v___x_3055_;
goto v___jp_3040_;
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec_ref(v___x_2986_);
lean_dec_ref(v_argMask_2975_);
lean_dec_ref(v_rhsArgs_2974_);
lean_dec_ref(v_ys_2972_);
lean_dec_ref(v___x_2970_);
lean_dec(v___x_2969_);
lean_dec(v___x_2968_);
lean_dec(v___x_2967_);
lean_dec(v_matchDeclName_2966_);
lean_dec_ref(v___x_2965_);
lean_dec_ref(v___x_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_a_2962_);
lean_dec_ref(v___x_2961_);
lean_dec_ref(v___x_2959_);
lean_dec(v___x_2958_);
lean_dec_ref(v___x_2957_);
lean_dec(v_a_2955_);
lean_dec(v___x_2953_);
v_a_3077_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_2990_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_2990_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3085_ = _args[0];
lean_object* v_overlaps_3086_ = _args[1];
lean_object* v_a_3087_ = _args[2];
lean_object* v_fst_3088_ = _args[3];
lean_object* v___x_3089_ = _args[4];
lean_object* v___x_3090_ = _args[5];
lean_object* v___x_3091_ = _args[6];
lean_object* v___x_3092_ = _args[7];
lean_object* v___x_3093_ = _args[8];
lean_object* v_a_3094_ = _args[9];
lean_object* v___x_3095_ = _args[10];
lean_object* v___x_3096_ = _args[11];
lean_object* v___x_3097_ = _args[12];
lean_object* v_matchDeclName_3098_ = _args[13];
lean_object* v___x_3099_ = _args[14];
lean_object* v___x_3100_ = _args[15];
lean_object* v___x_3101_ = _args[16];
lean_object* v___x_3102_ = _args[17];
lean_object* v___x_3103_ = _args[18];
lean_object* v_ys_3104_ = _args[19];
lean_object* v___eqs_3105_ = _args[20];
lean_object* v_rhsArgs_3106_ = _args[21];
lean_object* v_argMask_3107_ = _args[22];
lean_object* v_altResultType_3108_ = _args[23];
lean_object* v___y_3109_ = _args[24];
lean_object* v___y_3110_ = _args[25];
lean_object* v___y_3111_ = _args[26];
lean_object* v___y_3112_ = _args[27];
lean_object* v___y_3113_ = _args[28];
_start:
{
uint8_t v___x_19209__boxed_3114_; lean_object* v_res_3115_; 
v___x_19209__boxed_3114_ = lean_unbox(v___x_3092_);
v_res_3115_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3085_, v_overlaps_3086_, v_a_3087_, v_fst_3088_, v___x_3089_, v___x_3090_, v___x_3091_, v___x_19209__boxed_3114_, v___x_3093_, v_a_3094_, v___x_3095_, v___x_3096_, v___x_3097_, v_matchDeclName_3098_, v___x_3099_, v___x_3100_, v___x_3101_, v___x_3102_, v___x_3103_, v_ys_3104_, v___eqs_3105_, v_rhsArgs_3106_, v_argMask_3107_, v_altResultType_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec_ref(v___eqs_3105_);
lean_dec(v___x_3103_);
lean_dec(v_fst_3088_);
lean_dec_ref(v_overlaps_3086_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3116_, lean_object* v_val_3117_, lean_object* v_baseName_3118_, lean_object* v___x_3119_, lean_object* v_a_3120_, lean_object* v___x_3121_, lean_object* v___x_3122_, lean_object* v___x_3123_, lean_object* v_matchDeclName_3124_, lean_object* v___x_3125_, lean_object* v___x_3126_, lean_object* v___x_3127_, lean_object* v_a_3128_, lean_object* v_b_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
uint8_t v___x_3135_; 
v___x_3135_ = lean_nat_dec_lt(v_a_3128_, v_upperBound_3116_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
lean_dec(v_a_3128_);
lean_dec(v___x_3127_);
lean_dec_ref(v___x_3126_);
lean_dec(v___x_3125_);
lean_dec(v_matchDeclName_3124_);
lean_dec_ref(v___x_3123_);
lean_dec_ref(v___x_3122_);
lean_dec(v___x_3121_);
lean_dec_ref(v_a_3120_);
lean_dec_ref(v___x_3119_);
lean_dec(v_baseName_3118_);
lean_dec_ref(v_val_3117_);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_b_3129_);
return v___x_3136_;
}
else
{
lean_object* v_snd_3137_; lean_object* v_snd_3138_; lean_object* v_snd_3139_; lean_object* v_fst_3140_; lean_object* v_fst_3141_; lean_object* v_fst_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3225_; 
v_snd_3137_ = lean_ctor_get(v_b_3129_, 1);
lean_inc(v_snd_3137_);
v_snd_3138_ = lean_ctor_get(v_snd_3137_, 1);
lean_inc(v_snd_3138_);
v_snd_3139_ = lean_ctor_get(v_snd_3138_, 1);
lean_inc(v_snd_3139_);
v_fst_3140_ = lean_ctor_get(v_b_3129_, 0);
lean_inc(v_fst_3140_);
lean_dec_ref(v_b_3129_);
v_fst_3141_ = lean_ctor_get(v_snd_3137_, 0);
lean_inc(v_fst_3141_);
lean_dec(v_snd_3137_);
v_fst_3142_ = lean_ctor_get(v_snd_3138_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_snd_3138_);
if (v_isSharedCheck_3225_ == 0)
{
lean_object* v_unused_3226_; 
v_unused_3226_ = lean_ctor_get(v_snd_3138_, 1);
lean_dec(v_unused_3226_);
v___x_3144_ = v_snd_3138_;
v_isShared_3145_ = v_isSharedCheck_3225_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_fst_3142_);
lean_dec(v_snd_3138_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3225_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v_fst_3146_; lean_object* v_snd_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3224_; 
v_fst_3146_ = lean_ctor_get(v_snd_3139_, 0);
v_snd_3147_ = lean_ctor_get(v_snd_3139_, 1);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_snd_3139_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3149_ = v_snd_3139_;
v_isShared_3150_ = v_isSharedCheck_3224_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_snd_3147_);
lean_inc(v_fst_3146_);
lean_dec(v_snd_3139_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3224_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_altInfos_3151_; lean_object* v_overlaps_3152_; lean_object* v_start_3153_; lean_object* v_stop_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___f_3166_; lean_object* v___x_3167_; lean_object* v___y_3169_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v_altInfos_3151_ = lean_ctor_get(v_val_3117_, 2);
v_overlaps_3152_ = lean_ctor_get(v_val_3117_, 5);
v_start_3153_ = lean_ctor_get(v___x_3126_, 1);
v_stop_3154_ = lean_ctor_get(v___x_3126_, 2);
v___x_3155_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3156_ = l_Lean_instInhabitedExpr;
v___x_3157_ = lean_unsigned_to_nat(0u);
v___x_3158_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3159_ = lean_box(0);
v___x_3160_ = lean_unsigned_to_nat(1u);
v___x_3161_ = lean_array_get_borrowed(v___x_3155_, v_altInfos_3151_, v_a_3128_);
v___x_3162_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3118_);
v___x_3163_ = l_Lean_Name_str___override(v_baseName_3118_, v___x_3162_);
lean_inc(v_fst_3142_);
v___x_3164_ = lean_name_append_index_after(v___x_3163_, v_fst_3142_);
v___x_3165_ = lean_box(v___x_3135_);
lean_inc(v___x_3127_);
lean_inc_ref(v___x_3126_);
lean_inc(v___x_3125_);
lean_inc(v___x_3164_);
lean_inc(v_matchDeclName_3124_);
lean_inc_ref(v___x_3123_);
lean_inc_ref(v___x_3122_);
lean_inc(v___x_3121_);
lean_inc_ref(v_a_3120_);
lean_inc_ref(v___x_3119_);
lean_inc(v_fst_3141_);
lean_inc(v_a_3128_);
lean_inc_ref(v_overlaps_3152_);
v___f_3166_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3166_, 0, v___x_3160_);
lean_closure_set(v___f_3166_, 1, v_overlaps_3152_);
lean_closure_set(v___f_3166_, 2, v_a_3128_);
lean_closure_set(v___f_3166_, 3, v_fst_3141_);
lean_closure_set(v___f_3166_, 4, v___x_3158_);
lean_closure_set(v___f_3166_, 5, v___x_3157_);
lean_closure_set(v___f_3166_, 6, v___x_3119_);
lean_closure_set(v___f_3166_, 7, v___x_3165_);
lean_closure_set(v___f_3166_, 8, v___x_3156_);
lean_closure_set(v___f_3166_, 9, v_a_3120_);
lean_closure_set(v___f_3166_, 10, v___x_3121_);
lean_closure_set(v___f_3166_, 11, v___x_3122_);
lean_closure_set(v___f_3166_, 12, v___x_3123_);
lean_closure_set(v___f_3166_, 13, v_matchDeclName_3124_);
lean_closure_set(v___f_3166_, 14, v___x_3164_);
lean_closure_set(v___f_3166_, 15, v___x_3125_);
lean_closure_set(v___f_3166_, 16, v___x_3159_);
lean_closure_set(v___f_3166_, 17, v___x_3126_);
lean_closure_set(v___f_3166_, 18, v___x_3127_);
v___x_3167_ = lean_array_push(v_fst_3140_, v___x_3164_);
v___x_3220_ = lean_nat_sub(v_stop_3154_, v_start_3153_);
v___x_3221_ = lean_nat_dec_lt(v_a_3128_, v___x_3220_);
lean_dec(v___x_3220_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; 
v___x_3222_ = l_outOfBounds___redArg(v___x_3156_);
v___y_3169_ = v___x_3222_;
goto v___jp_3168_;
}
else
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Subarray_get___redArg(v___x_3126_, v_a_3128_);
v___y_3169_ = v___x_3223_;
goto v___jp_3168_;
}
v___jp_3168_:
{
lean_object* v___x_3170_; 
lean_inc(v___y_3133_);
lean_inc_ref(v___y_3132_);
lean_inc(v___y_3131_);
lean_inc_ref(v___y_3130_);
v___x_3170_ = lean_infer_type(v___y_3169_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3172_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref(v___x_3170_);
lean_inc(v___x_3127_);
lean_inc(v___x_3161_);
v___x_3172_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3171_, v___x_3161_, v___x_3127_, v___f_3166_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v_snd_3174_; lean_object* v_fst_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3203_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref(v___x_3172_);
v_snd_3174_ = lean_ctor_get(v_a_3173_, 1);
v_fst_3175_ = lean_ctor_get(v_a_3173_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_a_3173_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3177_ = v_a_3173_;
v_isShared_3178_ = v_isSharedCheck_3203_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_snd_3174_);
lean_inc(v_fst_3175_);
lean_dec(v_a_3173_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3203_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v_fst_3179_; lean_object* v_snd_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3202_; 
v_fst_3179_ = lean_ctor_get(v_snd_3174_, 0);
v_snd_3180_ = lean_ctor_get(v_snd_3174_, 1);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_snd_3174_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3182_ = v_snd_3174_;
v_isShared_3183_ = v_isSharedCheck_3202_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_snd_3180_);
lean_inc(v_fst_3179_);
lean_dec(v_snd_3174_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3202_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3184_ = lean_array_push(v_fst_3141_, v_fst_3175_);
v___x_3185_ = lean_array_push(v_fst_3146_, v_fst_3179_);
v___x_3186_ = lean_array_push(v_snd_3147_, v_snd_3180_);
v___x_3187_ = lean_nat_add(v_fst_3142_, v___x_3160_);
lean_dec(v_fst_3142_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 1, v___x_3186_);
lean_ctor_set(v___x_3182_, 0, v___x_3185_);
v___x_3189_ = v___x_3182_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_3186_);
v___x_3189_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3191_; 
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 1, v___x_3189_);
lean_ctor_set(v___x_3177_, 0, v___x_3187_);
v___x_3191_ = v___x_3177_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3193_; 
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 1, v___x_3191_);
lean_ctor_set(v___x_3149_, 0, v___x_3184_);
v___x_3193_ = v___x_3149_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3195_; 
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 1, v___x_3193_);
lean_ctor_set(v___x_3144_, 0, v___x_3167_);
v___x_3195_ = v___x_3144_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_nat_add(v_a_3128_, v___x_3160_);
lean_dec(v_a_3128_);
v_a_3128_ = v___x_3196_;
v_b_3129_ = v___x_3195_;
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
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec_ref(v___x_3167_);
lean_del_object(v___x_3149_);
lean_dec(v_snd_3147_);
lean_dec(v_fst_3146_);
lean_del_object(v___x_3144_);
lean_dec(v_fst_3142_);
lean_dec(v_fst_3141_);
lean_dec(v_a_3128_);
lean_dec(v___x_3127_);
lean_dec_ref(v___x_3126_);
lean_dec(v___x_3125_);
lean_dec(v_matchDeclName_3124_);
lean_dec_ref(v___x_3123_);
lean_dec_ref(v___x_3122_);
lean_dec(v___x_3121_);
lean_dec_ref(v_a_3120_);
lean_dec_ref(v___x_3119_);
lean_dec(v_baseName_3118_);
lean_dec_ref(v_val_3117_);
v_a_3204_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3172_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3172_);
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
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec_ref(v___x_3167_);
lean_dec_ref(v___f_3166_);
lean_del_object(v___x_3149_);
lean_dec(v_snd_3147_);
lean_dec(v_fst_3146_);
lean_del_object(v___x_3144_);
lean_dec(v_fst_3142_);
lean_dec(v_fst_3141_);
lean_dec(v_a_3128_);
lean_dec(v___x_3127_);
lean_dec_ref(v___x_3126_);
lean_dec(v___x_3125_);
lean_dec(v_matchDeclName_3124_);
lean_dec_ref(v___x_3123_);
lean_dec_ref(v___x_3122_);
lean_dec(v___x_3121_);
lean_dec_ref(v_a_3120_);
lean_dec_ref(v___x_3119_);
lean_dec(v_baseName_3118_);
lean_dec_ref(v_val_3117_);
v_a_3212_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3170_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3170_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
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
lean_object* v_upperBound_3227_ = _args[0];
lean_object* v_val_3228_ = _args[1];
lean_object* v_baseName_3229_ = _args[2];
lean_object* v___x_3230_ = _args[3];
lean_object* v_a_3231_ = _args[4];
lean_object* v___x_3232_ = _args[5];
lean_object* v___x_3233_ = _args[6];
lean_object* v___x_3234_ = _args[7];
lean_object* v_matchDeclName_3235_ = _args[8];
lean_object* v___x_3236_ = _args[9];
lean_object* v___x_3237_ = _args[10];
lean_object* v___x_3238_ = _args[11];
lean_object* v_a_3239_ = _args[12];
lean_object* v_b_3240_ = _args[13];
lean_object* v___y_3241_ = _args[14];
lean_object* v___y_3242_ = _args[15];
lean_object* v___y_3243_ = _args[16];
lean_object* v___y_3244_ = _args[17];
lean_object* v___y_3245_ = _args[18];
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3227_, v_val_3228_, v_baseName_3229_, v___x_3230_, v_a_3231_, v___x_3232_, v___x_3233_, v___x_3234_, v_matchDeclName_3235_, v___x_3236_, v___x_3237_, v___x_3238_, v_a_3239_, v_b_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v_upperBound_3227_);
return v_res_3246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3250_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3251_ = lean_unsigned_to_nat(6u);
v___x_3252_ = lean_unsigned_to_nat(233u);
v___x_3253_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3254_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3255_ = l_mkPanicMessageWithDecl(v___x_3254_, v___x_3253_, v___x_3252_, v___x_3251_, v___x_3250_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3268_, lean_object* v_matchDeclName_3269_, lean_object* v_numParams_3270_, lean_object* v_val_3271_, lean_object* v___x_3272_, lean_object* v_numDiscrs_3273_, lean_object* v_baseName_3274_, lean_object* v_a_3275_, lean_object* v___x_3276_, lean_object* v___x_3277_, lean_object* v___x_3278_, lean_object* v_uElimPos_x3f_3279_, lean_object* v_discrInfos_3280_, lean_object* v_overlaps_3281_, lean_object* v___f_3282_, lean_object* v___x_3283_, lean_object* v_altInfos_3284_, lean_object* v_xs_3285_, lean_object* v___matchResultType_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; uint8_t v___y_3304_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v_lower_3312_; lean_object* v_upper_3313_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3270_);
lean_inc_ref(v_xs_3285_);
v___x_3308_ = l_Array_toSubarray___redArg(v_xs_3285_, v___x_3307_, v_numParams_3270_);
v___x_3309_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3271_);
v___x_3310_ = lean_array_get(v___x_3272_, v_xs_3285_, v___x_3309_);
lean_dec(v___x_3309_);
v___x_3366_ = lean_array_get_size(v_xs_3285_);
v___x_3367_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3271_);
v___x_3368_ = lean_nat_sub(v___x_3366_, v___x_3367_);
lean_dec(v___x_3367_);
v___x_3369_ = lean_nat_dec_le(v___x_3368_, v___x_3307_);
if (v___x_3369_ == 0)
{
v_lower_3312_ = v___x_3368_;
v_upper_3313_ = v___x_3366_;
goto v___jp_3311_;
}
else
{
lean_dec(v___x_3368_);
v_lower_3312_ = v___x_3307_;
v_upper_3313_ = v___x_3366_;
goto v___jp_3311_;
}
v___jp_3292_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3294_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3293_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
return v___x_3294_;
}
v___jp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3298_, 0, v___y_3297_);
lean_ctor_set(v___x_3298_, 1, v_splitterName_3268_);
lean_ctor_set(v___x_3298_, 2, v___y_3296_);
v___x_3299_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3269_, v___x_3298_, v___y_3290_);
return v___x_3299_;
}
v___jp_3300_:
{
lean_object* v___x_3305_; 
lean_inc(v_matchDeclName_3269_);
v___x_3305_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3269_, v___y_3304_, v___y_3301_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_dec_ref(v___x_3305_);
v___y_3296_ = v___y_3302_;
v___y_3297_ = v___y_3303_;
goto v___jp_3295_;
}
else
{
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v_matchDeclName_3269_);
lean_dec(v_splitterName_3268_);
return v___x_3305_;
}
}
v___jp_3311_:
{
lean_object* v___x_3314_; lean_object* v_start_3315_; lean_object* v_stop_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
lean_inc_ref(v_xs_3285_);
v___x_3314_ = l_Array_toSubarray___redArg(v_xs_3285_, v_lower_3312_, v_upper_3313_);
v_start_3315_ = lean_ctor_get(v___x_3314_, 1);
lean_inc(v_start_3315_);
v_stop_3316_ = lean_ctor_get(v___x_3314_, 2);
lean_inc(v_stop_3316_);
v___x_3317_ = lean_unsigned_to_nat(1u);
v___x_3318_ = lean_nat_add(v_numParams_3270_, v___x_3317_);
v___x_3319_ = lean_nat_add(v___x_3318_, v_numDiscrs_3273_);
v___x_3320_ = lean_nat_sub(v_stop_3316_, v_start_3315_);
lean_dec(v_start_3315_);
lean_dec(v_stop_3316_);
v___x_3321_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3322_ = l_Array_toSubarray___redArg(v_xs_3285_, v___x_3318_, v___x_3319_);
lean_inc(v___x_3277_);
lean_inc(v_matchDeclName_3269_);
lean_inc(v___x_3276_);
v___x_3323_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3320_, v_val_3271_, v_baseName_3274_, v___x_3322_, v_a_3275_, v___x_3276_, v___x_3308_, v___x_3310_, v_matchDeclName_3269_, v___x_3277_, v___x_3314_, v___x_3278_, v___x_3307_, v___x_3321_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
lean_dec(v___x_3320_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v_snd_3325_; lean_object* v_snd_3326_; lean_object* v_snd_3327_; lean_object* v_fst_3328_; lean_object* v_fst_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3356_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref(v___x_3323_);
v_snd_3325_ = lean_ctor_get(v_a_3324_, 1);
v_snd_3326_ = lean_ctor_get(v_snd_3325_, 1);
v_snd_3327_ = lean_ctor_get(v_snd_3326_, 1);
lean_inc(v_snd_3327_);
v_fst_3328_ = lean_ctor_get(v_a_3324_, 0);
lean_inc(v_fst_3328_);
lean_dec(v_a_3324_);
v_fst_3329_ = lean_ctor_get(v_snd_3327_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_snd_3327_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v_snd_3327_, 1);
lean_dec(v_unused_3357_);
v___x_3331_ = v_snd_3327_;
v_isShared_3332_ = v_isSharedCheck_3356_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_fst_3329_);
lean_dec(v_snd_3327_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3356_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; uint8_t v___x_3334_; 
lean_inc_ref(v_overlaps_3281_);
lean_inc(v_fst_3329_);
v___x_3333_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3333_, 0, v_numParams_3270_);
lean_ctor_set(v___x_3333_, 1, v_numDiscrs_3273_);
lean_ctor_set(v___x_3333_, 2, v_fst_3329_);
lean_ctor_set(v___x_3333_, 3, v_uElimPos_x3f_3279_);
lean_ctor_set(v___x_3333_, 4, v_discrInfos_3280_);
lean_ctor_set(v___x_3333_, 5, v_overlaps_3281_);
v___x_3334_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3281_);
lean_dec_ref(v_overlaps_3281_);
if (v___x_3334_ == 0)
{
uint8_t v___x_3335_; 
lean_del_object(v___x_3331_);
lean_dec(v_fst_3329_);
lean_dec_ref(v___x_3283_);
lean_dec(v___x_3277_);
lean_dec(v___x_3276_);
v___x_3335_ = 1;
v___y_3301_ = v___f_3282_;
v___y_3302_ = v___x_3333_;
v___y_3303_ = v_fst_3328_;
v___y_3304_ = v___x_3335_;
goto v___jp_3300_;
}
else
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3337_ = lean_find_expr(v___x_3336_, v___x_3283_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
lean_dec_ref(v___f_3282_);
v___x_3338_ = lean_array_get_size(v_altInfos_3284_);
v___x_3339_ = lean_array_get_size(v_fst_3329_);
v___x_3340_ = lean_nat_dec_eq(v___x_3338_, v___x_3339_);
if (v___x_3340_ == 0)
{
lean_dec_ref(v___x_3333_);
lean_del_object(v___x_3331_);
lean_dec(v_fst_3329_);
lean_dec(v_fst_3328_);
lean_dec_ref(v___x_3283_);
lean_dec(v___x_3277_);
lean_dec(v___x_3276_);
lean_dec(v_matchDeclName_3269_);
lean_dec(v_splitterName_3268_);
goto v___jp_3292_;
}
else
{
uint8_t v___x_3341_; 
v___x_3341_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3284_, v_fst_3329_, v___x_3338_);
lean_dec(v_fst_3329_);
if (v___x_3341_ == 0)
{
lean_dec_ref(v___x_3333_);
lean_del_object(v___x_3331_);
lean_dec(v_fst_3328_);
lean_dec_ref(v___x_3283_);
lean_dec(v___x_3277_);
lean_dec(v___x_3276_);
lean_dec(v_matchDeclName_3269_);
lean_dec(v_splitterName_3268_);
goto v___jp_3292_;
}
else
{
uint8_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; lean_object* v___x_3348_; 
v___x_3342_ = 0;
lean_inc_n(v_splitterName_3268_, 2);
v___x_3343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3343_, 0, v_splitterName_3268_);
lean_ctor_set(v___x_3343_, 1, v___x_3277_);
lean_ctor_set(v___x_3343_, 2, v___x_3283_);
lean_inc(v_matchDeclName_3269_);
v___x_3344_ = l_Lean_mkConst(v_matchDeclName_3269_, v___x_3276_);
v___x_3345_ = lean_box(1);
v___x_3346_ = 1;
if (v_isShared_3332_ == 0)
{
lean_ctor_set_tag(v___x_3331_, 1);
lean_ctor_set(v___x_3331_, 1, v___x_3306_);
lean_ctor_set(v___x_3331_, 0, v_splitterName_3268_);
v___x_3348_ = v___x_3331_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_splitterName_3268_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3306_);
v___x_3348_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3349_, 0, v___x_3343_);
lean_ctor_set(v___x_3349_, 1, v___x_3344_);
lean_ctor_set(v___x_3349_, 2, v___x_3345_);
lean_ctor_set(v___x_3349_, 3, v___x_3348_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*4, v___x_3346_);
v___x_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
lean_inc_ref(v___x_3350_);
v___x_3351_ = l_Lean_addDecl(v___x_3350_, v___x_3342_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3351_) == 0)
{
uint8_t v___x_3352_; lean_object* v___x_3353_; 
lean_dec_ref(v___x_3351_);
v___x_3352_ = 0;
lean_inc(v_splitterName_3268_);
v___x_3353_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3268_, v___x_3352_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v___x_3354_; 
lean_dec_ref(v___x_3353_);
v___x_3354_ = l_Lean_compileDecl(v___x_3350_, v___x_3342_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_dec_ref(v___x_3354_);
v___y_3296_ = v___x_3333_;
v___y_3297_ = v_fst_3328_;
goto v___jp_3295_;
}
else
{
lean_dec_ref(v___x_3333_);
lean_dec(v_fst_3328_);
lean_dec(v_matchDeclName_3269_);
lean_dec(v_splitterName_3268_);
return v___x_3354_;
}
}
else
{
lean_dec_ref(v___x_3350_);
lean_dec_ref(v___x_3333_);
lean_dec(v_fst_3328_);
lean_dec(v_matchDeclName_3269_);
lean_dec(v_splitterName_3268_);
return v___x_3353_;
}
}
else
{
lean_dec_ref(v___x_3350_);
lean_dec_ref(v___x_3333_);
lean_dec(v_fst_3328_);
lean_dec(v_matchDeclName_3269_);
lean_dec(v_splitterName_3268_);
return v___x_3351_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3337_);
lean_del_object(v___x_3331_);
lean_dec(v_fst_3329_);
lean_dec_ref(v___x_3283_);
lean_dec(v___x_3277_);
lean_dec(v___x_3276_);
v___y_3301_ = v___f_3282_;
v___y_3302_ = v___x_3333_;
v___y_3303_ = v_fst_3328_;
v___y_3304_ = v___x_3334_;
goto v___jp_3300_;
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec_ref(v___x_3283_);
lean_dec_ref(v___f_3282_);
lean_dec_ref(v_overlaps_3281_);
lean_dec_ref(v_discrInfos_3280_);
lean_dec(v_uElimPos_x3f_3279_);
lean_dec(v___x_3277_);
lean_dec(v___x_3276_);
lean_dec(v_numDiscrs_3273_);
lean_dec(v_numParams_3270_);
lean_dec(v_matchDeclName_3269_);
lean_dec(v_splitterName_3268_);
v_a_3358_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3323_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3323_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3370_ = _args[0];
lean_object* v_matchDeclName_3371_ = _args[1];
lean_object* v_numParams_3372_ = _args[2];
lean_object* v_val_3373_ = _args[3];
lean_object* v___x_3374_ = _args[4];
lean_object* v_numDiscrs_3375_ = _args[5];
lean_object* v_baseName_3376_ = _args[6];
lean_object* v_a_3377_ = _args[7];
lean_object* v___x_3378_ = _args[8];
lean_object* v___x_3379_ = _args[9];
lean_object* v___x_3380_ = _args[10];
lean_object* v_uElimPos_x3f_3381_ = _args[11];
lean_object* v_discrInfos_3382_ = _args[12];
lean_object* v_overlaps_3383_ = _args[13];
lean_object* v___f_3384_ = _args[14];
lean_object* v___x_3385_ = _args[15];
lean_object* v_altInfos_3386_ = _args[16];
lean_object* v_xs_3387_ = _args[17];
lean_object* v___matchResultType_3388_ = _args[18];
lean_object* v___y_3389_ = _args[19];
lean_object* v___y_3390_ = _args[20];
lean_object* v___y_3391_ = _args[21];
lean_object* v___y_3392_ = _args[22];
lean_object* v___y_3393_ = _args[23];
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3370_, v_matchDeclName_3371_, v_numParams_3372_, v_val_3373_, v___x_3374_, v_numDiscrs_3375_, v_baseName_3376_, v_a_3377_, v___x_3378_, v___x_3379_, v___x_3380_, v_uElimPos_x3f_3381_, v_discrInfos_3382_, v_overlaps_3383_, v___f_3384_, v___x_3385_, v_altInfos_3386_, v_xs_3387_, v___matchResultType_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec_ref(v___matchResultType_3388_);
lean_dec_ref(v_altInfos_3386_);
lean_dec_ref(v___x_3374_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
if (lean_obj_tag(v_a_3395_) == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = l_List_reverse___redArg(v_a_3396_);
return v___x_3397_;
}
else
{
lean_object* v_head_3398_; lean_object* v_tail_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3408_; 
v_head_3398_ = lean_ctor_get(v_a_3395_, 0);
v_tail_3399_ = lean_ctor_get(v_a_3395_, 1);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_a_3395_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3401_ = v_a_3395_;
v_isShared_3402_ = v_isSharedCheck_3408_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_tail_3399_);
lean_inc(v_head_3398_);
lean_dec(v_a_3395_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3408_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3403_ = l_Lean_mkLevelParam(v_head_3398_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 1, v_a_3396_);
lean_ctor_set(v___x_3401_, 0, v___x_3403_);
v___x_3405_ = v___x_3401_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3403_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_a_3396_);
v___x_3405_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
v_a_3395_ = v_tail_3399_;
v_a_3396_ = v___x_3405_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3409_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
return v___x_3411_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3412_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3413_ = lean_unsigned_to_nat(0u);
v___x_3414_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
lean_ctor_set(v___x_3414_, 2, v___x_3413_);
lean_ctor_set(v___x_3414_, 3, v___x_3413_);
lean_ctor_set(v___x_3414_, 4, v___x_3412_);
lean_ctor_set(v___x_3414_, 5, v___x_3412_);
lean_ctor_set(v___x_3414_, 6, v___x_3412_);
lean_ctor_set(v___x_3414_, 7, v___x_3412_);
lean_ctor_set(v___x_3414_, 8, v___x_3412_);
lean_ctor_set(v___x_3414_, 9, v___x_3412_);
return v___x_3414_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3415_ = lean_box(1);
v___x_3416_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3417_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
lean_ctor_set(v___x_3418_, 1, v___x_3416_);
lean_ctor_set(v___x_3418_, 2, v___x_3415_);
return v___x_3418_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_3421_ = l_Lean_stringToMessageData(v___x_3420_);
return v___x_3421_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_3424_ = l_Lean_stringToMessageData(v___x_3423_);
return v___x_3424_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_3427_ = l_Lean_stringToMessageData(v___x_3426_);
return v___x_3427_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_3430_ = l_Lean_stringToMessageData(v___x_3429_);
return v___x_3430_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_3433_ = l_Lean_stringToMessageData(v___x_3432_);
return v___x_3433_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_3436_ = l_Lean_stringToMessageData(v___x_3435_);
return v___x_3436_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_3439_ = l_Lean_stringToMessageData(v___x_3438_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3440_, lean_object* v_declHint_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v___x_3444_; lean_object* v_env_3445_; uint8_t v___x_3446_; 
v___x_3444_ = lean_st_ref_get(v___y_3442_);
v_env_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc_ref(v_env_3445_);
lean_dec(v___x_3444_);
v___x_3446_ = l_Lean_Name_isAnonymous(v_declHint_3441_);
if (v___x_3446_ == 0)
{
uint8_t v_isExporting_3447_; 
v_isExporting_3447_ = lean_ctor_get_uint8(v_env_3445_, sizeof(void*)*8);
if (v_isExporting_3447_ == 0)
{
lean_object* v___x_3448_; 
lean_dec_ref(v_env_3445_);
lean_dec(v_declHint_3441_);
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v_msg_3440_);
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; uint8_t v___x_3450_; 
lean_inc_ref(v_env_3445_);
v___x_3449_ = l_Lean_Environment_setExporting(v_env_3445_, v___x_3446_);
lean_inc(v_declHint_3441_);
lean_inc_ref(v___x_3449_);
v___x_3450_ = l_Lean_Environment_contains(v___x_3449_, v_declHint_3441_, v_isExporting_3447_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; 
lean_dec_ref(v___x_3449_);
lean_dec_ref(v_env_3445_);
lean_dec(v_declHint_3441_);
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_msg_3440_);
return v___x_3451_;
}
else
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v_c_3457_; lean_object* v___x_3458_; 
v___x_3452_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3453_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3454_ = l_Lean_Options_empty;
v___x_3455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3449_);
lean_ctor_set(v___x_3455_, 1, v___x_3452_);
lean_ctor_set(v___x_3455_, 2, v___x_3453_);
lean_ctor_set(v___x_3455_, 3, v___x_3454_);
lean_inc(v_declHint_3441_);
v___x_3456_ = l_Lean_MessageData_ofConstName(v_declHint_3441_, v___x_3446_);
v_c_3457_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3457_, 0, v___x_3455_);
lean_ctor_set(v_c_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3445_, v_declHint_3441_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_dec_ref(v_env_3445_);
lean_dec(v_declHint_3441_);
v___x_3459_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
lean_ctor_set(v___x_3460_, 1, v_c_3457_);
v___x_3461_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = l_Lean_MessageData_note(v___x_3462_);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v_msg_3440_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
return v___x_3465_;
}
else
{
lean_object* v_val_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3501_; 
v_val_3466_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3468_ = v___x_3458_;
v_isShared_3469_ = v_isSharedCheck_3501_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_val_3466_);
lean_dec(v___x_3458_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3501_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v_mod_3473_; uint8_t v___x_3474_; 
v___x_3470_ = lean_box(0);
v___x_3471_ = l_Lean_Environment_header(v_env_3445_);
lean_dec_ref(v_env_3445_);
v___x_3472_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3471_);
v_mod_3473_ = lean_array_get(v___x_3470_, v___x_3472_, v_val_3466_);
lean_dec(v_val_3466_);
lean_dec_ref(v___x_3472_);
v___x_3474_ = l_Lean_isPrivateName(v_declHint_3441_);
lean_dec(v_declHint_3441_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3475_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
lean_ctor_set(v___x_3476_, 1, v_c_3457_);
v___x_3477_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3476_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = l_Lean_MessageData_ofName(v_mod_3473_);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_3482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = l_Lean_MessageData_note(v___x_3482_);
v___x_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3484_, 0, v_msg_3440_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set_tag(v___x_3468_, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3484_);
v___x_3486_ = v___x_3468_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
v___x_3488_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
lean_ctor_set(v___x_3489_, 1, v_c_3457_);
v___x_3490_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = l_Lean_MessageData_ofName(v_mod_3473_);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3491_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_3495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = l_Lean_MessageData_note(v___x_3495_);
v___x_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3497_, 0, v_msg_3440_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
if (v_isShared_3469_ == 0)
{
lean_ctor_set_tag(v___x_3468_, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3497_);
v___x_3499_ = v___x_3468_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3502_; 
lean_dec_ref(v_env_3445_);
lean_dec(v_declHint_3441_);
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_msg_3440_);
return v___x_3502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3503_, lean_object* v_declHint_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3503_, v_declHint_3504_, v___y_3505_);
lean_dec(v___y_3505_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3508_, lean_object* v_declHint_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3525_; 
v___x_3515_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3508_, v_declHint_3509_, v___y_3513_);
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3525_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3525_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3520_ = l_Lean_unknownIdentifierMessageTag;
v___x_3521_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v_a_3516_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3521_);
v___x_3523_ = v___x_3518_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3526_, lean_object* v_declHint_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3526_, v_declHint_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3534_, lean_object* v_msg_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_fileName_3541_; lean_object* v_fileMap_3542_; lean_object* v_options_3543_; lean_object* v_currRecDepth_3544_; lean_object* v_maxRecDepth_3545_; lean_object* v_ref_3546_; lean_object* v_currNamespace_3547_; lean_object* v_openDecls_3548_; lean_object* v_initHeartbeats_3549_; lean_object* v_maxHeartbeats_3550_; lean_object* v_quotContext_3551_; lean_object* v_currMacroScope_3552_; uint8_t v_diag_3553_; lean_object* v_cancelTk_x3f_3554_; uint8_t v_suppressElabErrors_3555_; lean_object* v_inheritedTraceOptions_3556_; lean_object* v_ref_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v_fileName_3541_ = lean_ctor_get(v___y_3538_, 0);
v_fileMap_3542_ = lean_ctor_get(v___y_3538_, 1);
v_options_3543_ = lean_ctor_get(v___y_3538_, 2);
v_currRecDepth_3544_ = lean_ctor_get(v___y_3538_, 3);
v_maxRecDepth_3545_ = lean_ctor_get(v___y_3538_, 4);
v_ref_3546_ = lean_ctor_get(v___y_3538_, 5);
v_currNamespace_3547_ = lean_ctor_get(v___y_3538_, 6);
v_openDecls_3548_ = lean_ctor_get(v___y_3538_, 7);
v_initHeartbeats_3549_ = lean_ctor_get(v___y_3538_, 8);
v_maxHeartbeats_3550_ = lean_ctor_get(v___y_3538_, 9);
v_quotContext_3551_ = lean_ctor_get(v___y_3538_, 10);
v_currMacroScope_3552_ = lean_ctor_get(v___y_3538_, 11);
v_diag_3553_ = lean_ctor_get_uint8(v___y_3538_, sizeof(void*)*14);
v_cancelTk_x3f_3554_ = lean_ctor_get(v___y_3538_, 12);
v_suppressElabErrors_3555_ = lean_ctor_get_uint8(v___y_3538_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3556_ = lean_ctor_get(v___y_3538_, 13);
v_ref_3557_ = l_Lean_replaceRef(v_ref_3534_, v_ref_3546_);
lean_inc_ref(v_inheritedTraceOptions_3556_);
lean_inc(v_cancelTk_x3f_3554_);
lean_inc(v_currMacroScope_3552_);
lean_inc(v_quotContext_3551_);
lean_inc(v_maxHeartbeats_3550_);
lean_inc(v_initHeartbeats_3549_);
lean_inc(v_openDecls_3548_);
lean_inc(v_currNamespace_3547_);
lean_inc(v_maxRecDepth_3545_);
lean_inc(v_currRecDepth_3544_);
lean_inc_ref(v_options_3543_);
lean_inc_ref(v_fileMap_3542_);
lean_inc_ref(v_fileName_3541_);
v___x_3558_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3558_, 0, v_fileName_3541_);
lean_ctor_set(v___x_3558_, 1, v_fileMap_3542_);
lean_ctor_set(v___x_3558_, 2, v_options_3543_);
lean_ctor_set(v___x_3558_, 3, v_currRecDepth_3544_);
lean_ctor_set(v___x_3558_, 4, v_maxRecDepth_3545_);
lean_ctor_set(v___x_3558_, 5, v_ref_3557_);
lean_ctor_set(v___x_3558_, 6, v_currNamespace_3547_);
lean_ctor_set(v___x_3558_, 7, v_openDecls_3548_);
lean_ctor_set(v___x_3558_, 8, v_initHeartbeats_3549_);
lean_ctor_set(v___x_3558_, 9, v_maxHeartbeats_3550_);
lean_ctor_set(v___x_3558_, 10, v_quotContext_3551_);
lean_ctor_set(v___x_3558_, 11, v_currMacroScope_3552_);
lean_ctor_set(v___x_3558_, 12, v_cancelTk_x3f_3554_);
lean_ctor_set(v___x_3558_, 13, v_inheritedTraceOptions_3556_);
lean_ctor_set_uint8(v___x_3558_, sizeof(void*)*14, v_diag_3553_);
lean_ctor_set_uint8(v___x_3558_, sizeof(void*)*14 + 1, v_suppressElabErrors_3555_);
v___x_3559_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3535_, v___y_3536_, v___y_3537_, v___x_3558_, v___y_3539_);
lean_dec_ref(v___x_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3560_, lean_object* v_msg_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3560_, v_msg_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v_ref_3560_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3568_, lean_object* v_msg_3569_, lean_object* v_declHint_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___x_3576_; lean_object* v_a_3577_; lean_object* v___x_3578_; 
v___x_3576_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3569_, v_declHint_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref(v___x_3576_);
v___x_3578_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3568_, v_a_3577_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3579_, lean_object* v_msg_3580_, lean_object* v_declHint_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3579_, v_msg_3580_, v_declHint_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v_ref_3579_);
return v_res_3587_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3590_ = l_Lean_stringToMessageData(v___x_3589_);
return v___x_3590_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3593_ = l_Lean_stringToMessageData(v___x_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3594_, lean_object* v_constName_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v___x_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3601_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3602_ = 0;
lean_inc(v_constName_3595_);
v___x_3603_ = l_Lean_MessageData_ofConstName(v_constName_3595_, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3601_);
lean_ctor_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3604_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3594_, v___x_3606_, v_constName_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3608_, lean_object* v_constName_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3608_, v_constName_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v_ref_3608_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_ref_3622_; lean_object* v___x_3623_; 
v_ref_3622_ = lean_ctor_get(v___y_3619_, 5);
v___x_3623_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3622_, v_constName_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v___x_3637_; lean_object* v_env_3638_; uint8_t v___x_3639_; lean_object* v___x_3640_; 
v___x_3637_ = lean_st_ref_get(v___y_3635_);
v_env_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc_ref(v_env_3638_);
lean_dec(v___x_3637_);
v___x_3639_ = 0;
lean_inc(v_constName_3631_);
v___x_3640_ = l_Lean_Environment_find_x3f(v_env_3638_, v_constName_3631_, v___x_3639_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
return v___x_3641_;
}
else
{
lean_object* v_val_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec(v_constName_3631_);
v_val_3642_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3640_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_val_3642_);
lean_dec(v___x_3640_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set_tag(v___x_3644_, 0);
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_val_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
return v_res_3656_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3659_ = l_Lean_stringToMessageData(v___x_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3660_, lean_object* v_baseName_3661_, lean_object* v_splitterName_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v___x_3668_; uint8_t v_foApprox_3669_; uint8_t v_ctxApprox_3670_; uint8_t v_quasiPatternApprox_3671_; uint8_t v_constApprox_3672_; uint8_t v_isDefEqStuckEx_3673_; uint8_t v_unificationHints_3674_; uint8_t v_proofIrrelevance_3675_; uint8_t v_assignSyntheticOpaque_3676_; uint8_t v_offsetCnstrs_3677_; uint8_t v_transparency_3678_; uint8_t v_univApprox_3679_; uint8_t v_iota_3680_; uint8_t v_beta_3681_; uint8_t v_proj_3682_; uint8_t v_zeta_3683_; uint8_t v_zetaDelta_3684_; uint8_t v_zetaUnused_3685_; uint8_t v_zetaHave_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3749_; 
v___x_3668_ = l_Lean_Meta_Context_config(v_a_3663_);
v_foApprox_3669_ = lean_ctor_get_uint8(v___x_3668_, 0);
v_ctxApprox_3670_ = lean_ctor_get_uint8(v___x_3668_, 1);
v_quasiPatternApprox_3671_ = lean_ctor_get_uint8(v___x_3668_, 2);
v_constApprox_3672_ = lean_ctor_get_uint8(v___x_3668_, 3);
v_isDefEqStuckEx_3673_ = lean_ctor_get_uint8(v___x_3668_, 4);
v_unificationHints_3674_ = lean_ctor_get_uint8(v___x_3668_, 5);
v_proofIrrelevance_3675_ = lean_ctor_get_uint8(v___x_3668_, 6);
v_assignSyntheticOpaque_3676_ = lean_ctor_get_uint8(v___x_3668_, 7);
v_offsetCnstrs_3677_ = lean_ctor_get_uint8(v___x_3668_, 8);
v_transparency_3678_ = lean_ctor_get_uint8(v___x_3668_, 9);
v_univApprox_3679_ = lean_ctor_get_uint8(v___x_3668_, 11);
v_iota_3680_ = lean_ctor_get_uint8(v___x_3668_, 12);
v_beta_3681_ = lean_ctor_get_uint8(v___x_3668_, 13);
v_proj_3682_ = lean_ctor_get_uint8(v___x_3668_, 14);
v_zeta_3683_ = lean_ctor_get_uint8(v___x_3668_, 15);
v_zetaDelta_3684_ = lean_ctor_get_uint8(v___x_3668_, 16);
v_zetaUnused_3685_ = lean_ctor_get_uint8(v___x_3668_, 17);
v_zetaHave_3686_ = lean_ctor_get_uint8(v___x_3668_, 18);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3688_ = v___x_3668_;
v_isShared_3689_ = v_isSharedCheck_3749_;
goto v_resetjp_3687_;
}
else
{
lean_dec(v___x_3668_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3749_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
uint8_t v_trackZetaDelta_3690_; lean_object* v_zetaDeltaSet_3691_; lean_object* v_lctx_3692_; lean_object* v_localInstances_3693_; lean_object* v_defEqCtx_x3f_3694_; lean_object* v_synthPendingDepth_3695_; lean_object* v_canUnfold_x3f_3696_; uint8_t v_univApprox_3697_; uint8_t v_inTypeClassResolution_3698_; uint8_t v_cacheInferType_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3747_; 
v_trackZetaDelta_3690_ = lean_ctor_get_uint8(v_a_3663_, sizeof(void*)*7);
v_zetaDeltaSet_3691_ = lean_ctor_get(v_a_3663_, 1);
v_lctx_3692_ = lean_ctor_get(v_a_3663_, 2);
v_localInstances_3693_ = lean_ctor_get(v_a_3663_, 3);
v_defEqCtx_x3f_3694_ = lean_ctor_get(v_a_3663_, 4);
v_synthPendingDepth_3695_ = lean_ctor_get(v_a_3663_, 5);
v_canUnfold_x3f_3696_ = lean_ctor_get(v_a_3663_, 6);
v_univApprox_3697_ = lean_ctor_get_uint8(v_a_3663_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3698_ = lean_ctor_get_uint8(v_a_3663_, sizeof(void*)*7 + 2);
v_cacheInferType_3699_ = lean_ctor_get_uint8(v_a_3663_, sizeof(void*)*7 + 3);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_a_3663_);
if (v_isSharedCheck_3747_ == 0)
{
lean_object* v_unused_3748_; 
v_unused_3748_ = lean_ctor_get(v_a_3663_, 0);
lean_dec(v_unused_3748_);
v___x_3701_ = v_a_3663_;
v_isShared_3702_ = v_isSharedCheck_3747_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_canUnfold_x3f_3696_);
lean_inc(v_synthPendingDepth_3695_);
lean_inc(v_defEqCtx_x3f_3694_);
lean_inc(v_localInstances_3693_);
lean_inc(v_lctx_3692_);
lean_inc(v_zetaDeltaSet_3691_);
lean_dec(v_a_3663_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3747_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
uint8_t v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = 2;
if (v_isShared_3689_ == 0)
{
v___x_3705_ = v___x_3688_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 0, v_foApprox_3669_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 1, v_ctxApprox_3670_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 2, v_quasiPatternApprox_3671_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 3, v_constApprox_3672_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 4, v_isDefEqStuckEx_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 5, v_unificationHints_3674_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 6, v_proofIrrelevance_3675_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 7, v_assignSyntheticOpaque_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 8, v_offsetCnstrs_3677_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 9, v_transparency_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 11, v_univApprox_3679_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 12, v_iota_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 13, v_beta_3681_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 14, v_proj_3682_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 15, v_zeta_3683_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 16, v_zetaDelta_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 17, v_zetaUnused_3685_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, 18, v_zetaHave_3686_);
v___x_3705_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
uint64_t v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3709_; 
lean_ctor_set_uint8(v___x_3705_, 10, v___x_3703_);
v___x_3706_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3705_);
v___x_3707_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3707_, 0, v___x_3705_);
lean_ctor_set_uint64(v___x_3707_, sizeof(void*)*1, v___x_3706_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3707_);
v___x_3709_ = v___x_3701_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3707_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_zetaDeltaSet_3691_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v_lctx_3692_);
lean_ctor_set(v_reuseFailAlloc_3745_, 3, v_localInstances_3693_);
lean_ctor_set(v_reuseFailAlloc_3745_, 4, v_defEqCtx_x3f_3694_);
lean_ctor_set(v_reuseFailAlloc_3745_, 5, v_synthPendingDepth_3695_);
lean_ctor_set(v_reuseFailAlloc_3745_, 6, v_canUnfold_x3f_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3745_, sizeof(void*)*7, v_trackZetaDelta_3690_);
lean_ctor_set_uint8(v_reuseFailAlloc_3745_, sizeof(void*)*7 + 1, v_univApprox_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3745_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3745_, sizeof(void*)*7 + 3, v_cacheInferType_3699_);
v___x_3709_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3710_; 
lean_inc(v_matchDeclName_3660_);
v___x_3710_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3660_, v___x_3709_, v_a_3664_, v_a_3665_, v_a_3666_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3712_; lean_object* v_a_3713_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref(v___x_3710_);
lean_inc(v_matchDeclName_3660_);
v___x_3712_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_3660_, v_a_3666_);
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref(v___x_3712_);
if (lean_obj_tag(v_a_3713_) == 1)
{
lean_object* v_val_3714_; lean_object* v_numParams_3715_; lean_object* v_numDiscrs_3716_; lean_object* v_altInfos_3717_; lean_object* v_uElimPos_x3f_3718_; lean_object* v_discrInfos_3719_; lean_object* v_overlaps_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___f_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___f_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; 
v_val_3714_ = lean_ctor_get(v_a_3713_, 0);
lean_inc(v_val_3714_);
lean_dec_ref(v_a_3713_);
v_numParams_3715_ = lean_ctor_get(v_val_3714_, 0);
lean_inc(v_numParams_3715_);
v_numDiscrs_3716_ = lean_ctor_get(v_val_3714_, 1);
lean_inc(v_numDiscrs_3716_);
v_altInfos_3717_ = lean_ctor_get(v_val_3714_, 2);
lean_inc_ref(v_altInfos_3717_);
v_uElimPos_x3f_3718_ = lean_ctor_get(v_val_3714_, 3);
lean_inc(v_uElimPos_x3f_3718_);
v_discrInfos_3719_ = lean_ctor_get(v_val_3714_, 4);
lean_inc_ref(v_discrInfos_3719_);
v_overlaps_3720_ = lean_ctor_get(v_val_3714_, 5);
lean_inc_ref_n(v_overlaps_3720_, 2);
v___x_3721_ = l_Lean_instInhabitedExpr;
v___x_3722_ = l_Lean_ConstantInfo_levelParams(v_a_3711_);
v___x_3723_ = lean_box(0);
lean_inc(v___x_3722_);
v___x_3724_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_3722_, v___x_3723_);
lean_inc(v_splitterName_3662_);
v___f_3725_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3725_, 0, v_overlaps_3720_);
lean_closure_set(v___f_3725_, 1, v_splitterName_3662_);
v___x_3726_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3719_);
v___x_3727_ = l_Lean_ConstantInfo_type(v_a_3711_);
lean_inc_ref(v___x_3727_);
v___f_3728_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3728_, 0, v_splitterName_3662_);
lean_closure_set(v___f_3728_, 1, v_matchDeclName_3660_);
lean_closure_set(v___f_3728_, 2, v_numParams_3715_);
lean_closure_set(v___f_3728_, 3, v_val_3714_);
lean_closure_set(v___f_3728_, 4, v___x_3721_);
lean_closure_set(v___f_3728_, 5, v_numDiscrs_3716_);
lean_closure_set(v___f_3728_, 6, v_baseName_3661_);
lean_closure_set(v___f_3728_, 7, v_a_3711_);
lean_closure_set(v___f_3728_, 8, v___x_3724_);
lean_closure_set(v___f_3728_, 9, v___x_3722_);
lean_closure_set(v___f_3728_, 10, v___x_3726_);
lean_closure_set(v___f_3728_, 11, v_uElimPos_x3f_3718_);
lean_closure_set(v___f_3728_, 12, v_discrInfos_3719_);
lean_closure_set(v___f_3728_, 13, v_overlaps_3720_);
lean_closure_set(v___f_3728_, 14, v___f_3725_);
lean_closure_set(v___f_3728_, 15, v___x_3727_);
lean_closure_set(v___f_3728_, 16, v_altInfos_3717_);
v___x_3729_ = 0;
v___x_3730_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3727_, v___f_3728_, v___x_3729_, v___x_3729_, v___x_3709_, v_a_3664_, v_a_3665_, v_a_3666_);
lean_dec_ref(v___x_3709_);
return v___x_3730_;
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
lean_dec(v_a_3713_);
lean_dec(v_a_3711_);
lean_dec(v_splitterName_3662_);
lean_dec(v_baseName_3661_);
v___x_3731_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3732_ = l_Lean_MessageData_ofName(v_matchDeclName_3660_);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3735_, v___x_3709_, v_a_3664_, v_a_3665_, v_a_3666_);
lean_dec_ref(v___x_3709_);
return v___x_3736_;
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec_ref(v___x_3709_);
lean_dec(v_splitterName_3662_);
lean_dec(v_baseName_3661_);
lean_dec(v_matchDeclName_3660_);
v_a_3737_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3710_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3710_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3750_, lean_object* v_baseName_3751_, lean_object* v_splitterName_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3750_, v_baseName_3751_, v_splitterName_3752_, v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
lean_dec(v_a_3754_);
return v_res_3758_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3759_, lean_object* v_ys_3760_, lean_object* v_hsz_3761_, lean_object* v_x_3762_, lean_object* v_x_3763_){
_start:
{
uint8_t v___x_3764_; 
v___x_3764_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3759_, v_ys_3760_, v_x_3762_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3765_, lean_object* v_ys_3766_, lean_object* v_hsz_3767_, lean_object* v_x_3768_, lean_object* v_x_3769_){
_start:
{
uint8_t v_res_3770_; lean_object* v_r_3771_; 
v_res_3770_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3765_, v_ys_3766_, v_hsz_3767_, v_x_3768_, v_x_3769_);
lean_dec_ref(v_ys_3766_);
lean_dec_ref(v_xs_3765_);
v_r_3771_ = lean_box(v_res_3770_);
return v_r_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3772_, lean_object* v_R_3773_, lean_object* v_a_3774_, lean_object* v_b_3775_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3774_, v_b_3775_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3777_, lean_object* v_val_3778_, lean_object* v_baseName_3779_, lean_object* v___x_3780_, lean_object* v_a_3781_, lean_object* v___x_3782_, lean_object* v___x_3783_, lean_object* v___x_3784_, lean_object* v_matchDeclName_3785_, lean_object* v___x_3786_, lean_object* v___x_3787_, lean_object* v___x_3788_, lean_object* v_inst_3789_, lean_object* v_R_3790_, lean_object* v_a_3791_, lean_object* v_b_3792_, lean_object* v_c_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3777_, v_val_3778_, v_baseName_3779_, v___x_3780_, v_a_3781_, v___x_3782_, v___x_3783_, v___x_3784_, v_matchDeclName_3785_, v___x_3786_, v___x_3787_, v___x_3788_, v_a_3791_, v_b_3792_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3800_ = _args[0];
lean_object* v_val_3801_ = _args[1];
lean_object* v_baseName_3802_ = _args[2];
lean_object* v___x_3803_ = _args[3];
lean_object* v_a_3804_ = _args[4];
lean_object* v___x_3805_ = _args[5];
lean_object* v___x_3806_ = _args[6];
lean_object* v___x_3807_ = _args[7];
lean_object* v_matchDeclName_3808_ = _args[8];
lean_object* v___x_3809_ = _args[9];
lean_object* v___x_3810_ = _args[10];
lean_object* v___x_3811_ = _args[11];
lean_object* v_inst_3812_ = _args[12];
lean_object* v_R_3813_ = _args[13];
lean_object* v_a_3814_ = _args[14];
lean_object* v_b_3815_ = _args[15];
lean_object* v_c_3816_ = _args[16];
lean_object* v___y_3817_ = _args[17];
lean_object* v___y_3818_ = _args[18];
lean_object* v___y_3819_ = _args[19];
lean_object* v___y_3820_ = _args[20];
lean_object* v___y_3821_ = _args[21];
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3800_, v_val_3801_, v_baseName_3802_, v___x_3803_, v_a_3804_, v___x_3805_, v___x_3806_, v___x_3807_, v_matchDeclName_3808_, v___x_3809_, v___x_3810_, v___x_3811_, v_inst_3812_, v_R_3813_, v_a_3814_, v_b_3815_, v_c_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v_upperBound_3800_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3823_, lean_object* v_constName_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3831_, lean_object* v_constName_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3831_, v_constName_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3839_, lean_object* v_ref_3840_, lean_object* v_constName_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3840_, v_constName_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3848_, lean_object* v_ref_3849_, lean_object* v_constName_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3848_, v_ref_3849_, v_constName_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v_ref_3849_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3857_, lean_object* v_ref_3858_, lean_object* v_msg_3859_, lean_object* v_declHint_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3858_, v_msg_3859_, v_declHint_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3867_, lean_object* v_ref_3868_, lean_object* v_msg_3869_, lean_object* v_declHint_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3867_, v_ref_3868_, v_msg_3869_, v_declHint_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v_ref_3868_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3877_, lean_object* v_declHint_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3877_, v_declHint_3878_, v___y_3882_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3885_, lean_object* v_declHint_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3885_, v_declHint_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3893_, lean_object* v_ref_3894_, lean_object* v_msg_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v___x_3901_; 
v___x_3901_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3894_, v_msg_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3902_, lean_object* v_ref_3903_, lean_object* v_msg_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3902_, v_ref_3903_, v_msg_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v_ref_3903_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3911_, lean_object* v_vals_3912_, lean_object* v_i_3913_, lean_object* v_k_3914_){
_start:
{
lean_object* v___x_3915_; uint8_t v___x_3916_; 
v___x_3915_ = lean_array_get_size(v_keys_3911_);
v___x_3916_ = lean_nat_dec_lt(v_i_3913_, v___x_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; 
lean_dec(v_i_3913_);
v___x_3917_ = lean_box(0);
return v___x_3917_;
}
else
{
lean_object* v_k_x27_3918_; uint8_t v___x_3919_; 
v_k_x27_3918_ = lean_array_fget_borrowed(v_keys_3911_, v_i_3913_);
v___x_3919_ = lean_name_eq(v_k_3914_, v_k_x27_3918_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = lean_unsigned_to_nat(1u);
v___x_3921_ = lean_nat_add(v_i_3913_, v___x_3920_);
lean_dec(v_i_3913_);
v_i_3913_ = v___x_3921_;
goto _start;
}
else
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_array_fget_borrowed(v_vals_3912_, v_i_3913_);
lean_dec(v_i_3913_);
lean_inc(v___x_3923_);
v___x_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3925_, lean_object* v_vals_3926_, lean_object* v_i_3927_, lean_object* v_k_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3925_, v_vals_3926_, v_i_3927_, v_k_3928_);
lean_dec(v_k_3928_);
lean_dec_ref(v_vals_3926_);
lean_dec_ref(v_keys_3925_);
return v_res_3929_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_3930_; size_t v___x_3931_; size_t v___x_3932_; 
v___x_3930_ = ((size_t)5ULL);
v___x_3931_ = ((size_t)1ULL);
v___x_3932_ = lean_usize_shift_left(v___x_3931_, v___x_3930_);
return v___x_3932_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_3933_; size_t v___x_3934_; size_t v___x_3935_; 
v___x_3933_ = ((size_t)1ULL);
v___x_3934_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0);
v___x_3935_ = lean_usize_sub(v___x_3934_, v___x_3933_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3936_, size_t v_x_3937_, lean_object* v_x_3938_){
_start:
{
if (lean_obj_tag(v_x_3936_) == 0)
{
lean_object* v_es_3939_; lean_object* v___x_3940_; size_t v___x_3941_; size_t v___x_3942_; size_t v___x_3943_; lean_object* v_j_3944_; lean_object* v___x_3945_; 
v_es_3939_ = lean_ctor_get(v_x_3936_, 0);
v___x_3940_ = lean_box(2);
v___x_3941_ = ((size_t)5ULL);
v___x_3942_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1);
v___x_3943_ = lean_usize_land(v_x_3937_, v___x_3942_);
v_j_3944_ = lean_usize_to_nat(v___x_3943_);
v___x_3945_ = lean_array_get_borrowed(v___x_3940_, v_es_3939_, v_j_3944_);
lean_dec(v_j_3944_);
switch(lean_obj_tag(v___x_3945_))
{
case 0:
{
lean_object* v_key_3946_; lean_object* v_val_3947_; uint8_t v___x_3948_; 
v_key_3946_ = lean_ctor_get(v___x_3945_, 0);
v_val_3947_ = lean_ctor_get(v___x_3945_, 1);
v___x_3948_ = lean_name_eq(v_x_3938_, v_key_3946_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_box(0);
return v___x_3949_;
}
else
{
lean_object* v___x_3950_; 
lean_inc(v_val_3947_);
v___x_3950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3950_, 0, v_val_3947_);
return v___x_3950_;
}
}
case 1:
{
lean_object* v_node_3951_; size_t v___x_3952_; 
v_node_3951_ = lean_ctor_get(v___x_3945_, 0);
v___x_3952_ = lean_usize_shift_right(v_x_3937_, v___x_3941_);
v_x_3936_ = v_node_3951_;
v_x_3937_ = v___x_3952_;
goto _start;
}
default: 
{
lean_object* v___x_3954_; 
v___x_3954_ = lean_box(0);
return v___x_3954_;
}
}
}
else
{
lean_object* v_ks_3955_; lean_object* v_vs_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v_ks_3955_ = lean_ctor_get(v_x_3936_, 0);
v_vs_3956_ = lean_ctor_get(v_x_3936_, 1);
v___x_3957_ = lean_unsigned_to_nat(0u);
v___x_3958_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3955_, v_vs_3956_, v___x_3957_, v_x_3938_);
return v___x_3958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3959_, lean_object* v_x_3960_, lean_object* v_x_3961_){
_start:
{
size_t v_x_715__boxed_3962_; lean_object* v_res_3963_; 
v_x_715__boxed_3962_ = lean_unbox_usize(v_x_3960_);
lean_dec(v_x_3960_);
v_res_3963_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3959_, v_x_715__boxed_3962_, v_x_3961_);
lean_dec(v_x_3961_);
lean_dec_ref(v_x_3959_);
return v_res_3963_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3964_; uint64_t v___x_3965_; 
v___x_3964_ = lean_unsigned_to_nat(1723u);
v___x_3965_ = lean_uint64_of_nat(v___x_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3966_, lean_object* v_x_3967_){
_start:
{
uint64_t v___y_3969_; 
if (lean_obj_tag(v_x_3967_) == 0)
{
uint64_t v___x_3972_; 
v___x_3972_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0);
v___y_3969_ = v___x_3972_;
goto v___jp_3968_;
}
else
{
uint64_t v_hash_3973_; 
v_hash_3973_ = lean_ctor_get_uint64(v_x_3967_, sizeof(void*)*2);
v___y_3969_ = v_hash_3973_;
goto v___jp_3968_;
}
v___jp_3968_:
{
size_t v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = lean_uint64_to_usize(v___y_3969_);
v___x_3971_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3966_, v___x_3970_, v_x_3967_);
return v___x_3971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3974_, lean_object* v_x_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3974_, v_x_3975_);
lean_dec(v_x_3975_);
lean_dec_ref(v_x_3974_);
return v_res_3976_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3984_ = l_Lean_stringToMessageData(v___x_3983_);
return v___x_3984_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3986_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3987_ = l_Lean_stringToMessageData(v___x_3986_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_){
_start:
{
lean_object* v___x_3994_; lean_object* v_env_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3994_ = lean_st_ref_get(v_a_3992_);
v_env_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc_ref(v_env_3995_);
lean_dec(v___x_3994_);
lean_inc_n(v_matchDeclName_3988_, 3);
v___x_3996_ = l_Lean_mkPrivateName(v_env_3995_, v_matchDeclName_3988_);
lean_dec_ref(v_env_3995_);
v___x_3997_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_3996_);
v___x_3998_ = l_Lean_Name_append(v___x_3996_, v___x_3997_);
lean_inc_n(v___x_3998_, 2);
v___x_3999_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_3999_, 0, v_matchDeclName_3988_);
lean_closure_set(v___x_3999_, 1, v___x_3996_);
lean_closure_set(v___x_3999_, 2, v___x_3998_);
v___x_4000_ = l_Lean_Meta_realizeConst(v_matchDeclName_3988_, v___x_3998_, v___x_3999_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4029_; 
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4029_ == 0)
{
lean_object* v_unused_4030_; 
v_unused_4030_ = lean_ctor_get(v___x_4000_, 0);
lean_dec(v_unused_4030_);
v___x_4002_ = v___x_4000_;
v_isShared_4003_ = v_isSharedCheck_4029_;
goto v_resetjp_4001_;
}
else
{
lean_dec(v___x_4000_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4029_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; lean_object* v_env_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v_map_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4027_; 
v___x_4004_ = lean_st_ref_get(v_a_3992_);
v_env_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc_ref(v_env_4005_);
lean_dec(v___x_4004_);
v___x_4006_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_4007_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_4008_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_4009_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4006_, v___x_4007_, v_env_4005_, v___x_4008_, v___x_3998_);
v_map_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4027_ == 0)
{
lean_object* v_unused_4028_; 
v_unused_4028_ = lean_ctor_get(v___x_4009_, 1);
lean_dec(v_unused_4028_);
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4027_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_map_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4027_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_4010_, v_matchDeclName_3988_);
lean_dec_ref(v_map_4010_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4018_; 
lean_del_object(v___x_4002_);
v___x_4015_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_4016_ = l_Lean_MessageData_ofName(v_matchDeclName_3988_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set_tag(v___x_4012_, 7);
lean_ctor_set(v___x_4012_, 1, v___x_4016_);
lean_ctor_set(v___x_4012_, 0, v___x_4015_);
v___x_4018_ = v___x_4012_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4015_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4019_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_4020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4018_);
lean_ctor_set(v___x_4020_, 1, v___x_4019_);
v___x_4021_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_4020_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
return v___x_4021_;
}
}
else
{
lean_object* v_val_4023_; lean_object* v___x_4025_; 
lean_del_object(v___x_4012_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
lean_dec(v_matchDeclName_3988_);
v_val_4023_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_val_4023_);
lean_dec_ref(v___x_4014_);
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v_val_4023_);
v___x_4025_ = v___x_4002_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_val_4023_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
lean_dec(v___x_3998_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
lean_dec(v_matchDeclName_3988_);
v_a_4031_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4000_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4000_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = lean_get_match_equations_for(v_matchDeclName_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4046_, lean_object* v_x_4047_, lean_object* v_x_4048_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4047_, v_x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4050_, lean_object* v_x_4051_, lean_object* v_x_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4050_, v_x_4051_, v_x_4052_);
lean_dec(v_x_4052_);
lean_dec_ref(v_x_4051_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4054_, lean_object* v_x_4055_, size_t v_x_4056_, lean_object* v_x_4057_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4055_, v_x_4056_, v_x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4059_, lean_object* v_x_4060_, lean_object* v_x_4061_, lean_object* v_x_4062_){
_start:
{
size_t v_x_919__boxed_4063_; lean_object* v_res_4064_; 
v_x_919__boxed_4063_ = lean_unbox_usize(v_x_4061_);
lean_dec(v_x_4061_);
v_res_4064_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4059_, v_x_4060_, v_x_919__boxed_4063_, v_x_4062_);
lean_dec(v_x_4062_);
lean_dec_ref(v_x_4060_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4065_, lean_object* v_keys_4066_, lean_object* v_vals_4067_, lean_object* v_heq_4068_, lean_object* v_i_4069_, lean_object* v_k_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4066_, v_vals_4067_, v_i_4069_, v_k_4070_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4072_, lean_object* v_keys_4073_, lean_object* v_vals_4074_, lean_object* v_heq_4075_, lean_object* v_i_4076_, lean_object* v_k_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4072_, v_keys_4073_, v_vals_4074_, v_heq_4075_, v_i_4076_, v_k_4077_);
lean_dec(v_k_4077_);
lean_dec_ref(v_vals_4074_);
lean_dec_ref(v_keys_4073_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4079_, lean_object* v_k_4080_, uint8_t v_cleanupAnnotations_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v___f_4087_; uint8_t v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___f_4087_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4087_, 0, v_k_4080_);
v___x_4088_ = 0;
v___x_4089_ = lean_box(0);
v___x_4090_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4088_, v___x_4089_, v_type_4079_, v___f_4087_, v_cleanupAnnotations_4081_, v___x_4088_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4090_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
v_a_4099_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4090_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4090_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4107_, lean_object* v_k_4108_, lean_object* v_cleanupAnnotations_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4115_; lean_object* v_res_4116_; 
v_cleanupAnnotations_boxed_4115_ = lean_unbox(v_cleanupAnnotations_4109_);
v_res_4116_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4107_, v_k_4108_, v_cleanupAnnotations_boxed_4115_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4117_, lean_object* v_type_4118_, lean_object* v_k_4119_, uint8_t v_cleanupAnnotations_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v___x_4126_; 
v___x_4126_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4118_, v_k_4119_, v_cleanupAnnotations_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4127_, lean_object* v_type_4128_, lean_object* v_k_4129_, lean_object* v_cleanupAnnotations_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4136_; lean_object* v_res_4137_; 
v_cleanupAnnotations_boxed_4136_ = lean_unbox(v_cleanupAnnotations_4130_);
v_res_4137_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4127_, v_type_4128_, v_k_4129_, v_cleanupAnnotations_boxed_4136_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v_msg_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___f_4144_; lean_object* v___x_19931__overap_4145_; lean_object* v___x_4146_; 
v___f_4144_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_19931__overap_4145_ = lean_panic_fn_borrowed(v___f_4144_, v_msg_4138_);
lean_inc(v___y_4142_);
lean_inc_ref(v___y_4141_);
lean_inc(v___y_4140_);
lean_inc_ref(v___y_4139_);
v___x_4146_ = lean_apply_5(v___x_19931__overap_4145_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, lean_box(0));
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v_msg_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_msg_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4154_){
_start:
{
uint8_t v_foApprox_4155_; uint8_t v_ctxApprox_4156_; uint8_t v_quasiPatternApprox_4157_; uint8_t v_constApprox_4158_; uint8_t v_isDefEqStuckEx_4159_; uint8_t v_unificationHints_4160_; uint8_t v_proofIrrelevance_4161_; uint8_t v_assignSyntheticOpaque_4162_; uint8_t v_offsetCnstrs_4163_; uint8_t v_transparency_4164_; uint8_t v_univApprox_4165_; uint8_t v_iota_4166_; uint8_t v_beta_4167_; uint8_t v_proj_4168_; uint8_t v_zeta_4169_; uint8_t v_zetaDelta_4170_; uint8_t v_zetaUnused_4171_; uint8_t v_zetaHave_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4180_; 
v_foApprox_4155_ = lean_ctor_get_uint8(v_c_4154_, 0);
v_ctxApprox_4156_ = lean_ctor_get_uint8(v_c_4154_, 1);
v_quasiPatternApprox_4157_ = lean_ctor_get_uint8(v_c_4154_, 2);
v_constApprox_4158_ = lean_ctor_get_uint8(v_c_4154_, 3);
v_isDefEqStuckEx_4159_ = lean_ctor_get_uint8(v_c_4154_, 4);
v_unificationHints_4160_ = lean_ctor_get_uint8(v_c_4154_, 5);
v_proofIrrelevance_4161_ = lean_ctor_get_uint8(v_c_4154_, 6);
v_assignSyntheticOpaque_4162_ = lean_ctor_get_uint8(v_c_4154_, 7);
v_offsetCnstrs_4163_ = lean_ctor_get_uint8(v_c_4154_, 8);
v_transparency_4164_ = lean_ctor_get_uint8(v_c_4154_, 9);
v_univApprox_4165_ = lean_ctor_get_uint8(v_c_4154_, 11);
v_iota_4166_ = lean_ctor_get_uint8(v_c_4154_, 12);
v_beta_4167_ = lean_ctor_get_uint8(v_c_4154_, 13);
v_proj_4168_ = lean_ctor_get_uint8(v_c_4154_, 14);
v_zeta_4169_ = lean_ctor_get_uint8(v_c_4154_, 15);
v_zetaDelta_4170_ = lean_ctor_get_uint8(v_c_4154_, 16);
v_zetaUnused_4171_ = lean_ctor_get_uint8(v_c_4154_, 17);
v_zetaHave_4172_ = lean_ctor_get_uint8(v_c_4154_, 18);
v_isSharedCheck_4180_ = !lean_is_exclusive(v_c_4154_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4174_ = v_c_4154_;
v_isShared_4175_ = v_isSharedCheck_4180_;
goto v_resetjp_4173_;
}
else
{
lean_dec(v_c_4154_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4180_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
uint8_t v___x_4176_; lean_object* v___x_4178_; 
v___x_4176_ = 2;
if (v_isShared_4175_ == 0)
{
v___x_4178_ = v___x_4174_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 0, v_foApprox_4155_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 1, v_ctxApprox_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 2, v_quasiPatternApprox_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 3, v_constApprox_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 4, v_isDefEqStuckEx_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 5, v_unificationHints_4160_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 6, v_proofIrrelevance_4161_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 7, v_assignSyntheticOpaque_4162_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 8, v_offsetCnstrs_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 9, v_transparency_4164_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 11, v_univApprox_4165_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 12, v_iota_4166_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 13, v_beta_4167_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 14, v_proj_4168_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 15, v_zeta_4169_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 16, v_zetaDelta_4170_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 17, v_zetaUnused_4171_);
lean_ctor_set_uint8(v_reuseFailAlloc_4179_, 18, v_zetaHave_4172_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
lean_ctor_set_uint8(v___x_4178_, 10, v___x_4176_);
return v___x_4178_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4181_, lean_object* v_t_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v_dummy_4188_; lean_object* v_nargs_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v_dummy_4188_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4189_ = l_Lean_Expr_getAppNumArgs(v_t_4182_);
lean_inc(v_nargs_4189_);
v___x_4190_ = lean_mk_array(v_nargs_4189_, v_dummy_4188_);
v___x_4191_ = lean_unsigned_to_nat(1u);
v___x_4192_ = lean_nat_sub(v_nargs_4189_, v___x_4191_);
lean_dec(v_nargs_4189_);
v___x_4193_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4182_, v___x_4190_, v___x_4192_);
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4195_, lean_object* v_t_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4195_, v_t_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec_ref(v_x_4195_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4203_, lean_object* v_x_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v_snd_4203_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4211_, lean_object* v_x_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4211_, v_x_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec_ref(v_x_4212_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4219_, size_t v_i_4220_, lean_object* v_bs_4221_){
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
lean_object* v_v_4223_; lean_object* v_fst_4224_; lean_object* v_snd_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4239_; 
v_v_4223_ = lean_array_uget(v_bs_4221_, v_i_4220_);
v_fst_4224_ = lean_ctor_get(v_v_4223_, 0);
v_snd_4225_ = lean_ctor_get(v_v_4223_, 1);
v_isSharedCheck_4239_ = !lean_is_exclusive(v_v_4223_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4227_ = v_v_4223_;
v_isShared_4228_ = v_isSharedCheck_4239_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_snd_4225_);
lean_inc(v_fst_4224_);
lean_dec(v_v_4223_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4239_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4229_; lean_object* v_bs_x27_4230_; lean_object* v___f_4231_; lean_object* v___x_4233_; 
v___x_4229_ = lean_unsigned_to_nat(0u);
v_bs_x27_4230_ = lean_array_uset(v_bs_4221_, v_i_4220_, v___x_4229_);
v___f_4231_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4231_, 0, v_snd_4225_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 1, v___f_4231_);
v___x_4233_ = v___x_4227_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_fst_4224_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v___f_4231_);
v___x_4233_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
size_t v___x_4234_; size_t v___x_4235_; lean_object* v___x_4236_; 
v___x_4234_ = ((size_t)1ULL);
v___x_4235_ = lean_usize_add(v_i_4220_, v___x_4234_);
v___x_4236_ = lean_array_uset(v_bs_x27_4230_, v_i_4220_, v___x_4233_);
v_i_4220_ = v___x_4235_;
v_bs_4221_ = v___x_4236_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4240_, lean_object* v_i_4241_, lean_object* v_bs_4242_){
_start:
{
size_t v_sz_boxed_4243_; size_t v_i_boxed_4244_; lean_object* v_res_4245_; 
v_sz_boxed_4243_ = lean_unbox_usize(v_sz_4240_);
lean_dec(v_sz_4240_);
v_i_boxed_4244_ = lean_unbox_usize(v_i_4241_);
lean_dec(v_i_4241_);
v_res_4245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4243_, v_i_boxed_4244_, v_bs_4242_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4246_, size_t v_i_4247_, lean_object* v_bs_4248_){
_start:
{
uint8_t v___x_4249_; 
v___x_4249_ = lean_usize_dec_lt(v_i_4247_, v_sz_4246_);
if (v___x_4249_ == 0)
{
return v_bs_4248_;
}
else
{
lean_object* v_v_4250_; lean_object* v_fst_4251_; lean_object* v_snd_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4268_; 
v_v_4250_ = lean_array_uget(v_bs_4248_, v_i_4247_);
v_fst_4251_ = lean_ctor_get(v_v_4250_, 0);
v_snd_4252_ = lean_ctor_get(v_v_4250_, 1);
v_isSharedCheck_4268_ = !lean_is_exclusive(v_v_4250_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4254_ = v_v_4250_;
v_isShared_4255_ = v_isSharedCheck_4268_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_snd_4252_);
lean_inc(v_fst_4251_);
lean_dec(v_v_4250_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4268_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4256_; lean_object* v_bs_x27_4257_; uint8_t v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4261_; 
v___x_4256_ = lean_unsigned_to_nat(0u);
v_bs_x27_4257_ = lean_array_uset(v_bs_4248_, v_i_4247_, v___x_4256_);
v___x_4258_ = 0;
v___x_4259_ = lean_box(v___x_4258_);
if (v_isShared_4255_ == 0)
{
lean_ctor_set(v___x_4254_, 0, v___x_4259_);
v___x_4261_ = v___x_4254_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4259_);
lean_ctor_set(v_reuseFailAlloc_4267_, 1, v_snd_4252_);
v___x_4261_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
lean_object* v___x_4262_; size_t v___x_4263_; size_t v___x_4264_; lean_object* v___x_4265_; 
v___x_4262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4262_, 0, v_fst_4251_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
v___x_4263_ = ((size_t)1ULL);
v___x_4264_ = lean_usize_add(v_i_4247_, v___x_4263_);
v___x_4265_ = lean_array_uset(v_bs_x27_4257_, v_i_4247_, v___x_4262_);
v_i_4247_ = v___x_4264_;
v_bs_4248_ = v___x_4265_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4269_, lean_object* v_i_4270_, lean_object* v_bs_4271_){
_start:
{
size_t v_sz_boxed_4272_; size_t v_i_boxed_4273_; lean_object* v_res_4274_; 
v_sz_boxed_4272_ = lean_unbox_usize(v_sz_4269_);
lean_dec(v_sz_4269_);
v_i_boxed_4273_ = lean_unbox_usize(v_i_4270_);
lean_dec(v_i_4270_);
v_res_4274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4272_, v_i_boxed_4273_, v_bs_4271_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4275_, lean_object* v_a_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_21853__overap_4283_; lean_object* v___x_4284_; 
v___x_4282_ = l_Lean_instInhabitedExpr;
v___x_21853__overap_4283_ = l_instInhabitedOfMonad___redArg(v___x_4275_, v___x_4282_);
lean_inc(v___y_4280_);
lean_inc_ref(v___y_4279_);
lean_inc(v___y_4278_);
lean_inc_ref(v___y_4277_);
v___x_4284_ = lean_apply_5(v___x_21853__overap_4283_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, lean_box(0));
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4285_, lean_object* v_a_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4285_, v_a_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec_ref(v_a_4286_);
return v_res_4292_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_instMonadEIO(lean_box(0));
return v___x_4293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4294_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4295_ = l_StateRefT_x27_instMonad___redArg(v___x_4294_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4300_, lean_object* v_declInfos_4301_, lean_object* v_k_4302_, lean_object* v_kind_4303_, lean_object* v_x_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
uint8_t v_kind_boxed_4310_; lean_object* v_res_4311_; 
v_kind_boxed_4310_ = lean_unbox(v_kind_4303_);
v_res_4311_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4300_, v_declInfos_4301_, v_k_4302_, v_kind_boxed_4310_, v_x_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4312_, lean_object* v_k_4313_, uint8_t v_kind_4314_, lean_object* v_acc_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v___x_4321_; lean_object* v_toApplicative_4322_; lean_object* v_toFunctor_4323_; lean_object* v_toSeq_4324_; lean_object* v_toSeqLeft_4325_; lean_object* v_toSeqRight_4326_; lean_object* v___f_4327_; lean_object* v___f_4328_; lean_object* v___f_4329_; lean_object* v___f_4330_; lean_object* v___x_4331_; lean_object* v___f_4332_; lean_object* v___f_4333_; lean_object* v___f_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v_toApplicative_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4387_; 
v___x_4321_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4322_ = lean_ctor_get(v___x_4321_, 0);
v_toFunctor_4323_ = lean_ctor_get(v_toApplicative_4322_, 0);
v_toSeq_4324_ = lean_ctor_get(v_toApplicative_4322_, 2);
v_toSeqLeft_4325_ = lean_ctor_get(v_toApplicative_4322_, 3);
v_toSeqRight_4326_ = lean_ctor_get(v_toApplicative_4322_, 4);
v___f_4327_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4328_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4323_, 2);
v___f_4329_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4329_, 0, v_toFunctor_4323_);
v___f_4330_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4330_, 0, v_toFunctor_4323_);
v___x_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___f_4329_);
lean_ctor_set(v___x_4331_, 1, v___f_4330_);
lean_inc(v_toSeqRight_4326_);
v___f_4332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4332_, 0, v_toSeqRight_4326_);
lean_inc(v_toSeqLeft_4325_);
v___f_4333_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4333_, 0, v_toSeqLeft_4325_);
lean_inc(v_toSeq_4324_);
v___f_4334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4334_, 0, v_toSeq_4324_);
v___x_4335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4331_);
lean_ctor_set(v___x_4335_, 1, v___f_4327_);
lean_ctor_set(v___x_4335_, 2, v___f_4334_);
lean_ctor_set(v___x_4335_, 3, v___f_4333_);
lean_ctor_set(v___x_4335_, 4, v___f_4332_);
v___x_4336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
lean_ctor_set(v___x_4336_, 1, v___f_4328_);
v___x_4337_ = l_StateRefT_x27_instMonad___redArg(v___x_4336_);
v_toApplicative_4338_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4387_ == 0)
{
lean_object* v_unused_4388_; 
v_unused_4388_ = lean_ctor_get(v___x_4337_, 1);
lean_dec(v_unused_4388_);
v___x_4340_ = v___x_4337_;
v_isShared_4341_ = v_isSharedCheck_4387_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_toApplicative_4338_);
lean_dec(v___x_4337_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4387_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v_toFunctor_4342_; lean_object* v_toSeq_4343_; lean_object* v_toSeqLeft_4344_; lean_object* v_toSeqRight_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4385_; 
v_toFunctor_4342_ = lean_ctor_get(v_toApplicative_4338_, 0);
v_toSeq_4343_ = lean_ctor_get(v_toApplicative_4338_, 2);
v_toSeqLeft_4344_ = lean_ctor_get(v_toApplicative_4338_, 3);
v_toSeqRight_4345_ = lean_ctor_get(v_toApplicative_4338_, 4);
v_isSharedCheck_4385_ = !lean_is_exclusive(v_toApplicative_4338_);
if (v_isSharedCheck_4385_ == 0)
{
lean_object* v_unused_4386_; 
v_unused_4386_ = lean_ctor_get(v_toApplicative_4338_, 1);
lean_dec(v_unused_4386_);
v___x_4347_ = v_toApplicative_4338_;
v_isShared_4348_ = v_isSharedCheck_4385_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_toSeqRight_4345_);
lean_inc(v_toSeqLeft_4344_);
lean_inc(v_toSeq_4343_);
lean_inc(v_toFunctor_4342_);
lean_dec(v_toApplicative_4338_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4385_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___f_4349_; lean_object* v___f_4350_; lean_object* v___f_4351_; lean_object* v___f_4352_; lean_object* v___x_4353_; lean_object* v___f_4354_; lean_object* v___f_4355_; lean_object* v___f_4356_; lean_object* v___x_4358_; 
v___f_4349_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4350_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4342_);
v___f_4351_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4351_, 0, v_toFunctor_4342_);
v___f_4352_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4352_, 0, v_toFunctor_4342_);
v___x_4353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___f_4351_);
lean_ctor_set(v___x_4353_, 1, v___f_4352_);
v___f_4354_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4354_, 0, v_toSeqRight_4345_);
v___f_4355_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4355_, 0, v_toSeqLeft_4344_);
v___f_4356_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4356_, 0, v_toSeq_4343_);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 4, v___f_4354_);
lean_ctor_set(v___x_4347_, 3, v___f_4355_);
lean_ctor_set(v___x_4347_, 2, v___f_4356_);
lean_ctor_set(v___x_4347_, 1, v___f_4349_);
lean_ctor_set(v___x_4347_, 0, v___x_4353_);
v___x_4358_ = v___x_4347_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4353_);
lean_ctor_set(v_reuseFailAlloc_4384_, 1, v___f_4349_);
lean_ctor_set(v_reuseFailAlloc_4384_, 2, v___f_4356_);
lean_ctor_set(v_reuseFailAlloc_4384_, 3, v___f_4355_);
lean_ctor_set(v_reuseFailAlloc_4384_, 4, v___f_4354_);
v___x_4358_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
lean_object* v___x_4360_; 
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 1, v___f_4350_);
lean_ctor_set(v___x_4340_, 0, v___x_4358_);
v___x_4360_ = v___x_4340_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4358_);
lean_ctor_set(v_reuseFailAlloc_4383_, 1, v___f_4350_);
v___x_4360_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; 
v___x_4361_ = lean_array_get_size(v_acc_4315_);
v___x_4362_ = lean_array_get_size(v_declInfos_4312_);
v___x_4363_ = lean_nat_dec_lt(v___x_4361_, v___x_4362_);
if (v___x_4363_ == 0)
{
lean_object* v___x_4364_; 
lean_dec_ref(v___x_4360_);
lean_dec_ref(v_declInfos_4312_);
lean_inc(v___y_4319_);
lean_inc_ref(v___y_4318_);
lean_inc(v___y_4317_);
lean_inc_ref(v___y_4316_);
v___x_4364_ = lean_apply_6(v_k_4313_, v_acc_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, lean_box(0));
return v___x_4364_;
}
else
{
lean_object* v___f_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; lean_object* v___f_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v_snd_4373_; lean_object* v_fst_4374_; lean_object* v_fst_4375_; lean_object* v_snd_4376_; lean_object* v___x_4377_; 
v___f_4365_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4365_, 0, v___x_4360_);
v___x_4366_ = lean_box(0);
v___x_4367_ = 0;
v___f_4368_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4368_, 0, v___f_4365_);
v___x_4369_ = lean_box(v___x_4367_);
v___x_4370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4369_);
lean_ctor_set(v___x_4370_, 1, v___f_4368_);
v___x_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4366_);
lean_ctor_set(v___x_4371_, 1, v___x_4370_);
v___x_4372_ = lean_array_get(v___x_4371_, v_declInfos_4312_, v___x_4361_);
lean_dec_ref(v___x_4371_);
v_snd_4373_ = lean_ctor_get(v___x_4372_, 1);
lean_inc(v_snd_4373_);
v_fst_4374_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_fst_4374_);
lean_dec(v___x_4372_);
v_fst_4375_ = lean_ctor_get(v_snd_4373_, 0);
lean_inc(v_fst_4375_);
v_snd_4376_ = lean_ctor_get(v_snd_4373_, 1);
lean_inc(v_snd_4376_);
lean_dec(v_snd_4373_);
lean_inc(v___y_4319_);
lean_inc_ref(v___y_4318_);
lean_inc(v___y_4317_);
lean_inc_ref(v___y_4316_);
lean_inc_ref(v_acc_4315_);
v___x_4377_ = lean_apply_6(v_snd_4376_, v_acc_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, lean_box(0));
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; lean_object* v___f_4380_; uint8_t v___x_4381_; lean_object* v___x_4382_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref(v___x_4377_);
v___x_4379_ = lean_box(v_kind_4314_);
v___f_4380_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4380_, 0, v_acc_4315_);
lean_closure_set(v___f_4380_, 1, v_declInfos_4312_);
lean_closure_set(v___f_4380_, 2, v_k_4313_);
lean_closure_set(v___f_4380_, 3, v___x_4379_);
v___x_4381_ = lean_unbox(v_fst_4375_);
lean_dec(v_fst_4375_);
v___x_4382_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4374_, v___x_4381_, v_a_4378_, v___f_4380_, v_kind_4314_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
return v___x_4382_;
}
else
{
lean_dec(v_fst_4375_);
lean_dec(v_fst_4374_);
lean_dec_ref(v_acc_4315_);
lean_dec_ref(v_k_4313_);
lean_dec_ref(v_declInfos_4312_);
return v___x_4377_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4389_, lean_object* v_declInfos_4390_, lean_object* v_k_4391_, uint8_t v_kind_4392_, lean_object* v_x_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4399_ = lean_array_push(v_acc_4389_, v_x_4393_);
v___x_4400_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4390_, v_k_4391_, v_kind_4392_, v___x_4399_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4401_, lean_object* v_k_4402_, lean_object* v_kind_4403_, lean_object* v_acc_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
uint8_t v_kind_boxed_4410_; lean_object* v_res_4411_; 
v_kind_boxed_4410_ = lean_unbox(v_kind_4403_);
v_res_4411_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4401_, v_k_4402_, v_kind_boxed_4410_, v_acc_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4412_, lean_object* v_k_4413_, uint8_t v_kind_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4420_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4421_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4412_, v_k_4413_, v_kind_4414_, v___x_4420_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4422_, lean_object* v_k_4423_, lean_object* v_kind_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
uint8_t v_kind_boxed_4430_; lean_object* v_res_4431_; 
v_kind_boxed_4430_ = lean_unbox(v_kind_4424_);
v_res_4431_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4422_, v_k_4423_, v_kind_boxed_4430_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4432_, lean_object* v_k_4433_, uint8_t v_kind_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
size_t v_sz_4440_; size_t v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v_sz_4440_ = lean_array_size(v_declInfos_4432_);
v___x_4441_ = ((size_t)0ULL);
v___x_4442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4440_, v___x_4441_, v_declInfos_4432_);
v___x_4443_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4442_, v_k_4433_, v_kind_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4444_, lean_object* v_k_4445_, lean_object* v_kind_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
uint8_t v_kind_boxed_4452_; lean_object* v_res_4453_; 
v_kind_boxed_4452_ = lean_unbox(v_kind_4446_);
v_res_4453_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4444_, v_k_4445_, v_kind_boxed_4452_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4454_, lean_object* v_k_4455_, uint8_t v_kind_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
size_t v_sz_4462_; size_t v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v_sz_4462_ = lean_array_size(v_declInfos_4454_);
v___x_4463_ = ((size_t)0ULL);
v___x_4464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4462_, v___x_4463_, v_declInfos_4454_);
v___x_4465_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4464_, v_k_4455_, v_kind_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4466_, lean_object* v_k_4467_, lean_object* v_kind_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
uint8_t v_kind_boxed_4474_; lean_object* v_res_4475_; 
v_kind_boxed_4474_ = lean_unbox(v_kind_4468_);
v_res_4475_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4466_, v_k_4467_, v_kind_boxed_4474_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(lean_object* v_a_4479_, lean_object* v_b_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_array_4486_; lean_object* v_start_4487_; lean_object* v_stop_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4546_; 
v_array_4486_ = lean_ctor_get(v_a_4479_, 0);
v_start_4487_ = lean_ctor_get(v_a_4479_, 1);
v_stop_4488_ = lean_ctor_get(v_a_4479_, 2);
v_isSharedCheck_4546_ = !lean_is_exclusive(v_a_4479_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4490_ = v_a_4479_;
v_isShared_4491_ = v_isSharedCheck_4546_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_stop_4488_);
lean_inc(v_start_4487_);
lean_inc(v_array_4486_);
lean_dec(v_a_4479_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4546_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
uint8_t v___x_4492_; 
v___x_4492_ = lean_nat_dec_lt(v_start_4487_, v_stop_4488_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; 
lean_del_object(v___x_4490_);
lean_dec(v_stop_4488_);
lean_dec(v_start_4487_);
lean_dec_ref(v_array_4486_);
v___x_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4493_, 0, v_b_4480_);
return v___x_4493_;
}
else
{
lean_object* v_snd_4494_; lean_object* v_fst_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4545_; 
v_snd_4494_ = lean_ctor_get(v_b_4480_, 1);
v_fst_4495_ = lean_ctor_get(v_b_4480_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_b_4480_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4497_ = v_b_4480_;
v_isShared_4498_ = v_isSharedCheck_4545_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_snd_4494_);
lean_inc(v_fst_4495_);
lean_dec(v_b_4480_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4545_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v_array_4499_; lean_object* v_start_4500_; lean_object* v_stop_4501_; uint8_t v___x_4502_; 
v_array_4499_ = lean_ctor_get(v_snd_4494_, 0);
v_start_4500_ = lean_ctor_get(v_snd_4494_, 1);
v_stop_4501_ = lean_ctor_get(v_snd_4494_, 2);
v___x_4502_ = lean_nat_dec_lt(v_start_4500_, v_stop_4501_);
if (v___x_4502_ == 0)
{
lean_object* v___x_4504_; 
lean_del_object(v___x_4490_);
lean_dec(v_stop_4488_);
lean_dec(v_start_4487_);
lean_dec_ref(v_array_4486_);
if (v_isShared_4498_ == 0)
{
v___x_4504_ = v___x_4497_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_fst_4495_);
lean_ctor_set(v_reuseFailAlloc_4506_, 1, v_snd_4494_);
v___x_4504_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
lean_object* v___x_4505_; 
v___x_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
return v___x_4505_;
}
}
else
{
lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4541_; 
lean_inc(v_stop_4501_);
lean_inc(v_start_4500_);
lean_inc_ref(v_array_4499_);
v_isSharedCheck_4541_ = !lean_is_exclusive(v_snd_4494_);
if (v_isSharedCheck_4541_ == 0)
{
lean_object* v_unused_4542_; lean_object* v_unused_4543_; lean_object* v_unused_4544_; 
v_unused_4542_ = lean_ctor_get(v_snd_4494_, 2);
lean_dec(v_unused_4542_);
v_unused_4543_ = lean_ctor_get(v_snd_4494_, 1);
lean_dec(v_unused_4543_);
v_unused_4544_ = lean_ctor_get(v_snd_4494_, 0);
lean_dec(v_unused_4544_);
v___x_4508_ = v_snd_4494_;
v_isShared_4509_ = v_isSharedCheck_4541_;
goto v_resetjp_4507_;
}
else
{
lean_dec(v_snd_4494_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4541_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4510_ = lean_array_fget_borrowed(v_array_4486_, v_start_4487_);
v___x_4511_ = lean_array_fget_borrowed(v_array_4499_, v_start_4500_);
lean_inc(v___x_4511_);
lean_inc(v___x_4510_);
v___x_4512_ = l_Lean_Meta_mkEqHEq(v___x_4510_, v___x_4511_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4517_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_a_4513_);
lean_dec_ref(v___x_4512_);
v___x_4514_ = lean_unsigned_to_nat(1u);
v___x_4515_ = lean_nat_add(v_start_4487_, v___x_4514_);
lean_dec(v_start_4487_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 2, v_stop_4488_);
lean_ctor_set(v___x_4508_, 1, v___x_4515_);
lean_ctor_set(v___x_4508_, 0, v_array_4486_);
v___x_4517_ = v___x_4508_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_array_4486_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v___x_4515_);
lean_ctor_set(v_reuseFailAlloc_4532_, 2, v_stop_4488_);
v___x_4517_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4518_; lean_object* v___x_4520_; 
v___x_4518_ = lean_nat_add(v_start_4500_, v___x_4514_);
lean_dec(v_start_4500_);
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 2, v_stop_4501_);
lean_ctor_set(v___x_4490_, 1, v___x_4518_);
lean_ctor_set(v___x_4490_, 0, v_array_4499_);
v___x_4520_ = v___x_4490_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_array_4499_);
lean_ctor_set(v_reuseFailAlloc_4531_, 1, v___x_4518_);
lean_ctor_set(v_reuseFailAlloc_4531_, 2, v_stop_4501_);
v___x_4520_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4526_; 
v___x_4521_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__1));
v___x_4522_ = lean_array_get_size(v_fst_4495_);
v___x_4523_ = lean_nat_add(v___x_4522_, v___x_4514_);
v___x_4524_ = lean_name_append_index_after(v___x_4521_, v___x_4523_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 1, v_a_4513_);
lean_ctor_set(v___x_4497_, 0, v___x_4524_);
v___x_4526_ = v___x_4497_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4524_);
lean_ctor_set(v_reuseFailAlloc_4530_, 1, v_a_4513_);
v___x_4526_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4527_ = lean_array_push(v_fst_4495_, v___x_4526_);
v___x_4528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
lean_ctor_set(v___x_4528_, 1, v___x_4520_);
v_a_4479_ = v___x_4517_;
v_b_4480_ = v___x_4528_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
lean_del_object(v___x_4508_);
lean_dec(v_stop_4501_);
lean_dec(v_start_4500_);
lean_dec_ref(v_array_4499_);
lean_del_object(v___x_4497_);
lean_dec(v_fst_4495_);
lean_del_object(v___x_4490_);
lean_dec(v_stop_4488_);
lean_dec(v_start_4487_);
lean_dec_ref(v_array_4486_);
v_a_4533_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4512_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4512_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___boxed(lean_object* v_a_4547_, lean_object* v_b_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_4547_, v_b_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v___x_4555_, lean_object* v_a_4556_, lean_object* v___x_4557_, lean_object* v_as_4558_, size_t v_sz_4559_, size_t v_i_4560_, lean_object* v_b_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
uint8_t v___x_4567_; 
v___x_4567_ = lean_usize_dec_lt(v_i_4560_, v_sz_4559_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; 
lean_dec(v___x_4557_);
v___x_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4568_, 0, v_b_4561_);
return v___x_4568_;
}
else
{
lean_object* v___x_4569_; lean_object* v_a_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
v___x_4569_ = l_Lean_instInhabitedExpr;
v_a_4570_ = lean_array_uget_borrowed(v_as_4558_, v_i_4560_);
v___x_4571_ = lean_array_get_borrowed(v___x_4569_, v___x_4555_, v_a_4570_);
lean_inc(v___x_4571_);
v___x_4572_ = l_Lean_Meta_instantiateForall(v___x_4571_, v_a_4556_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_a_4573_; lean_object* v___x_4574_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4573_);
lean_dec_ref(v___x_4572_);
lean_inc(v___x_4557_);
v___x_4574_ = l_Lean_Meta_Match_simpH_x3f(v_a_4573_, v___x_4557_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v_a_4577_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref(v___x_4574_);
if (lean_obj_tag(v_a_4575_) == 1)
{
lean_object* v_val_4581_; lean_object* v___x_4582_; 
v_val_4581_ = lean_ctor_get(v_a_4575_, 0);
lean_inc(v_val_4581_);
lean_dec_ref(v_a_4575_);
v___x_4582_ = lean_array_push(v_b_4561_, v_val_4581_);
v_a_4577_ = v___x_4582_;
goto v___jp_4576_;
}
else
{
lean_dec(v_a_4575_);
v_a_4577_ = v_b_4561_;
goto v___jp_4576_;
}
v___jp_4576_:
{
size_t v___x_4578_; size_t v___x_4579_; 
v___x_4578_ = ((size_t)1ULL);
v___x_4579_ = lean_usize_add(v_i_4560_, v___x_4578_);
v_i_4560_ = v___x_4579_;
v_b_4561_ = v_a_4577_;
goto _start;
}
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_dec_ref(v_b_4561_);
lean_dec(v___x_4557_);
v_a_4583_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4574_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4574_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
else
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4598_; 
lean_dec_ref(v_b_4561_);
lean_dec(v___x_4557_);
v_a_4591_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4593_ = v___x_4572_;
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v___x_4572_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v___x_4599_, lean_object* v_a_4600_, lean_object* v___x_4601_, lean_object* v_as_4602_, lean_object* v_sz_4603_, lean_object* v_i_4604_, lean_object* v_b_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
size_t v_sz_boxed_4611_; size_t v_i_boxed_4612_; lean_object* v_res_4613_; 
v_sz_boxed_4611_ = lean_unbox_usize(v_sz_4603_);
lean_dec(v_sz_4603_);
v_i_boxed_4612_ = lean_unbox_usize(v_i_4604_);
lean_dec(v_i_4604_);
v_res_4613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v___x_4599_, v_a_4600_, v___x_4601_, v_as_4602_, v_sz_boxed_4611_, v_i_boxed_4612_, v_b_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec_ref(v_as_4602_);
lean_dec_ref(v_a_4600_);
lean_dec_ref(v___x_4599_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4614_, lean_object* v_args_4615_, lean_object* v___x_4616_, lean_object* v_overlaps_4617_, lean_object* v_a_4618_, lean_object* v_fst_4619_, lean_object* v_a_4620_, lean_object* v___x_4621_, lean_object* v___x_4622_, lean_object* v___x_4623_, lean_object* v___x_4624_, lean_object* v_altVars_4625_, uint8_t v___x_4626_, uint8_t v___x_4627_, lean_object* v_a_4628_, lean_object* v___x_4629_, lean_object* v___x_4630_, lean_object* v___x_4631_, lean_object* v___x_4632_, lean_object* v___x_4633_, lean_object* v___x_4634_, lean_object* v___x_4635_, lean_object* v_matchDeclName_4636_, lean_object* v___x_4637_, lean_object* v___x_4638_, lean_object* v___x_4639_, lean_object* v_heqs_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = l_Lean_mkAppN(v___y_4614_, v_args_4615_);
lean_inc_ref(v_heqs_4640_);
v___x_4647_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4646_, v_heqs_4640_, v___x_4616_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v___x_4649_; size_t v_sz_4650_; size_t v___x_4651_; lean_object* v___x_4652_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_a_4648_);
lean_dec_ref(v___x_4647_);
v___x_4649_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4617_, v_a_4618_);
v_sz_4650_ = lean_array_size(v___x_4649_);
v___x_4651_ = ((size_t)0ULL);
lean_inc_ref(v___x_4622_);
v___x_4652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_fst_4619_, v_a_4620_, v___x_4621_, v___x_4649_, v_sz_4650_, v___x_4651_, v___x_4622_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
lean_dec_ref(v___x_4649_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v_options_4765_; uint8_t v_hasTrace_4766_; 
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
lean_inc(v_a_4653_);
lean_dec_ref(v___x_4652_);
v_options_4765_ = lean_ctor_get(v___y_4643_, 2);
v_hasTrace_4766_ = lean_ctor_get_uint8(v_options_4765_, sizeof(void*)*1);
if (v_hasTrace_4766_ == 0)
{
v___y_4655_ = v___y_4641_;
v___y_4656_ = v___y_4642_;
v___y_4657_ = v___y_4643_;
v___y_4658_ = v___y_4644_;
goto v___jp_4654_;
}
else
{
lean_object* v_inheritedTraceOptions_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; uint8_t v___x_4770_; 
v_inheritedTraceOptions_4767_ = lean_ctor_get(v___y_4643_, 13);
v___x_4768_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4769_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4770_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4767_, v_options_4765_, v___x_4769_);
if (v___x_4770_ == 0)
{
v___y_4655_ = v___y_4641_;
v___y_4656_ = v___y_4642_;
v___y_4657_ = v___y_4643_;
v___y_4658_ = v___y_4644_;
goto v___jp_4654_;
}
else
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4771_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4653_);
v___x_4772_ = lean_array_to_list(v_a_4653_);
v___x_4773_ = lean_box(0);
v___x_4774_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4772_, v___x_4773_);
v___x_4775_ = l_Lean_MessageData_ofList(v___x_4774_);
v___x_4776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4771_);
lean_ctor_set(v___x_4776_, 1, v___x_4775_);
v___x_4777_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4768_, v___x_4776_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_dec_ref(v___x_4777_);
v___y_4655_ = v___y_4641_;
v___y_4656_ = v___y_4642_;
v___y_4657_ = v___y_4643_;
v___y_4658_ = v___y_4644_;
goto v___jp_4654_;
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
lean_dec(v_a_4653_);
lean_dec(v_a_4648_);
lean_dec_ref(v_heqs_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
lean_dec(v_matchDeclName_4636_);
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___x_4632_);
lean_dec_ref(v___x_4630_);
lean_dec(v___x_4629_);
lean_dec_ref(v___x_4624_);
lean_dec(v___x_4623_);
lean_dec_ref(v___x_4622_);
lean_dec_ref(v_a_4620_);
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4777_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4777_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
}
v___jp_4654_:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; size_t v_sz_4666_; lean_object* v___x_4667_; 
v___x_4659_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4660_ = l_Array_reverse___redArg(v_a_4620_);
v___x_4661_ = lean_array_get_size(v___x_4660_);
v___x_4662_ = l_Array_toSubarray___redArg(v___x_4660_, v___x_4623_, v___x_4661_);
lean_inc_ref(v___x_4624_);
v___x_4663_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4624_, v___x_4622_);
v___x_4664_ = l_Array_reverse___redArg(v___x_4663_);
v___x_4665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4665_, 0, v___x_4659_);
lean_ctor_set(v___x_4665_, 1, v___x_4662_);
v_sz_4666_ = lean_array_size(v___x_4664_);
v___x_4667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4664_, v_sz_4666_, v___x_4651_, v___x_4665_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
lean_dec_ref(v___x_4664_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v_fst_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4755_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref(v___x_4667_);
v_fst_4669_ = lean_ctor_get(v_a_4668_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v_a_4668_);
if (v_isSharedCheck_4755_ == 0)
{
lean_object* v_unused_4756_; 
v_unused_4756_ = lean_ctor_get(v_a_4668_, 1);
lean_dec(v_unused_4756_);
v___x_4671_ = v_a_4668_;
v_isShared_4672_ = v_isSharedCheck_4755_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_fst_4669_);
lean_dec(v_a_4668_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4755_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; uint8_t v___x_4675_; lean_object* v___x_4676_; 
v___x_4673_ = l_Subarray_copy___redArg(v___x_4624_);
lean_inc_ref(v___x_4673_);
v___x_4674_ = l_Array_append___redArg(v___x_4673_, v_altVars_4625_);
v___x_4675_ = 1;
v___x_4676_ = l_Lean_Meta_mkForallFVars(v___x_4674_, v_fst_4669_, v___x_4626_, v___x_4627_, v___x_4627_, v___x_4675_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
lean_dec_ref(v___x_4674_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref(v___x_4676_);
v___x_4678_ = l_Lean_ConstantInfo_name(v_a_4628_);
v___x_4679_ = l_Lean_mkConst(v___x_4678_, v___x_4629_);
lean_inc_ref(v___x_4630_);
v___x_4680_ = l_Subarray_copy___redArg(v___x_4630_);
v___x_4681_ = lean_mk_empty_array_with_capacity(v___x_4631_);
v___x_4682_ = lean_array_push(v___x_4681_, v___x_4632_);
v___x_4683_ = l_Array_append___redArg(v___x_4680_, v___x_4682_);
lean_dec_ref(v___x_4682_);
v___x_4684_ = l_Array_append___redArg(v___x_4683_, v___x_4673_);
lean_dec_ref(v___x_4673_);
v___x_4685_ = l_Subarray_copy___redArg(v___x_4633_);
v___x_4686_ = l_Array_append___redArg(v___x_4684_, v___x_4685_);
lean_dec_ref(v___x_4685_);
v___x_4687_ = l_Lean_mkAppN(v___x_4679_, v___x_4686_);
v___x_4688_ = l_Lean_Meta_mkHEq(v___x_4687_, v_a_4648_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4690_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_a_4689_);
lean_dec_ref(v___x_4688_);
v___x_4690_ = l_Lean_mkArrowN(v_a_4653_, v_a_4689_, v___y_4657_, v___y_4658_);
lean_dec(v_a_4653_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
lean_inc(v_a_4691_);
lean_dec_ref(v___x_4690_);
v___x_4692_ = l_Array_append___redArg(v___x_4686_, v_altVars_4625_);
v___x_4693_ = l_Array_append___redArg(v___x_4692_, v_heqs_4640_);
v___x_4694_ = l_Lean_Meta_mkForallFVars(v___x_4693_, v_a_4691_, v___x_4626_, v___x_4627_, v___x_4627_, v___x_4675_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
lean_dec_ref(v___x_4693_);
if (lean_obj_tag(v___x_4694_) == 0)
{
lean_object* v_a_4695_; lean_object* v___x_4696_; 
v_a_4695_ = lean_ctor_get(v___x_4694_, 0);
lean_inc(v_a_4695_);
lean_dec_ref(v___x_4694_);
v___x_4696_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4695_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4754_; 
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4699_ = v___x_4696_;
v_isShared_4700_ = v_isSharedCheck_4754_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_dec(v___x_4696_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4754_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v_start_4701_; lean_object* v_stop_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4752_; 
v_start_4701_ = lean_ctor_get(v___x_4630_, 1);
v_stop_4702_ = lean_ctor_get(v___x_4630_, 2);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4630_);
if (v_isSharedCheck_4752_ == 0)
{
lean_object* v_unused_4753_; 
v_unused_4753_ = lean_ctor_get(v___x_4630_, 0);
lean_dec(v_unused_4753_);
v___x_4704_ = v___x_4630_;
v_isShared_4705_ = v_isSharedCheck_4752_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_stop_4702_);
lean_inc(v_start_4701_);
lean_dec(v___x_4630_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4752_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4706_ = lean_nat_sub(v_stop_4702_, v_start_4701_);
lean_dec(v_start_4701_);
lean_dec(v_stop_4702_);
v___x_4707_ = lean_nat_add(v___x_4706_, v___x_4631_);
lean_dec(v___x_4706_);
v___x_4708_ = lean_nat_add(v___x_4707_, v___x_4634_);
lean_dec(v___x_4707_);
v___x_4709_ = lean_nat_add(v___x_4708_, v___x_4635_);
lean_dec(v___x_4708_);
v___x_4710_ = lean_array_get_size(v_altVars_4625_);
v___x_4711_ = lean_nat_add(v___x_4709_, v___x_4710_);
lean_dec(v___x_4709_);
v___x_4712_ = lean_array_get_size(v_heqs_4640_);
lean_dec_ref(v_heqs_4640_);
lean_inc(v_a_4697_);
v___x_4713_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4636_, v_a_4697_, v___x_4711_, v___x_4712_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4751_; 
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4716_ = v___x_4713_;
v_isShared_4717_ = v_isSharedCheck_4751_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4713_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4751_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4718_; lean_object* v_env_4719_; uint8_t v___x_4720_; 
v___x_4718_ = lean_st_ref_get(v___y_4658_);
v_env_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc_ref(v_env_4719_);
lean_dec(v___x_4718_);
lean_inc(v___x_4637_);
v___x_4720_ = l_Lean_Environment_contains(v_env_4719_, v___x_4637_, v___x_4627_);
if (v___x_4720_ == 0)
{
lean_object* v___x_4722_; 
lean_del_object(v___x_4716_);
lean_inc(v___x_4637_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 2, v_a_4697_);
lean_ctor_set(v___x_4704_, 1, v___x_4638_);
lean_ctor_set(v___x_4704_, 0, v___x_4637_);
v___x_4722_ = v___x_4704_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4637_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v___x_4638_);
lean_ctor_set(v_reuseFailAlloc_4747_, 2, v_a_4697_);
v___x_4722_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
lean_object* v___x_4724_; 
if (v_isShared_4672_ == 0)
{
lean_ctor_set_tag(v___x_4671_, 1);
lean_ctor_set(v___x_4671_, 1, v___x_4639_);
lean_ctor_set(v___x_4671_, 0, v___x_4637_);
v___x_4724_ = v___x_4671_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4637_);
lean_ctor_set(v_reuseFailAlloc_4746_, 1, v___x_4639_);
v___x_4724_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4725_; lean_object* v___x_4727_; 
v___x_4725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4722_);
lean_ctor_set(v___x_4725_, 1, v_a_4714_);
lean_ctor_set(v___x_4725_, 2, v___x_4724_);
if (v_isShared_4700_ == 0)
{
lean_ctor_set_tag(v___x_4699_, 2);
lean_ctor_set(v___x_4699_, 0, v___x_4725_);
v___x_4727_ = v___x_4699_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4725_);
v___x_4727_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
lean_object* v___x_4728_; 
v___x_4728_ = l_Lean_addDecl(v___x_4727_, v___x_4626_, v___y_4657_, v___y_4658_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4735_; 
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4735_ == 0)
{
lean_object* v_unused_4736_; 
v_unused_4736_ = lean_ctor_get(v___x_4728_, 0);
lean_dec(v_unused_4736_);
v___x_4730_ = v___x_4728_;
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
else
{
lean_dec(v___x_4728_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
lean_ctor_set(v___x_4730_, 0, v_a_4677_);
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4677_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
else
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
lean_dec(v_a_4677_);
v_a_4737_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4728_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4728_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4749_; 
lean_dec(v_a_4714_);
lean_del_object(v___x_4704_);
lean_del_object(v___x_4699_);
lean_dec(v_a_4697_);
lean_del_object(v___x_4671_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v_a_4677_);
v___x_4749_ = v___x_4716_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4677_);
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
else
{
lean_del_object(v___x_4704_);
lean_del_object(v___x_4699_);
lean_dec(v_a_4697_);
lean_dec(v_a_4677_);
lean_del_object(v___x_4671_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
return v___x_4713_;
}
}
}
}
else
{
lean_dec(v_a_4677_);
lean_del_object(v___x_4671_);
lean_dec_ref(v_heqs_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
lean_dec(v_matchDeclName_4636_);
lean_dec_ref(v___x_4630_);
return v___x_4696_;
}
}
else
{
lean_dec(v_a_4677_);
lean_del_object(v___x_4671_);
lean_dec_ref(v_heqs_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
lean_dec(v_matchDeclName_4636_);
lean_dec_ref(v___x_4630_);
return v___x_4694_;
}
}
else
{
lean_dec_ref(v___x_4686_);
lean_dec(v_a_4677_);
lean_del_object(v___x_4671_);
lean_dec_ref(v_heqs_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
lean_dec(v_matchDeclName_4636_);
lean_dec_ref(v___x_4630_);
return v___x_4690_;
}
}
else
{
lean_dec_ref(v___x_4686_);
lean_dec(v_a_4677_);
lean_del_object(v___x_4671_);
lean_dec(v_a_4653_);
lean_dec_ref(v_heqs_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
lean_dec(v_matchDeclName_4636_);
lean_dec_ref(v___x_4630_);
return v___x_4688_;
}
}
else
{
lean_dec_ref(v___x_4673_);
lean_del_object(v___x_4671_);
lean_dec(v_a_4653_);
lean_dec(v_a_4648_);
lean_dec_ref(v_heqs_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
lean_dec(v_matchDeclName_4636_);
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___x_4632_);
lean_dec_ref(v___x_4630_);
lean_dec(v___x_4629_);
return v___x_4676_;
}
}
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
lean_dec(v_a_4653_);
lean_dec(v_a_4648_);
lean_dec_ref(v_heqs_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
lean_dec(v_matchDeclName_4636_);
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___x_4632_);
lean_dec_ref(v___x_4630_);
lean_dec(v___x_4629_);
lean_dec_ref(v___x_4624_);
v_a_4757_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4667_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4667_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec(v_a_4648_);
lean_dec_ref(v_heqs_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
lean_dec(v_matchDeclName_4636_);
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___x_4632_);
lean_dec_ref(v___x_4630_);
lean_dec(v___x_4629_);
lean_dec_ref(v___x_4624_);
lean_dec(v___x_4623_);
lean_dec_ref(v___x_4622_);
lean_dec_ref(v_a_4620_);
v_a_4786_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4652_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4652_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v___x_4637_);
lean_dec(v_matchDeclName_4636_);
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___x_4632_);
lean_dec_ref(v___x_4630_);
lean_dec(v___x_4629_);
lean_dec_ref(v___x_4624_);
lean_dec(v___x_4623_);
lean_dec_ref(v___x_4622_);
lean_dec(v___x_4621_);
lean_dec_ref(v_a_4620_);
return v___x_4647_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4794_ = _args[0];
lean_object* v_args_4795_ = _args[1];
lean_object* v___x_4796_ = _args[2];
lean_object* v_overlaps_4797_ = _args[3];
lean_object* v_a_4798_ = _args[4];
lean_object* v_fst_4799_ = _args[5];
lean_object* v_a_4800_ = _args[6];
lean_object* v___x_4801_ = _args[7];
lean_object* v___x_4802_ = _args[8];
lean_object* v___x_4803_ = _args[9];
lean_object* v___x_4804_ = _args[10];
lean_object* v_altVars_4805_ = _args[11];
lean_object* v___x_4806_ = _args[12];
lean_object* v___x_4807_ = _args[13];
lean_object* v_a_4808_ = _args[14];
lean_object* v___x_4809_ = _args[15];
lean_object* v___x_4810_ = _args[16];
lean_object* v___x_4811_ = _args[17];
lean_object* v___x_4812_ = _args[18];
lean_object* v___x_4813_ = _args[19];
lean_object* v___x_4814_ = _args[20];
lean_object* v___x_4815_ = _args[21];
lean_object* v_matchDeclName_4816_ = _args[22];
lean_object* v___x_4817_ = _args[23];
lean_object* v___x_4818_ = _args[24];
lean_object* v___x_4819_ = _args[25];
lean_object* v_heqs_4820_ = _args[26];
lean_object* v___y_4821_ = _args[27];
lean_object* v___y_4822_ = _args[28];
lean_object* v___y_4823_ = _args[29];
lean_object* v___y_4824_ = _args[30];
lean_object* v___y_4825_ = _args[31];
_start:
{
uint8_t v___x_22593__boxed_4826_; uint8_t v___x_22594__boxed_4827_; lean_object* v_res_4828_; 
v___x_22593__boxed_4826_ = lean_unbox(v___x_4806_);
v___x_22594__boxed_4827_ = lean_unbox(v___x_4807_);
v_res_4828_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4794_, v_args_4795_, v___x_4796_, v_overlaps_4797_, v_a_4798_, v_fst_4799_, v_a_4800_, v___x_4801_, v___x_4802_, v___x_4803_, v___x_4804_, v_altVars_4805_, v___x_22593__boxed_4826_, v___x_22594__boxed_4827_, v_a_4808_, v___x_4809_, v___x_4810_, v___x_4811_, v___x_4812_, v___x_4813_, v___x_4814_, v___x_4815_, v_matchDeclName_4816_, v___x_4817_, v___x_4818_, v___x_4819_, v_heqs_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec(v___x_4815_);
lean_dec(v___x_4814_);
lean_dec(v___x_4811_);
lean_dec_ref(v_a_4808_);
lean_dec_ref(v_altVars_4805_);
lean_dec(v_fst_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_overlaps_4797_);
lean_dec_ref(v_args_4795_);
return v_res_4828_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4831_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4832_ = lean_unsigned_to_nat(8u);
v___x_4833_ = lean_unsigned_to_nat(295u);
v___x_4834_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4835_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4836_ = l_mkPanicMessageWithDecl(v___x_4835_, v___x_4834_, v___x_4833_, v___x_4832_, v___x_4831_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4837_, lean_object* v___x_4838_, lean_object* v___x_4839_, lean_object* v___y_4840_, lean_object* v___x_4841_, lean_object* v_overlaps_4842_, lean_object* v_a_4843_, lean_object* v_fst_4844_, lean_object* v___x_4845_, lean_object* v_a_4846_, lean_object* v___x_4847_, lean_object* v___x_4848_, lean_object* v___x_4849_, lean_object* v___x_4850_, lean_object* v___x_4851_, lean_object* v___x_4852_, lean_object* v_matchDeclName_4853_, lean_object* v___x_4854_, lean_object* v___x_4855_, lean_object* v___x_4856_, lean_object* v_altVars_4857_, lean_object* v_args_4858_, lean_object* v___mask_4859_, lean_object* v_altResultType_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
uint8_t v___x_4866_; lean_object* v___x_4867_; 
v___x_4866_ = 0;
v___x_4867_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4860_, v___f_4837_, v___x_4866_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v_start_4869_; lean_object* v_stop_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; uint8_t v___x_4873_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
lean_inc(v_a_4868_);
lean_dec_ref(v___x_4867_);
v_start_4869_ = lean_ctor_get(v___x_4838_, 1);
v_stop_4870_ = lean_ctor_get(v___x_4838_, 2);
v___x_4871_ = lean_array_get_size(v_a_4868_);
v___x_4872_ = lean_nat_sub(v_stop_4870_, v_start_4869_);
v___x_4873_ = lean_nat_dec_eq(v___x_4871_, v___x_4872_);
if (v___x_4873_ == 0)
{
lean_object* v___x_4874_; lean_object* v___x_4875_; 
lean_dec(v___x_4872_);
lean_dec(v_a_4868_);
lean_dec_ref(v_args_4858_);
lean_dec_ref(v_altVars_4857_);
lean_dec(v___x_4856_);
lean_dec(v___x_4855_);
lean_dec(v___x_4854_);
lean_dec(v_matchDeclName_4853_);
lean_dec(v___x_4852_);
lean_dec_ref(v___x_4851_);
lean_dec_ref(v___x_4850_);
lean_dec(v___x_4849_);
lean_dec_ref(v___x_4848_);
lean_dec(v___x_4847_);
lean_dec_ref(v_a_4846_);
lean_dec_ref(v___x_4845_);
lean_dec(v_fst_4844_);
lean_dec(v_a_4843_);
lean_dec_ref(v_overlaps_4842_);
lean_dec(v___x_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v___x_4839_);
lean_dec_ref(v___x_4838_);
v___x_4874_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4875_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4874_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
return v___x_4875_;
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4876_ = lean_mk_empty_array_with_capacity(v___x_4839_);
lean_inc(v___x_4839_);
lean_inc(v_a_4868_);
v___x_4877_ = l_Array_toSubarray___redArg(v_a_4868_, v___x_4839_, v___x_4871_);
v___x_4878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4876_);
lean_ctor_set(v___x_4878_, 1, v___x_4877_);
lean_inc_ref(v___x_4838_);
v___x_4879_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v___x_4838_, v___x_4878_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v_a_4880_; lean_object* v_fst_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___f_4884_; uint8_t v___x_4885_; lean_object* v___x_4886_; 
v_a_4880_ = lean_ctor_get(v___x_4879_, 0);
lean_inc(v_a_4880_);
lean_dec_ref(v___x_4879_);
v_fst_4881_ = lean_ctor_get(v_a_4880_, 0);
lean_inc(v_fst_4881_);
lean_dec(v_a_4880_);
v___x_4882_ = lean_box(v___x_4866_);
v___x_4883_ = lean_box(v___x_4873_);
v___f_4884_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4884_, 0, v___y_4840_);
lean_closure_set(v___f_4884_, 1, v_args_4858_);
lean_closure_set(v___f_4884_, 2, v___x_4841_);
lean_closure_set(v___f_4884_, 3, v_overlaps_4842_);
lean_closure_set(v___f_4884_, 4, v_a_4843_);
lean_closure_set(v___f_4884_, 5, v_fst_4844_);
lean_closure_set(v___f_4884_, 6, v_a_4868_);
lean_closure_set(v___f_4884_, 7, v___x_4871_);
lean_closure_set(v___f_4884_, 8, v___x_4845_);
lean_closure_set(v___f_4884_, 9, v___x_4839_);
lean_closure_set(v___f_4884_, 10, v___x_4838_);
lean_closure_set(v___f_4884_, 11, v_altVars_4857_);
lean_closure_set(v___f_4884_, 12, v___x_4882_);
lean_closure_set(v___f_4884_, 13, v___x_4883_);
lean_closure_set(v___f_4884_, 14, v_a_4846_);
lean_closure_set(v___f_4884_, 15, v___x_4847_);
lean_closure_set(v___f_4884_, 16, v___x_4848_);
lean_closure_set(v___f_4884_, 17, v___x_4849_);
lean_closure_set(v___f_4884_, 18, v___x_4850_);
lean_closure_set(v___f_4884_, 19, v___x_4851_);
lean_closure_set(v___f_4884_, 20, v___x_4872_);
lean_closure_set(v___f_4884_, 21, v___x_4852_);
lean_closure_set(v___f_4884_, 22, v_matchDeclName_4853_);
lean_closure_set(v___f_4884_, 23, v___x_4854_);
lean_closure_set(v___f_4884_, 24, v___x_4855_);
lean_closure_set(v___f_4884_, 25, v___x_4856_);
v___x_4885_ = 0;
v___x_4886_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4881_, v___f_4884_, v___x_4885_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
return v___x_4886_;
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
lean_dec(v___x_4872_);
lean_dec(v_a_4868_);
lean_dec_ref(v_args_4858_);
lean_dec_ref(v_altVars_4857_);
lean_dec(v___x_4856_);
lean_dec(v___x_4855_);
lean_dec(v___x_4854_);
lean_dec(v_matchDeclName_4853_);
lean_dec(v___x_4852_);
lean_dec_ref(v___x_4851_);
lean_dec_ref(v___x_4850_);
lean_dec(v___x_4849_);
lean_dec_ref(v___x_4848_);
lean_dec(v___x_4847_);
lean_dec_ref(v_a_4846_);
lean_dec_ref(v___x_4845_);
lean_dec(v_fst_4844_);
lean_dec(v_a_4843_);
lean_dec_ref(v_overlaps_4842_);
lean_dec(v___x_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v___x_4839_);
lean_dec_ref(v___x_4838_);
v_a_4887_ = lean_ctor_get(v___x_4879_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4879_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4879_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
lean_dec_ref(v_args_4858_);
lean_dec_ref(v_altVars_4857_);
lean_dec(v___x_4856_);
lean_dec(v___x_4855_);
lean_dec(v___x_4854_);
lean_dec(v_matchDeclName_4853_);
lean_dec(v___x_4852_);
lean_dec_ref(v___x_4851_);
lean_dec_ref(v___x_4850_);
lean_dec(v___x_4849_);
lean_dec_ref(v___x_4848_);
lean_dec(v___x_4847_);
lean_dec_ref(v_a_4846_);
lean_dec_ref(v___x_4845_);
lean_dec(v_fst_4844_);
lean_dec(v_a_4843_);
lean_dec_ref(v_overlaps_4842_);
lean_dec(v___x_4841_);
lean_dec_ref(v___y_4840_);
lean_dec(v___x_4839_);
lean_dec_ref(v___x_4838_);
v_a_4895_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4867_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4867_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4903_ = _args[0];
lean_object* v___x_4904_ = _args[1];
lean_object* v___x_4905_ = _args[2];
lean_object* v___y_4906_ = _args[3];
lean_object* v___x_4907_ = _args[4];
lean_object* v_overlaps_4908_ = _args[5];
lean_object* v_a_4909_ = _args[6];
lean_object* v_fst_4910_ = _args[7];
lean_object* v___x_4911_ = _args[8];
lean_object* v_a_4912_ = _args[9];
lean_object* v___x_4913_ = _args[10];
lean_object* v___x_4914_ = _args[11];
lean_object* v___x_4915_ = _args[12];
lean_object* v___x_4916_ = _args[13];
lean_object* v___x_4917_ = _args[14];
lean_object* v___x_4918_ = _args[15];
lean_object* v_matchDeclName_4919_ = _args[16];
lean_object* v___x_4920_ = _args[17];
lean_object* v___x_4921_ = _args[18];
lean_object* v___x_4922_ = _args[19];
lean_object* v_altVars_4923_ = _args[20];
lean_object* v_args_4924_ = _args[21];
lean_object* v___mask_4925_ = _args[22];
lean_object* v_altResultType_4926_ = _args[23];
lean_object* v___y_4927_ = _args[24];
lean_object* v___y_4928_ = _args[25];
lean_object* v___y_4929_ = _args[26];
lean_object* v___y_4930_ = _args[27];
lean_object* v___y_4931_ = _args[28];
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4903_, v___x_4904_, v___x_4905_, v___y_4906_, v___x_4907_, v_overlaps_4908_, v_a_4909_, v_fst_4910_, v___x_4911_, v_a_4912_, v___x_4913_, v___x_4914_, v___x_4915_, v___x_4916_, v___x_4917_, v___x_4918_, v_matchDeclName_4919_, v___x_4920_, v___x_4921_, v___x_4922_, v_altVars_4923_, v_args_4924_, v___mask_4925_, v_altResultType_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
lean_dec(v___y_4930_);
lean_dec_ref(v___y_4929_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
lean_dec_ref(v___mask_4925_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4934_, lean_object* v_val_4935_, lean_object* v_matchDeclName_4936_, lean_object* v___x_4937_, lean_object* v___x_4938_, lean_object* v_a_4939_, lean_object* v___x_4940_, lean_object* v___x_4941_, lean_object* v___x_4942_, lean_object* v___x_4943_, lean_object* v___x_4944_, lean_object* v___x_4945_, lean_object* v_a_4946_, lean_object* v_b_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
uint8_t v___x_4953_; 
v___x_4953_ = lean_nat_dec_lt(v_a_4946_, v_upperBound_4934_);
if (v___x_4953_ == 0)
{
lean_object* v___x_4954_; 
lean_dec(v_a_4946_);
lean_dec(v___x_4945_);
lean_dec(v___x_4944_);
lean_dec_ref(v___x_4943_);
lean_dec_ref(v___x_4942_);
lean_dec_ref(v___x_4941_);
lean_dec(v___x_4940_);
lean_dec_ref(v_a_4939_);
lean_dec(v___x_4938_);
lean_dec_ref(v___x_4937_);
lean_dec(v_matchDeclName_4936_);
lean_dec_ref(v_val_4935_);
v___x_4954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4954_, 0, v_b_4947_);
return v___x_4954_;
}
else
{
lean_object* v_snd_4955_; lean_object* v_fst_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_5019_; 
v_snd_4955_ = lean_ctor_get(v_b_4947_, 1);
v_fst_4956_ = lean_ctor_get(v_b_4947_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v_b_4947_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_4958_ = v_b_4947_;
v_isShared_4959_ = v_isSharedCheck_5019_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_snd_4955_);
lean_inc(v_fst_4956_);
lean_dec(v_b_4947_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_5019_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v_fst_4960_; lean_object* v_snd_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_5018_; 
v_fst_4960_ = lean_ctor_get(v_snd_4955_, 0);
v_snd_4961_ = lean_ctor_get(v_snd_4955_, 1);
v_isSharedCheck_5018_ = !lean_is_exclusive(v_snd_4955_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_4963_ = v_snd_4955_;
v_isShared_4964_ = v_isSharedCheck_5018_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_snd_4961_);
lean_inc(v_fst_4960_);
lean_dec(v_snd_4955_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_5018_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v_altInfos_4965_; lean_object* v_overlaps_4966_; lean_object* v_start_4967_; lean_object* v_stop_4968_; lean_object* v___f_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___y_4981_; lean_object* v___x_5013_; uint8_t v___x_5014_; 
v_altInfos_4965_ = lean_ctor_get(v_val_4935_, 2);
v_overlaps_4966_ = lean_ctor_get(v_val_4935_, 5);
v_start_4967_ = lean_ctor_get(v___x_4943_, 1);
v_stop_4968_ = lean_ctor_get(v___x_4943_, 2);
v___f_4969_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4970_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4971_ = lean_unsigned_to_nat(0u);
v___x_4972_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4973_ = lean_unsigned_to_nat(1u);
v___x_4974_ = lean_box(0);
v___x_4975_ = lean_array_get_borrowed(v___x_4970_, v_altInfos_4965_, v_a_4946_);
v___x_4976_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4936_);
v___x_4977_ = l_Lean_Name_str___override(v_matchDeclName_4936_, v___x_4976_);
lean_inc(v_snd_4961_);
v___x_4978_ = lean_name_append_index_after(v___x_4977_, v_snd_4961_);
lean_inc(v___x_4978_);
v___x_4979_ = lean_array_push(v_fst_4956_, v___x_4978_);
v___x_5013_ = lean_nat_sub(v_stop_4968_, v_start_4967_);
v___x_5014_ = lean_nat_dec_lt(v_a_4946_, v___x_5013_);
lean_dec(v___x_5013_);
if (v___x_5014_ == 0)
{
lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5015_ = l_Lean_instInhabitedExpr;
v___x_5016_ = l_outOfBounds___redArg(v___x_5015_);
v___y_4981_ = v___x_5016_;
goto v___jp_4980_;
}
else
{
lean_object* v___x_5017_; 
v___x_5017_ = l_Subarray_get___redArg(v___x_4943_, v_a_4946_);
v___y_4981_ = v___x_5017_;
goto v___jp_4980_;
}
v___jp_4980_:
{
lean_object* v___x_4982_; 
lean_inc(v___y_4951_);
lean_inc_ref(v___y_4950_);
lean_inc(v___y_4949_);
lean_inc_ref(v___y_4948_);
lean_inc_ref(v___y_4981_);
v___x_4982_ = lean_infer_type(v___y_4981_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___f_4984_; lean_object* v___x_4985_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref(v___x_4982_);
lean_inc(v___x_4945_);
lean_inc(v_matchDeclName_4936_);
lean_inc(v___x_4944_);
lean_inc_ref(v___x_4943_);
lean_inc_ref(v___x_4942_);
lean_inc_ref(v___x_4941_);
lean_inc(v___x_4940_);
lean_inc_ref(v_a_4939_);
lean_inc(v_fst_4960_);
lean_inc(v_a_4946_);
lean_inc_ref(v_overlaps_4966_);
lean_inc(v___x_4938_);
lean_inc_ref(v___x_4937_);
v___f_4984_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 29, 20);
lean_closure_set(v___f_4984_, 0, v___f_4969_);
lean_closure_set(v___f_4984_, 1, v___x_4937_);
lean_closure_set(v___f_4984_, 2, v___x_4971_);
lean_closure_set(v___f_4984_, 3, v___y_4981_);
lean_closure_set(v___f_4984_, 4, v___x_4938_);
lean_closure_set(v___f_4984_, 5, v_overlaps_4966_);
lean_closure_set(v___f_4984_, 6, v_a_4946_);
lean_closure_set(v___f_4984_, 7, v_fst_4960_);
lean_closure_set(v___f_4984_, 8, v___x_4972_);
lean_closure_set(v___f_4984_, 9, v_a_4939_);
lean_closure_set(v___f_4984_, 10, v___x_4940_);
lean_closure_set(v___f_4984_, 11, v___x_4941_);
lean_closure_set(v___f_4984_, 12, v___x_4973_);
lean_closure_set(v___f_4984_, 13, v___x_4942_);
lean_closure_set(v___f_4984_, 14, v___x_4943_);
lean_closure_set(v___f_4984_, 15, v___x_4944_);
lean_closure_set(v___f_4984_, 16, v_matchDeclName_4936_);
lean_closure_set(v___f_4984_, 17, v___x_4978_);
lean_closure_set(v___f_4984_, 18, v___x_4945_);
lean_closure_set(v___f_4984_, 19, v___x_4974_);
lean_inc(v___x_4975_);
v___x_4985_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4983_, v___x_4975_, v___f_4984_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4990_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4986_);
lean_dec_ref(v___x_4985_);
v___x_4987_ = lean_array_push(v_fst_4960_, v_a_4986_);
v___x_4988_ = lean_nat_add(v_snd_4961_, v___x_4973_);
lean_dec(v_snd_4961_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 1, v___x_4988_);
lean_ctor_set(v___x_4963_, 0, v___x_4987_);
v___x_4990_ = v___x_4963_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4987_);
lean_ctor_set(v_reuseFailAlloc_4996_, 1, v___x_4988_);
v___x_4990_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
lean_object* v___x_4992_; 
if (v_isShared_4959_ == 0)
{
lean_ctor_set(v___x_4958_, 1, v___x_4990_);
lean_ctor_set(v___x_4958_, 0, v___x_4979_);
v___x_4992_ = v___x_4958_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v___x_4979_);
lean_ctor_set(v_reuseFailAlloc_4995_, 1, v___x_4990_);
v___x_4992_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
lean_object* v___x_4993_; 
v___x_4993_ = lean_nat_add(v_a_4946_, v___x_4973_);
lean_dec(v_a_4946_);
v_a_4946_ = v___x_4993_;
v_b_4947_ = v___x_4992_;
goto _start;
}
}
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
lean_dec_ref(v___x_4979_);
lean_del_object(v___x_4963_);
lean_dec(v_snd_4961_);
lean_dec(v_fst_4960_);
lean_del_object(v___x_4958_);
lean_dec(v_a_4946_);
lean_dec(v___x_4945_);
lean_dec(v___x_4944_);
lean_dec_ref(v___x_4943_);
lean_dec_ref(v___x_4942_);
lean_dec_ref(v___x_4941_);
lean_dec(v___x_4940_);
lean_dec_ref(v_a_4939_);
lean_dec(v___x_4938_);
lean_dec_ref(v___x_4937_);
lean_dec(v_matchDeclName_4936_);
lean_dec_ref(v_val_4935_);
v_a_4997_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v___x_4985_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4985_);
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
else
{
lean_object* v_a_5005_; lean_object* v___x_5007_; uint8_t v_isShared_5008_; uint8_t v_isSharedCheck_5012_; 
lean_dec_ref(v___y_4981_);
lean_dec_ref(v___x_4979_);
lean_dec(v___x_4978_);
lean_del_object(v___x_4963_);
lean_dec(v_snd_4961_);
lean_dec(v_fst_4960_);
lean_del_object(v___x_4958_);
lean_dec(v_a_4946_);
lean_dec(v___x_4945_);
lean_dec(v___x_4944_);
lean_dec_ref(v___x_4943_);
lean_dec_ref(v___x_4942_);
lean_dec_ref(v___x_4941_);
lean_dec(v___x_4940_);
lean_dec_ref(v_a_4939_);
lean_dec(v___x_4938_);
lean_dec_ref(v___x_4937_);
lean_dec(v_matchDeclName_4936_);
lean_dec_ref(v_val_4935_);
v_a_5005_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5012_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5012_ == 0)
{
v___x_5007_ = v___x_4982_;
v_isShared_5008_ = v_isSharedCheck_5012_;
goto v_resetjp_5006_;
}
else
{
lean_inc(v_a_5005_);
lean_dec(v___x_4982_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5020_ = _args[0];
lean_object* v_val_5021_ = _args[1];
lean_object* v_matchDeclName_5022_ = _args[2];
lean_object* v___x_5023_ = _args[3];
lean_object* v___x_5024_ = _args[4];
lean_object* v_a_5025_ = _args[5];
lean_object* v___x_5026_ = _args[6];
lean_object* v___x_5027_ = _args[7];
lean_object* v___x_5028_ = _args[8];
lean_object* v___x_5029_ = _args[9];
lean_object* v___x_5030_ = _args[10];
lean_object* v___x_5031_ = _args[11];
lean_object* v_a_5032_ = _args[12];
lean_object* v_b_5033_ = _args[13];
lean_object* v___y_5034_ = _args[14];
lean_object* v___y_5035_ = _args[15];
lean_object* v___y_5036_ = _args[16];
lean_object* v___y_5037_ = _args[17];
lean_object* v___y_5038_ = _args[18];
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5020_, v_val_5021_, v_matchDeclName_5022_, v___x_5023_, v___x_5024_, v_a_5025_, v___x_5026_, v___x_5027_, v___x_5028_, v___x_5029_, v___x_5030_, v___x_5031_, v_a_5032_, v_b_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_);
lean_dec(v___y_5037_);
lean_dec_ref(v___y_5036_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v_upperBound_5020_);
return v_res_5039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5046_, lean_object* v___x_5047_, lean_object* v_matchDeclName_5048_, lean_object* v___x_5049_, lean_object* v_a_5050_, lean_object* v___x_5051_, lean_object* v___x_5052_, lean_object* v_xs_5053_, lean_object* v___matchResultType_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v_numParams_5060_; lean_object* v_numDiscrs_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v_lower_5067_; lean_object* v_upper_5068_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; uint8_t v___x_5099_; 
v_numParams_5060_ = lean_ctor_get(v_val_5046_, 0);
v_numDiscrs_5061_ = lean_ctor_get(v_val_5046_, 1);
v___x_5062_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5060_);
lean_inc_ref(v_xs_5053_);
v___x_5063_ = l_Array_toSubarray___redArg(v_xs_5053_, v___x_5062_, v_numParams_5060_);
v___x_5064_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5046_);
v___x_5065_ = lean_array_get(v___x_5047_, v_xs_5053_, v___x_5064_);
lean_dec(v___x_5064_);
v___x_5096_ = lean_array_get_size(v_xs_5053_);
v___x_5097_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5046_);
v___x_5098_ = lean_nat_sub(v___x_5096_, v___x_5097_);
lean_dec(v___x_5097_);
v___x_5099_ = lean_nat_dec_le(v___x_5098_, v___x_5062_);
if (v___x_5099_ == 0)
{
v_lower_5067_ = v___x_5098_;
v_upper_5068_ = v___x_5096_;
goto v___jp_5066_;
}
else
{
lean_dec(v___x_5098_);
v_lower_5067_ = v___x_5062_;
v_upper_5068_ = v___x_5096_;
goto v___jp_5066_;
}
v___jp_5066_:
{
lean_object* v___x_5069_; lean_object* v_start_5070_; lean_object* v_stop_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; 
lean_inc_ref(v_xs_5053_);
v___x_5069_ = l_Array_toSubarray___redArg(v_xs_5053_, v_lower_5067_, v_upper_5068_);
v_start_5070_ = lean_ctor_get(v___x_5069_, 1);
lean_inc(v_start_5070_);
v_stop_5071_ = lean_ctor_get(v___x_5069_, 2);
lean_inc(v_stop_5071_);
v___x_5072_ = lean_unsigned_to_nat(1u);
v___x_5073_ = lean_nat_add(v_numParams_5060_, v___x_5072_);
v___x_5074_ = lean_nat_add(v___x_5073_, v_numDiscrs_5061_);
v___x_5075_ = lean_nat_sub(v_stop_5071_, v_start_5070_);
lean_dec(v_start_5070_);
lean_dec(v_stop_5071_);
v___x_5076_ = l_Array_toSubarray___redArg(v_xs_5053_, v___x_5073_, v___x_5074_);
v___x_5077_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5075_);
v___x_5078_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5075_, v_val_5046_, v_matchDeclName_5048_, v___x_5076_, v___x_5049_, v_a_5050_, v___x_5051_, v___x_5063_, v___x_5065_, v___x_5069_, v___x_5075_, v___x_5052_, v___x_5062_, v___x_5077_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
lean_dec(v___x_5075_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_object* v___x_5080_; uint8_t v_isShared_5081_; uint8_t v_isSharedCheck_5086_; 
v_isSharedCheck_5086_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5086_ == 0)
{
lean_object* v_unused_5087_; 
v_unused_5087_ = lean_ctor_get(v___x_5078_, 0);
lean_dec(v_unused_5087_);
v___x_5080_ = v___x_5078_;
v_isShared_5081_ = v_isSharedCheck_5086_;
goto v_resetjp_5079_;
}
else
{
lean_dec(v___x_5078_);
v___x_5080_ = lean_box(0);
v_isShared_5081_ = v_isSharedCheck_5086_;
goto v_resetjp_5079_;
}
v_resetjp_5079_:
{
lean_object* v___x_5082_; lean_object* v___x_5084_; 
v___x_5082_ = lean_box(0);
if (v_isShared_5081_ == 0)
{
lean_ctor_set(v___x_5080_, 0, v___x_5082_);
v___x_5084_ = v___x_5080_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5082_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
return v___x_5084_;
}
}
}
else
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
v_a_5088_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___x_5078_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5078_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5093_; 
if (v_isShared_5091_ == 0)
{
v___x_5093_ = v___x_5090_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_a_5088_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5100_, lean_object* v___x_5101_, lean_object* v_matchDeclName_5102_, lean_object* v___x_5103_, lean_object* v_a_5104_, lean_object* v___x_5105_, lean_object* v___x_5106_, lean_object* v_xs_5107_, lean_object* v___matchResultType_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5100_, v___x_5101_, v_matchDeclName_5102_, v___x_5103_, v_a_5104_, v___x_5105_, v___x_5106_, v_xs_5107_, v___matchResultType_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
lean_dec(v___y_5112_);
lean_dec_ref(v___y_5111_);
lean_dec(v___y_5110_);
lean_dec_ref(v___y_5109_);
lean_dec_ref(v___matchResultType_5108_);
lean_dec_ref(v___x_5101_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_){
_start:
{
uint8_t v_trackZetaDelta_5121_; lean_object* v_zetaDeltaSet_5122_; lean_object* v_lctx_5123_; lean_object* v_localInstances_5124_; lean_object* v_defEqCtx_x3f_5125_; lean_object* v_synthPendingDepth_5126_; lean_object* v_canUnfold_x3f_5127_; uint8_t v_univApprox_5128_; uint8_t v_inTypeClassResolution_5129_; uint8_t v_cacheInferType_5130_; lean_object* v___x_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5174_; 
v_trackZetaDelta_5121_ = lean_ctor_get_uint8(v_a_5116_, sizeof(void*)*7);
v_zetaDeltaSet_5122_ = lean_ctor_get(v_a_5116_, 1);
lean_inc(v_zetaDeltaSet_5122_);
v_lctx_5123_ = lean_ctor_get(v_a_5116_, 2);
lean_inc_ref(v_lctx_5123_);
v_localInstances_5124_ = lean_ctor_get(v_a_5116_, 3);
lean_inc_ref(v_localInstances_5124_);
v_defEqCtx_x3f_5125_ = lean_ctor_get(v_a_5116_, 4);
lean_inc(v_defEqCtx_x3f_5125_);
v_synthPendingDepth_5126_ = lean_ctor_get(v_a_5116_, 5);
lean_inc(v_synthPendingDepth_5126_);
v_canUnfold_x3f_5127_ = lean_ctor_get(v_a_5116_, 6);
lean_inc(v_canUnfold_x3f_5127_);
v_univApprox_5128_ = lean_ctor_get_uint8(v_a_5116_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5129_ = lean_ctor_get_uint8(v_a_5116_, sizeof(void*)*7 + 2);
v_cacheInferType_5130_ = lean_ctor_get_uint8(v_a_5116_, sizeof(void*)*7 + 3);
v___x_5131_ = l_Lean_Meta_Context_config(v_a_5116_);
v_isSharedCheck_5174_ = !lean_is_exclusive(v_a_5116_);
if (v_isSharedCheck_5174_ == 0)
{
lean_object* v_unused_5175_; lean_object* v_unused_5176_; lean_object* v_unused_5177_; lean_object* v_unused_5178_; lean_object* v_unused_5179_; lean_object* v_unused_5180_; lean_object* v_unused_5181_; 
v_unused_5175_ = lean_ctor_get(v_a_5116_, 6);
lean_dec(v_unused_5175_);
v_unused_5176_ = lean_ctor_get(v_a_5116_, 5);
lean_dec(v_unused_5176_);
v_unused_5177_ = lean_ctor_get(v_a_5116_, 4);
lean_dec(v_unused_5177_);
v_unused_5178_ = lean_ctor_get(v_a_5116_, 3);
lean_dec(v_unused_5178_);
v_unused_5179_ = lean_ctor_get(v_a_5116_, 2);
lean_dec(v_unused_5179_);
v_unused_5180_ = lean_ctor_get(v_a_5116_, 1);
lean_dec(v_unused_5180_);
v_unused_5181_ = lean_ctor_get(v_a_5116_, 0);
lean_dec(v_unused_5181_);
v___x_5133_ = v_a_5116_;
v_isShared_5134_ = v_isSharedCheck_5174_;
goto v_resetjp_5132_;
}
else
{
lean_dec(v_a_5116_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5174_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v___x_5135_; uint64_t v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5139_; 
v___x_5135_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5131_);
v___x_5136_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5135_);
v___x_5137_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5137_, 0, v___x_5135_);
lean_ctor_set_uint64(v___x_5137_, sizeof(void*)*1, v___x_5136_);
lean_inc(v_canUnfold_x3f_5127_);
lean_inc(v_synthPendingDepth_5126_);
lean_inc(v_defEqCtx_x3f_5125_);
lean_inc_ref(v_localInstances_5124_);
lean_inc_ref(v_lctx_5123_);
lean_inc(v_zetaDeltaSet_5122_);
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 0, v___x_5137_);
v___x_5139_ = v___x_5133_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5137_);
lean_ctor_set(v_reuseFailAlloc_5173_, 1, v_zetaDeltaSet_5122_);
lean_ctor_set(v_reuseFailAlloc_5173_, 2, v_lctx_5123_);
lean_ctor_set(v_reuseFailAlloc_5173_, 3, v_localInstances_5124_);
lean_ctor_set(v_reuseFailAlloc_5173_, 4, v_defEqCtx_x3f_5125_);
lean_ctor_set(v_reuseFailAlloc_5173_, 5, v_synthPendingDepth_5126_);
lean_ctor_set(v_reuseFailAlloc_5173_, 6, v_canUnfold_x3f_5127_);
lean_ctor_set_uint8(v_reuseFailAlloc_5173_, sizeof(void*)*7, v_trackZetaDelta_5121_);
lean_ctor_set_uint8(v_reuseFailAlloc_5173_, sizeof(void*)*7 + 1, v_univApprox_5128_);
lean_ctor_set_uint8(v_reuseFailAlloc_5173_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5129_);
lean_ctor_set_uint8(v_reuseFailAlloc_5173_, sizeof(void*)*7 + 3, v_cacheInferType_5130_);
v___x_5139_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; uint64_t v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___x_5140_ = l_Lean_Meta_Context_config(v___x_5139_);
lean_dec_ref(v___x_5139_);
v___x_5141_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5140_);
v___x_5142_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5141_);
v___x_5143_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5143_, 0, v___x_5141_);
lean_ctor_set_uint64(v___x_5143_, sizeof(void*)*1, v___x_5142_);
v___x_5144_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5144_, 0, v___x_5143_);
lean_ctor_set(v___x_5144_, 1, v_zetaDeltaSet_5122_);
lean_ctor_set(v___x_5144_, 2, v_lctx_5123_);
lean_ctor_set(v___x_5144_, 3, v_localInstances_5124_);
lean_ctor_set(v___x_5144_, 4, v_defEqCtx_x3f_5125_);
lean_ctor_set(v___x_5144_, 5, v_synthPendingDepth_5126_);
lean_ctor_set(v___x_5144_, 6, v_canUnfold_x3f_5127_);
lean_ctor_set_uint8(v___x_5144_, sizeof(void*)*7, v_trackZetaDelta_5121_);
lean_ctor_set_uint8(v___x_5144_, sizeof(void*)*7 + 1, v_univApprox_5128_);
lean_ctor_set_uint8(v___x_5144_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5129_);
lean_ctor_set_uint8(v___x_5144_, sizeof(void*)*7 + 3, v_cacheInferType_5130_);
lean_inc(v_matchDeclName_5115_);
v___x_5145_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5115_, v___x_5144_, v_a_5117_, v_a_5118_, v_a_5119_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; lean_object* v___x_5147_; lean_object* v_a_5148_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5146_);
lean_dec_ref(v___x_5145_);
lean_inc(v_matchDeclName_5115_);
v___x_5147_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5115_, v_a_5119_);
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
lean_inc(v_a_5148_);
lean_dec_ref(v___x_5147_);
if (lean_obj_tag(v_a_5148_) == 1)
{
lean_object* v_val_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___f_5155_; lean_object* v___x_5156_; uint8_t v___x_5157_; lean_object* v___x_5158_; 
v_val_5149_ = lean_ctor_get(v_a_5148_, 0);
lean_inc(v_val_5149_);
lean_dec_ref(v_a_5148_);
v___x_5150_ = l_Lean_instInhabitedExpr;
v___x_5151_ = l_Lean_ConstantInfo_levelParams(v_a_5146_);
v___x_5152_ = lean_box(0);
lean_inc(v___x_5151_);
v___x_5153_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_5151_, v___x_5152_);
v___x_5154_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5149_);
lean_inc(v_a_5146_);
v___f_5155_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5155_, 0, v_val_5149_);
lean_closure_set(v___f_5155_, 1, v___x_5150_);
lean_closure_set(v___f_5155_, 2, v_matchDeclName_5115_);
lean_closure_set(v___f_5155_, 3, v___x_5154_);
lean_closure_set(v___f_5155_, 4, v_a_5146_);
lean_closure_set(v___f_5155_, 5, v___x_5153_);
lean_closure_set(v___f_5155_, 6, v___x_5151_);
v___x_5156_ = l_Lean_ConstantInfo_type(v_a_5146_);
lean_dec(v_a_5146_);
v___x_5157_ = 0;
v___x_5158_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5156_, v___f_5155_, v___x_5157_, v___x_5157_, v___x_5144_, v_a_5117_, v_a_5118_, v_a_5119_);
lean_dec_ref(v___x_5144_);
return v___x_5158_;
}
else
{
lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; 
lean_dec(v_a_5148_);
lean_dec(v_a_5146_);
v___x_5159_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5160_ = l_Lean_MessageData_ofName(v_matchDeclName_5115_);
v___x_5161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5159_);
lean_ctor_set(v___x_5161_, 1, v___x_5160_);
v___x_5162_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5163_, 0, v___x_5161_);
lean_ctor_set(v___x_5163_, 1, v___x_5162_);
v___x_5164_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5163_, v___x_5144_, v_a_5117_, v_a_5118_, v_a_5119_);
lean_dec_ref(v___x_5144_);
return v___x_5164_;
}
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
lean_dec_ref(v___x_5144_);
lean_dec(v_matchDeclName_5115_);
v_a_5165_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5145_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5145_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_);
lean_dec(v_a_5186_);
lean_dec_ref(v_a_5185_);
lean_dec(v_a_5184_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_inst_5189_, lean_object* v_R_5190_, lean_object* v_a_5191_, lean_object* v_b_5192_, lean_object* v_c_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
lean_object* v___x_5199_; 
v___x_5199_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_5191_, v_b_5192_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_inst_5200_, lean_object* v_R_5201_, lean_object* v_a_5202_, lean_object* v_b_5203_, lean_object* v_c_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_inst_5200_, v_R_5201_, v_a_5202_, v_b_5203_, v_c_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
lean_dec(v___y_5208_);
lean_dec_ref(v___y_5207_);
lean_dec(v___y_5206_);
lean_dec_ref(v___y_5205_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5211_, lean_object* v_val_5212_, lean_object* v_matchDeclName_5213_, lean_object* v___x_5214_, lean_object* v___x_5215_, lean_object* v_a_5216_, lean_object* v___x_5217_, lean_object* v___x_5218_, lean_object* v___x_5219_, lean_object* v___x_5220_, lean_object* v___x_5221_, lean_object* v___x_5222_, lean_object* v_inst_5223_, lean_object* v_R_5224_, lean_object* v_a_5225_, lean_object* v_b_5226_, lean_object* v_c_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5211_, v_val_5212_, v_matchDeclName_5213_, v___x_5214_, v___x_5215_, v_a_5216_, v___x_5217_, v___x_5218_, v___x_5219_, v___x_5220_, v___x_5221_, v___x_5222_, v_a_5225_, v_b_5226_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5234_ = _args[0];
lean_object* v_val_5235_ = _args[1];
lean_object* v_matchDeclName_5236_ = _args[2];
lean_object* v___x_5237_ = _args[3];
lean_object* v___x_5238_ = _args[4];
lean_object* v_a_5239_ = _args[5];
lean_object* v___x_5240_ = _args[6];
lean_object* v___x_5241_ = _args[7];
lean_object* v___x_5242_ = _args[8];
lean_object* v___x_5243_ = _args[9];
lean_object* v___x_5244_ = _args[10];
lean_object* v___x_5245_ = _args[11];
lean_object* v_inst_5246_ = _args[12];
lean_object* v_R_5247_ = _args[13];
lean_object* v_a_5248_ = _args[14];
lean_object* v_b_5249_ = _args[15];
lean_object* v_c_5250_ = _args[16];
lean_object* v___y_5251_ = _args[17];
lean_object* v___y_5252_ = _args[18];
lean_object* v___y_5253_ = _args[19];
lean_object* v___y_5254_ = _args[20];
lean_object* v___y_5255_ = _args[21];
_start:
{
lean_object* v_res_5256_; 
v_res_5256_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5234_, v_val_5235_, v_matchDeclName_5236_, v___x_5237_, v___x_5238_, v_a_5239_, v___x_5240_, v___x_5241_, v___x_5242_, v___x_5243_, v___x_5244_, v___x_5245_, v_inst_5246_, v_R_5247_, v_a_5248_, v_b_5249_, v_c_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v_upperBound_5234_);
return v_res_5256_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5257_, lean_object* v_matchDeclName_5258_, lean_object* v_a_5259_, lean_object* v_b_5260_){
_start:
{
uint8_t v___x_5262_; 
v___x_5262_ = lean_nat_dec_lt(v_a_5259_, v_upperBound_5257_);
if (v___x_5262_ == 0)
{
lean_object* v___x_5263_; 
lean_dec(v_a_5259_);
lean_dec(v_matchDeclName_5258_);
v___x_5263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5263_, 0, v_b_5260_);
return v___x_5263_;
}
else
{
lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5264_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5258_);
v___x_5265_ = l_Lean_Name_str___override(v_matchDeclName_5258_, v___x_5264_);
v___x_5266_ = lean_unsigned_to_nat(1u);
v___x_5267_ = lean_nat_add(v_a_5259_, v___x_5266_);
lean_dec(v_a_5259_);
lean_inc(v___x_5267_);
v___x_5268_ = lean_name_append_index_after(v___x_5265_, v___x_5267_);
v___x_5269_ = lean_array_push(v_b_5260_, v___x_5268_);
v_a_5259_ = v___x_5267_;
v_b_5260_ = v___x_5269_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5271_, lean_object* v_matchDeclName_5272_, lean_object* v_a_5273_, lean_object* v_b_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5271_, v_matchDeclName_5272_, v_a_5273_, v_b_5274_);
lean_dec(v_upperBound_5271_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_){
_start:
{
lean_object* v___x_5283_; lean_object* v_firstEqnName_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5283_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5277_, 3);
v_firstEqnName_5284_ = l_Lean_Name_str___override(v_matchDeclName_5277_, v___x_5283_);
v___x_5285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5285_, 0, v_matchDeclName_5277_);
v___x_5286_ = l_Lean_Meta_realizeConst(v_matchDeclName_5277_, v_firstEqnName_5284_, v___x_5285_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_);
if (lean_obj_tag(v___x_5286_) == 0)
{
lean_object* v___x_5287_; lean_object* v_a_5288_; 
lean_dec_ref(v___x_5286_);
lean_inc(v_matchDeclName_5277_);
v___x_5287_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5277_, v_a_5281_);
v_a_5288_ = lean_ctor_get(v___x_5287_, 0);
lean_inc(v_a_5288_);
lean_dec_ref(v___x_5287_);
if (lean_obj_tag(v_a_5288_) == 1)
{
lean_object* v_val_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
lean_dec(v_a_5281_);
lean_dec_ref(v_a_5280_);
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
v_val_5289_ = lean_ctor_get(v_a_5288_, 0);
lean_inc(v_val_5289_);
lean_dec_ref(v_a_5288_);
v___x_5290_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5289_);
lean_dec(v_val_5289_);
v___x_5291_ = lean_unsigned_to_nat(0u);
v___x_5292_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5293_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5290_, v_matchDeclName_5277_, v___x_5291_, v___x_5292_);
lean_dec(v___x_5290_);
return v___x_5293_;
}
else
{
lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; 
lean_dec(v_a_5288_);
v___x_5294_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5295_ = l_Lean_MessageData_ofName(v_matchDeclName_5277_);
v___x_5296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5296_, 0, v___x_5294_);
lean_ctor_set(v___x_5296_, 1, v___x_5295_);
v___x_5297_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5296_);
lean_ctor_set(v___x_5298_, 1, v___x_5297_);
v___x_5299_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5298_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_);
lean_dec(v_a_5281_);
lean_dec_ref(v_a_5280_);
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
return v___x_5299_;
}
}
else
{
lean_object* v_a_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5307_; 
lean_dec(v_a_5281_);
lean_dec_ref(v_a_5280_);
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
lean_dec(v_matchDeclName_5277_);
v_a_5300_ = lean_ctor_get(v___x_5286_, 0);
v_isSharedCheck_5307_ = !lean_is_exclusive(v___x_5286_);
if (v_isSharedCheck_5307_ == 0)
{
v___x_5302_ = v___x_5286_;
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_a_5300_);
lean_dec(v___x_5286_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5305_; 
if (v_isShared_5303_ == 0)
{
v___x_5305_ = v___x_5302_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5300_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
return v___x_5305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_){
_start:
{
lean_object* v_res_5314_; 
v_res_5314_ = lean_get_congr_match_equations_for(v_matchDeclName_5308_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_);
return v_res_5314_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5315_, lean_object* v_matchDeclName_5316_, lean_object* v_inst_5317_, lean_object* v_R_5318_, lean_object* v_a_5319_, lean_object* v_b_5320_, lean_object* v_c_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_){
_start:
{
lean_object* v___x_5327_; 
v___x_5327_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5315_, v_matchDeclName_5316_, v_a_5319_, v_b_5320_);
return v___x_5327_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5328_, lean_object* v_matchDeclName_5329_, lean_object* v_inst_5330_, lean_object* v_R_5331_, lean_object* v_a_5332_, lean_object* v_b_5333_, lean_object* v_c_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5328_, v_matchDeclName_5329_, v_inst_5330_, v_R_5331_, v_a_5332_, v_b_5333_, v_c_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_);
lean_dec(v___y_5338_);
lean_dec_ref(v___y_5337_);
lean_dec(v___y_5336_);
lean_dec_ref(v___y_5335_);
lean_dec(v_upperBound_5328_);
return v_res_5340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5391_ = lean_unsigned_to_nat(3248161880u);
v___x_5392_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5393_ = l_Lean_Name_num___override(v___x_5392_, v___x_5391_);
return v___x_5393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5395_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5396_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5397_ = l_Lean_Name_str___override(v___x_5396_, v___x_5395_);
return v___x_5397_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5399_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5400_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5401_ = l_Lean_Name_str___override(v___x_5400_, v___x_5399_);
return v___x_5401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5402_ = lean_unsigned_to_nat(2u);
v___x_5403_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5404_ = l_Lean_Name_num___override(v___x_5403_, v___x_5402_);
return v___x_5404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5406_; uint8_t v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; 
v___x_5406_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5407_ = 0;
v___x_5408_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5409_ = l_Lean_registerTraceClass(v___x_5406_, v___x_5407_, v___x_5408_);
return v___x_5409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5412_, lean_object* v_n_5413_){
_start:
{
if (lean_obj_tag(v_n_5413_) == 1)
{
lean_object* v_pre_5414_; lean_object* v_str_5415_; uint8_t v___y_5417_; uint8_t v___x_5423_; 
v_pre_5414_ = lean_ctor_get(v_n_5413_, 0);
lean_inc(v_pre_5414_);
v_str_5415_ = lean_ctor_get(v_n_5413_, 1);
lean_inc_ref_n(v_str_5415_, 2);
lean_dec_ref(v_n_5413_);
v___x_5423_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5415_);
if (v___x_5423_ == 0)
{
lean_object* v___x_5424_; uint8_t v___x_5425_; 
v___x_5424_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5425_ = lean_string_dec_eq(v_str_5415_, v___x_5424_);
lean_dec_ref(v_str_5415_);
v___y_5417_ = v___x_5425_;
goto v___jp_5416_;
}
else
{
lean_dec_ref(v_str_5415_);
v___y_5417_ = v___x_5423_;
goto v___jp_5416_;
}
v___jp_5416_:
{
if (v___y_5417_ == 0)
{
lean_object* v___x_5418_; 
lean_dec(v_pre_5414_);
lean_dec_ref(v_env_5412_);
v___x_5418_ = lean_box(0);
return v___x_5418_;
}
else
{
lean_object* v___x_5419_; 
v___x_5419_ = lean_private_to_user_name(v_pre_5414_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_dec_ref(v_env_5412_);
return v___x_5419_;
}
else
{
lean_object* v_val_5420_; uint8_t v___x_5421_; 
v_val_5420_ = lean_ctor_get(v___x_5419_, 0);
lean_inc(v_val_5420_);
v___x_5421_ = lean_is_matcher(v_env_5412_, v_val_5420_);
if (v___x_5421_ == 0)
{
lean_object* v___x_5422_; 
lean_dec_ref(v___x_5419_);
v___x_5422_ = lean_box(0);
return v___x_5422_;
}
else
{
return v___x_5419_;
}
}
}
}
}
else
{
lean_object* v___x_5426_; 
lean_dec(v_n_5413_);
lean_dec_ref(v_env_5412_);
v___x_5426_ = lean_box(0);
return v___x_5426_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5427_, lean_object* v_x2_5428_){
_start:
{
lean_object* v___x_5429_; 
v___x_5429_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5427_, v_x2_5428_);
if (lean_obj_tag(v___x_5429_) == 0)
{
uint8_t v___x_5430_; 
v___x_5430_ = 0;
return v___x_5430_;
}
else
{
uint8_t v___x_5431_; 
lean_dec_ref(v___x_5429_);
v___x_5431_ = 1;
return v___x_5431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5432_, lean_object* v_x2_5433_){
_start:
{
uint8_t v_res_5434_; lean_object* v_r_5435_; 
v_res_5434_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5432_, v_x2_5433_);
v_r_5435_ = lean_box(v_res_5434_);
return v_r_5435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5438_; lean_object* v___x_5439_; 
v___f_5438_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5439_ = l_Lean_registerReservedNamePredicate(v___f_5438_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5441_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5448_; uint64_t v___x_5449_; 
v___x_5448_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5449_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5448_);
return v___x_5449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; 
v___x_5450_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5451_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5452_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5452_, 0, v___x_5451_);
lean_ctor_set_uint64(v___x_5452_, sizeof(void*)*1, v___x_5450_);
return v___x_5452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; 
v___x_5455_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5456_ = lean_unsigned_to_nat(0u);
v___x_5457_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5457_, 0, v___x_5456_);
lean_ctor_set(v___x_5457_, 1, v___x_5456_);
lean_ctor_set(v___x_5457_, 2, v___x_5456_);
lean_ctor_set(v___x_5457_, 3, v___x_5456_);
lean_ctor_set(v___x_5457_, 4, v___x_5455_);
lean_ctor_set(v___x_5457_, 5, v___x_5455_);
lean_ctor_set(v___x_5457_, 6, v___x_5455_);
lean_ctor_set(v___x_5457_, 7, v___x_5455_);
lean_ctor_set(v___x_5457_, 8, v___x_5455_);
lean_ctor_set(v___x_5457_, 9, v___x_5455_);
return v___x_5457_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5458_; lean_object* v___x_5459_; 
v___x_5458_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5459_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5459_, 0, v___x_5458_);
lean_ctor_set(v___x_5459_, 1, v___x_5458_);
lean_ctor_set(v___x_5459_, 2, v___x_5458_);
lean_ctor_set(v___x_5459_, 3, v___x_5458_);
lean_ctor_set(v___x_5459_, 4, v___x_5458_);
lean_ctor_set(v___x_5459_, 5, v___x_5458_);
return v___x_5459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___x_5460_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5461_, 0, v___x_5460_);
lean_ctor_set(v___x_5461_, 1, v___x_5460_);
lean_ctor_set(v___x_5461_, 2, v___x_5460_);
lean_ctor_set(v___x_5461_, 3, v___x_5460_);
lean_ctor_set(v___x_5461_, 4, v___x_5460_);
return v___x_5461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5462_, lean_object* v_name_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_){
_start:
{
lean_object* v___x_5467_; lean_object* v_env_5468_; lean_object* v___x_5469_; 
v___x_5467_ = lean_st_ref_get(v___y_5465_);
v_env_5468_ = lean_ctor_get(v___x_5467_, 0);
lean_inc_ref(v_env_5468_);
lean_dec(v___x_5467_);
v___x_5469_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5468_, v_name_5463_);
if (lean_obj_tag(v___x_5469_) == 1)
{
lean_object* v_val_5470_; uint8_t v___x_5471_; uint8_t v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; 
v_val_5470_ = lean_ctor_get(v___x_5469_, 0);
lean_inc(v_val_5470_);
lean_dec_ref(v___x_5469_);
v___x_5471_ = 0;
v___x_5472_ = 1;
v___x_5473_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5474_ = lean_unsigned_to_nat(0u);
v___x_5475_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5476_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5477_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5478_ = lean_box(0);
lean_inc(v___x_5462_);
v___x_5479_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5479_, 0, v___x_5473_);
lean_ctor_set(v___x_5479_, 1, v___x_5462_);
lean_ctor_set(v___x_5479_, 2, v___x_5476_);
lean_ctor_set(v___x_5479_, 3, v___x_5477_);
lean_ctor_set(v___x_5479_, 4, v___x_5478_);
lean_ctor_set(v___x_5479_, 5, v___x_5474_);
lean_ctor_set(v___x_5479_, 6, v___x_5478_);
lean_ctor_set_uint8(v___x_5479_, sizeof(void*)*7, v___x_5471_);
lean_ctor_set_uint8(v___x_5479_, sizeof(void*)*7 + 1, v___x_5471_);
lean_ctor_set_uint8(v___x_5479_, sizeof(void*)*7 + 2, v___x_5471_);
lean_ctor_set_uint8(v___x_5479_, sizeof(void*)*7 + 3, v___x_5472_);
v___x_5480_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5481_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5482_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5483_, 0, v___x_5480_);
lean_ctor_set(v___x_5483_, 1, v___x_5481_);
lean_ctor_set(v___x_5483_, 2, v___x_5462_);
lean_ctor_set(v___x_5483_, 3, v___x_5475_);
lean_ctor_set(v___x_5483_, 4, v___x_5482_);
v___x_5484_ = lean_st_mk_ref(v___x_5483_);
lean_inc(v___y_5465_);
lean_inc_ref(v___y_5464_);
lean_inc(v___x_5484_);
v___x_5485_ = lean_get_match_equations_for(v_val_5470_, v___x_5479_, v___x_5484_, v___y_5464_, v___y_5465_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5494_; 
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5494_ == 0)
{
lean_object* v_unused_5495_; 
v_unused_5495_ = lean_ctor_get(v___x_5485_, 0);
lean_dec(v_unused_5495_);
v___x_5487_ = v___x_5485_;
v_isShared_5488_ = v_isSharedCheck_5494_;
goto v_resetjp_5486_;
}
else
{
lean_dec(v___x_5485_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5494_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5492_; 
v___x_5489_ = lean_st_ref_get(v___x_5484_);
lean_dec(v___x_5484_);
lean_dec(v___x_5489_);
v___x_5490_ = lean_box(v___x_5472_);
if (v_isShared_5488_ == 0)
{
lean_ctor_set(v___x_5487_, 0, v___x_5490_);
v___x_5492_ = v___x_5487_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5490_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
else
{
lean_dec(v___x_5484_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5503_; 
v_isSharedCheck_5503_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5503_ == 0)
{
lean_object* v_unused_5504_; 
v_unused_5504_ = lean_ctor_get(v___x_5485_, 0);
lean_dec(v_unused_5504_);
v___x_5497_ = v___x_5485_;
v_isShared_5498_ = v_isSharedCheck_5503_;
goto v_resetjp_5496_;
}
else
{
lean_dec(v___x_5485_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5503_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
lean_object* v___x_5499_; lean_object* v___x_5501_; 
v___x_5499_ = lean_box(v___x_5472_);
if (v_isShared_5498_ == 0)
{
lean_ctor_set_tag(v___x_5497_, 0);
lean_ctor_set(v___x_5497_, 0, v___x_5499_);
v___x_5501_ = v___x_5497_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v___x_5499_);
v___x_5501_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
return v___x_5501_;
}
}
}
else
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5512_; 
v_a_5505_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5512_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5507_ = v___x_5485_;
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5485_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5512_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5510_; 
if (v_isShared_5508_ == 0)
{
v___x_5510_ = v___x_5507_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_a_5505_);
v___x_5510_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
return v___x_5510_;
}
}
}
}
}
else
{
uint8_t v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; 
lean_dec(v___x_5469_);
lean_dec(v___x_5462_);
v___x_5513_ = 0;
v___x_5514_ = lean_box(v___x_5513_);
v___x_5515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5515_, 0, v___x_5514_);
return v___x_5515_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5516_, lean_object* v_name_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_){
_start:
{
lean_object* v_res_5521_; 
v_res_5521_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5516_, v_name_5517_, v___y_5518_, v___y_5519_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
return v_res_5521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5525_; lean_object* v___x_5526_; 
v___f_5525_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5526_ = l_Lean_registerReservedNameAction(v___f_5525_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5527_){
_start:
{
lean_object* v_res_5528_; 
v_res_5528_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5529_, lean_object* v_n_5530_){
_start:
{
if (lean_obj_tag(v_n_5530_) == 1)
{
lean_object* v_pre_5531_; lean_object* v_str_5532_; uint8_t v___x_5533_; 
v_pre_5531_ = lean_ctor_get(v_n_5530_, 0);
lean_inc(v_pre_5531_);
v_str_5532_ = lean_ctor_get(v_n_5530_, 1);
lean_inc_ref(v_str_5532_);
lean_dec_ref(v_n_5530_);
v___x_5533_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5532_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; 
lean_dec(v_pre_5531_);
lean_dec_ref(v_env_5529_);
v___x_5534_ = lean_box(0);
return v___x_5534_;
}
else
{
uint8_t v___x_5535_; 
lean_inc(v_pre_5531_);
v___x_5535_ = lean_is_matcher(v_env_5529_, v_pre_5531_);
if (v___x_5535_ == 0)
{
lean_object* v___x_5536_; 
lean_dec(v_pre_5531_);
v___x_5536_ = lean_box(0);
return v___x_5536_;
}
else
{
lean_object* v___x_5537_; 
v___x_5537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5537_, 0, v_pre_5531_);
return v___x_5537_;
}
}
}
else
{
lean_object* v___x_5538_; 
lean_dec(v_n_5530_);
lean_dec_ref(v_env_5529_);
v___x_5538_ = lean_box(0);
return v___x_5538_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5539_, lean_object* v_x2_5540_){
_start:
{
lean_object* v___x_5541_; 
v___x_5541_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5539_, v_x2_5540_);
if (lean_obj_tag(v___x_5541_) == 0)
{
uint8_t v___x_5542_; 
v___x_5542_ = 0;
return v___x_5542_;
}
else
{
uint8_t v___x_5543_; 
lean_dec_ref(v___x_5541_);
v___x_5543_ = 1;
return v___x_5543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5544_, lean_object* v_x2_5545_){
_start:
{
uint8_t v_res_5546_; lean_object* v_r_5547_; 
v_res_5546_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5544_, v_x2_5545_);
v_r_5547_ = lean_box(v_res_5546_);
return v_r_5547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5550_; lean_object* v___x_5551_; 
v___f_5550_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5551_ = l_Lean_registerReservedNamePredicate(v___f_5550_);
return v___x_5551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5552_){
_start:
{
lean_object* v_res_5553_; 
v_res_5553_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5554_, lean_object* v_name_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_){
_start:
{
lean_object* v___x_5559_; lean_object* v_env_5560_; lean_object* v___x_5561_; 
v___x_5559_ = lean_st_ref_get(v___y_5557_);
v_env_5560_ = lean_ctor_get(v___x_5559_, 0);
lean_inc_ref(v_env_5560_);
lean_dec(v___x_5559_);
v___x_5561_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5560_, v_name_5555_);
if (lean_obj_tag(v___x_5561_) == 1)
{
lean_object* v_val_5562_; uint8_t v___x_5563_; uint8_t v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; 
v_val_5562_ = lean_ctor_get(v___x_5561_, 0);
lean_inc(v_val_5562_);
lean_dec_ref(v___x_5561_);
v___x_5563_ = 0;
v___x_5564_ = 1;
v___x_5565_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5566_ = lean_unsigned_to_nat(32u);
v___x_5567_ = lean_mk_empty_array_with_capacity(v___x_5566_);
lean_dec_ref(v___x_5567_);
v___x_5568_ = lean_unsigned_to_nat(0u);
v___x_5569_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5570_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5571_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5572_ = lean_box(0);
lean_inc(v___x_5554_);
v___x_5573_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5573_, 0, v___x_5565_);
lean_ctor_set(v___x_5573_, 1, v___x_5554_);
lean_ctor_set(v___x_5573_, 2, v___x_5570_);
lean_ctor_set(v___x_5573_, 3, v___x_5571_);
lean_ctor_set(v___x_5573_, 4, v___x_5572_);
lean_ctor_set(v___x_5573_, 5, v___x_5568_);
lean_ctor_set(v___x_5573_, 6, v___x_5572_);
lean_ctor_set_uint8(v___x_5573_, sizeof(void*)*7, v___x_5563_);
lean_ctor_set_uint8(v___x_5573_, sizeof(void*)*7 + 1, v___x_5563_);
lean_ctor_set_uint8(v___x_5573_, sizeof(void*)*7 + 2, v___x_5563_);
lean_ctor_set_uint8(v___x_5573_, sizeof(void*)*7 + 3, v___x_5564_);
v___x_5574_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5575_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5576_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5577_, 0, v___x_5574_);
lean_ctor_set(v___x_5577_, 1, v___x_5575_);
lean_ctor_set(v___x_5577_, 2, v___x_5554_);
lean_ctor_set(v___x_5577_, 3, v___x_5569_);
lean_ctor_set(v___x_5577_, 4, v___x_5576_);
v___x_5578_ = lean_st_mk_ref(v___x_5577_);
lean_inc(v___y_5557_);
lean_inc_ref(v___y_5556_);
lean_inc(v___x_5578_);
v___x_5579_ = lean_get_congr_match_equations_for(v_val_5562_, v___x_5573_, v___x_5578_, v___y_5556_, v___y_5557_);
if (lean_obj_tag(v___x_5579_) == 0)
{
lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5588_; 
v_isSharedCheck_5588_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5588_ == 0)
{
lean_object* v_unused_5589_; 
v_unused_5589_ = lean_ctor_get(v___x_5579_, 0);
lean_dec(v_unused_5589_);
v___x_5581_ = v___x_5579_;
v_isShared_5582_ = v_isSharedCheck_5588_;
goto v_resetjp_5580_;
}
else
{
lean_dec(v___x_5579_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5588_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5586_; 
v___x_5583_ = lean_st_ref_get(v___x_5578_);
lean_dec(v___x_5578_);
lean_dec(v___x_5583_);
v___x_5584_ = lean_box(v___x_5564_);
if (v_isShared_5582_ == 0)
{
lean_ctor_set(v___x_5581_, 0, v___x_5584_);
v___x_5586_ = v___x_5581_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5584_);
v___x_5586_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
return v___x_5586_;
}
}
}
else
{
lean_dec(v___x_5578_);
if (lean_obj_tag(v___x_5579_) == 0)
{
lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5597_; 
v_isSharedCheck_5597_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5597_ == 0)
{
lean_object* v_unused_5598_; 
v_unused_5598_ = lean_ctor_get(v___x_5579_, 0);
lean_dec(v_unused_5598_);
v___x_5591_ = v___x_5579_;
v_isShared_5592_ = v_isSharedCheck_5597_;
goto v_resetjp_5590_;
}
else
{
lean_dec(v___x_5579_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5597_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
lean_object* v___x_5593_; lean_object* v___x_5595_; 
v___x_5593_ = lean_box(v___x_5564_);
if (v_isShared_5592_ == 0)
{
lean_ctor_set_tag(v___x_5591_, 0);
lean_ctor_set(v___x_5591_, 0, v___x_5593_);
v___x_5595_ = v___x_5591_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5593_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
else
{
lean_object* v_a_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5606_; 
v_a_5599_ = lean_ctor_get(v___x_5579_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5601_ = v___x_5579_;
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_a_5599_);
lean_dec(v___x_5579_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5604_; 
if (v_isShared_5602_ == 0)
{
v___x_5604_ = v___x_5601_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_a_5599_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
}
}
else
{
uint8_t v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; 
lean_dec(v___x_5561_);
lean_dec(v___x_5554_);
v___x_5607_ = 0;
v___x_5608_ = lean_box(v___x_5607_);
v___x_5609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5609_, 0, v___x_5608_);
return v___x_5609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5610_, lean_object* v_name_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_){
_start:
{
lean_object* v_res_5615_; 
v_res_5615_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5610_, v_name_5611_, v___y_5612_, v___y_5613_);
lean_dec(v___y_5613_);
lean_dec_ref(v___y_5612_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5619_; lean_object* v___x_5620_; 
v___f_5619_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5620_ = l_Lean_registerReservedNameAction(v___f_5619_);
return v___x_5620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5621_){
_start:
{
lean_object* v_res_5622_; 
v_res_5622_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5622_;
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
