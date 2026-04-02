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
lean_object* v_cs_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_718_; 
v_cs_684_ = lean_ctor_get(v_n_677_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v_n_677_);
if (v_isSharedCheck_718_ == 0)
{
v___x_686_ = v_n_677_;
v_isShared_687_ = v_isSharedCheck_718_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_cs_684_);
lean_dec(v_n_677_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_718_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; size_t v_sz_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v_b_678_);
v_sz_690_ = lean_array_size(v_cs_684_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_675_, v_mvarId_676_, v_cs_684_, v_sz_690_, v___x_691_, v___x_689_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v_cs_684_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_709_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_709_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_709_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_709_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_fst_697_; 
v_fst_697_ = lean_ctor_get(v_a_693_, 0);
if (lean_obj_tag(v_fst_697_) == 0)
{
lean_object* v_snd_698_; lean_object* v___x_700_; 
v_snd_698_ = lean_ctor_get(v_a_693_, 1);
lean_inc(v_snd_698_);
lean_dec(v_a_693_);
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 1);
lean_ctor_set(v___x_686_, 0, v_snd_698_);
v___x_700_ = v___x_686_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_snd_698_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_700_);
v___x_702_ = v___x_695_;
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
}
else
{
lean_object* v_val_705_; lean_object* v___x_707_; 
lean_inc_ref(v_fst_697_);
lean_dec(v_a_693_);
lean_del_object(v___x_686_);
v_val_705_ = lean_ctor_get(v_fst_697_, 0);
lean_inc(v_val_705_);
lean_dec_ref(v_fst_697_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v_val_705_);
v___x_707_ = v___x_695_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_val_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_del_object(v___x_686_);
v_a_710_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_692_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_692_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
else
{
lean_object* v_vs_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_753_; 
v_vs_719_ = lean_ctor_get(v_n_677_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v_n_677_);
if (v_isSharedCheck_753_ == 0)
{
v___x_721_ = v_n_677_;
v_isShared_722_ = v_isSharedCheck_753_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_vs_719_);
lean_dec(v_n_677_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_753_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; size_t v_sz_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___x_723_ = lean_box(0);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v_b_678_);
v_sz_725_ = lean_array_size(v_vs_719_);
v___x_726_ = ((size_t)0ULL);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_676_, v_vs_719_, v_sz_725_, v___x_726_, v___x_724_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v_vs_719_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_744_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_744_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_fst_732_; 
v_fst_732_ = lean_ctor_get(v_a_728_, 0);
if (lean_obj_tag(v_fst_732_) == 0)
{
lean_object* v_snd_733_; lean_object* v___x_735_; 
v_snd_733_ = lean_ctor_get(v_a_728_, 1);
lean_inc(v_snd_733_);
lean_dec(v_a_728_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_snd_733_);
v___x_735_ = v___x_721_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_snd_733_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_735_);
v___x_737_ = v___x_730_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
else
{
lean_object* v_val_740_; lean_object* v___x_742_; 
lean_inc_ref(v_fst_732_);
lean_dec(v_a_728_);
lean_del_object(v___x_721_);
v_val_740_ = lean_ctor_get(v_fst_732_, 0);
lean_inc(v_val_740_);
lean_dec_ref(v_fst_732_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v_val_740_);
v___x_742_ = v___x_730_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_val_740_);
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
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_del_object(v___x_721_);
v_a_745_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_727_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_727_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(lean_object* v_init_754_, lean_object* v_mvarId_755_, lean_object* v_as_756_, size_t v_sz_757_, size_t v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
lean_dec(v_mvarId_755_);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_b_759_);
return v___x_766_;
}
else
{
lean_object* v_snd_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_801_; 
v_snd_767_ = lean_ctor_get(v_b_759_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_b_759_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v_b_759_, 0);
lean_dec(v_unused_802_);
v___x_769_ = v_b_759_;
v_isShared_770_ = v_isSharedCheck_801_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_snd_767_);
lean_dec(v_b_759_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_801_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_array_uget_borrowed(v_as_756_, v_i_758_);
lean_inc(v_snd_767_);
lean_inc(v_a_771_);
lean_inc(v_mvarId_755_);
v___x_772_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_754_, v_mvarId_755_, v_a_771_, v_snd_767_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_792_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_792_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_792_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_792_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
if (lean_obj_tag(v_a_773_) == 0)
{
lean_object* v___x_777_; lean_object* v___x_779_; 
lean_dec(v_mvarId_755_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v_a_773_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_777_);
v___x_779_ = v___x_769_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_snd_767_);
v___x_779_ = v_reuseFailAlloc_783_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_781_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_779_);
v___x_781_ = v___x_775_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
lean_del_object(v___x_775_);
lean_dec(v_snd_767_);
v_a_784_ = lean_ctor_get(v_a_773_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v_a_773_);
v___x_785_ = lean_box(0);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_a_784_);
lean_ctor_set(v___x_769_, 0, v___x_785_);
v___x_787_ = v___x_769_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_a_784_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
size_t v___x_788_; size_t v___x_789_; 
v___x_788_ = ((size_t)1ULL);
v___x_789_ = lean_usize_add(v_i_758_, v___x_788_);
v_i_758_ = v___x_789_;
v_b_759_ = v___x_787_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_del_object(v___x_769_);
lean_dec(v_snd_767_);
lean_dec(v_mvarId_755_);
v_a_793_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_772_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_772_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3___boxed(lean_object* v_init_803_, lean_object* v_mvarId_804_, lean_object* v_as_805_, lean_object* v_sz_806_, lean_object* v_i_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
size_t v_sz_boxed_814_; size_t v_i_boxed_815_; lean_object* v_res_816_; 
v_sz_boxed_814_ = lean_unbox_usize(v_sz_806_);
lean_dec(v_sz_806_);
v_i_boxed_815_ = lean_unbox_usize(v_i_807_);
lean_dec(v_i_807_);
v_res_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_803_, v_mvarId_804_, v_as_805_, v_sz_boxed_814_, v_i_boxed_815_, v_b_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec_ref(v_as_805_);
lean_dec_ref(v_init_803_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1___boxed(lean_object* v_init_817_, lean_object* v_mvarId_818_, lean_object* v_n_819_, lean_object* v_b_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_817_, v_mvarId_818_, v_n_819_, v_b_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v_init_817_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(lean_object* v_mvarId_830_, lean_object* v_as_831_, size_t v_sz_832_, size_t v_i_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = lean_usize_dec_lt(v_i_833_, v_sz_832_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v_mvarId_830_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v_b_834_);
return v___x_841_;
}
else
{
lean_object* v_snd_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_937_; 
v_snd_842_ = lean_ctor_get(v_b_834_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_b_834_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_b_834_, 0);
lean_dec(v_unused_938_);
v___x_844_ = v_b_834_;
v_isShared_845_ = v_isSharedCheck_937_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_snd_842_);
lean_dec(v_b_834_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_937_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v_a_848_; lean_object* v_a_855_; 
v___x_846_ = lean_box(0);
v_a_855_ = lean_array_uget_borrowed(v_as_831_, v_i_833_);
if (lean_obj_tag(v_a_855_) == 0)
{
v_a_848_ = v_snd_842_;
goto v___jp_847_;
}
else
{
lean_object* v_val_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_val_856_ = lean_ctor_get(v_a_855_, 0);
v___x_857_ = l_Lean_LocalDecl_type(v_val_856_);
v___x_858_ = l_Lean_Meta_matchEq_x3f(v___x_857_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = lean_box(0);
v___x_861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_859_) == 1)
{
lean_object* v_val_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_928_; 
v_val_862_ = lean_ctor_get(v_a_859_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_a_859_);
if (v_isSharedCheck_928_ == 0)
{
v___x_864_ = v_a_859_;
v_isShared_865_ = v_isSharedCheck_928_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_val_862_);
lean_dec(v_a_859_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_928_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_snd_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_926_; 
v_snd_866_ = lean_ctor_get(v_val_862_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_val_862_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_val_862_, 0);
lean_dec(v_unused_927_);
v___x_868_ = v_val_862_;
v_isShared_869_ = v_isSharedCheck_926_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_snd_866_);
lean_dec(v_val_862_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_926_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_fst_870_; lean_object* v_snd_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_925_; 
v_fst_870_ = lean_ctor_get(v_snd_866_, 0);
v_snd_871_ = lean_ctor_get(v_snd_866_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v_snd_866_);
if (v_isSharedCheck_925_ == 0)
{
v___x_873_ = v_snd_866_;
v_isShared_874_ = v_isSharedCheck_925_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_snd_871_);
lean_inc(v_fst_870_);
lean_dec(v_snd_866_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_925_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_Expr_isFVar(v_fst_870_);
if (v___x_875_ == 0)
{
lean_del_object(v___x_873_);
lean_dec(v_snd_871_);
lean_dec(v_fst_870_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_dec(v_snd_842_);
v_a_848_ = v___x_861_;
goto v___jp_847_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = l_Lean_Expr_fvarId_x21(v_fst_870_);
lean_dec(v_fst_870_);
lean_inc(v___x_876_);
v___x_877_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_871_, v___x_876_, v___y_836_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; uint8_t v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
v___x_879_ = lean_unbox(v_a_878_);
lean_dec(v_a_878_);
if (v___x_879_ == 0)
{
if (v___x_875_ == 0)
{
lean_dec(v___x_876_);
lean_del_object(v___x_873_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_dec(v_snd_842_);
v_a_848_ = v___x_861_;
goto v___jp_847_;
}
else
{
lean_object* v___x_880_; 
lean_inc(v_mvarId_830_);
v___x_880_ = l_Lean_Meta_subst_x3f(v_mvarId_830_, v___x_876_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_908_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_908_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_908_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_908_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
if (lean_obj_tag(v_a_881_) == 0)
{
lean_del_object(v___x_883_);
lean_del_object(v___x_873_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_dec(v_snd_842_);
v_a_848_ = v___x_861_;
goto v___jp_847_;
}
else
{
lean_object* v_val_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_907_; 
lean_del_object(v___x_844_);
lean_dec(v_mvarId_830_);
v_val_885_ = lean_ctor_get(v_a_881_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_a_881_);
if (v_isSharedCheck_907_ == 0)
{
v___x_887_ = v_a_881_;
v_isShared_888_ = v_isSharedCheck_907_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_val_885_);
lean_dec(v_a_881_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_907_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_mk_empty_array_with_capacity(v___x_889_);
v___x_891_ = lean_array_push(v___x_890_, v_val_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_891_);
v___x_893_ = v___x_887_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_906_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 1, v___x_860_);
lean_ctor_set(v___x_873_, 0, v___x_893_);
v___x_895_ = v___x_873_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_860_);
v___x_895_ = v_reuseFailAlloc_905_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_897_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_895_);
v___x_897_ = v___x_864_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_904_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v_snd_842_);
lean_ctor_set(v___x_868_, 0, v___x_897_);
v___x_899_ = v___x_868_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_snd_842_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_899_);
v___x_901_ = v___x_883_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
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
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_del_object(v___x_873_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_del_object(v___x_844_);
lean_dec(v_snd_842_);
lean_dec(v_mvarId_830_);
v_a_909_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_880_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_880_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
else
{
lean_dec(v___x_876_);
lean_del_object(v___x_873_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_dec(v_snd_842_);
v_a_848_ = v___x_861_;
goto v___jp_847_;
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v___x_876_);
lean_del_object(v___x_873_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_del_object(v___x_844_);
lean_dec(v_snd_842_);
lean_dec(v_mvarId_830_);
v_a_917_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_877_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_877_);
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
}
}
}
}
else
{
lean_dec(v_a_859_);
lean_dec(v_snd_842_);
v_a_848_ = v___x_861_;
goto v___jp_847_;
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_del_object(v___x_844_);
lean_dec(v_snd_842_);
lean_dec(v_mvarId_830_);
v_a_929_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_858_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_858_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
v___jp_847_:
{
lean_object* v___x_850_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_a_848_);
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_850_ = v___x_844_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_a_848_);
v___x_850_ = v_reuseFailAlloc_854_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
size_t v___x_851_; size_t v___x_852_; 
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_833_, v___x_851_);
v_i_833_ = v___x_852_;
v_b_834_ = v___x_850_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___boxed(lean_object* v_mvarId_939_, lean_object* v_as_940_, lean_object* v_sz_941_, lean_object* v_i_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
size_t v_sz_boxed_949_; size_t v_i_boxed_950_; lean_object* v_res_951_; 
v_sz_boxed_949_ = lean_unbox_usize(v_sz_941_);
lean_dec(v_sz_941_);
v_i_boxed_950_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_res_951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_939_, v_as_940_, v_sz_boxed_949_, v_i_boxed_950_, v_b_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v_as_940_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(lean_object* v_mvarId_952_, lean_object* v_as_953_, size_t v_sz_954_, size_t v_i_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_usize_dec_lt(v_i_955_, v_sz_954_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec(v_mvarId_952_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_b_956_);
return v___x_963_;
}
else
{
lean_object* v_snd_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1059_; 
v_snd_964_ = lean_ctor_get(v_b_956_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_b_956_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v_b_956_, 0);
lean_dec(v_unused_1060_);
v___x_966_ = v_b_956_;
v_isShared_967_ = v_isSharedCheck_1059_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_snd_964_);
lean_dec(v_b_956_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1059_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v_a_970_; lean_object* v_a_977_; 
v___x_968_ = lean_box(0);
v_a_977_ = lean_array_uget_borrowed(v_as_953_, v_i_955_);
if (lean_obj_tag(v_a_977_) == 0)
{
v_a_970_ = v_snd_964_;
goto v___jp_969_;
}
else
{
lean_object* v_val_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_val_978_ = lean_ctor_get(v_a_977_, 0);
v___x_979_ = l_Lean_LocalDecl_type(v_val_978_);
v___x_980_ = l_Lean_Meta_matchEq_x3f(v___x_979_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v___x_982_ = lean_box(0);
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_981_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1050_; 
v_val_984_ = lean_ctor_get(v_a_981_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_a_981_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_986_ = v_a_981_;
v_isShared_987_ = v_isSharedCheck_1050_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_val_984_);
lean_dec(v_a_981_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1050_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_snd_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1048_; 
v_snd_988_ = lean_ctor_get(v_val_984_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_val_984_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_val_984_, 0);
lean_dec(v_unused_1049_);
v___x_990_ = v_val_984_;
v_isShared_991_ = v_isSharedCheck_1048_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_snd_988_);
lean_dec(v_val_984_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1048_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1047_; 
v_fst_992_ = lean_ctor_get(v_snd_988_, 0);
v_snd_993_ = lean_ctor_get(v_snd_988_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_snd_988_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_995_ = v_snd_988_;
v_isShared_996_ = v_isSharedCheck_1047_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_inc(v_fst_992_);
lean_dec(v_snd_988_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1047_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
uint8_t v___x_997_; 
v___x_997_ = l_Lean_Expr_isFVar(v_fst_992_);
if (v___x_997_ == 0)
{
lean_del_object(v___x_995_);
lean_dec(v_snd_993_);
lean_dec(v_fst_992_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_dec(v_snd_964_);
v_a_970_ = v___x_983_;
goto v___jp_969_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = l_Lean_Expr_fvarId_x21(v_fst_992_);
lean_dec(v_fst_992_);
lean_inc(v___x_998_);
v___x_999_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_993_, v___x_998_, v___y_958_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; uint8_t v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v___x_1001_ = lean_unbox(v_a_1000_);
lean_dec(v_a_1000_);
if (v___x_1001_ == 0)
{
if (v___x_997_ == 0)
{
lean_dec(v___x_998_);
lean_del_object(v___x_995_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_dec(v_snd_964_);
v_a_970_ = v___x_983_;
goto v___jp_969_;
}
else
{
lean_object* v___x_1002_; 
lean_inc(v_mvarId_952_);
v___x_1002_ = l_Lean_Meta_subst_x3f(v_mvarId_952_, v___x_998_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1030_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1030_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1030_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
if (lean_obj_tag(v_a_1003_) == 0)
{
lean_del_object(v___x_1005_);
lean_del_object(v___x_995_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_dec(v_snd_964_);
v_a_970_ = v___x_983_;
goto v___jp_969_;
}
else
{
lean_object* v_val_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1029_; 
lean_del_object(v___x_966_);
lean_dec(v_mvarId_952_);
v_val_1007_ = lean_ctor_get(v_a_1003_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_a_1003_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1009_ = v_a_1003_;
v_isShared_1010_ = v_isSharedCheck_1029_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_val_1007_);
lean_dec(v_a_1003_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1029_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_mk_empty_array_with_capacity(v___x_1011_);
v___x_1013_ = lean_array_push(v___x_1012_, v_val_1007_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1013_);
v___x_1015_ = v___x_1009_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v___x_982_);
lean_ctor_set(v___x_995_, 0, v___x_1015_);
v___x_1017_ = v___x_995_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_982_);
v___x_1017_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_1017_);
v___x_1019_ = v___x_986_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v_snd_964_);
lean_ctor_set(v___x_990_, 0, v___x_1019_);
v___x_1021_ = v___x_990_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_snd_964_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1021_);
v___x_1023_ = v___x_1005_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
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
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_995_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_del_object(v___x_966_);
lean_dec(v_snd_964_);
lean_dec(v_mvarId_952_);
v_a_1031_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1002_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1002_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
else
{
lean_dec(v___x_998_);
lean_del_object(v___x_995_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_dec(v_snd_964_);
v_a_970_ = v___x_983_;
goto v___jp_969_;
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v___x_998_);
lean_del_object(v___x_995_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_del_object(v___x_966_);
lean_dec(v_snd_964_);
lean_dec(v_mvarId_952_);
v_a_1039_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_999_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_999_);
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
}
}
}
else
{
lean_dec(v_a_981_);
lean_dec(v_snd_964_);
v_a_970_ = v___x_983_;
goto v___jp_969_;
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_del_object(v___x_966_);
lean_dec(v_snd_964_);
lean_dec(v_mvarId_952_);
v_a_1051_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_980_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_980_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
v___jp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v_a_970_);
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_972_ = v___x_966_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_a_970_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
size_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_add(v_i_955_, v___x_973_);
v___x_975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_952_, v_as_953_, v_sz_954_, v___x_974_, v___x_972_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
return v___x_975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2___boxed(lean_object* v_mvarId_1061_, lean_object* v_as_1062_, lean_object* v_sz_1063_, lean_object* v_i_1064_, lean_object* v_b_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
size_t v_sz_boxed_1071_; size_t v_i_boxed_1072_; lean_object* v_res_1073_; 
v_sz_boxed_1071_ = lean_unbox_usize(v_sz_1063_);
lean_dec(v_sz_1063_);
v_i_boxed_1072_ = lean_unbox_usize(v_i_1064_);
lean_dec(v_i_1064_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1061_, v_as_1062_, v_sz_boxed_1071_, v_i_boxed_1072_, v_b_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec_ref(v_as_1062_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(lean_object* v_mvarId_1074_, lean_object* v_t_1075_, lean_object* v_init_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_root_1082_; lean_object* v_tail_1083_; lean_object* v___x_1084_; 
v_root_1082_ = lean_ctor_get(v_t_1075_, 0);
lean_inc_ref(v_root_1082_);
v_tail_1083_ = lean_ctor_get(v_t_1075_, 1);
lean_inc_ref(v_tail_1083_);
lean_dec_ref(v_t_1075_);
lean_inc(v_mvarId_1074_);
lean_inc_ref(v_init_1076_);
v___x_1084_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_1076_, v_mvarId_1074_, v_root_1082_, v_init_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec_ref(v_init_1076_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1121_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1121_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1121_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
if (lean_obj_tag(v_a_1085_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; 
lean_dec_ref(v_tail_1083_);
lean_dec(v_mvarId_1074_);
v_a_1089_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_a_1089_);
lean_dec_ref(v_a_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_a_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; size_t v_sz_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
lean_del_object(v___x_1087_);
v_a_1093_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_a_1093_);
lean_dec_ref(v_a_1085_);
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v_a_1093_);
v_sz_1096_ = lean_array_size(v_tail_1083_);
v___x_1097_ = ((size_t)0ULL);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1074_, v_tail_1083_, v_sz_1096_, v___x_1097_, v___x_1095_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec_ref(v_tail_1083_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1112_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1112_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1112_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_fst_1103_; 
v_fst_1103_ = lean_ctor_get(v_a_1099_, 0);
if (lean_obj_tag(v_fst_1103_) == 0)
{
lean_object* v_snd_1104_; lean_object* v___x_1106_; 
v_snd_1104_ = lean_ctor_get(v_a_1099_, 1);
lean_inc(v_snd_1104_);
lean_dec(v_a_1099_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_snd_1104_);
v___x_1106_ = v___x_1101_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_snd_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v_val_1108_; lean_object* v___x_1110_; 
lean_inc_ref(v_fst_1103_);
lean_dec(v_a_1099_);
v_val_1108_ = lean_ctor_get(v_fst_1103_, 0);
lean_inc(v_val_1108_);
lean_dec_ref(v_fst_1103_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_val_1108_);
v___x_1110_ = v___x_1101_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_val_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_a_1113_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1098_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1098_);
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
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v_tail_1083_);
lean_dec(v_mvarId_1074_);
v_a_1122_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1084_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1084_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1___boxed(lean_object* v_mvarId_1130_, lean_object* v_t_1131_, lean_object* v_init_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1130_, v_t_1131_, v_init_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(lean_object* v_mvarId_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_lctx_1151_; lean_object* v_decls_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_lctx_1151_ = lean_ctor_get(v___y_1146_, 2);
v_decls_1152_ = lean_ctor_get(v_lctx_1151_, 1);
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0));
lean_inc_ref(v_decls_1152_);
v___x_1154_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1145_, v_decls_1152_, v___x_1153_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1166_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1166_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1166_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_fst_1159_; 
v_fst_1159_ = lean_ctor_get(v_a_1155_, 0);
lean_inc(v_fst_1159_);
lean_dec(v_a_1155_);
if (lean_obj_tag(v_fst_1159_) == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_del_object(v___x_1157_);
v___x_1160_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2);
v___x_1161_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1160_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec_ref(v___y_1146_);
return v___x_1161_;
}
else
{
lean_object* v_val_1162_; lean_object* v___x_1164_; 
lean_dec_ref(v___y_1146_);
v_val_1162_ = lean_ctor_get(v_fst_1159_, 0);
lean_inc(v_val_1162_);
lean_dec_ref(v_fst_1159_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v_val_1162_);
v___x_1164_ = v___x_1157_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_val_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v___y_1146_);
v_a_1167_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1154_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1154_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed(lean_object* v_mvarId_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(v_mvarId_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(lean_object* v_mvarId_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___f_1188_; lean_object* v___x_1189_; 
lean_inc(v_mvarId_1182_);
v___f_1188_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1188_, 0, v_mvarId_1182_);
v___x_1189_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_1182_, v___f_1188_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___boxed(lean_object* v_mvarId_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v_mvarId_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
return v_res_1196_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object* v_x_1202_){
_start:
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2));
v___x_1204_ = lean_name_eq(v_x_1202_, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object* v_x_1205_){
_start:
{
uint8_t v_res_1206_; lean_object* v_r_1207_; 
v_res_1206_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(v_x_1205_);
lean_dec(v_x_1205_);
v_r_1207_ = lean_box(v_res_1206_);
return v_r_1207_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object* v_e_1208_){
_start:
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2));
v___x_1210_ = l_Lean_Expr_isConstOf(v_e_1208_, v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object* v_e_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(v_e_1211_);
lean_dec_ref(v_e_1211_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2));
v___x_1218_ = l_Lean_stringToMessageData(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object* v_mvarId_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___x_1225_; 
lean_inc(v_mvarId_1219_);
v___x_1225_ = l_Lean_MVarId_getType(v_mvarId_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref(v___x_1225_);
v___f_1227_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0));
v___f_1228_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1));
v___x_1229_ = lean_find_expr(v___f_1228_, v_a_1226_);
lean_dec(v_a_1226_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_mvarId_1219_);
v___x_1230_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3);
v___x_1231_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1230_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
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
else
{
lean_object* v___x_1240_; 
lean_dec_ref(v___x_1229_);
v___x_1240_ = l_Lean_MVarId_deltaTarget(v_mvarId_1219_, v___f_1227_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
return v___x_1240_;
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_mvarId_1219_);
v_a_1241_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1225_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1225_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object* v_mvarId_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_mvarId_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
return v_res_1255_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = l_Lean_maxRecDepthErrorMessage;
v___x_1262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3);
v___x_1264_ = l_Lean_MessageData_ofFormat(v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4);
v___x_1266_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2));
v___x_1267_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___x_1265_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(lean_object* v_ref_1268_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v_ref_1268_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___boxed(lean_object* v_ref_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object* v_00_u03b1_1276_, lean_object* v_ref_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1277_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_ref_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v_00_u03b1_1284_, v_ref_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object* v_a_1292_, lean_object* v_____r_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_mk_empty_array_with_capacity(v___x_1299_);
v___x_1301_ = lean_array_push(v___x_1300_, v_a_1292_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object* v_a_1303_, lean_object* v_____r_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1303_, v_____r_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1310_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1311_; double v___x_1312_; 
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_float_of_nat(v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object* v_cls_1316_, lean_object* v_msg_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_ref_1323_; lean_object* v___x_1324_; lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1369_; 
v_ref_1323_ = lean_ctor_get(v___y_1320_, 5);
v___x_1324_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1369_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1369_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v_traceState_1330_; lean_object* v_env_1331_; lean_object* v_nextMacroScope_1332_; lean_object* v_ngen_1333_; lean_object* v_auxDeclNGen_1334_; lean_object* v_cache_1335_; lean_object* v_messages_1336_; lean_object* v_infoState_1337_; lean_object* v_snapshotTasks_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1368_; 
v___x_1329_ = lean_st_ref_take(v___y_1321_);
v_traceState_1330_ = lean_ctor_get(v___x_1329_, 4);
v_env_1331_ = lean_ctor_get(v___x_1329_, 0);
v_nextMacroScope_1332_ = lean_ctor_get(v___x_1329_, 1);
v_ngen_1333_ = lean_ctor_get(v___x_1329_, 2);
v_auxDeclNGen_1334_ = lean_ctor_get(v___x_1329_, 3);
v_cache_1335_ = lean_ctor_get(v___x_1329_, 5);
v_messages_1336_ = lean_ctor_get(v___x_1329_, 6);
v_infoState_1337_ = lean_ctor_get(v___x_1329_, 7);
v_snapshotTasks_1338_ = lean_ctor_get(v___x_1329_, 8);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1340_ = v___x_1329_;
v_isShared_1341_ = v_isSharedCheck_1368_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_snapshotTasks_1338_);
lean_inc(v_infoState_1337_);
lean_inc(v_messages_1336_);
lean_inc(v_cache_1335_);
lean_inc(v_traceState_1330_);
lean_inc(v_auxDeclNGen_1334_);
lean_inc(v_ngen_1333_);
lean_inc(v_nextMacroScope_1332_);
lean_inc(v_env_1331_);
lean_dec(v___x_1329_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1368_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
uint64_t v_tid_1342_; lean_object* v_traces_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1367_; 
v_tid_1342_ = lean_ctor_get_uint64(v_traceState_1330_, sizeof(void*)*1);
v_traces_1343_ = lean_ctor_get(v_traceState_1330_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_traceState_1330_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1345_ = v_traceState_1330_;
v_isShared_1346_ = v_isSharedCheck_1367_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_traces_1343_);
lean_dec(v_traceState_1330_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1367_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; double v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0);
v___x_1349_ = 0;
v___x_1350_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1));
v___x_1351_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1351_, 0, v_cls_1316_);
lean_ctor_set(v___x_1351_, 1, v___x_1347_);
lean_ctor_set(v___x_1351_, 2, v___x_1350_);
lean_ctor_set_float(v___x_1351_, sizeof(void*)*3, v___x_1348_);
lean_ctor_set_float(v___x_1351_, sizeof(void*)*3 + 8, v___x_1348_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 16, v___x_1349_);
v___x_1352_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2));
v___x_1353_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v_a_1325_);
lean_ctor_set(v___x_1353_, 2, v___x_1352_);
lean_inc(v_ref_1323_);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_ref_1323_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_PersistentArray_push___redArg(v_traces_1343_, v___x_1354_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1355_);
v___x_1357_ = v___x_1345_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1355_);
lean_ctor_set_uint64(v_reuseFailAlloc_1366_, sizeof(void*)*1, v_tid_1342_);
v___x_1357_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1359_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 4, v___x_1357_);
v___x_1359_ = v___x_1340_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_env_1331_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_nextMacroScope_1332_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_ngen_1333_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_auxDeclNGen_1334_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1365_, 5, v_cache_1335_);
lean_ctor_set(v_reuseFailAlloc_1365_, 6, v_messages_1336_);
lean_ctor_set(v_reuseFailAlloc_1365_, 7, v_infoState_1337_);
lean_ctor_set(v_reuseFailAlloc_1365_, 8, v_snapshotTasks_1338_);
v___x_1359_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1360_ = lean_st_ref_set(v___y_1321_, v___x_1359_);
v___x_1361_ = lean_box(0);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1361_);
v___x_1363_ = v___x_1327_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object* v_cls_1370_, lean_object* v_msg_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1370_, v_msg_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4));
v___x_1386_ = l_Lean_stringToMessageData(v___x_1385_);
return v___x_1386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1389_ = l_Lean_stringToMessageData(v___x_1388_);
return v___x_1389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16(void){
_start:
{
lean_object* v_cls_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_cls_1403_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1404_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15));
v___x_1405_ = l_Lean_Name_append(v___x_1404_, v_cls_1403_);
return v___x_1405_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17));
v___x_1408_ = l_Lean_stringToMessageData(v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1409_, lean_object* v_mvarId_1410_, lean_object* v_depth_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v_a_1422_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; uint8_t v___y_1459_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; uint8_t v___y_1484_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v_a_1508_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; uint8_t v___y_1519_; uint8_t v___y_1520_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; uint8_t v___y_1561_; lean_object* v_a_1562_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; uint8_t v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; uint8_t v___y_1584_; uint8_t v___y_1585_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; uint8_t v___y_1616_; uint8_t v___y_1617_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; uint8_t v___y_1640_; lean_object* v___y_1641_; uint8_t v___y_1642_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; uint8_t v___y_1665_; lean_object* v___y_1666_; uint8_t v___y_1667_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; uint8_t v___y_1692_; uint8_t v___y_1693_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; uint8_t v___y_1721_; uint8_t v___y_1722_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v_fileName_1773_; lean_object* v_fileMap_1774_; lean_object* v_options_1775_; lean_object* v_currRecDepth_1776_; lean_object* v_maxRecDepth_1777_; lean_object* v_ref_1778_; lean_object* v_currNamespace_1779_; lean_object* v_openDecls_1780_; lean_object* v_initHeartbeats_1781_; lean_object* v_maxHeartbeats_1782_; lean_object* v_quotContext_1783_; lean_object* v_currMacroScope_1784_; uint8_t v_diag_1785_; lean_object* v_cancelTk_x3f_1786_; uint8_t v_suppressElabErrors_1787_; lean_object* v_inheritedTraceOptions_1788_; lean_object* v_cls_1789_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v_fileName_1773_ = lean_ctor_get(v_a_1414_, 0);
v_fileMap_1774_ = lean_ctor_get(v_a_1414_, 1);
v_options_1775_ = lean_ctor_get(v_a_1414_, 2);
v_currRecDepth_1776_ = lean_ctor_get(v_a_1414_, 3);
v_maxRecDepth_1777_ = lean_ctor_get(v_a_1414_, 4);
v_ref_1778_ = lean_ctor_get(v_a_1414_, 5);
v_currNamespace_1779_ = lean_ctor_get(v_a_1414_, 6);
v_openDecls_1780_ = lean_ctor_get(v_a_1414_, 7);
v_initHeartbeats_1781_ = lean_ctor_get(v_a_1414_, 8);
v_maxHeartbeats_1782_ = lean_ctor_get(v_a_1414_, 9);
v_quotContext_1783_ = lean_ctor_get(v_a_1414_, 10);
v_currMacroScope_1784_ = lean_ctor_get(v_a_1414_, 11);
v_diag_1785_ = lean_ctor_get_uint8(v_a_1414_, sizeof(void*)*14);
v_cancelTk_x3f_1786_ = lean_ctor_get(v_a_1414_, 12);
v_suppressElabErrors_1787_ = lean_ctor_get_uint8(v_a_1414_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1788_ = lean_ctor_get(v_a_1414_, 13);
v_cls_1789_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_nat_dec_eq(v_maxRecDepth_1777_, v___x_1801_);
if (v___x_1802_ == 0)
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_nat_dec_eq(v_currRecDepth_1776_, v_maxRecDepth_1777_);
if (v___x_1803_ == 0)
{
goto v___jp_1790_;
}
else
{
lean_object* v___x_1804_; 
lean_dec(v_mvarId_1410_);
lean_dec(v_matchDeclName_1409_);
lean_inc(v_ref_1778_);
v___x_1804_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1778_);
return v___x_1804_;
}
}
else
{
goto v___jp_1790_;
}
v___jp_1417_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_array_get_size(v_a_1422_);
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; 
lean_dec_ref(v_a_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v_matchDeclName_1409_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
return v___x_1427_;
}
else
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_nat_dec_le(v___x_1424_, v___x_1424_);
if (v___x_1428_ == 0)
{
if (v___x_1426_ == 0)
{
lean_object* v___x_1429_; 
lean_dec_ref(v_a_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v_matchDeclName_1409_);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1425_);
return v___x_1429_;
}
else
{
size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = ((size_t)0ULL);
v___x_1431_ = lean_usize_of_nat(v___x_1424_);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1411_, v_matchDeclName_1409_, v_a_1422_, v___x_1430_, v___x_1431_, v___x_1425_, v___y_1420_, v___y_1418_, v___y_1421_, v___y_1419_);
lean_dec_ref(v___y_1421_);
lean_dec_ref(v_a_1422_);
return v___x_1432_;
}
}
else
{
size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = lean_usize_of_nat(v___x_1424_);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1411_, v_matchDeclName_1409_, v_a_1422_, v___x_1433_, v___x_1434_, v___x_1425_, v___y_1420_, v___y_1418_, v___y_1421_, v___y_1419_);
lean_dec_ref(v___y_1421_);
lean_dec_ref(v_a_1422_);
return v___x_1435_;
}
}
}
v___jp_1436_:
{
if (lean_obj_tag(v___y_1441_) == 0)
{
lean_object* v_a_1442_; 
v_a_1442_ = lean_ctor_get(v___y_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref(v___y_1441_);
v___y_1418_ = v___y_1437_;
v___y_1419_ = v___y_1439_;
v___y_1420_ = v___y_1438_;
v___y_1421_ = v___y_1440_;
v_a_1422_ = v_a_1442_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v___y_1440_);
lean_dec(v_matchDeclName_1409_);
v_a_1443_ = lean_ctor_get(v___y_1441_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___y_1441_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___y_1441_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___y_1441_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
v___jp_1451_:
{
if (v___y_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v___y_1455_);
v___x_1460_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1454_, v___y_1452_, v___y_1457_);
lean_dec_ref(v___y_1454_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1474_; 
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v___x_1460_, 0);
lean_dec(v_unused_1475_);
v___x_1462_ = v___x_1460_;
v_isShared_1463_ = v_isSharedCheck_1474_;
goto v_resetjp_1461_;
}
else
{
lean_dec(v___x_1460_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1474_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1464_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1409_);
v___x_1465_ = l_Lean_MessageData_ofName(v_matchDeclName_1409_);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set_tag(v___x_1462_, 1);
lean_ctor_set(v___x_1462_, 0, v___y_1453_);
v___x_1470_ = v___x_1462_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___y_1453_);
v___x_1470_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1468_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1471_, v___y_1456_, v___y_1452_, v___y_1458_, v___y_1457_);
v___y_1437_ = v___y_1452_;
v___y_1438_ = v___y_1456_;
v___y_1439_ = v___y_1457_;
v___y_1440_ = v___y_1458_;
v___y_1441_ = v___x_1472_;
goto v___jp_1436_;
}
}
}
else
{
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1453_);
lean_dec(v_matchDeclName_1409_);
return v___x_1460_;
}
}
else
{
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
v___y_1437_ = v___y_1452_;
v___y_1438_ = v___y_1456_;
v___y_1439_ = v___y_1457_;
v___y_1440_ = v___y_1458_;
v___y_1441_ = v___y_1455_;
goto v___jp_1436_;
}
}
v___jp_1476_:
{
if (v___y_1484_ == 0)
{
lean_object* v___x_1485_; 
lean_dec_ref(v___y_1480_);
v___x_1485_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1478_, v___y_1477_, v___y_1482_);
lean_dec_ref(v___y_1478_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v___x_1486_; 
lean_dec_ref(v___x_1485_);
v___x_1486_ = l_Lean_Meta_saveState___redArg(v___y_1477_, v___y_1482_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1488_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref(v___x_1486_);
lean_inc(v___y_1479_);
v___x_1488_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1479_, v___y_1481_, v___y_1477_, v___y_1483_, v___y_1482_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_dec(v_a_1487_);
lean_dec(v___y_1479_);
v___y_1437_ = v___y_1477_;
v___y_1438_ = v___y_1481_;
v___y_1439_ = v___y_1482_;
v___y_1440_ = v___y_1483_;
v___y_1441_ = v___x_1488_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1489_; uint8_t v___x_1490_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
v___x_1490_ = l_Lean_Exception_isInterrupt(v_a_1489_);
if (v___x_1490_ == 0)
{
uint8_t v___x_1491_; 
v___x_1491_ = l_Lean_Exception_isRuntime(v_a_1489_);
v___y_1452_ = v___y_1477_;
v___y_1453_ = v___y_1479_;
v___y_1454_ = v_a_1487_;
v___y_1455_ = v___x_1488_;
v___y_1456_ = v___y_1481_;
v___y_1457_ = v___y_1482_;
v___y_1458_ = v___y_1483_;
v___y_1459_ = v___x_1491_;
goto v___jp_1451_;
}
else
{
lean_dec(v_a_1489_);
v___y_1452_ = v___y_1477_;
v___y_1453_ = v___y_1479_;
v___y_1454_ = v_a_1487_;
v___y_1455_ = v___x_1488_;
v___y_1456_ = v___y_1481_;
v___y_1457_ = v___y_1482_;
v___y_1458_ = v___y_1483_;
v___y_1459_ = v___x_1490_;
goto v___jp_1451_;
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1479_);
lean_dec(v_matchDeclName_1409_);
v_a_1492_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1486_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1486_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1479_);
lean_dec(v_matchDeclName_1409_);
return v___x_1485_;
}
}
else
{
lean_object* v___x_1500_; 
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v_matchDeclName_1409_);
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___y_1480_);
return v___x_1500_;
}
}
v___jp_1501_:
{
uint8_t v___x_1509_; 
v___x_1509_ = l_Lean_Exception_isInterrupt(v_a_1508_);
if (v___x_1509_ == 0)
{
uint8_t v___x_1510_; 
lean_inc_ref(v_a_1508_);
v___x_1510_ = l_Lean_Exception_isRuntime(v_a_1508_);
v___y_1477_ = v___y_1502_;
v___y_1478_ = v___y_1503_;
v___y_1479_ = v___y_1504_;
v___y_1480_ = v_a_1508_;
v___y_1481_ = v___y_1506_;
v___y_1482_ = v___y_1505_;
v___y_1483_ = v___y_1507_;
v___y_1484_ = v___x_1510_;
goto v___jp_1476_;
}
else
{
v___y_1477_ = v___y_1502_;
v___y_1478_ = v___y_1503_;
v___y_1479_ = v___y_1504_;
v___y_1480_ = v_a_1508_;
v___y_1481_ = v___y_1506_;
v___y_1482_ = v___y_1505_;
v___y_1483_ = v___y_1507_;
v___y_1484_ = v___x_1509_;
goto v___jp_1476_;
}
}
v___jp_1511_:
{
if (v___y_1520_ == 0)
{
lean_object* v___x_1521_; 
lean_dec_ref(v___y_1513_);
v___x_1521_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1515_, v___y_1512_, v___y_1517_);
lean_dec_ref(v___y_1515_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v___x_1522_; 
lean_dec_ref(v___x_1521_);
v___x_1522_ = l_Lean_Meta_saveState___redArg(v___y_1512_, v___y_1517_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v___x_1522_);
v___x_1524_ = lean_box(0);
lean_inc(v___y_1514_);
v___x_1525_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1514_, v___x_1524_, v___y_1519_, v___y_1516_, v___y_1512_, v___y_1518_, v___y_1517_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref(v___x_1525_);
if (lean_obj_tag(v_a_1526_) == 1)
{
lean_object* v_val_1527_; lean_object* v_fst_1528_; lean_object* v_snd_1529_; lean_object* v_mvarId_1530_; lean_object* v_fvarId_1531_; lean_object* v___x_1532_; 
v_val_1527_ = lean_ctor_get(v_a_1526_, 0);
lean_inc(v_val_1527_);
lean_dec_ref(v_a_1526_);
v_fst_1528_ = lean_ctor_get(v_val_1527_, 0);
lean_inc(v_fst_1528_);
v_snd_1529_ = lean_ctor_get(v_val_1527_, 1);
lean_inc(v_snd_1529_);
lean_dec(v_val_1527_);
v_mvarId_1530_ = lean_ctor_get(v_fst_1528_, 0);
lean_inc(v_mvarId_1530_);
v_fvarId_1531_ = lean_ctor_get(v_fst_1528_, 1);
lean_inc(v_fvarId_1531_);
lean_dec(v_fst_1528_);
v___x_1532_ = l_Lean_Meta_trySubst(v_mvarId_1530_, v_fvarId_1531_, v___y_1516_, v___y_1512_, v___y_1518_, v___y_1517_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v_mvarId_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec(v_a_1523_);
lean_dec(v___y_1514_);
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v___x_1532_);
v_mvarId_1534_ = lean_ctor_get(v_snd_1529_, 0);
lean_inc(v_mvarId_1534_);
lean_dec(v_snd_1529_);
v___x_1535_ = lean_unsigned_to_nat(2u);
v___x_1536_ = lean_mk_empty_array_with_capacity(v___x_1535_);
v___x_1537_ = lean_array_push(v___x_1536_, v_a_1533_);
v___x_1538_ = lean_array_push(v___x_1537_, v_mvarId_1534_);
v___y_1418_ = v___y_1512_;
v___y_1419_ = v___y_1517_;
v___y_1420_ = v___y_1516_;
v___y_1421_ = v___y_1518_;
v_a_1422_ = v___x_1538_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1539_; 
lean_dec(v_snd_1529_);
v_a_1539_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1539_);
lean_dec_ref(v___x_1532_);
v___y_1502_ = v___y_1512_;
v___y_1503_ = v_a_1523_;
v___y_1504_ = v___y_1514_;
v___y_1505_ = v___y_1517_;
v___y_1506_ = v___y_1516_;
v___y_1507_ = v___y_1518_;
v_a_1508_ = v_a_1539_;
goto v___jp_1501_;
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec(v_a_1526_);
v___x_1540_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1541_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1540_, v___y_1516_, v___y_1512_, v___y_1518_, v___y_1517_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; 
lean_dec(v_a_1523_);
lean_dec(v___y_1514_);
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
v___y_1418_ = v___y_1512_;
v___y_1419_ = v___y_1517_;
v___y_1420_ = v___y_1516_;
v___y_1421_ = v___y_1518_;
v_a_1422_ = v_a_1542_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1543_; 
v_a_1543_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1541_);
v___y_1502_ = v___y_1512_;
v___y_1503_ = v_a_1523_;
v___y_1504_ = v___y_1514_;
v___y_1505_ = v___y_1517_;
v___y_1506_ = v___y_1516_;
v___y_1507_ = v___y_1518_;
v_a_1508_ = v_a_1543_;
goto v___jp_1501_;
}
}
}
else
{
lean_object* v_a_1544_; 
v_a_1544_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1525_);
v___y_1502_ = v___y_1512_;
v___y_1503_ = v_a_1523_;
v___y_1504_ = v___y_1514_;
v___y_1505_ = v___y_1517_;
v___y_1506_ = v___y_1516_;
v___y_1507_ = v___y_1518_;
v_a_1508_ = v_a_1544_;
goto v___jp_1501_;
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1514_);
lean_dec(v_matchDeclName_1409_);
v_a_1545_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1522_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1522_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1514_);
lean_dec(v_matchDeclName_1409_);
return v___x_1521_;
}
}
else
{
lean_object* v___x_1553_; 
lean_dec_ref(v___y_1518_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v_matchDeclName_1409_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___y_1513_);
return v___x_1553_;
}
}
v___jp_1554_:
{
uint8_t v___x_1563_; 
v___x_1563_ = l_Lean_Exception_isInterrupt(v_a_1562_);
if (v___x_1563_ == 0)
{
uint8_t v___x_1564_; 
lean_inc_ref(v_a_1562_);
v___x_1564_ = l_Lean_Exception_isRuntime(v_a_1562_);
v___y_1512_ = v___y_1555_;
v___y_1513_ = v_a_1562_;
v___y_1514_ = v___y_1556_;
v___y_1515_ = v___y_1557_;
v___y_1516_ = v___y_1559_;
v___y_1517_ = v___y_1558_;
v___y_1518_ = v___y_1560_;
v___y_1519_ = v___y_1561_;
v___y_1520_ = v___x_1564_;
goto v___jp_1511_;
}
else
{
v___y_1512_ = v___y_1555_;
v___y_1513_ = v_a_1562_;
v___y_1514_ = v___y_1556_;
v___y_1515_ = v___y_1557_;
v___y_1516_ = v___y_1559_;
v___y_1517_ = v___y_1558_;
v___y_1518_ = v___y_1560_;
v___y_1519_ = v___y_1561_;
v___y_1520_ = v___x_1563_;
goto v___jp_1511_;
}
}
v___jp_1565_:
{
if (lean_obj_tag(v___y_1573_) == 0)
{
lean_object* v_a_1574_; 
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
v_a_1574_ = lean_ctor_get(v___y_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref(v___y_1573_);
v___y_1418_ = v___y_1566_;
v___y_1419_ = v___y_1570_;
v___y_1420_ = v___y_1569_;
v___y_1421_ = v___y_1571_;
v_a_1422_ = v_a_1574_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1575_; 
v_a_1575_ = lean_ctor_get(v___y_1573_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___y_1573_);
v___y_1555_ = v___y_1566_;
v___y_1556_ = v___y_1567_;
v___y_1557_ = v___y_1568_;
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___y_1569_;
v___y_1560_ = v___y_1571_;
v___y_1561_ = v___y_1572_;
v_a_1562_ = v_a_1575_;
goto v___jp_1554_;
}
}
v___jp_1576_:
{
if (v___y_1585_ == 0)
{
lean_object* v___x_1586_; 
lean_dec_ref(v___y_1579_);
v___x_1586_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1577_, v___y_1578_, v___y_1582_);
lean_dec_ref(v___y_1577_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref(v___x_1586_);
v___x_1587_ = l_Lean_Meta_saveState___redArg(v___y_1578_, v___y_1582_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v___x_1587_);
lean_inc(v___y_1580_);
v___x_1589_ = l_Lean_Meta_simpIfTarget(v___y_1580_, v___y_1584_, v___y_1584_, v___y_1581_, v___y_1578_, v___y_1583_, v___y_1582_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; uint8_t v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = l_Lean_instBEqMVarId_beq(v_a_1590_, v___y_1580_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_box(0);
v___x_1593_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1590_, v___x_1592_, v___y_1581_, v___y_1578_, v___y_1583_, v___y_1582_);
v___y_1566_ = v___y_1578_;
v___y_1567_ = v___y_1580_;
v___y_1568_ = v_a_1588_;
v___y_1569_ = v___y_1581_;
v___y_1570_ = v___y_1582_;
v___y_1571_ = v___y_1583_;
v___y_1572_ = v___y_1584_;
v___y_1573_ = v___x_1593_;
goto v___jp_1565_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1595_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1594_, v___y_1581_, v___y_1578_, v___y_1583_, v___y_1582_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1590_, v_a_1596_, v___y_1581_, v___y_1578_, v___y_1583_, v___y_1582_);
v___y_1566_ = v___y_1578_;
v___y_1567_ = v___y_1580_;
v___y_1568_ = v_a_1588_;
v___y_1569_ = v___y_1581_;
v___y_1570_ = v___y_1582_;
v___y_1571_ = v___y_1583_;
v___y_1572_ = v___y_1584_;
v___y_1573_ = v___x_1597_;
goto v___jp_1565_;
}
else
{
lean_object* v_a_1598_; 
lean_dec(v_a_1590_);
v_a_1598_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v___x_1595_);
v___y_1555_ = v___y_1578_;
v___y_1556_ = v___y_1580_;
v___y_1557_ = v_a_1588_;
v___y_1558_ = v___y_1582_;
v___y_1559_ = v___y_1581_;
v___y_1560_ = v___y_1583_;
v___y_1561_ = v___y_1584_;
v_a_1562_ = v_a_1598_;
goto v___jp_1554_;
}
}
}
else
{
lean_object* v_a_1599_; 
v_a_1599_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1589_);
v___y_1555_ = v___y_1578_;
v___y_1556_ = v___y_1580_;
v___y_1557_ = v_a_1588_;
v___y_1558_ = v___y_1582_;
v___y_1559_ = v___y_1581_;
v___y_1560_ = v___y_1583_;
v___y_1561_ = v___y_1584_;
v_a_1562_ = v_a_1599_;
goto v___jp_1554_;
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1580_);
lean_dec(v_matchDeclName_1409_);
v_a_1600_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1587_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1587_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1580_);
lean_dec(v_matchDeclName_1409_);
return v___x_1586_;
}
}
else
{
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1577_);
v___y_1437_ = v___y_1578_;
v___y_1438_ = v___y_1581_;
v___y_1439_ = v___y_1582_;
v___y_1440_ = v___y_1583_;
v___y_1441_ = v___y_1579_;
goto v___jp_1436_;
}
}
v___jp_1608_:
{
if (v___y_1617_ == 0)
{
lean_object* v___x_1618_; 
lean_dec_ref(v___y_1612_);
v___x_1618_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1610_, v___y_1609_, v___y_1614_);
lean_dec_ref(v___y_1610_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v___x_1619_; 
lean_dec_ref(v___x_1618_);
v___x_1619_ = l_Lean_Meta_saveState___redArg(v___y_1609_, v___y_1614_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref(v___x_1619_);
lean_inc(v___y_1611_);
v___x_1621_ = l_Lean_Meta_splitSparseCasesOn(v___y_1611_, v___y_1613_, v___y_1609_, v___y_1615_, v___y_1614_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_dec(v_a_1620_);
lean_dec(v___y_1611_);
v___y_1437_ = v___y_1609_;
v___y_1438_ = v___y_1613_;
v___y_1439_ = v___y_1614_;
v___y_1440_ = v___y_1615_;
v___y_1441_ = v___x_1621_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1622_; uint8_t v___x_1623_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
v___x_1623_ = l_Lean_Exception_isInterrupt(v_a_1622_);
if (v___x_1623_ == 0)
{
uint8_t v___x_1624_; 
v___x_1624_ = l_Lean_Exception_isRuntime(v_a_1622_);
v___y_1577_ = v_a_1620_;
v___y_1578_ = v___y_1609_;
v___y_1579_ = v___x_1621_;
v___y_1580_ = v___y_1611_;
v___y_1581_ = v___y_1613_;
v___y_1582_ = v___y_1614_;
v___y_1583_ = v___y_1615_;
v___y_1584_ = v___y_1616_;
v___y_1585_ = v___x_1624_;
goto v___jp_1576_;
}
else
{
lean_dec(v_a_1622_);
v___y_1577_ = v_a_1620_;
v___y_1578_ = v___y_1609_;
v___y_1579_ = v___x_1621_;
v___y_1580_ = v___y_1611_;
v___y_1581_ = v___y_1613_;
v___y_1582_ = v___y_1614_;
v___y_1583_ = v___y_1615_;
v___y_1584_ = v___y_1616_;
v___y_1585_ = v___x_1623_;
goto v___jp_1576_;
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1611_);
lean_dec(v_matchDeclName_1409_);
v_a_1625_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1619_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1619_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1611_);
lean_dec(v_matchDeclName_1409_);
return v___x_1618_;
}
}
else
{
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
v___y_1437_ = v___y_1609_;
v___y_1438_ = v___y_1613_;
v___y_1439_ = v___y_1614_;
v___y_1440_ = v___y_1615_;
v___y_1441_ = v___y_1612_;
goto v___jp_1436_;
}
}
v___jp_1633_:
{
if (v___y_1642_ == 0)
{
lean_object* v___x_1643_; 
lean_dec_ref(v___y_1634_);
v___x_1643_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1641_, v___y_1635_, v___y_1638_);
lean_dec_ref(v___y_1641_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1644_; 
lean_dec_ref(v___x_1643_);
v___x_1644_ = l_Lean_Meta_saveState___redArg(v___y_1635_, v___y_1638_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref(v___x_1644_);
lean_inc(v___y_1636_);
v___x_1646_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1636_, v___y_1637_, v___y_1635_, v___y_1639_, v___y_1638_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_dec(v_a_1645_);
lean_dec(v___y_1636_);
v___y_1437_ = v___y_1635_;
v___y_1438_ = v___y_1637_;
v___y_1439_ = v___y_1638_;
v___y_1440_ = v___y_1639_;
v___y_1441_ = v___x_1646_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1647_; uint8_t v___x_1648_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
v___x_1648_ = l_Lean_Exception_isInterrupt(v_a_1647_);
if (v___x_1648_ == 0)
{
uint8_t v___x_1649_; 
v___x_1649_ = l_Lean_Exception_isRuntime(v_a_1647_);
v___y_1609_ = v___y_1635_;
v___y_1610_ = v_a_1645_;
v___y_1611_ = v___y_1636_;
v___y_1612_ = v___x_1646_;
v___y_1613_ = v___y_1637_;
v___y_1614_ = v___y_1638_;
v___y_1615_ = v___y_1639_;
v___y_1616_ = v___y_1640_;
v___y_1617_ = v___x_1649_;
goto v___jp_1608_;
}
else
{
lean_dec(v_a_1647_);
v___y_1609_ = v___y_1635_;
v___y_1610_ = v_a_1645_;
v___y_1611_ = v___y_1636_;
v___y_1612_ = v___x_1646_;
v___y_1613_ = v___y_1637_;
v___y_1614_ = v___y_1638_;
v___y_1615_ = v___y_1639_;
v___y_1616_ = v___y_1640_;
v___y_1617_ = v___x_1648_;
goto v___jp_1608_;
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1636_);
lean_dec(v_matchDeclName_1409_);
v_a_1650_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1644_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1644_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1636_);
lean_dec(v_matchDeclName_1409_);
return v___x_1643_;
}
}
else
{
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1636_);
v___y_1437_ = v___y_1635_;
v___y_1438_ = v___y_1637_;
v___y_1439_ = v___y_1638_;
v___y_1440_ = v___y_1639_;
v___y_1441_ = v___y_1634_;
goto v___jp_1436_;
}
}
v___jp_1658_:
{
if (v___y_1667_ == 0)
{
lean_object* v___x_1668_; 
lean_dec_ref(v___y_1659_);
v___x_1668_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1666_, v___y_1660_, v___y_1663_);
lean_dec_ref(v___y_1666_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v___x_1669_; 
lean_dec_ref(v___x_1668_);
v___x_1669_ = l_Lean_Meta_saveState___redArg(v___y_1660_, v___y_1663_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref(v___x_1669_);
lean_inc(v___y_1661_);
v___x_1671_ = l_Lean_Meta_casesOnStuckLHS(v___y_1661_, v___y_1662_, v___y_1660_, v___y_1664_, v___y_1663_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_dec(v_a_1670_);
lean_dec(v___y_1661_);
v___y_1437_ = v___y_1660_;
v___y_1438_ = v___y_1662_;
v___y_1439_ = v___y_1663_;
v___y_1440_ = v___y_1664_;
v___y_1441_ = v___x_1671_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1672_; uint8_t v___x_1673_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
v___x_1673_ = l_Lean_Exception_isInterrupt(v_a_1672_);
if (v___x_1673_ == 0)
{
uint8_t v___x_1674_; 
v___x_1674_ = l_Lean_Exception_isRuntime(v_a_1672_);
v___y_1634_ = v___x_1671_;
v___y_1635_ = v___y_1660_;
v___y_1636_ = v___y_1661_;
v___y_1637_ = v___y_1662_;
v___y_1638_ = v___y_1663_;
v___y_1639_ = v___y_1664_;
v___y_1640_ = v___y_1665_;
v___y_1641_ = v_a_1670_;
v___y_1642_ = v___x_1674_;
goto v___jp_1633_;
}
else
{
lean_dec(v_a_1672_);
v___y_1634_ = v___x_1671_;
v___y_1635_ = v___y_1660_;
v___y_1636_ = v___y_1661_;
v___y_1637_ = v___y_1662_;
v___y_1638_ = v___y_1663_;
v___y_1639_ = v___y_1664_;
v___y_1640_ = v___y_1665_;
v___y_1641_ = v_a_1670_;
v___y_1642_ = v___x_1673_;
goto v___jp_1633_;
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1661_);
lean_dec(v_matchDeclName_1409_);
v_a_1675_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1669_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1669_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1661_);
lean_dec(v_matchDeclName_1409_);
return v___x_1668_;
}
}
else
{
lean_object* v___x_1683_; 
lean_dec_ref(v___y_1666_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1661_);
lean_dec(v_matchDeclName_1409_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___y_1659_);
return v___x_1683_;
}
}
v___jp_1684_:
{
if (v___y_1693_ == 0)
{
lean_object* v___x_1694_; 
lean_dec_ref(v___y_1686_);
v___x_1694_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1685_, v___y_1687_, v___y_1690_);
lean_dec_ref(v___y_1685_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v___x_1695_; 
lean_dec_ref(v___x_1694_);
v___x_1695_ = l_Lean_Meta_saveState___redArg(v___y_1687_, v___y_1690_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1697_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref(v___x_1695_);
lean_inc(v___y_1688_);
v___x_1697_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1688_, v___y_1689_, v___y_1687_, v___y_1691_, v___y_1690_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_dec(v_a_1696_);
lean_dec(v___y_1688_);
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref(v___x_1697_);
v___x_1699_ = lean_unsigned_to_nat(1u);
v___x_1700_ = lean_mk_empty_array_with_capacity(v___x_1699_);
v___x_1701_ = lean_array_push(v___x_1700_, v_a_1698_);
v___y_1418_ = v___y_1687_;
v___y_1419_ = v___y_1690_;
v___y_1420_ = v___y_1689_;
v___y_1421_ = v___y_1691_;
v_a_1422_ = v___x_1701_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1702_; uint8_t v___x_1703_; 
v_a_1702_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1702_);
lean_dec_ref(v___x_1697_);
v___x_1703_ = l_Lean_Exception_isInterrupt(v_a_1702_);
if (v___x_1703_ == 0)
{
uint8_t v___x_1704_; 
lean_inc(v_a_1702_);
v___x_1704_ = l_Lean_Exception_isRuntime(v_a_1702_);
v___y_1659_ = v_a_1702_;
v___y_1660_ = v___y_1687_;
v___y_1661_ = v___y_1688_;
v___y_1662_ = v___y_1689_;
v___y_1663_ = v___y_1690_;
v___y_1664_ = v___y_1691_;
v___y_1665_ = v___y_1692_;
v___y_1666_ = v_a_1696_;
v___y_1667_ = v___x_1704_;
goto v___jp_1658_;
}
else
{
v___y_1659_ = v_a_1702_;
v___y_1660_ = v___y_1687_;
v___y_1661_ = v___y_1688_;
v___y_1662_ = v___y_1689_;
v___y_1663_ = v___y_1690_;
v___y_1664_ = v___y_1691_;
v___y_1665_ = v___y_1692_;
v___y_1666_ = v_a_1696_;
v___y_1667_ = v___x_1703_;
goto v___jp_1658_;
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v_matchDeclName_1409_);
v_a_1705_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1695_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1695_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
else
{
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec(v_matchDeclName_1409_);
return v___x_1694_;
}
}
else
{
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1685_);
lean_dec(v_matchDeclName_1409_);
return v___y_1686_;
}
}
v___jp_1713_:
{
if (v___y_1722_ == 0)
{
lean_object* v___x_1723_; 
lean_dec_ref(v___y_1717_);
v___x_1723_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1715_, v___y_1714_, v___y_1719_);
lean_dec_ref(v___y_1715_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
lean_dec_ref(v___x_1723_);
v___x_1724_ = lean_unsigned_to_nat(16u);
v___x_1725_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*1, v___y_1721_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*1 + 1, v___y_1721_);
lean_ctor_set_uint8(v___x_1725_, sizeof(void*)*1 + 2, v___y_1721_);
v___x_1726_ = l_Lean_Meta_saveState___redArg(v___y_1714_, v___y_1719_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref(v___x_1726_);
lean_inc(v___y_1716_);
v___x_1728_ = l_Lean_MVarId_contradiction(v___y_1716_, v___x_1725_, v___y_1718_, v___y_1714_, v___y_1720_, v___y_1719_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref(v___x_1728_);
lean_dec(v_a_1727_);
lean_dec(v___y_1716_);
v___x_1729_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1418_ = v___y_1714_;
v___y_1419_ = v___y_1719_;
v___y_1420_ = v___y_1718_;
v___y_1421_ = v___y_1720_;
v_a_1422_ = v___x_1729_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1730_; uint8_t v___x_1731_; 
v_a_1730_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1730_);
v___x_1731_ = l_Lean_Exception_isInterrupt(v_a_1730_);
if (v___x_1731_ == 0)
{
uint8_t v___x_1732_; 
v___x_1732_ = l_Lean_Exception_isRuntime(v_a_1730_);
v___y_1685_ = v_a_1727_;
v___y_1686_ = v___x_1728_;
v___y_1687_ = v___y_1714_;
v___y_1688_ = v___y_1716_;
v___y_1689_ = v___y_1718_;
v___y_1690_ = v___y_1719_;
v___y_1691_ = v___y_1720_;
v___y_1692_ = v___y_1721_;
v___y_1693_ = v___x_1732_;
goto v___jp_1684_;
}
else
{
lean_dec(v_a_1730_);
v___y_1685_ = v_a_1727_;
v___y_1686_ = v___x_1728_;
v___y_1687_ = v___y_1714_;
v___y_1688_ = v___y_1716_;
v___y_1689_ = v___y_1718_;
v___y_1690_ = v___y_1719_;
v___y_1691_ = v___y_1720_;
v___y_1692_ = v___y_1721_;
v___y_1693_ = v___x_1731_;
goto v___jp_1684_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec_ref(v___x_1725_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1716_);
lean_dec(v_matchDeclName_1409_);
v_a_1733_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1726_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1726_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1716_);
lean_dec(v_matchDeclName_1409_);
return v___x_1723_;
}
}
else
{
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v_matchDeclName_1409_);
return v___y_1717_;
}
}
v___jp_1741_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1747_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1410_, v___x_1746_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = l_Lean_Meta_saveState___redArg(v___y_1743_, v___y_1745_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = 1;
lean_inc(v_a_1748_);
v___x_1752_ = l_Lean_MVarId_refl(v_a_1748_, v___x_1751_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v___x_1753_; 
lean_dec_ref(v___x_1752_);
lean_dec(v_a_1750_);
lean_dec(v_a_1748_);
v___x_1753_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1418_ = v___y_1743_;
v___y_1419_ = v___y_1745_;
v___y_1420_ = v___y_1742_;
v___y_1421_ = v___y_1744_;
v_a_1422_ = v___x_1753_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1754_; uint8_t v___x_1755_; 
v_a_1754_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1754_);
v___x_1755_ = l_Lean_Exception_isInterrupt(v_a_1754_);
if (v___x_1755_ == 0)
{
uint8_t v___x_1756_; 
v___x_1756_ = l_Lean_Exception_isRuntime(v_a_1754_);
v___y_1714_ = v___y_1743_;
v___y_1715_ = v_a_1750_;
v___y_1716_ = v_a_1748_;
v___y_1717_ = v___x_1752_;
v___y_1718_ = v___y_1742_;
v___y_1719_ = v___y_1745_;
v___y_1720_ = v___y_1744_;
v___y_1721_ = v___x_1751_;
v___y_1722_ = v___x_1756_;
goto v___jp_1713_;
}
else
{
lean_dec(v_a_1754_);
v___y_1714_ = v___y_1743_;
v___y_1715_ = v_a_1750_;
v___y_1716_ = v_a_1748_;
v___y_1717_ = v___x_1752_;
v___y_1718_ = v___y_1742_;
v___y_1719_ = v___y_1745_;
v___y_1720_ = v___y_1744_;
v___y_1721_ = v___x_1751_;
v___y_1722_ = v___x_1755_;
goto v___jp_1713_;
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec(v_a_1748_);
lean_dec_ref(v___y_1744_);
lean_dec(v_matchDeclName_1409_);
v_a_1757_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1749_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1749_);
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
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v___y_1744_);
lean_dec(v_matchDeclName_1409_);
v_a_1765_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1747_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1747_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
v___jp_1790_:
{
uint8_t v_hasTrace_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_hasTrace_1791_ = lean_ctor_get_uint8(v_options_1775_, sizeof(void*)*1);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_add(v_currRecDepth_1776_, v___x_1792_);
lean_inc_ref(v_inheritedTraceOptions_1788_);
lean_inc(v_cancelTk_x3f_1786_);
lean_inc(v_currMacroScope_1784_);
lean_inc(v_quotContext_1783_);
lean_inc(v_maxHeartbeats_1782_);
lean_inc(v_initHeartbeats_1781_);
lean_inc(v_openDecls_1780_);
lean_inc(v_currNamespace_1779_);
lean_inc(v_ref_1778_);
lean_inc(v_maxRecDepth_1777_);
lean_inc_ref(v_options_1775_);
lean_inc_ref(v_fileMap_1774_);
lean_inc_ref(v_fileName_1773_);
v___x_1794_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1794_, 0, v_fileName_1773_);
lean_ctor_set(v___x_1794_, 1, v_fileMap_1774_);
lean_ctor_set(v___x_1794_, 2, v_options_1775_);
lean_ctor_set(v___x_1794_, 3, v___x_1793_);
lean_ctor_set(v___x_1794_, 4, v_maxRecDepth_1777_);
lean_ctor_set(v___x_1794_, 5, v_ref_1778_);
lean_ctor_set(v___x_1794_, 6, v_currNamespace_1779_);
lean_ctor_set(v___x_1794_, 7, v_openDecls_1780_);
lean_ctor_set(v___x_1794_, 8, v_initHeartbeats_1781_);
lean_ctor_set(v___x_1794_, 9, v_maxHeartbeats_1782_);
lean_ctor_set(v___x_1794_, 10, v_quotContext_1783_);
lean_ctor_set(v___x_1794_, 11, v_currMacroScope_1784_);
lean_ctor_set(v___x_1794_, 12, v_cancelTk_x3f_1786_);
lean_ctor_set(v___x_1794_, 13, v_inheritedTraceOptions_1788_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*14, v_diag_1785_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*14 + 1, v_suppressElabErrors_1787_);
if (v_hasTrace_1791_ == 0)
{
v___y_1742_ = v_a_1412_;
v___y_1743_ = v_a_1413_;
v___y_1744_ = v___x_1794_;
v___y_1745_ = v_a_1415_;
goto v___jp_1741_;
}
else
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1796_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1788_, v_options_1775_, v___x_1795_);
if (v___x_1796_ == 0)
{
v___y_1742_ = v_a_1412_;
v___y_1743_ = v_a_1413_;
v___y_1744_ = v___x_1794_;
v___y_1745_ = v_a_1415_;
goto v___jp_1741_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1797_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1410_);
v___x_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1798_, 0, v_mvarId_1410_);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1789_, v___x_1799_, v_a_1412_, v_a_1413_, v___x_1794_, v_a_1415_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_dec_ref(v___x_1800_);
v___y_1742_ = v_a_1412_;
v___y_1743_ = v_a_1413_;
v___y_1744_ = v___x_1794_;
v___y_1745_ = v_a_1415_;
goto v___jp_1741_;
}
else
{
lean_dec_ref(v___x_1794_);
lean_dec(v_mvarId_1410_);
lean_dec(v_matchDeclName_1409_);
return v___x_1800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1805_, lean_object* v_matchDeclName_1806_, lean_object* v_as_1807_, size_t v_i_1808_, size_t v_stop_1809_, lean_object* v_b_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_usize_dec_eq(v_i_1808_, v_stop_1809_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1817_ = lean_array_uget_borrowed(v_as_1807_, v_i_1808_);
v___x_1818_ = lean_unsigned_to_nat(1u);
v___x_1819_ = lean_nat_add(v_depth_1805_, v___x_1818_);
lean_inc(v___x_1817_);
lean_inc(v_matchDeclName_1806_);
v___x_1820_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1806_, v___x_1817_, v___x_1819_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___x_1819_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; size_t v___x_1822_; size_t v___x_1823_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = ((size_t)1ULL);
v___x_1823_ = lean_usize_add(v_i_1808_, v___x_1822_);
v_i_1808_ = v___x_1823_;
v_b_1810_ = v_a_1821_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1806_);
return v___x_1820_;
}
}
else
{
lean_object* v___x_1825_; 
lean_dec(v_matchDeclName_1806_);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_b_1810_);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1826_, lean_object* v_matchDeclName_1827_, lean_object* v_as_1828_, lean_object* v_i_1829_, lean_object* v_stop_1830_, lean_object* v_b_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
size_t v_i_boxed_1837_; size_t v_stop_boxed_1838_; lean_object* v_res_1839_; 
v_i_boxed_1837_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_stop_boxed_1838_ = lean_unbox_usize(v_stop_1830_);
lean_dec(v_stop_1830_);
v_res_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1826_, v_matchDeclName_1827_, v_as_1828_, v_i_boxed_1837_, v_stop_boxed_1838_, v_b_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec_ref(v_as_1828_);
lean_dec(v_depth_1826_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1840_, lean_object* v_mvarId_1841_, lean_object* v_depth_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1840_, v_mvarId_1841_, v_depth_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_depth_1842_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1849_, lean_object* v___y_1850_){
_start:
{
uint8_t v___x_1852_; 
v___x_1852_ = l_Lean_Expr_hasMVar(v_e_1849_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_e_1849_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; lean_object* v_mctx_1855_; lean_object* v___x_1856_; lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v___x_1859_; lean_object* v_cache_1860_; lean_object* v_zetaDeltaFVarIds_1861_; lean_object* v_postponed_1862_; lean_object* v_diag_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1872_; 
v___x_1854_ = lean_st_ref_get(v___y_1850_);
v_mctx_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc_ref(v_mctx_1855_);
lean_dec(v___x_1854_);
v___x_1856_ = l_Lean_instantiateMVarsCore(v_mctx_1855_, v_e_1849_);
v_fst_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_fst_1857_);
v_snd_1858_ = lean_ctor_get(v___x_1856_, 1);
lean_inc(v_snd_1858_);
lean_dec_ref(v___x_1856_);
v___x_1859_ = lean_st_ref_take(v___y_1850_);
v_cache_1860_ = lean_ctor_get(v___x_1859_, 1);
v_zetaDeltaFVarIds_1861_ = lean_ctor_get(v___x_1859_, 2);
v_postponed_1862_ = lean_ctor_get(v___x_1859_, 3);
v_diag_1863_ = lean_ctor_get(v___x_1859_, 4);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; 
v_unused_1873_ = lean_ctor_get(v___x_1859_, 0);
lean_dec(v_unused_1873_);
v___x_1865_ = v___x_1859_;
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_diag_1863_);
lean_inc(v_postponed_1862_);
lean_inc(v_zetaDeltaFVarIds_1861_);
lean_inc(v_cache_1860_);
lean_dec(v___x_1859_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1872_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v_snd_1858_);
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_snd_1858_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_cache_1860_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_zetaDeltaFVarIds_1861_);
lean_ctor_set(v_reuseFailAlloc_1871_, 3, v_postponed_1862_);
lean_ctor_set(v_reuseFailAlloc_1871_, 4, v_diag_1863_);
v___x_1868_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_st_ref_set(v___y_1850_, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_fst_1857_);
return v___x_1870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1874_, v___y_1875_);
lean_dec(v___y_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1878_, v___y_1880_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1892_, lean_object* v_localInsts_1893_, lean_object* v_x_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1892_, v_localInsts_1893_, v_x_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1900_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1900_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1917_, lean_object* v_localInsts_1918_, lean_object* v_x_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1917_, v_localInsts_1918_, v_x_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1926_, lean_object* v_lctx_1927_, lean_object* v_localInsts_1928_, lean_object* v_x_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1927_, v_localInsts_1928_, v_x_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1936_, lean_object* v_lctx_1937_, lean_object* v_localInsts_1938_, lean_object* v_x_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1936_, v_lctx_1937_, v_localInsts_1938_, v_x_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
return v_res_1945_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1946_, lean_object* v_x_1947_){
_start:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_name_eq(v_x_1947_, v_matchDeclName_1946_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1949_, lean_object* v_x_1950_){
_start:
{
uint8_t v_res_1951_; lean_object* v_r_1952_; 
v_res_1951_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1949_, v_x_1950_);
lean_dec(v_x_1950_);
lean_dec(v_matchDeclName_1949_);
v_r_1952_ = lean_box(v_res_1951_);
return v_r_1952_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1953_, lean_object* v_a_1954_, lean_object* v_b_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_nat_dec_lt(v_a_1954_, v_upperBound_1953_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_dec(v_a_1954_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v_b_1955_);
return v___x_1962_;
}
else
{
uint8_t v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = 0;
v___x_1964_ = l_Lean_Meta_introSubstEq(v_b_1955_, v___x_1963_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v_snd_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref(v___x_1964_);
v_snd_1966_ = lean_ctor_get(v_a_1965_, 1);
lean_inc(v_snd_1966_);
lean_dec(v_a_1965_);
v___x_1967_ = lean_unsigned_to_nat(1u);
v___x_1968_ = lean_nat_add(v_a_1954_, v___x_1967_);
lean_dec(v_a_1954_);
v_a_1954_ = v___x_1968_;
v_b_1955_ = v_snd_1966_;
goto _start;
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec(v_a_1954_);
v_a_1970_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1964_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1964_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1978_, lean_object* v_a_1979_, lean_object* v_b_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1978_, v_a_1979_, v_b_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v_upperBound_1978_);
return v_res_1986_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1989_ = l_Lean_stringToMessageData(v___x_1988_);
return v___x_1989_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1992_ = l_Lean_stringToMessageData(v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1993_, lean_object* v___f_1994_, lean_object* v_matchDeclName_1995_, lean_object* v___x_1996_, uint8_t v___x_1997_, lean_object* v_heqPos_1998_, lean_object* v_heqNum_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___x_2005_; lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2156_; 
v___x_2005_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1993_, v___y_2001_);
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2156_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2156_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_box(0);
v___x_2011_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2006_, v___x_2010_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2155_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2155_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2155_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; uint8_t v___y_2023_; lean_object* v_mvarId_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v_options_2080_; lean_object* v_inheritedTraceOptions_2081_; uint8_t v_hasTrace_2082_; lean_object* v___x_2083_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; 
v_options_2080_ = lean_ctor_get(v___y_2002_, 2);
v_inheritedTraceOptions_2081_ = lean_ctor_get(v___y_2002_, 13);
v_hasTrace_2082_ = lean_ctor_get_uint8(v_options_2080_, sizeof(void*)*1);
v___x_2083_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2082_ == 0)
{
v___y_2085_ = v___y_2000_;
v___y_2086_ = v___y_2001_;
v___y_2087_ = v___y_2002_;
v___y_2088_ = v___y_2003_;
goto v___jp_2084_;
}
else
{
lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2141_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2081_, v_options_2080_, v___x_2140_);
if (v___x_2141_ == 0)
{
v___y_2085_ = v___y_2000_;
v___y_2086_ = v___y_2001_;
v___y_2087_ = v___y_2002_;
v___y_2088_ = v___y_2003_;
goto v___jp_2084_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2142_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2143_ = l_Lean_Expr_mvarId_x21(v_a_2012_);
v___x_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2142_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2083_, v___x_2145_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_dec_ref(v___x_2146_);
v___y_2085_ = v___y_2000_;
v___y_2086_ = v___y_2001_;
v___y_2087_ = v___y_2002_;
v___y_2088_ = v___y_2003_;
goto v___jp_2084_;
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_del_object(v___x_2014_);
lean_dec(v_a_2012_);
lean_del_object(v___x_2008_);
lean_dec(v_heqPos_1998_);
lean_dec(v___x_1996_);
lean_dec(v_matchDeclName_1995_);
lean_dec_ref(v___f_1994_);
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2146_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
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
v___jp_2016_:
{
if (v___y_2023_ == 0)
{
lean_object* v___x_2024_; 
lean_dec_ref(v___y_2017_);
lean_del_object(v___x_2014_);
v___x_2024_ = l_Lean_MVarId_deltaTarget(v___y_2022_, v___f_1994_, v___y_2021_, v___y_2020_, v___y_2019_, v___y_2018_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
v___x_2026_ = l_Lean_MVarId_heqOfEq(v_a_2025_, v___y_2021_, v___y_2020_, v___y_2019_, v___y_2018_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2026_);
v___x_2028_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1995_, v_a_2027_, v___x_1996_, v___y_2021_, v___y_2020_, v___y_2019_, v___y_2018_);
lean_dec(v___x_1996_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v___x_2029_; 
lean_dec_ref(v___x_2028_);
v___x_2029_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2012_, v___y_2020_);
return v___x_2029_;
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_a_2012_);
v_a_2030_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2028_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2028_);
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
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_a_2012_);
lean_dec(v___x_1996_);
lean_dec(v_matchDeclName_1995_);
v_a_2038_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2026_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2026_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_a_2012_);
lean_dec(v___x_1996_);
lean_dec(v_matchDeclName_1995_);
v_a_2046_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2024_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2024_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_object* v___x_2055_; 
lean_dec(v___y_2022_);
lean_dec(v_a_2012_);
lean_dec(v___x_1996_);
lean_dec(v_matchDeclName_1995_);
lean_dec_ref(v___f_1994_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 1);
lean_ctor_set(v___x_2014_, 0, v___y_2017_);
v___x_2055_ = v___x_2014_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___y_2017_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
v___jp_2057_:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_MVarId_intros(v_mvarId_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v_snd_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
v_snd_2065_ = lean_ctor_get(v_a_2064_, 1);
lean_inc_n(v_snd_2065_, 2);
lean_dec(v_a_2064_);
v___x_2066_ = 1;
v___x_2067_ = l_Lean_MVarId_refl(v_snd_2065_, v___x_2066_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v___x_2068_; 
lean_dec_ref(v___x_2067_);
lean_dec(v_snd_2065_);
lean_del_object(v___x_2014_);
lean_dec(v___x_1996_);
lean_dec(v_matchDeclName_1995_);
lean_dec_ref(v___f_1994_);
v___x_2068_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2012_, v___y_2060_);
return v___x_2068_;
}
else
{
lean_object* v_a_2069_; uint8_t v___x_2070_; 
v_a_2069_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2069_);
lean_dec_ref(v___x_2067_);
v___x_2070_ = l_Lean_Exception_isInterrupt(v_a_2069_);
if (v___x_2070_ == 0)
{
uint8_t v___x_2071_; 
lean_inc(v_a_2069_);
v___x_2071_ = l_Lean_Exception_isRuntime(v_a_2069_);
v___y_2017_ = v_a_2069_;
v___y_2018_ = v___y_2062_;
v___y_2019_ = v___y_2061_;
v___y_2020_ = v___y_2060_;
v___y_2021_ = v___y_2059_;
v___y_2022_ = v_snd_2065_;
v___y_2023_ = v___x_2071_;
goto v___jp_2016_;
}
else
{
v___y_2017_ = v_a_2069_;
v___y_2018_ = v___y_2062_;
v___y_2019_ = v___y_2061_;
v___y_2020_ = v___y_2060_;
v___y_2021_ = v___y_2059_;
v___y_2022_ = v_snd_2065_;
v___y_2023_ = v___x_2070_;
goto v___jp_2016_;
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_del_object(v___x_2014_);
lean_dec(v_a_2012_);
lean_dec(v___x_1996_);
lean_dec(v_matchDeclName_1995_);
lean_dec_ref(v___f_1994_);
v_a_2072_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2063_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2063_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
v___jp_2084_:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Expr_mvarId_x21(v_a_2012_);
if (v___x_1997_ == 0)
{
lean_del_object(v___x_2008_);
lean_dec(v_heqPos_1998_);
v_mvarId_2058_ = v___x_2089_;
v___y_2059_ = v___y_2085_;
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2087_;
v___y_2062_ = v___y_2088_;
goto v___jp_2057_;
}
else
{
lean_object* v___x_2090_; uint8_t v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = lean_box(0);
v___x_2091_ = 0;
v___x_2092_ = l_Lean_Meta_introNCore(v___x_2089_, v_heqPos_1998_, v___x_2090_, v___x_2091_, v___x_2091_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v_snd_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2130_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref(v___x_2092_);
v_snd_2094_ = lean_ctor_get(v_a_2093_, 1);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_a_2093_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v_a_2093_, 0);
lean_dec(v_unused_2131_);
v___x_2096_ = v_a_2093_;
v_isShared_2097_ = v_isSharedCheck_2130_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_snd_2094_);
lean_dec(v_a_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2130_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; 
lean_inc(v___x_1996_);
v___x_2098_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1999_, v___x_1996_, v_snd_2094_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_options_2099_; uint8_t v_hasTrace_2100_; 
v_options_2099_ = lean_ctor_get(v___y_2087_, 2);
v_hasTrace_2100_ = lean_ctor_get_uint8(v_options_2099_, sizeof(void*)*1);
if (v_hasTrace_2100_ == 0)
{
lean_object* v_a_2101_; 
lean_del_object(v___x_2096_);
lean_del_object(v___x_2008_);
v_a_2101_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2098_);
v_mvarId_2058_ = v_a_2101_;
v___y_2059_ = v___y_2085_;
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2087_;
v___y_2062_ = v___y_2088_;
goto v___jp_2057_;
}
else
{
lean_object* v_a_2102_; lean_object* v_inheritedTraceOptions_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
v_a_2102_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2098_);
v_inheritedTraceOptions_2103_ = lean_ctor_get(v___y_2087_, 13);
v___x_2104_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2105_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2103_, v_options_2099_, v___x_2104_);
if (v___x_2105_ == 0)
{
lean_del_object(v___x_2096_);
lean_del_object(v___x_2008_);
v_mvarId_2058_ = v_a_2102_;
v___y_2059_ = v___y_2085_;
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2087_;
v___y_2062_ = v___y_2088_;
goto v___jp_2057_;
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2102_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set_tag(v___x_2008_, 1);
lean_ctor_set(v___x_2008_, 0, v_a_2102_);
v___x_2108_ = v___x_2008_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2102_);
v___x_2108_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 7);
lean_ctor_set(v___x_2096_, 1, v___x_2108_);
lean_ctor_set(v___x_2096_, 0, v___x_2106_);
v___x_2110_ = v___x_2096_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2083_, v___x_2110_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_dec_ref(v___x_2111_);
v_mvarId_2058_ = v_a_2102_;
v___y_2059_ = v___y_2085_;
v___y_2060_ = v___y_2086_;
v___y_2061_ = v___y_2087_;
v___y_2062_ = v___y_2088_;
goto v___jp_2057_;
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_a_2102_);
lean_del_object(v___x_2014_);
lean_dec(v_a_2012_);
lean_dec(v___x_1996_);
lean_dec(v_matchDeclName_1995_);
lean_dec_ref(v___f_1994_);
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
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
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_del_object(v___x_2096_);
lean_del_object(v___x_2014_);
lean_dec(v_a_2012_);
lean_del_object(v___x_2008_);
lean_dec(v___x_1996_);
lean_dec(v_matchDeclName_1995_);
lean_dec_ref(v___f_1994_);
v_a_2122_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2098_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2098_);
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
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_del_object(v___x_2014_);
lean_dec(v_a_2012_);
lean_del_object(v___x_2008_);
lean_dec(v___x_1996_);
lean_dec(v_matchDeclName_1995_);
lean_dec_ref(v___f_1994_);
v_a_2132_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2092_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2092_);
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
}
}
else
{
lean_del_object(v___x_2008_);
lean_dec(v_heqPos_1998_);
lean_dec(v___x_1996_);
lean_dec(v_matchDeclName_1995_);
lean_dec_ref(v___f_1994_);
return v___x_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2157_, lean_object* v___f_2158_, lean_object* v_matchDeclName_2159_, lean_object* v___x_2160_, lean_object* v___x_2161_, lean_object* v_heqPos_2162_, lean_object* v_heqNum_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
uint8_t v___x_6046__boxed_2169_; lean_object* v_res_2170_; 
v___x_6046__boxed_2169_ = lean_unbox(v___x_2161_);
v_res_2170_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2157_, v___f_2158_, v_matchDeclName_2159_, v___x_2160_, v___x_6046__boxed_2169_, v_heqPos_2162_, v_heqNum_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v_heqNum_2163_);
return v_res_2170_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_unsigned_to_nat(32u);
v___x_2175_ = lean_mk_empty_array_with_capacity(v___x_2174_);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2177_ = ((size_t)5ULL);
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2179_ = lean_unsigned_to_nat(32u);
v___x_2180_ = lean_mk_empty_array_with_capacity(v___x_2179_);
v___x_2181_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2182_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2180_);
lean_ctor_set(v___x_2182_, 2, v___x_2178_);
lean_ctor_set(v___x_2182_, 3, v___x_2178_);
lean_ctor_set_usize(v___x_2182_, 4, v___x_2177_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2183_ = lean_box(1);
v___x_2184_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2185_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v___x_2184_);
lean_ctor_set(v___x_2186_, 2, v___x_2183_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2189_, lean_object* v_type_2190_, lean_object* v_heqPos_2191_, lean_object* v_heqNum_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___f_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; 
lean_inc(v_matchDeclName_2189_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2198_, 0, v_matchDeclName_2189_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2201_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2202_ = lean_nat_dec_lt(v___x_2199_, v_heqNum_2192_);
v___x_2203_ = lean_box(v___x_2202_);
v___f_2204_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2204_, 0, v_type_2190_);
lean_closure_set(v___f_2204_, 1, v___f_2198_);
lean_closure_set(v___f_2204_, 2, v_matchDeclName_2189_);
lean_closure_set(v___f_2204_, 3, v___x_2199_);
lean_closure_set(v___f_2204_, 4, v___x_2203_);
lean_closure_set(v___f_2204_, 5, v_heqPos_2191_);
lean_closure_set(v___f_2204_, 6, v_heqNum_2192_);
v___x_2205_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2200_, v___x_2201_, v___f_2204_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2206_, lean_object* v_type_2207_, lean_object* v_heqPos_2208_, lean_object* v_heqNum_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2206_, v_type_2207_, v_heqPos_2208_, v_heqNum_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2216_, lean_object* v_inst_2217_, lean_object* v_R_2218_, lean_object* v_a_2219_, lean_object* v_b_2220_, lean_object* v_c_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2216_, v_a_2219_, v_b_2220_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2228_, lean_object* v_inst_2229_, lean_object* v_R_2230_, lean_object* v_a_2231_, lean_object* v_b_2232_, lean_object* v_c_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2228_, v_inst_2229_, v_R_2230_, v_a_2231_, v_b_2232_, v_c_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v_upperBound_2228_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2240_, lean_object* v_b_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; 
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
lean_inc(v___y_2243_);
lean_inc_ref(v___y_2242_);
v___x_2247_ = lean_apply_6(v_k_2240_, v_b_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, lean_box(0));
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2248_, lean_object* v_b_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2248_, v_b_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2256_, uint8_t v_bi_2257_, lean_object* v_type_2258_, lean_object* v_k_2259_, uint8_t v_kind_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___f_2266_; lean_object* v___x_2267_; 
v___f_2266_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2266_, 0, v_k_2259_);
v___x_2267_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2256_, v_bi_2257_, v_type_2258_, v___f_2266_, v_kind_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2267_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
v_a_2276_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2267_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2267_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2284_, lean_object* v_bi_2285_, lean_object* v_type_2286_, lean_object* v_k_2287_, lean_object* v_kind_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
uint8_t v_bi_boxed_2294_; uint8_t v_kind_boxed_2295_; lean_object* v_res_2296_; 
v_bi_boxed_2294_ = lean_unbox(v_bi_2285_);
v_kind_boxed_2295_ = lean_unbox(v_kind_2288_);
v_res_2296_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2284_, v_bi_boxed_2294_, v_type_2286_, v_k_2287_, v_kind_boxed_2295_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2297_, lean_object* v_name_2298_, uint8_t v_bi_2299_, lean_object* v_type_2300_, lean_object* v_k_2301_, uint8_t v_kind_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2298_, v_bi_2299_, v_type_2300_, v_k_2301_, v_kind_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2309_, lean_object* v_name_2310_, lean_object* v_bi_2311_, lean_object* v_type_2312_, lean_object* v_k_2313_, lean_object* v_kind_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
uint8_t v_bi_boxed_2320_; uint8_t v_kind_boxed_2321_; lean_object* v_res_2322_; 
v_bi_boxed_2320_ = lean_unbox(v_bi_2311_);
v_kind_boxed_2321_ = lean_unbox(v_kind_2314_);
v_res_2322_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2309_, v_name_2310_, v_bi_boxed_2320_, v_type_2312_, v_k_2313_, v_kind_boxed_2321_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2323_, lean_object* v_altsNew_2324_, lean_object* v_discrs_2325_, lean_object* v_patterns_2326_, lean_object* v_alts_2327_, lean_object* v_k_2328_, lean_object* v_altNew_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2323_, v_altsNew_2324_, v_discrs_2325_, v_patterns_2326_, v_alts_2327_, v_k_2328_, v_altNew_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v_i_2323_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2336_, lean_object* v_patterns_2337_, lean_object* v_alts_2338_, lean_object* v_k_2339_, lean_object* v_i_2340_, lean_object* v_altsNew_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2347_ = lean_array_get_size(v_alts_2338_);
v___x_2348_ = lean_nat_dec_lt(v_i_2340_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; 
lean_dec(v_i_2340_);
lean_dec_ref(v_alts_2338_);
lean_dec_ref(v_patterns_2337_);
lean_dec_ref(v_discrs_2336_);
lean_inc(v_a_2345_);
lean_inc_ref(v_a_2344_);
lean_inc(v_a_2343_);
lean_inc_ref(v_a_2342_);
v___x_2349_ = lean_apply_6(v_k_2339_, v_altsNew_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, lean_box(0));
return v___x_2349_;
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_array_fget_borrowed(v_alts_2338_, v_i_2340_);
v___x_2351_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2350_, v_a_2342_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___f_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2359_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref(v___x_2351_);
lean_inc_ref(v_patterns_2337_);
lean_inc_ref(v_discrs_2336_);
v___f_2353_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2353_, 0, v_i_2340_);
lean_closure_set(v___f_2353_, 1, v_altsNew_2341_);
lean_closure_set(v___f_2353_, 2, v_discrs_2336_);
lean_closure_set(v___f_2353_, 3, v_patterns_2337_);
lean_closure_set(v___f_2353_, 4, v_alts_2338_);
lean_closure_set(v___f_2353_, 5, v_k_2339_);
v___x_2354_ = l_Lean_LocalDecl_type(v_a_2352_);
v___x_2355_ = l_Lean_Expr_replaceFVars(v___x_2354_, v_discrs_2336_, v_patterns_2337_);
lean_dec_ref(v_patterns_2337_);
lean_dec_ref(v_discrs_2336_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = l_Lean_LocalDecl_userName(v_a_2352_);
v___x_2357_ = l_Lean_LocalDecl_binderInfo(v_a_2352_);
lean_dec(v_a_2352_);
v___x_2358_ = 0;
v___x_2359_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2356_, v___x_2357_, v___x_2355_, v___f_2353_, v___x_2358_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
return v___x_2359_;
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v_altsNew_2341_);
lean_dec(v_i_2340_);
lean_dec_ref(v_k_2339_);
lean_dec_ref(v_alts_2338_);
lean_dec_ref(v_patterns_2337_);
lean_dec_ref(v_discrs_2336_);
v_a_2360_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2351_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2351_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2368_, lean_object* v_altsNew_2369_, lean_object* v_discrs_2370_, lean_object* v_patterns_2371_, lean_object* v_alts_2372_, lean_object* v_k_2373_, lean_object* v_altNew_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2380_ = lean_unsigned_to_nat(1u);
v___x_2381_ = lean_nat_add(v_i_2368_, v___x_2380_);
v___x_2382_ = lean_array_push(v_altsNew_2369_, v_altNew_2374_);
v___x_2383_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2370_, v_patterns_2371_, v_alts_2372_, v_k_2373_, v___x_2381_, v___x_2382_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2384_, lean_object* v_patterns_2385_, lean_object* v_alts_2386_, lean_object* v_k_2387_, lean_object* v_i_2388_, lean_object* v_altsNew_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2384_, v_patterns_2385_, v_alts_2386_, v_k_2387_, v_i_2388_, v_altsNew_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2396_, lean_object* v_discrs_2397_, lean_object* v_patterns_2398_, lean_object* v_alts_2399_, lean_object* v_k_2400_, lean_object* v_i_2401_, lean_object* v_altsNew_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2397_, v_patterns_2398_, v_alts_2399_, v_k_2400_, v_i_2401_, v_altsNew_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2409_, lean_object* v_discrs_2410_, lean_object* v_patterns_2411_, lean_object* v_alts_2412_, lean_object* v_k_2413_, lean_object* v_i_2414_, lean_object* v_altsNew_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2409_, v_discrs_2410_, v_patterns_2411_, v_alts_2412_, v_k_2413_, v_i_2414_, v_altsNew_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2424_, lean_object* v_discrs_2425_, lean_object* v_patterns_2426_, lean_object* v_alts_2427_, lean_object* v_k_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2434_ = lean_unsigned_to_nat(0u);
v___x_2435_ = lean_nat_dec_eq(v_numDiscrEqs_2424_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2437_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2425_, v_patterns_2426_, v_alts_2427_, v_k_2428_, v___x_2434_, v___x_2436_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
return v___x_2437_;
}
else
{
lean_object* v___x_2438_; 
lean_dec_ref(v_patterns_2426_);
lean_dec_ref(v_discrs_2425_);
lean_inc(v_a_2432_);
lean_inc_ref(v_a_2431_);
lean_inc(v_a_2430_);
lean_inc_ref(v_a_2429_);
v___x_2438_ = lean_apply_6(v_k_2428_, v_alts_2427_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, lean_box(0));
return v___x_2438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2439_, lean_object* v_discrs_2440_, lean_object* v_patterns_2441_, lean_object* v_alts_2442_, lean_object* v_k_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2439_, v_discrs_2440_, v_patterns_2441_, v_alts_2442_, v_k_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_numDiscrEqs_2439_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2450_, lean_object* v_numDiscrEqs_2451_, lean_object* v_discrs_2452_, lean_object* v_patterns_2453_, lean_object* v_alts_2454_, lean_object* v_k_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2451_, v_discrs_2452_, v_patterns_2453_, v_alts_2454_, v_k_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2462_, lean_object* v_numDiscrEqs_2463_, lean_object* v_discrs_2464_, lean_object* v_patterns_2465_, lean_object* v_alts_2466_, lean_object* v_k_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2462_, v_numDiscrEqs_2463_, v_discrs_2464_, v_patterns_2465_, v_alts_2466_, v_k_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_numDiscrEqs_2463_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(lean_object* v_declName_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v_env_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2477_ = lean_st_ref_get(v___y_2475_);
v_env_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc_ref(v_env_2478_);
lean_dec(v___x_2477_);
v___x_2479_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2478_, v_declName_2474_);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg___boxed(lean_object* v_declName_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2481_, v___y_2482_);
lean_dec(v___y_2482_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_declName_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2485_, v___y_2489_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___boxed(lean_object* v_declName_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v_declName_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v___f_2506_; lean_object* v___x_14707__overap_2507_; lean_object* v___x_2508_; 
v___f_2506_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14707__overap_2507_ = lean_panic_fn_borrowed(v___f_2506_, v_msg_2500_);
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
v___x_2508_ = lean_apply_5(v___x_14707__overap_2507_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, lean_box(0));
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2516_, lean_object* v_b_2517_, lean_object* v_c_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; 
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
v___x_2524_ = lean_apply_7(v_k_2516_, v_b_2517_, v_c_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, lean_box(0));
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2525_, lean_object* v_b_2526_, lean_object* v_c_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2525_, v_b_2526_, v_c_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2534_, lean_object* v_k_2535_, uint8_t v_cleanupAnnotations_2536_, uint8_t v_whnfType_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v___f_2543_; lean_object* v___x_2544_; 
v___f_2543_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2543_, 0, v_k_2535_);
v___x_2544_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2534_, v___f_2543_, v_cleanupAnnotations_2536_, v_whnfType_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
v_a_2553_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2544_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2544_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2561_, lean_object* v_k_2562_, lean_object* v_cleanupAnnotations_2563_, lean_object* v_whnfType_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2570_; uint8_t v_whnfType_boxed_2571_; lean_object* v_res_2572_; 
v_cleanupAnnotations_boxed_2570_ = lean_unbox(v_cleanupAnnotations_2563_);
v_whnfType_boxed_2571_ = lean_unbox(v_whnfType_2564_);
v_res_2572_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2561_, v_k_2562_, v_cleanupAnnotations_boxed_2570_, v_whnfType_boxed_2571_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2573_, lean_object* v_type_2574_, lean_object* v_k_2575_, uint8_t v_cleanupAnnotations_2576_, uint8_t v_whnfType_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2574_, v_k_2575_, v_cleanupAnnotations_2576_, v_whnfType_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2584_, lean_object* v_type_2585_, lean_object* v_k_2586_, lean_object* v_cleanupAnnotations_2587_, lean_object* v_whnfType_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2594_; uint8_t v_whnfType_boxed_2595_; lean_object* v_res_2596_; 
v_cleanupAnnotations_boxed_2594_ = lean_unbox(v_cleanupAnnotations_2587_);
v_whnfType_boxed_2595_ = lean_unbox(v_whnfType_2588_);
v_res_2596_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2584_, v_type_2585_, v_k_2586_, v_cleanupAnnotations_boxed_2594_, v_whnfType_boxed_2595_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2597_, lean_object* v_splitterName_2598_, lean_object* v_matcherInput_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_matchType_2605_; lean_object* v_discrInfos_2606_; lean_object* v_lhss_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2627_; 
v_matchType_2605_ = lean_ctor_get(v_matcherInput_2599_, 1);
v_discrInfos_2606_ = lean_ctor_get(v_matcherInput_2599_, 2);
v_lhss_2607_ = lean_ctor_get(v_matcherInput_2599_, 3);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_matcherInput_2599_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; lean_object* v_unused_2629_; 
v_unused_2628_ = lean_ctor_get(v_matcherInput_2599_, 4);
lean_dec(v_unused_2628_);
v_unused_2629_ = lean_ctor_get(v_matcherInput_2599_, 0);
lean_dec(v_unused_2629_);
v___x_2609_ = v_matcherInput_2599_;
v_isShared_2610_ = v_isSharedCheck_2627_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_lhss_2607_);
lean_inc(v_discrInfos_2606_);
lean_inc(v_matchType_2605_);
lean_dec(v_matcherInput_2599_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2627_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_overlaps_2597_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 4, v___x_2611_);
lean_ctor_set(v___x_2609_, 0, v_splitterName_2598_);
v___x_2613_ = v___x_2609_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_splitterName_2598_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_matchType_2605_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_discrInfos_2606_);
lean_ctor_set(v_reuseFailAlloc_2626_, 3, v_lhss_2607_);
lean_ctor_set(v_reuseFailAlloc_2626_, 4, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_Meta_Match_mkMatcher(v___x_2613_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v_addMatcher_2616_; lean_object* v___x_2617_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref(v___x_2614_);
v_addMatcher_2616_ = lean_ctor_get(v_a_2615_, 3);
lean_inc_ref(v_addMatcher_2616_);
lean_dec(v_a_2615_);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
v___x_2617_ = lean_apply_5(v_addMatcher_2616_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, lean_box(0));
return v___x_2617_;
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
v_a_2618_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2614_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2614_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2630_, lean_object* v_splitterName_2631_, lean_object* v_matcherInput_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2630_, v_splitterName_2631_, v_matcherInput_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
return v_res_2638_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2639_, lean_object* v_ys_2640_, lean_object* v_x_2641_){
_start:
{
lean_object* v_zero_2642_; uint8_t v_isZero_2643_; 
v_zero_2642_ = lean_unsigned_to_nat(0u);
v_isZero_2643_ = lean_nat_dec_eq(v_x_2641_, v_zero_2642_);
if (v_isZero_2643_ == 1)
{
lean_dec(v_x_2641_);
return v_isZero_2643_;
}
else
{
lean_object* v_one_2644_; lean_object* v_n_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v_one_2644_ = lean_unsigned_to_nat(1u);
v_n_2645_ = lean_nat_sub(v_x_2641_, v_one_2644_);
lean_dec(v_x_2641_);
v___x_2646_ = lean_array_fget_borrowed(v_xs_2639_, v_n_2645_);
v___x_2647_ = lean_array_fget_borrowed(v_ys_2640_, v_n_2645_);
v___x_2648_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2646_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_dec(v_n_2645_);
return v___x_2648_;
}
else
{
v_x_2641_ = v_n_2645_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2650_, lean_object* v_ys_2651_, lean_object* v_x_2652_){
_start:
{
uint8_t v_res_2653_; lean_object* v_r_2654_; 
v_res_2653_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2650_, v_ys_2651_, v_x_2652_);
lean_dec_ref(v_ys_2651_);
lean_dec_ref(v_xs_2650_);
v_r_2654_ = lean_box(v_res_2653_);
return v_r_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2655_, lean_object* v_b_2656_){
_start:
{
lean_object* v_array_2657_; lean_object* v_start_2658_; lean_object* v_stop_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2672_; 
v_array_2657_ = lean_ctor_get(v_a_2655_, 0);
v_start_2658_ = lean_ctor_get(v_a_2655_, 1);
v_stop_2659_ = lean_ctor_get(v_a_2655_, 2);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_a_2655_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2661_ = v_a_2655_;
v_isShared_2662_ = v_isSharedCheck_2672_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_stop_2659_);
lean_inc(v_start_2658_);
lean_inc(v_array_2657_);
lean_dec(v_a_2655_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2672_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
uint8_t v___x_2663_; 
v___x_2663_ = lean_nat_dec_lt(v_start_2658_, v_stop_2659_);
if (v___x_2663_ == 0)
{
lean_del_object(v___x_2661_);
lean_dec(v_stop_2659_);
lean_dec(v_start_2658_);
lean_dec_ref(v_array_2657_);
return v_b_2656_;
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2664_ = lean_unsigned_to_nat(1u);
v___x_2665_ = lean_nat_add(v_start_2658_, v___x_2664_);
lean_inc_ref(v_array_2657_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2665_);
v___x_2667_ = v___x_2661_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_array_2657_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_stop_2659_);
v___x_2667_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = lean_array_fget(v_array_2657_, v_start_2658_);
lean_dec(v_start_2658_);
lean_dec_ref(v_array_2657_);
v___x_2669_ = lean_array_push(v_b_2656_, v___x_2668_);
v_a_2655_ = v___x_2667_;
v_b_2656_ = v___x_2669_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2673_, size_t v_sz_2674_, size_t v_i_2675_, lean_object* v_b_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
uint8_t v___x_2682_; 
v___x_2682_ = lean_usize_dec_lt(v_i_2675_, v_sz_2674_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_b_2676_);
return v___x_2683_;
}
else
{
lean_object* v_snd_2684_; lean_object* v_fst_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2737_; 
v_snd_2684_ = lean_ctor_get(v_b_2676_, 1);
v_fst_2685_ = lean_ctor_get(v_b_2676_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_b_2676_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2687_ = v_b_2676_;
v_isShared_2688_ = v_isSharedCheck_2737_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_snd_2684_);
lean_inc(v_fst_2685_);
lean_dec(v_b_2676_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2737_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_array_2689_; lean_object* v_start_2690_; lean_object* v_stop_2691_; uint8_t v___x_2692_; 
v_array_2689_ = lean_ctor_get(v_snd_2684_, 0);
v_start_2690_ = lean_ctor_get(v_snd_2684_, 1);
v_stop_2691_ = lean_ctor_get(v_snd_2684_, 2);
v___x_2692_ = lean_nat_dec_lt(v_start_2690_, v_stop_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2694_; 
if (v_isShared_2688_ == 0)
{
v___x_2694_ = v___x_2687_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_fst_2685_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_snd_2684_);
v___x_2694_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2695_; 
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
}
else
{
lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2733_; 
lean_inc(v_stop_2691_);
lean_inc(v_start_2690_);
lean_inc_ref(v_array_2689_);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_snd_2684_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; lean_object* v_unused_2735_; lean_object* v_unused_2736_; 
v_unused_2734_ = lean_ctor_get(v_snd_2684_, 2);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_snd_2684_, 1);
lean_dec(v_unused_2735_);
v_unused_2736_ = lean_ctor_get(v_snd_2684_, 0);
lean_dec(v_unused_2736_);
v___x_2698_ = v_snd_2684_;
v_isShared_2699_ = v_isSharedCheck_2733_;
goto v_resetjp_2697_;
}
else
{
lean_dec(v_snd_2684_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2733_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v_a_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v_a_2700_ = lean_array_uget_borrowed(v_as_2673_, v_i_2675_);
v___x_2701_ = lean_array_fget_borrowed(v_array_2689_, v_start_2690_);
lean_inc(v___x_2701_);
lean_inc(v_a_2700_);
v___x_2702_ = l_Lean_Meta_mkEqHEq(v_a_2700_, v___x_2701_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref(v___x_2702_);
v___x_2704_ = l_Lean_mkArrow(v_a_2703_, v_fst_2685_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2709_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref(v___x_2704_);
v___x_2706_ = lean_unsigned_to_nat(1u);
v___x_2707_ = lean_nat_add(v_start_2690_, v___x_2706_);
lean_dec(v_start_2690_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 1, v___x_2707_);
v___x_2709_ = v___x_2698_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_array_2689_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v_stop_2691_);
v___x_2709_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2711_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v___x_2709_);
lean_ctor_set(v___x_2687_, 0, v_a_2705_);
v___x_2711_ = v___x_2687_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2705_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
size_t v___x_2712_; size_t v___x_2713_; 
v___x_2712_ = ((size_t)1ULL);
v___x_2713_ = lean_usize_add(v_i_2675_, v___x_2712_);
v_i_2675_ = v___x_2713_;
v_b_2676_ = v___x_2711_;
goto _start;
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_del_object(v___x_2698_);
lean_dec(v_stop_2691_);
lean_dec(v_start_2690_);
lean_dec_ref(v_array_2689_);
lean_del_object(v___x_2687_);
v_a_2717_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2704_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2704_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_del_object(v___x_2698_);
lean_dec(v_stop_2691_);
lean_dec(v_start_2690_);
lean_dec_ref(v_array_2689_);
lean_del_object(v___x_2687_);
lean_dec(v_fst_2685_);
v_a_2725_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2702_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2702_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2738_, lean_object* v_sz_2739_, lean_object* v_i_2740_, lean_object* v_b_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
size_t v_sz_boxed_2747_; size_t v_i_boxed_2748_; lean_object* v_res_2749_; 
v_sz_boxed_2747_ = lean_unbox_usize(v_sz_2739_);
lean_dec(v_sz_2739_);
v_i_boxed_2748_ = lean_unbox_usize(v_i_2740_);
lean_dec(v_i_2740_);
v_res_2749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2738_, v_sz_boxed_2747_, v_i_boxed_2748_, v_b_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v_as_2738_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2750_, lean_object* v___x_2751_, lean_object* v_as_2752_, size_t v_sz_2753_, size_t v_i_2754_, lean_object* v_b_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_usize_dec_lt(v_i_2754_, v_sz_2753_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; 
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v_b_2755_);
return v___x_2762_;
}
else
{
lean_object* v___x_2763_; lean_object* v_a_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2763_ = l_Lean_instInhabitedExpr;
v_a_2764_ = lean_array_uget_borrowed(v_as_2752_, v_i_2754_);
v___x_2765_ = lean_array_get_borrowed(v___x_2763_, v___x_2750_, v_a_2764_);
lean_inc(v___x_2765_);
v___x_2766_ = l_Lean_Meta_instantiateForall(v___x_2765_, v___x_2751_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref(v___x_2766_);
v___x_2768_ = lean_array_get_size(v___x_2751_);
v___x_2769_ = l_Lean_Meta_Match_simpH_x3f(v_a_2767_, v___x_2768_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v_a_2772_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref(v___x_2769_);
if (lean_obj_tag(v_a_2770_) == 1)
{
lean_object* v_val_2776_; lean_object* v___x_2777_; 
v_val_2776_ = lean_ctor_get(v_a_2770_, 0);
lean_inc(v_val_2776_);
lean_dec_ref(v_a_2770_);
v___x_2777_ = lean_array_push(v_b_2755_, v_val_2776_);
v_a_2772_ = v___x_2777_;
goto v___jp_2771_;
}
else
{
lean_dec(v_a_2770_);
v_a_2772_ = v_b_2755_;
goto v___jp_2771_;
}
v___jp_2771_:
{
size_t v___x_2773_; size_t v___x_2774_; 
v___x_2773_ = ((size_t)1ULL);
v___x_2774_ = lean_usize_add(v_i_2754_, v___x_2773_);
v_i_2754_ = v___x_2774_;
v_b_2755_ = v_a_2772_;
goto _start;
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec_ref(v_b_2755_);
v_a_2778_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2769_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2769_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v_b_2755_);
v_a_2786_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2766_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2766_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2794_, lean_object* v___x_2795_, lean_object* v_as_2796_, lean_object* v_sz_2797_, lean_object* v_i_2798_, lean_object* v_b_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
size_t v_sz_boxed_2805_; size_t v_i_boxed_2806_; lean_object* v_res_2807_; 
v_sz_boxed_2805_ = lean_unbox_usize(v_sz_2797_);
lean_dec(v_sz_2797_);
v_i_boxed_2806_ = lean_unbox_usize(v_i_2798_);
lean_dec(v_i_2798_);
v_res_2807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2794_, v___x_2795_, v_as_2796_, v_sz_boxed_2805_, v_i_boxed_2806_, v_b_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec_ref(v_as_2796_);
lean_dec_ref(v___x_2795_);
lean_dec_ref(v___x_2794_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v___x_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v_rhsArgs_2816_, lean_object* v_a_2817_, lean_object* v_ys_2818_, uint8_t v___x_2819_, uint8_t v___x_2820_, uint8_t v___x_2821_, lean_object* v_matchDeclName_2822_, lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v___x_2826_, lean_object* v___x_2827_, lean_object* v_argMask_2828_, lean_object* v_a_2829_, lean_object* v_alts_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2836_ = lean_array_get_borrowed(v___x_2808_, v_alts_2830_, v_a_2809_);
v___x_2837_ = l_Lean_ConstantInfo_name(v_a_2810_);
v___x_2838_ = l_Lean_mkConst(v___x_2837_, v___x_2811_);
v___x_2839_ = l_Subarray_copy___redArg(v___x_2812_);
v___x_2840_ = lean_mk_empty_array_with_capacity(v___x_2813_);
v___x_2841_ = lean_array_push(v___x_2840_, v___x_2814_);
v___x_2842_ = l_Array_append___redArg(v___x_2839_, v___x_2841_);
lean_dec_ref(v___x_2841_);
lean_inc_ref(v___x_2842_);
v___x_2843_ = l_Array_append___redArg(v___x_2842_, v___x_2815_);
v___x_2844_ = l_Array_append___redArg(v___x_2843_, v_alts_2830_);
v___x_2845_ = l_Lean_mkAppN(v___x_2838_, v___x_2844_);
lean_dec_ref(v___x_2844_);
lean_inc(v___x_2836_);
v___x_2846_ = l_Lean_mkAppN(v___x_2836_, v_rhsArgs_2816_);
v___x_2847_ = l_Lean_Meta_mkEq(v___x_2845_, v___x_2846_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref(v___x_2847_);
v___x_2849_ = l_Lean_mkArrowN(v_a_2817_, v_a_2848_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2849_);
v___x_2851_ = l_Array_append___redArg(v___x_2842_, v_ys_2818_);
v___x_2852_ = l_Array_append___redArg(v___x_2851_, v_alts_2830_);
v___x_2853_ = l_Lean_Meta_mkForallFVars(v___x_2852_, v_a_2850_, v___x_2819_, v___x_2820_, v___x_2820_, v___x_2821_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
lean_dec_ref(v___x_2852_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2855_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref(v___x_2853_);
v___x_2855_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2854_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc_n(v_a_2856_, 2);
lean_dec_ref(v___x_2855_);
lean_inc(v___x_2823_);
v___x_2857_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2822_, v_a_2856_, v___x_2823_, v___x_2823_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2857_);
lean_inc(v___x_2824_);
v___x_2859_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2824_);
lean_ctor_set(v___x_2859_, 1, v___x_2825_);
lean_ctor_set(v___x_2859_, 2, v_a_2856_);
v___x_2860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2824_);
lean_ctor_set(v___x_2860_, 1, v___x_2826_);
v___x_2861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2859_);
lean_ctor_set(v___x_2861_, 1, v_a_2858_);
lean_ctor_set(v___x_2861_, 2, v___x_2860_);
v___x_2862_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
v___x_2863_ = l_Lean_addDecl(v___x_2862_, v___x_2819_, v___y_2833_, v___y_2834_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2872_; 
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2872_ == 0)
{
lean_object* v_unused_2873_; 
v_unused_2873_ = lean_ctor_get(v___x_2863_, 0);
lean_dec(v_unused_2873_);
v___x_2865_ = v___x_2863_;
v_isShared_2866_ = v_isSharedCheck_2872_;
goto v_resetjp_2864_;
}
else
{
lean_dec(v___x_2863_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2872_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2827_);
lean_ctor_set(v___x_2867_, 1, v_argMask_2828_);
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v_a_2829_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2868_);
v___x_2870_ = v___x_2865_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec_ref(v_a_2829_);
lean_dec_ref(v_argMask_2828_);
lean_dec_ref(v___x_2827_);
v_a_2874_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2863_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2863_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2829_);
lean_dec_ref(v_argMask_2828_);
lean_dec_ref(v___x_2827_);
lean_dec(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v___x_2824_);
v_a_2882_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2857_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2857_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec_ref(v_a_2829_);
lean_dec_ref(v_argMask_2828_);
lean_dec_ref(v___x_2827_);
lean_dec(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v___x_2824_);
lean_dec(v___x_2823_);
lean_dec(v_matchDeclName_2822_);
v_a_2890_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2855_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2855_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v_a_2829_);
lean_dec_ref(v_argMask_2828_);
lean_dec_ref(v___x_2827_);
lean_dec(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v___x_2824_);
lean_dec(v___x_2823_);
lean_dec(v_matchDeclName_2822_);
v_a_2898_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2853_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2853_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v___x_2842_);
lean_dec_ref(v_a_2829_);
lean_dec_ref(v_argMask_2828_);
lean_dec_ref(v___x_2827_);
lean_dec(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v___x_2824_);
lean_dec(v___x_2823_);
lean_dec(v_matchDeclName_2822_);
v_a_2906_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2849_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2849_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v___x_2842_);
lean_dec_ref(v_a_2829_);
lean_dec_ref(v_argMask_2828_);
lean_dec_ref(v___x_2827_);
lean_dec(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v___x_2824_);
lean_dec(v___x_2823_);
lean_dec(v_matchDeclName_2822_);
v_a_2914_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2847_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2847_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2922_ = _args[0];
lean_object* v_a_2923_ = _args[1];
lean_object* v_a_2924_ = _args[2];
lean_object* v___x_2925_ = _args[3];
lean_object* v___x_2926_ = _args[4];
lean_object* v___x_2927_ = _args[5];
lean_object* v___x_2928_ = _args[6];
lean_object* v___x_2929_ = _args[7];
lean_object* v_rhsArgs_2930_ = _args[8];
lean_object* v_a_2931_ = _args[9];
lean_object* v_ys_2932_ = _args[10];
lean_object* v___x_2933_ = _args[11];
lean_object* v___x_2934_ = _args[12];
lean_object* v___x_2935_ = _args[13];
lean_object* v_matchDeclName_2936_ = _args[14];
lean_object* v___x_2937_ = _args[15];
lean_object* v___x_2938_ = _args[16];
lean_object* v___x_2939_ = _args[17];
lean_object* v___x_2940_ = _args[18];
lean_object* v___x_2941_ = _args[19];
lean_object* v_argMask_2942_ = _args[20];
lean_object* v_a_2943_ = _args[21];
lean_object* v_alts_2944_ = _args[22];
lean_object* v___y_2945_ = _args[23];
lean_object* v___y_2946_ = _args[24];
lean_object* v___y_2947_ = _args[25];
lean_object* v___y_2948_ = _args[26];
lean_object* v___y_2949_ = _args[27];
_start:
{
uint8_t v___x_18941__boxed_2950_; uint8_t v___x_18942__boxed_2951_; uint8_t v___x_18943__boxed_2952_; lean_object* v_res_2953_; 
v___x_18941__boxed_2950_ = lean_unbox(v___x_2933_);
v___x_18942__boxed_2951_ = lean_unbox(v___x_2934_);
v___x_18943__boxed_2952_ = lean_unbox(v___x_2935_);
v_res_2953_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2922_, v_a_2923_, v_a_2924_, v___x_2925_, v___x_2926_, v___x_2927_, v___x_2928_, v___x_2929_, v_rhsArgs_2930_, v_a_2931_, v_ys_2932_, v___x_18941__boxed_2950_, v___x_18942__boxed_2951_, v___x_18943__boxed_2952_, v_matchDeclName_2936_, v___x_2937_, v___x_2938_, v___x_2939_, v___x_2940_, v___x_2941_, v_argMask_2942_, v_a_2943_, v_alts_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v_alts_2944_);
lean_dec_ref(v_ys_2932_);
lean_dec_ref(v_a_2931_);
lean_dec_ref(v_rhsArgs_2930_);
lean_dec_ref(v___x_2929_);
lean_dec(v___x_2927_);
lean_dec_ref(v_a_2924_);
lean_dec(v_a_2923_);
lean_dec_ref(v___x_2922_);
return v_res_2953_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2954_; lean_object* v_dummy_2955_; 
v___x_2954_ = lean_box(0);
v_dummy_2955_ = l_Lean_Expr_sort___override(v___x_2954_);
return v_dummy_2955_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = lean_box(0);
v___x_2960_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_2961_ = l_Lean_mkConst(v___x_2960_, v___x_2959_);
return v___x_2961_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_2964_ = l_Lean_stringToMessageData(v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_2965_, lean_object* v_overlaps_2966_, lean_object* v_a_2967_, lean_object* v_fst_2968_, lean_object* v___x_2969_, lean_object* v___x_2970_, lean_object* v___x_2971_, uint8_t v___x_2972_, lean_object* v___x_2973_, lean_object* v_a_2974_, lean_object* v___x_2975_, lean_object* v___x_2976_, lean_object* v___x_2977_, lean_object* v_matchDeclName_2978_, lean_object* v___x_2979_, lean_object* v___x_2980_, lean_object* v___x_2981_, lean_object* v___x_2982_, lean_object* v___x_2983_, lean_object* v_ys_2984_, lean_object* v___eqs_2985_, lean_object* v_rhsArgs_2986_, lean_object* v_argMask_2987_, lean_object* v_altResultType_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_dummy_2994_; lean_object* v_nargs_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; size_t v_sz_3000_; size_t v___x_3001_; lean_object* v___x_3002_; 
v_dummy_2994_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_2995_ = l_Lean_Expr_getAppNumArgs(v_altResultType_2988_);
lean_inc(v_nargs_2995_);
v___x_2996_ = lean_mk_array(v_nargs_2995_, v_dummy_2994_);
v___x_2997_ = lean_nat_sub(v_nargs_2995_, v___x_2965_);
lean_dec(v_nargs_2995_);
v___x_2998_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_2988_, v___x_2996_, v___x_2997_);
v___x_2999_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_2966_, v_a_2967_);
v_sz_3000_ = lean_array_size(v___x_2999_);
v___x_3001_ = ((size_t)0ULL);
lean_inc_ref(v___x_2969_);
v___x_3002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_2968_, v___x_2998_, v___x_2999_, v_sz_3000_, v___x_3001_, v___x_2969_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec_ref(v___x_2999_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; uint8_t v___y_3009_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; uint8_t v___y_3057_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v_options_3068_; uint8_t v_hasTrace_3069_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref(v___x_3002_);
v_options_3068_ = lean_ctor_get(v___y_2991_, 2);
v_hasTrace_3069_ = lean_ctor_get_uint8(v_options_3068_, sizeof(void*)*1);
if (v_hasTrace_3069_ == 0)
{
v___y_3060_ = v___y_2989_;
v___y_3061_ = v___y_2990_;
v___y_3062_ = v___y_2991_;
v___y_3063_ = v___y_2992_;
goto v___jp_3059_;
}
else
{
lean_object* v_inheritedTraceOptions_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v_inheritedTraceOptions_3070_ = lean_ctor_get(v___y_2991_, 13);
v___x_3071_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3072_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_3073_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3070_, v_options_3068_, v___x_3072_);
if (v___x_3073_ == 0)
{
v___y_3060_ = v___y_2989_;
v___y_3061_ = v___y_2990_;
v___y_3062_ = v___y_2991_;
v___y_3063_ = v___y_2992_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3074_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_3003_);
v___x_3075_ = lean_array_to_list(v_a_3003_);
v___x_3076_ = lean_box(0);
v___x_3077_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3075_, v___x_3076_);
v___x_3078_ = l_Lean_MessageData_ofList(v___x_3077_);
v___x_3079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3074_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3071_, v___x_3079_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_dec_ref(v___x_3080_);
v___y_3060_ = v___y_2989_;
v___y_3061_ = v___y_2990_;
v___y_3062_ = v___y_2991_;
v___y_3063_ = v___y_2992_;
goto v___jp_3059_;
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_a_3003_);
lean_dec_ref(v___x_2998_);
lean_dec_ref(v_argMask_2987_);
lean_dec_ref(v_rhsArgs_2986_);
lean_dec_ref(v_ys_2984_);
lean_dec_ref(v___x_2982_);
lean_dec(v___x_2981_);
lean_dec(v___x_2980_);
lean_dec(v___x_2979_);
lean_dec(v_matchDeclName_2978_);
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___x_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_a_2974_);
lean_dec_ref(v___x_2973_);
lean_dec_ref(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec_ref(v___x_2969_);
lean_dec(v_a_2967_);
lean_dec(v___x_2965_);
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
v___jp_3004_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; size_t v_sz_3017_; lean_object* v___x_3018_; 
v___x_3010_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2998_);
v___x_3011_ = l_Array_reverse___redArg(v___x_2998_);
v___x_3012_ = lean_array_get_size(v___x_3011_);
lean_inc(v___x_2970_);
v___x_3013_ = l_Array_toSubarray___redArg(v___x_3011_, v___x_2970_, v___x_3012_);
lean_inc_ref(v___x_2971_);
v___x_3014_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2971_, v___x_2969_);
v___x_3015_ = l_Array_reverse___redArg(v___x_3014_);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3010_);
lean_ctor_set(v___x_3016_, 1, v___x_3013_);
v_sz_3017_ = lean_array_size(v___x_3015_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3015_, v_sz_3017_, v___x_3001_, v___x_3016_, v___y_3007_, v___y_3005_, v___y_3008_, v___y_3006_);
lean_dec_ref(v___x_3015_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v_fst_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; uint8_t v___x_3023_; uint8_t v___x_3024_; lean_object* v___x_3025_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref(v___x_3018_);
v_fst_3020_ = lean_ctor_get(v_a_3019_, 0);
lean_inc(v_fst_3020_);
lean_dec(v_a_3019_);
v___x_3021_ = l_Subarray_copy___redArg(v___x_2971_);
lean_inc_ref(v___x_3021_);
v___x_3022_ = l_Array_append___redArg(v___x_3021_, v_ys_2984_);
v___x_3023_ = 0;
v___x_3024_ = 1;
v___x_3025_ = l_Lean_Meta_mkForallFVars(v___x_3022_, v_fst_3020_, v___x_3023_, v___x_2972_, v___x_2972_, v___x_3024_, v___y_3007_, v___y_3005_, v___y_3008_, v___y_3006_);
lean_dec_ref(v___x_3022_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___f_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref(v___x_3025_);
v___x_3027_ = lean_array_get_size(v_ys_2984_);
v___x_3028_ = lean_array_get_size(v_a_3003_);
v___x_3029_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
lean_ctor_set_uint8(v___x_3029_, sizeof(void*)*2, v___y_3009_);
v___x_3030_ = lean_box(v___x_3023_);
v___x_3031_ = lean_box(v___x_2972_);
v___x_3032_ = lean_box(v___x_3024_);
lean_inc_ref(v___x_2998_);
v___f_3033_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_3033_, 0, v___x_2973_);
lean_closure_set(v___f_3033_, 1, v_a_2967_);
lean_closure_set(v___f_3033_, 2, v_a_2974_);
lean_closure_set(v___f_3033_, 3, v___x_2975_);
lean_closure_set(v___f_3033_, 4, v___x_2976_);
lean_closure_set(v___f_3033_, 5, v___x_2965_);
lean_closure_set(v___f_3033_, 6, v___x_2977_);
lean_closure_set(v___f_3033_, 7, v___x_2998_);
lean_closure_set(v___f_3033_, 8, v_rhsArgs_2986_);
lean_closure_set(v___f_3033_, 9, v_a_3003_);
lean_closure_set(v___f_3033_, 10, v_ys_2984_);
lean_closure_set(v___f_3033_, 11, v___x_3030_);
lean_closure_set(v___f_3033_, 12, v___x_3031_);
lean_closure_set(v___f_3033_, 13, v___x_3032_);
lean_closure_set(v___f_3033_, 14, v_matchDeclName_2978_);
lean_closure_set(v___f_3033_, 15, v___x_2970_);
lean_closure_set(v___f_3033_, 16, v___x_2979_);
lean_closure_set(v___f_3033_, 17, v___x_2980_);
lean_closure_set(v___f_3033_, 18, v___x_2981_);
lean_closure_set(v___f_3033_, 19, v___x_3029_);
lean_closure_set(v___f_3033_, 20, v_argMask_2987_);
lean_closure_set(v___f_3033_, 21, v_a_3026_);
v___x_3034_ = l_Subarray_copy___redArg(v___x_2982_);
v___x_3035_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2983_, v___x_3021_, v___x_2998_, v___x_3034_, v___f_3033_, v___y_3007_, v___y_3005_, v___y_3008_, v___y_3006_);
return v___x_3035_;
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref(v___x_3021_);
lean_dec(v_a_3003_);
lean_dec_ref(v___x_2998_);
lean_dec_ref(v_argMask_2987_);
lean_dec_ref(v_rhsArgs_2986_);
lean_dec_ref(v_ys_2984_);
lean_dec_ref(v___x_2982_);
lean_dec(v___x_2981_);
lean_dec(v___x_2980_);
lean_dec(v___x_2979_);
lean_dec(v_matchDeclName_2978_);
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___x_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_a_2974_);
lean_dec_ref(v___x_2973_);
lean_dec(v___x_2970_);
lean_dec(v_a_2967_);
lean_dec(v___x_2965_);
v_a_3036_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3025_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3025_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v_a_3003_);
lean_dec_ref(v___x_2998_);
lean_dec_ref(v_argMask_2987_);
lean_dec_ref(v_rhsArgs_2986_);
lean_dec_ref(v_ys_2984_);
lean_dec_ref(v___x_2982_);
lean_dec(v___x_2981_);
lean_dec(v___x_2980_);
lean_dec(v___x_2979_);
lean_dec(v_matchDeclName_2978_);
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___x_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_a_2974_);
lean_dec_ref(v___x_2973_);
lean_dec_ref(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec(v_a_2967_);
lean_dec(v___x_2965_);
v_a_3044_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3018_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3018_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
v___jp_3052_:
{
if (v___y_3057_ == 0)
{
v___y_3005_ = v___y_3053_;
v___y_3006_ = v___y_3054_;
v___y_3007_ = v___y_3055_;
v___y_3008_ = v___y_3056_;
v___y_3009_ = v___y_3057_;
goto v___jp_3004_;
}
else
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_nat_dec_eq(v___x_2983_, v___x_2970_);
v___y_3005_ = v___y_3053_;
v___y_3006_ = v___y_3054_;
v___y_3007_ = v___y_3055_;
v___y_3008_ = v___y_3056_;
v___y_3009_ = v___x_3058_;
goto v___jp_3004_;
}
}
v___jp_3059_:
{
lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = lean_array_get_size(v_ys_2984_);
v___x_3065_ = lean_nat_dec_eq(v___x_3064_, v___x_2970_);
if (v___x_3065_ == 0)
{
v___y_3053_ = v___y_3061_;
v___y_3054_ = v___y_3063_;
v___y_3055_ = v___y_3060_;
v___y_3056_ = v___y_3062_;
v___y_3057_ = v___x_3065_;
goto v___jp_3052_;
}
else
{
lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = lean_array_get_size(v_a_3003_);
v___x_3067_ = lean_nat_dec_eq(v___x_3066_, v___x_2970_);
v___y_3053_ = v___y_3061_;
v___y_3054_ = v___y_3063_;
v___y_3055_ = v___y_3060_;
v___y_3056_ = v___y_3062_;
v___y_3057_ = v___x_3067_;
goto v___jp_3052_;
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec_ref(v___x_2998_);
lean_dec_ref(v_argMask_2987_);
lean_dec_ref(v_rhsArgs_2986_);
lean_dec_ref(v_ys_2984_);
lean_dec_ref(v___x_2982_);
lean_dec(v___x_2981_);
lean_dec(v___x_2980_);
lean_dec(v___x_2979_);
lean_dec(v_matchDeclName_2978_);
lean_dec_ref(v___x_2977_);
lean_dec_ref(v___x_2976_);
lean_dec(v___x_2975_);
lean_dec_ref(v_a_2974_);
lean_dec_ref(v___x_2973_);
lean_dec_ref(v___x_2971_);
lean_dec(v___x_2970_);
lean_dec_ref(v___x_2969_);
lean_dec(v_a_2967_);
lean_dec(v___x_2965_);
v_a_3089_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3002_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3002_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3097_ = _args[0];
lean_object* v_overlaps_3098_ = _args[1];
lean_object* v_a_3099_ = _args[2];
lean_object* v_fst_3100_ = _args[3];
lean_object* v___x_3101_ = _args[4];
lean_object* v___x_3102_ = _args[5];
lean_object* v___x_3103_ = _args[6];
lean_object* v___x_3104_ = _args[7];
lean_object* v___x_3105_ = _args[8];
lean_object* v_a_3106_ = _args[9];
lean_object* v___x_3107_ = _args[10];
lean_object* v___x_3108_ = _args[11];
lean_object* v___x_3109_ = _args[12];
lean_object* v_matchDeclName_3110_ = _args[13];
lean_object* v___x_3111_ = _args[14];
lean_object* v___x_3112_ = _args[15];
lean_object* v___x_3113_ = _args[16];
lean_object* v___x_3114_ = _args[17];
lean_object* v___x_3115_ = _args[18];
lean_object* v_ys_3116_ = _args[19];
lean_object* v___eqs_3117_ = _args[20];
lean_object* v_rhsArgs_3118_ = _args[21];
lean_object* v_argMask_3119_ = _args[22];
lean_object* v_altResultType_3120_ = _args[23];
lean_object* v___y_3121_ = _args[24];
lean_object* v___y_3122_ = _args[25];
lean_object* v___y_3123_ = _args[26];
lean_object* v___y_3124_ = _args[27];
lean_object* v___y_3125_ = _args[28];
_start:
{
uint8_t v___x_19209__boxed_3126_; lean_object* v_res_3127_; 
v___x_19209__boxed_3126_ = lean_unbox(v___x_3104_);
v_res_3127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3097_, v_overlaps_3098_, v_a_3099_, v_fst_3100_, v___x_3101_, v___x_3102_, v___x_3103_, v___x_19209__boxed_3126_, v___x_3105_, v_a_3106_, v___x_3107_, v___x_3108_, v___x_3109_, v_matchDeclName_3110_, v___x_3111_, v___x_3112_, v___x_3113_, v___x_3114_, v___x_3115_, v_ys_3116_, v___eqs_3117_, v_rhsArgs_3118_, v_argMask_3119_, v_altResultType_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec_ref(v___eqs_3117_);
lean_dec(v___x_3115_);
lean_dec(v_fst_3100_);
lean_dec_ref(v_overlaps_3098_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3128_, lean_object* v_val_3129_, lean_object* v_baseName_3130_, lean_object* v___x_3131_, lean_object* v_a_3132_, lean_object* v___x_3133_, lean_object* v___x_3134_, lean_object* v___x_3135_, lean_object* v_matchDeclName_3136_, lean_object* v___x_3137_, lean_object* v___x_3138_, lean_object* v___x_3139_, lean_object* v_a_3140_, lean_object* v_b_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
uint8_t v___x_3147_; 
v___x_3147_ = lean_nat_dec_lt(v_a_3140_, v_upperBound_3128_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; 
lean_dec(v_a_3140_);
lean_dec(v___x_3139_);
lean_dec_ref(v___x_3138_);
lean_dec(v___x_3137_);
lean_dec(v_matchDeclName_3136_);
lean_dec_ref(v___x_3135_);
lean_dec_ref(v___x_3134_);
lean_dec(v___x_3133_);
lean_dec_ref(v_a_3132_);
lean_dec_ref(v___x_3131_);
lean_dec(v_baseName_3130_);
lean_dec_ref(v_val_3129_);
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_b_3141_);
return v___x_3148_;
}
else
{
lean_object* v_snd_3149_; lean_object* v_snd_3150_; lean_object* v_snd_3151_; lean_object* v_fst_3152_; lean_object* v_fst_3153_; lean_object* v_fst_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3237_; 
v_snd_3149_ = lean_ctor_get(v_b_3141_, 1);
lean_inc(v_snd_3149_);
v_snd_3150_ = lean_ctor_get(v_snd_3149_, 1);
lean_inc(v_snd_3150_);
v_snd_3151_ = lean_ctor_get(v_snd_3150_, 1);
lean_inc(v_snd_3151_);
v_fst_3152_ = lean_ctor_get(v_b_3141_, 0);
lean_inc(v_fst_3152_);
lean_dec_ref(v_b_3141_);
v_fst_3153_ = lean_ctor_get(v_snd_3149_, 0);
lean_inc(v_fst_3153_);
lean_dec(v_snd_3149_);
v_fst_3154_ = lean_ctor_get(v_snd_3150_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_snd_3150_);
if (v_isSharedCheck_3237_ == 0)
{
lean_object* v_unused_3238_; 
v_unused_3238_ = lean_ctor_get(v_snd_3150_, 1);
lean_dec(v_unused_3238_);
v___x_3156_ = v_snd_3150_;
v_isShared_3157_ = v_isSharedCheck_3237_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_fst_3154_);
lean_dec(v_snd_3150_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3237_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v_fst_3158_; lean_object* v_snd_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3236_; 
v_fst_3158_ = lean_ctor_get(v_snd_3151_, 0);
v_snd_3159_ = lean_ctor_get(v_snd_3151_, 1);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_snd_3151_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3161_ = v_snd_3151_;
v_isShared_3162_ = v_isSharedCheck_3236_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_snd_3159_);
lean_inc(v_fst_3158_);
lean_dec(v_snd_3151_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3236_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v_altInfos_3163_; lean_object* v_overlaps_3164_; lean_object* v_start_3165_; lean_object* v_stop_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___y_3181_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v_altInfos_3163_ = lean_ctor_get(v_val_3129_, 2);
v_overlaps_3164_ = lean_ctor_get(v_val_3129_, 5);
v_start_3165_ = lean_ctor_get(v___x_3138_, 1);
v_stop_3166_ = lean_ctor_get(v___x_3138_, 2);
v___x_3167_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3168_ = l_Lean_instInhabitedExpr;
v___x_3169_ = lean_unsigned_to_nat(0u);
v___x_3170_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3171_ = lean_box(0);
v___x_3172_ = lean_unsigned_to_nat(1u);
v___x_3173_ = lean_array_get_borrowed(v___x_3167_, v_altInfos_3163_, v_a_3140_);
v___x_3174_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3130_);
v___x_3175_ = l_Lean_Name_str___override(v_baseName_3130_, v___x_3174_);
lean_inc(v_fst_3154_);
v___x_3176_ = lean_name_append_index_after(v___x_3175_, v_fst_3154_);
v___x_3177_ = lean_box(v___x_3147_);
lean_inc(v___x_3139_);
lean_inc_ref(v___x_3138_);
lean_inc(v___x_3137_);
lean_inc(v___x_3176_);
lean_inc(v_matchDeclName_3136_);
lean_inc_ref(v___x_3135_);
lean_inc_ref(v___x_3134_);
lean_inc(v___x_3133_);
lean_inc_ref(v_a_3132_);
lean_inc_ref(v___x_3131_);
lean_inc(v_fst_3153_);
lean_inc(v_a_3140_);
lean_inc_ref(v_overlaps_3164_);
v___f_3178_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3178_, 0, v___x_3172_);
lean_closure_set(v___f_3178_, 1, v_overlaps_3164_);
lean_closure_set(v___f_3178_, 2, v_a_3140_);
lean_closure_set(v___f_3178_, 3, v_fst_3153_);
lean_closure_set(v___f_3178_, 4, v___x_3170_);
lean_closure_set(v___f_3178_, 5, v___x_3169_);
lean_closure_set(v___f_3178_, 6, v___x_3131_);
lean_closure_set(v___f_3178_, 7, v___x_3177_);
lean_closure_set(v___f_3178_, 8, v___x_3168_);
lean_closure_set(v___f_3178_, 9, v_a_3132_);
lean_closure_set(v___f_3178_, 10, v___x_3133_);
lean_closure_set(v___f_3178_, 11, v___x_3134_);
lean_closure_set(v___f_3178_, 12, v___x_3135_);
lean_closure_set(v___f_3178_, 13, v_matchDeclName_3136_);
lean_closure_set(v___f_3178_, 14, v___x_3176_);
lean_closure_set(v___f_3178_, 15, v___x_3137_);
lean_closure_set(v___f_3178_, 16, v___x_3171_);
lean_closure_set(v___f_3178_, 17, v___x_3138_);
lean_closure_set(v___f_3178_, 18, v___x_3139_);
v___x_3179_ = lean_array_push(v_fst_3152_, v___x_3176_);
v___x_3232_ = lean_nat_sub(v_stop_3166_, v_start_3165_);
v___x_3233_ = lean_nat_dec_lt(v_a_3140_, v___x_3232_);
lean_dec(v___x_3232_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; 
v___x_3234_ = l_outOfBounds___redArg(v___x_3168_);
v___y_3181_ = v___x_3234_;
goto v___jp_3180_;
}
else
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Subarray_get___redArg(v___x_3138_, v_a_3140_);
v___y_3181_ = v___x_3235_;
goto v___jp_3180_;
}
v___jp_3180_:
{
lean_object* v___x_3182_; 
lean_inc(v___y_3145_);
lean_inc_ref(v___y_3144_);
lean_inc(v___y_3143_);
lean_inc_ref(v___y_3142_);
v___x_3182_ = lean_infer_type(v___y_3181_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3184_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref(v___x_3182_);
lean_inc(v___x_3139_);
lean_inc(v___x_3173_);
v___x_3184_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3183_, v___x_3173_, v___x_3139_, v___f_3178_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v_snd_3186_; lean_object* v_fst_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3215_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref(v___x_3184_);
v_snd_3186_ = lean_ctor_get(v_a_3185_, 1);
v_fst_3187_ = lean_ctor_get(v_a_3185_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_a_3185_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3189_ = v_a_3185_;
v_isShared_3190_ = v_isSharedCheck_3215_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_snd_3186_);
lean_inc(v_fst_3187_);
lean_dec(v_a_3185_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3215_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v_fst_3191_; lean_object* v_snd_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3214_; 
v_fst_3191_ = lean_ctor_get(v_snd_3186_, 0);
v_snd_3192_ = lean_ctor_get(v_snd_3186_, 1);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_snd_3186_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3194_ = v_snd_3186_;
v_isShared_3195_ = v_isSharedCheck_3214_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_snd_3192_);
lean_inc(v_fst_3191_);
lean_dec(v_snd_3186_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3214_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3196_ = lean_array_push(v_fst_3153_, v_fst_3187_);
v___x_3197_ = lean_array_push(v_fst_3158_, v_fst_3191_);
v___x_3198_ = lean_array_push(v_snd_3159_, v_snd_3192_);
v___x_3199_ = lean_nat_add(v_fst_3154_, v___x_3172_);
lean_dec(v_fst_3154_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 1, v___x_3198_);
lean_ctor_set(v___x_3194_, 0, v___x_3197_);
v___x_3201_ = v___x_3194_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___x_3198_);
v___x_3201_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 1, v___x_3201_);
lean_ctor_set(v___x_3189_, 0, v___x_3199_);
v___x_3203_ = v___x_3189_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3205_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 1, v___x_3203_);
lean_ctor_set(v___x_3161_, 0, v___x_3196_);
v___x_3205_ = v___x_3161_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3207_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 1, v___x_3205_);
lean_ctor_set(v___x_3156_, 0, v___x_3179_);
v___x_3207_ = v___x_3156_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v___x_3205_);
v___x_3207_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; 
v___x_3208_ = lean_nat_add(v_a_3140_, v___x_3172_);
lean_dec(v_a_3140_);
v_a_3140_ = v___x_3208_;
v_b_3141_ = v___x_3207_;
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
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v___x_3179_);
lean_del_object(v___x_3161_);
lean_dec(v_snd_3159_);
lean_dec(v_fst_3158_);
lean_del_object(v___x_3156_);
lean_dec(v_fst_3154_);
lean_dec(v_fst_3153_);
lean_dec(v_a_3140_);
lean_dec(v___x_3139_);
lean_dec_ref(v___x_3138_);
lean_dec(v___x_3137_);
lean_dec(v_matchDeclName_3136_);
lean_dec_ref(v___x_3135_);
lean_dec_ref(v___x_3134_);
lean_dec(v___x_3133_);
lean_dec_ref(v_a_3132_);
lean_dec_ref(v___x_3131_);
lean_dec(v_baseName_3130_);
lean_dec_ref(v_val_3129_);
v_a_3216_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3184_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3184_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v___x_3179_);
lean_dec_ref(v___f_3178_);
lean_del_object(v___x_3161_);
lean_dec(v_snd_3159_);
lean_dec(v_fst_3158_);
lean_del_object(v___x_3156_);
lean_dec(v_fst_3154_);
lean_dec(v_fst_3153_);
lean_dec(v_a_3140_);
lean_dec(v___x_3139_);
lean_dec_ref(v___x_3138_);
lean_dec(v___x_3137_);
lean_dec(v_matchDeclName_3136_);
lean_dec_ref(v___x_3135_);
lean_dec_ref(v___x_3134_);
lean_dec(v___x_3133_);
lean_dec_ref(v_a_3132_);
lean_dec_ref(v___x_3131_);
lean_dec(v_baseName_3130_);
lean_dec_ref(v_val_3129_);
v_a_3224_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3182_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3182_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
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
lean_object* v_upperBound_3239_ = _args[0];
lean_object* v_val_3240_ = _args[1];
lean_object* v_baseName_3241_ = _args[2];
lean_object* v___x_3242_ = _args[3];
lean_object* v_a_3243_ = _args[4];
lean_object* v___x_3244_ = _args[5];
lean_object* v___x_3245_ = _args[6];
lean_object* v___x_3246_ = _args[7];
lean_object* v_matchDeclName_3247_ = _args[8];
lean_object* v___x_3248_ = _args[9];
lean_object* v___x_3249_ = _args[10];
lean_object* v___x_3250_ = _args[11];
lean_object* v_a_3251_ = _args[12];
lean_object* v_b_3252_ = _args[13];
lean_object* v___y_3253_ = _args[14];
lean_object* v___y_3254_ = _args[15];
lean_object* v___y_3255_ = _args[16];
lean_object* v___y_3256_ = _args[17];
lean_object* v___y_3257_ = _args[18];
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3239_, v_val_3240_, v_baseName_3241_, v___x_3242_, v_a_3243_, v___x_3244_, v___x_3245_, v___x_3246_, v_matchDeclName_3247_, v___x_3248_, v___x_3249_, v___x_3250_, v_a_3251_, v_b_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v_upperBound_3239_);
return v_res_3258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3262_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3263_ = lean_unsigned_to_nat(6u);
v___x_3264_ = lean_unsigned_to_nat(233u);
v___x_3265_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3266_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3267_ = l_mkPanicMessageWithDecl(v___x_3266_, v___x_3265_, v___x_3264_, v___x_3263_, v___x_3262_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3280_, lean_object* v_matchDeclName_3281_, lean_object* v_numParams_3282_, lean_object* v_val_3283_, lean_object* v___x_3284_, lean_object* v_numDiscrs_3285_, lean_object* v_baseName_3286_, lean_object* v_a_3287_, lean_object* v___x_3288_, lean_object* v___x_3289_, lean_object* v___x_3290_, lean_object* v_uElimPos_x3f_3291_, lean_object* v_discrInfos_3292_, lean_object* v_overlaps_3293_, lean_object* v___f_3294_, lean_object* v___x_3295_, lean_object* v_altInfos_3296_, lean_object* v_xs_3297_, lean_object* v___matchResultType_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; uint8_t v___y_3316_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v_lower_3324_; lean_object* v_upper_3325_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3282_);
lean_inc_ref(v_xs_3297_);
v___x_3320_ = l_Array_toSubarray___redArg(v_xs_3297_, v___x_3319_, v_numParams_3282_);
v___x_3321_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3283_);
v___x_3322_ = lean_array_get(v___x_3284_, v_xs_3297_, v___x_3321_);
lean_dec(v___x_3321_);
v___x_3378_ = lean_array_get_size(v_xs_3297_);
v___x_3379_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3283_);
v___x_3380_ = lean_nat_sub(v___x_3378_, v___x_3379_);
lean_dec(v___x_3379_);
v___x_3381_ = lean_nat_dec_le(v___x_3380_, v___x_3319_);
if (v___x_3381_ == 0)
{
v_lower_3324_ = v___x_3380_;
v_upper_3325_ = v___x_3378_;
goto v___jp_3323_;
}
else
{
lean_dec(v___x_3380_);
v_lower_3324_ = v___x_3319_;
v_upper_3325_ = v___x_3378_;
goto v___jp_3323_;
}
v___jp_3304_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3306_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3305_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
return v___x_3306_;
}
v___jp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3310_, 0, v___y_3309_);
lean_ctor_set(v___x_3310_, 1, v_splitterName_3280_);
lean_ctor_set(v___x_3310_, 2, v___y_3308_);
v___x_3311_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3281_, v___x_3310_, v___y_3302_);
return v___x_3311_;
}
v___jp_3312_:
{
lean_object* v___x_3317_; 
lean_inc(v_matchDeclName_3281_);
v___x_3317_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3281_, v___y_3316_, v___y_3313_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_dec_ref(v___x_3317_);
v___y_3308_ = v___y_3314_;
v___y_3309_ = v___y_3315_;
goto v___jp_3307_;
}
else
{
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v_matchDeclName_3281_);
lean_dec(v_splitterName_3280_);
return v___x_3317_;
}
}
v___jp_3323_:
{
lean_object* v___x_3326_; lean_object* v_start_3327_; lean_object* v_stop_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_inc_ref(v_xs_3297_);
v___x_3326_ = l_Array_toSubarray___redArg(v_xs_3297_, v_lower_3324_, v_upper_3325_);
v_start_3327_ = lean_ctor_get(v___x_3326_, 1);
lean_inc(v_start_3327_);
v_stop_3328_ = lean_ctor_get(v___x_3326_, 2);
lean_inc(v_stop_3328_);
v___x_3329_ = lean_unsigned_to_nat(1u);
v___x_3330_ = lean_nat_add(v_numParams_3282_, v___x_3329_);
v___x_3331_ = lean_nat_add(v___x_3330_, v_numDiscrs_3285_);
v___x_3332_ = lean_nat_sub(v_stop_3328_, v_start_3327_);
lean_dec(v_start_3327_);
lean_dec(v_stop_3328_);
v___x_3333_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3334_ = l_Array_toSubarray___redArg(v_xs_3297_, v___x_3330_, v___x_3331_);
lean_inc(v___x_3289_);
lean_inc(v_matchDeclName_3281_);
lean_inc(v___x_3288_);
v___x_3335_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3332_, v_val_3283_, v_baseName_3286_, v___x_3334_, v_a_3287_, v___x_3288_, v___x_3320_, v___x_3322_, v_matchDeclName_3281_, v___x_3289_, v___x_3326_, v___x_3290_, v___x_3319_, v___x_3333_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___x_3332_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v_snd_3337_; lean_object* v_snd_3338_; lean_object* v_snd_3339_; lean_object* v_fst_3340_; lean_object* v_fst_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3368_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3335_);
v_snd_3337_ = lean_ctor_get(v_a_3336_, 1);
v_snd_3338_ = lean_ctor_get(v_snd_3337_, 1);
v_snd_3339_ = lean_ctor_get(v_snd_3338_, 1);
lean_inc(v_snd_3339_);
v_fst_3340_ = lean_ctor_get(v_a_3336_, 0);
lean_inc(v_fst_3340_);
lean_dec(v_a_3336_);
v_fst_3341_ = lean_ctor_get(v_snd_3339_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v_snd_3339_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; 
v_unused_3369_ = lean_ctor_get(v_snd_3339_, 1);
lean_dec(v_unused_3369_);
v___x_3343_ = v_snd_3339_;
v_isShared_3344_ = v_isSharedCheck_3368_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_fst_3341_);
lean_dec(v_snd_3339_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3368_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3345_; uint8_t v___x_3346_; 
lean_inc_ref(v_overlaps_3293_);
lean_inc(v_fst_3341_);
v___x_3345_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3345_, 0, v_numParams_3282_);
lean_ctor_set(v___x_3345_, 1, v_numDiscrs_3285_);
lean_ctor_set(v___x_3345_, 2, v_fst_3341_);
lean_ctor_set(v___x_3345_, 3, v_uElimPos_x3f_3291_);
lean_ctor_set(v___x_3345_, 4, v_discrInfos_3292_);
lean_ctor_set(v___x_3345_, 5, v_overlaps_3293_);
v___x_3346_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3293_);
lean_dec_ref(v_overlaps_3293_);
if (v___x_3346_ == 0)
{
uint8_t v___x_3347_; 
lean_del_object(v___x_3343_);
lean_dec(v_fst_3341_);
lean_dec_ref(v___x_3295_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
v___x_3347_ = 1;
v___y_3313_ = v___f_3294_;
v___y_3314_ = v___x_3345_;
v___y_3315_ = v_fst_3340_;
v___y_3316_ = v___x_3347_;
goto v___jp_3312_;
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3349_ = lean_find_expr(v___x_3348_, v___x_3295_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; 
lean_dec_ref(v___f_3294_);
v___x_3350_ = lean_array_get_size(v_altInfos_3296_);
v___x_3351_ = lean_array_get_size(v_fst_3341_);
v___x_3352_ = lean_nat_dec_eq(v___x_3350_, v___x_3351_);
if (v___x_3352_ == 0)
{
lean_dec_ref(v___x_3345_);
lean_del_object(v___x_3343_);
lean_dec(v_fst_3341_);
lean_dec(v_fst_3340_);
lean_dec_ref(v___x_3295_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
lean_dec(v_matchDeclName_3281_);
lean_dec(v_splitterName_3280_);
goto v___jp_3304_;
}
else
{
uint8_t v___x_3353_; 
v___x_3353_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3296_, v_fst_3341_, v___x_3350_);
lean_dec(v_fst_3341_);
if (v___x_3353_ == 0)
{
lean_dec_ref(v___x_3345_);
lean_del_object(v___x_3343_);
lean_dec(v_fst_3340_);
lean_dec_ref(v___x_3295_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
lean_dec(v_matchDeclName_3281_);
lean_dec(v_splitterName_3280_);
goto v___jp_3304_;
}
else
{
uint8_t v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; lean_object* v___x_3360_; 
v___x_3354_ = 0;
lean_inc_n(v_splitterName_3280_, 2);
v___x_3355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3355_, 0, v_splitterName_3280_);
lean_ctor_set(v___x_3355_, 1, v___x_3289_);
lean_ctor_set(v___x_3355_, 2, v___x_3295_);
lean_inc(v_matchDeclName_3281_);
v___x_3356_ = l_Lean_mkConst(v_matchDeclName_3281_, v___x_3288_);
v___x_3357_ = lean_box(1);
v___x_3358_ = 1;
if (v_isShared_3344_ == 0)
{
lean_ctor_set_tag(v___x_3343_, 1);
lean_ctor_set(v___x_3343_, 1, v___x_3318_);
lean_ctor_set(v___x_3343_, 0, v_splitterName_3280_);
v___x_3360_ = v___x_3343_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_splitterName_3280_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v___x_3318_);
v___x_3360_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3361_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3361_, 0, v___x_3355_);
lean_ctor_set(v___x_3361_, 1, v___x_3356_);
lean_ctor_set(v___x_3361_, 2, v___x_3357_);
lean_ctor_set(v___x_3361_, 3, v___x_3360_);
lean_ctor_set_uint8(v___x_3361_, sizeof(void*)*4, v___x_3358_);
v___x_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
lean_inc_ref(v___x_3362_);
v___x_3363_ = l_Lean_addDecl(v___x_3362_, v___x_3354_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3363_) == 0)
{
uint8_t v___x_3364_; lean_object* v___x_3365_; 
lean_dec_ref(v___x_3363_);
v___x_3364_ = 0;
lean_inc(v_splitterName_3280_);
v___x_3365_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3280_, v___x_3364_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3366_; 
lean_dec_ref(v___x_3365_);
v___x_3366_ = l_Lean_compileDecl(v___x_3362_, v___x_3354_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_dec_ref(v___x_3366_);
v___y_3308_ = v___x_3345_;
v___y_3309_ = v_fst_3340_;
goto v___jp_3307_;
}
else
{
lean_dec_ref(v___x_3345_);
lean_dec(v_fst_3340_);
lean_dec(v_matchDeclName_3281_);
lean_dec(v_splitterName_3280_);
return v___x_3366_;
}
}
else
{
lean_dec_ref(v___x_3362_);
lean_dec_ref(v___x_3345_);
lean_dec(v_fst_3340_);
lean_dec(v_matchDeclName_3281_);
lean_dec(v_splitterName_3280_);
return v___x_3365_;
}
}
else
{
lean_dec_ref(v___x_3362_);
lean_dec_ref(v___x_3345_);
lean_dec(v_fst_3340_);
lean_dec(v_matchDeclName_3281_);
lean_dec(v_splitterName_3280_);
return v___x_3363_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3349_);
lean_del_object(v___x_3343_);
lean_dec(v_fst_3341_);
lean_dec_ref(v___x_3295_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
v___y_3313_ = v___f_3294_;
v___y_3314_ = v___x_3345_;
v___y_3315_ = v_fst_3340_;
v___y_3316_ = v___x_3346_;
goto v___jp_3312_;
}
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec_ref(v___x_3295_);
lean_dec_ref(v___f_3294_);
lean_dec_ref(v_overlaps_3293_);
lean_dec_ref(v_discrInfos_3292_);
lean_dec(v_uElimPos_x3f_3291_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
lean_dec(v_numDiscrs_3285_);
lean_dec(v_numParams_3282_);
lean_dec(v_matchDeclName_3281_);
lean_dec(v_splitterName_3280_);
v_a_3370_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3335_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3335_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3382_ = _args[0];
lean_object* v_matchDeclName_3383_ = _args[1];
lean_object* v_numParams_3384_ = _args[2];
lean_object* v_val_3385_ = _args[3];
lean_object* v___x_3386_ = _args[4];
lean_object* v_numDiscrs_3387_ = _args[5];
lean_object* v_baseName_3388_ = _args[6];
lean_object* v_a_3389_ = _args[7];
lean_object* v___x_3390_ = _args[8];
lean_object* v___x_3391_ = _args[9];
lean_object* v___x_3392_ = _args[10];
lean_object* v_uElimPos_x3f_3393_ = _args[11];
lean_object* v_discrInfos_3394_ = _args[12];
lean_object* v_overlaps_3395_ = _args[13];
lean_object* v___f_3396_ = _args[14];
lean_object* v___x_3397_ = _args[15];
lean_object* v_altInfos_3398_ = _args[16];
lean_object* v_xs_3399_ = _args[17];
lean_object* v___matchResultType_3400_ = _args[18];
lean_object* v___y_3401_ = _args[19];
lean_object* v___y_3402_ = _args[20];
lean_object* v___y_3403_ = _args[21];
lean_object* v___y_3404_ = _args[22];
lean_object* v___y_3405_ = _args[23];
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3382_, v_matchDeclName_3383_, v_numParams_3384_, v_val_3385_, v___x_3386_, v_numDiscrs_3387_, v_baseName_3388_, v_a_3389_, v___x_3390_, v___x_3391_, v___x_3392_, v_uElimPos_x3f_3393_, v_discrInfos_3394_, v_overlaps_3395_, v___f_3396_, v___x_3397_, v_altInfos_3398_, v_xs_3399_, v___matchResultType_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___matchResultType_3400_);
lean_dec_ref(v_altInfos_3398_);
lean_dec_ref(v___x_3386_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
if (lean_obj_tag(v_a_3407_) == 0)
{
lean_object* v___x_3409_; 
v___x_3409_ = l_List_reverse___redArg(v_a_3408_);
return v___x_3409_;
}
else
{
lean_object* v_head_3410_; lean_object* v_tail_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3420_; 
v_head_3410_ = lean_ctor_get(v_a_3407_, 0);
v_tail_3411_ = lean_ctor_get(v_a_3407_, 1);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_a_3407_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3413_ = v_a_3407_;
v_isShared_3414_ = v_isSharedCheck_3420_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_tail_3411_);
lean_inc(v_head_3410_);
lean_dec(v_a_3407_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3420_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3415_ = l_Lean_mkLevelParam(v_head_3410_);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 1, v_a_3408_);
lean_ctor_set(v___x_3413_, 0, v___x_3415_);
v___x_3417_ = v___x_3413_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_a_3408_);
v___x_3417_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
v_a_3407_ = v_tail_3411_;
v_a_3408_ = v___x_3417_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3421_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
return v___x_3423_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3424_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3425_ = lean_unsigned_to_nat(0u);
v___x_3426_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
lean_ctor_set(v___x_3426_, 2, v___x_3425_);
lean_ctor_set(v___x_3426_, 3, v___x_3425_);
lean_ctor_set(v___x_3426_, 4, v___x_3424_);
lean_ctor_set(v___x_3426_, 5, v___x_3424_);
lean_ctor_set(v___x_3426_, 6, v___x_3424_);
lean_ctor_set(v___x_3426_, 7, v___x_3424_);
lean_ctor_set(v___x_3426_, 8, v___x_3424_);
lean_ctor_set(v___x_3426_, 9, v___x_3424_);
return v___x_3426_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3427_ = lean_box(1);
v___x_3428_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3429_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
lean_ctor_set(v___x_3430_, 1, v___x_3428_);
lean_ctor_set(v___x_3430_, 2, v___x_3427_);
return v___x_3430_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_3433_ = l_Lean_stringToMessageData(v___x_3432_);
return v___x_3433_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_3436_ = l_Lean_stringToMessageData(v___x_3435_);
return v___x_3436_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; 
v___x_3438_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_3439_ = l_Lean_stringToMessageData(v___x_3438_);
return v___x_3439_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_3442_ = l_Lean_stringToMessageData(v___x_3441_);
return v___x_3442_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_3445_ = l_Lean_stringToMessageData(v___x_3444_);
return v___x_3445_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_3448_ = l_Lean_stringToMessageData(v___x_3447_);
return v___x_3448_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_3451_ = l_Lean_stringToMessageData(v___x_3450_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3452_, lean_object* v_declHint_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v___x_3456_; lean_object* v_env_3457_; uint8_t v___x_3458_; 
v___x_3456_ = lean_st_ref_get(v___y_3454_);
v_env_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc_ref(v_env_3457_);
lean_dec(v___x_3456_);
v___x_3458_ = l_Lean_Name_isAnonymous(v_declHint_3453_);
if (v___x_3458_ == 0)
{
uint8_t v_isExporting_3459_; 
v_isExporting_3459_ = lean_ctor_get_uint8(v_env_3457_, sizeof(void*)*8);
if (v_isExporting_3459_ == 0)
{
lean_object* v___x_3460_; 
lean_dec_ref(v_env_3457_);
lean_dec(v_declHint_3453_);
v___x_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_msg_3452_);
return v___x_3460_;
}
else
{
lean_object* v___x_3461_; uint8_t v___x_3462_; 
lean_inc_ref(v_env_3457_);
v___x_3461_ = l_Lean_Environment_setExporting(v_env_3457_, v___x_3458_);
lean_inc(v_declHint_3453_);
lean_inc_ref(v___x_3461_);
v___x_3462_ = l_Lean_Environment_contains(v___x_3461_, v_declHint_3453_, v_isExporting_3459_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; 
lean_dec_ref(v___x_3461_);
lean_dec_ref(v_env_3457_);
lean_dec(v_declHint_3453_);
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v_msg_3452_);
return v___x_3463_;
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v_c_3469_; lean_object* v___x_3470_; 
v___x_3464_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3466_ = l_Lean_Options_empty;
v___x_3467_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3461_);
lean_ctor_set(v___x_3467_, 1, v___x_3464_);
lean_ctor_set(v___x_3467_, 2, v___x_3465_);
lean_ctor_set(v___x_3467_, 3, v___x_3466_);
lean_inc(v_declHint_3453_);
v___x_3468_ = l_Lean_MessageData_ofConstName(v_declHint_3453_, v___x_3458_);
v_c_3469_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3469_, 0, v___x_3467_);
lean_ctor_set(v_c_3469_, 1, v___x_3468_);
v___x_3470_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3457_, v_declHint_3453_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_dec_ref(v_env_3457_);
lean_dec(v_declHint_3453_);
v___x_3471_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
lean_ctor_set(v___x_3472_, 1, v_c_3469_);
v___x_3473_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3472_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = l_Lean_MessageData_note(v___x_3474_);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v_msg_3452_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
return v___x_3477_;
}
else
{
lean_object* v_val_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3513_; 
v_val_3478_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3480_ = v___x_3470_;
v_isShared_3481_ = v_isSharedCheck_3513_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_val_3478_);
lean_dec(v___x_3470_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3513_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v_mod_3485_; uint8_t v___x_3486_; 
v___x_3482_ = lean_box(0);
v___x_3483_ = l_Lean_Environment_header(v_env_3457_);
lean_dec_ref(v_env_3457_);
v___x_3484_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3483_);
v_mod_3485_ = lean_array_get(v___x_3482_, v___x_3484_, v_val_3478_);
lean_dec(v_val_3478_);
lean_dec_ref(v___x_3484_);
v___x_3486_ = l_Lean_isPrivateName(v_declHint_3453_);
lean_dec(v_declHint_3453_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3487_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_3488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v_c_3469_);
v___x_3489_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_3490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3488_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
v___x_3491_ = l_Lean_MessageData_ofName(v_mod_3485_);
v___x_3492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_3494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3492_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = l_Lean_MessageData_note(v___x_3494_);
v___x_3496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3496_, 0, v_msg_3452_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set_tag(v___x_3480_, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3496_);
v___x_3498_ = v___x_3480_;
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
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3500_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_ctor_set(v___x_3501_, 1, v_c_3469_);
v___x_3502_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_3503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3501_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
v___x_3504_ = l_Lean_MessageData_ofName(v_mod_3485_);
v___x_3505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3503_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_3507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3505_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
v___x_3508_ = l_Lean_MessageData_note(v___x_3507_);
v___x_3509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3509_, 0, v_msg_3452_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set_tag(v___x_3480_, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3509_);
v___x_3511_ = v___x_3480_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3514_; 
lean_dec_ref(v_env_3457_);
lean_dec(v_declHint_3453_);
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v_msg_3452_);
return v___x_3514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3515_, lean_object* v_declHint_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3515_, v_declHint_3516_, v___y_3517_);
lean_dec(v___y_3517_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3520_, lean_object* v_declHint_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v___x_3527_; lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3537_; 
v___x_3527_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3520_, v_declHint_3521_, v___y_3525_);
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3530_ = v___x_3527_;
v_isShared_3531_ = v_isSharedCheck_3537_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3527_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3537_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3532_ = l_Lean_unknownIdentifierMessageTag;
v___x_3533_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
lean_ctor_set(v___x_3533_, 1, v_a_3528_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3533_);
v___x_3535_ = v___x_3530_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3538_, lean_object* v_declHint_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3538_, v_declHint_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3546_, lean_object* v_msg_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v_fileName_3553_; lean_object* v_fileMap_3554_; lean_object* v_options_3555_; lean_object* v_currRecDepth_3556_; lean_object* v_maxRecDepth_3557_; lean_object* v_ref_3558_; lean_object* v_currNamespace_3559_; lean_object* v_openDecls_3560_; lean_object* v_initHeartbeats_3561_; lean_object* v_maxHeartbeats_3562_; lean_object* v_quotContext_3563_; lean_object* v_currMacroScope_3564_; uint8_t v_diag_3565_; lean_object* v_cancelTk_x3f_3566_; uint8_t v_suppressElabErrors_3567_; lean_object* v_inheritedTraceOptions_3568_; lean_object* v_ref_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_fileName_3553_ = lean_ctor_get(v___y_3550_, 0);
v_fileMap_3554_ = lean_ctor_get(v___y_3550_, 1);
v_options_3555_ = lean_ctor_get(v___y_3550_, 2);
v_currRecDepth_3556_ = lean_ctor_get(v___y_3550_, 3);
v_maxRecDepth_3557_ = lean_ctor_get(v___y_3550_, 4);
v_ref_3558_ = lean_ctor_get(v___y_3550_, 5);
v_currNamespace_3559_ = lean_ctor_get(v___y_3550_, 6);
v_openDecls_3560_ = lean_ctor_get(v___y_3550_, 7);
v_initHeartbeats_3561_ = lean_ctor_get(v___y_3550_, 8);
v_maxHeartbeats_3562_ = lean_ctor_get(v___y_3550_, 9);
v_quotContext_3563_ = lean_ctor_get(v___y_3550_, 10);
v_currMacroScope_3564_ = lean_ctor_get(v___y_3550_, 11);
v_diag_3565_ = lean_ctor_get_uint8(v___y_3550_, sizeof(void*)*14);
v_cancelTk_x3f_3566_ = lean_ctor_get(v___y_3550_, 12);
v_suppressElabErrors_3567_ = lean_ctor_get_uint8(v___y_3550_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3568_ = lean_ctor_get(v___y_3550_, 13);
v_ref_3569_ = l_Lean_replaceRef(v_ref_3546_, v_ref_3558_);
lean_inc_ref(v_inheritedTraceOptions_3568_);
lean_inc(v_cancelTk_x3f_3566_);
lean_inc(v_currMacroScope_3564_);
lean_inc(v_quotContext_3563_);
lean_inc(v_maxHeartbeats_3562_);
lean_inc(v_initHeartbeats_3561_);
lean_inc(v_openDecls_3560_);
lean_inc(v_currNamespace_3559_);
lean_inc(v_maxRecDepth_3557_);
lean_inc(v_currRecDepth_3556_);
lean_inc_ref(v_options_3555_);
lean_inc_ref(v_fileMap_3554_);
lean_inc_ref(v_fileName_3553_);
v___x_3570_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3570_, 0, v_fileName_3553_);
lean_ctor_set(v___x_3570_, 1, v_fileMap_3554_);
lean_ctor_set(v___x_3570_, 2, v_options_3555_);
lean_ctor_set(v___x_3570_, 3, v_currRecDepth_3556_);
lean_ctor_set(v___x_3570_, 4, v_maxRecDepth_3557_);
lean_ctor_set(v___x_3570_, 5, v_ref_3569_);
lean_ctor_set(v___x_3570_, 6, v_currNamespace_3559_);
lean_ctor_set(v___x_3570_, 7, v_openDecls_3560_);
lean_ctor_set(v___x_3570_, 8, v_initHeartbeats_3561_);
lean_ctor_set(v___x_3570_, 9, v_maxHeartbeats_3562_);
lean_ctor_set(v___x_3570_, 10, v_quotContext_3563_);
lean_ctor_set(v___x_3570_, 11, v_currMacroScope_3564_);
lean_ctor_set(v___x_3570_, 12, v_cancelTk_x3f_3566_);
lean_ctor_set(v___x_3570_, 13, v_inheritedTraceOptions_3568_);
lean_ctor_set_uint8(v___x_3570_, sizeof(void*)*14, v_diag_3565_);
lean_ctor_set_uint8(v___x_3570_, sizeof(void*)*14 + 1, v_suppressElabErrors_3567_);
v___x_3571_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3547_, v___y_3548_, v___y_3549_, v___x_3570_, v___y_3551_);
lean_dec_ref(v___x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3572_, lean_object* v_msg_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3572_, v_msg_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v_ref_3572_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3580_, lean_object* v_msg_3581_, lean_object* v_declHint_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v___x_3588_; lean_object* v_a_3589_; lean_object* v___x_3590_; 
v___x_3588_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3581_, v_declHint_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref(v___x_3588_);
v___x_3590_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3580_, v_a_3589_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3591_, lean_object* v_msg_3592_, lean_object* v_declHint_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3591_, v_msg_3592_, v_declHint_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v_ref_3591_);
return v_res_3599_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3602_ = l_Lean_stringToMessageData(v___x_3601_);
return v___x_3602_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3605_ = l_Lean_stringToMessageData(v___x_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3606_, lean_object* v_constName_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v___x_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3613_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3614_ = 0;
lean_inc(v_constName_3607_);
v___x_3615_ = l_Lean_MessageData_ofConstName(v_constName_3607_, v___x_3614_);
v___x_3616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3613_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3616_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3606_, v___x_3618_, v_constName_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3620_, lean_object* v_constName_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3620_, v_constName_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v_ref_3620_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v_ref_3634_; lean_object* v___x_3635_; 
v_ref_3634_ = lean_ctor_get(v___y_3631_, 5);
v___x_3635_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3634_, v_constName_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v___x_3649_; lean_object* v_env_3650_; uint8_t v___x_3651_; lean_object* v___x_3652_; 
v___x_3649_ = lean_st_ref_get(v___y_3647_);
v_env_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc_ref(v_env_3650_);
lean_dec(v___x_3649_);
v___x_3651_ = 0;
lean_inc(v_constName_3643_);
v___x_3652_ = l_Lean_Environment_find_x3f(v_env_3650_, v_constName_3643_, v___x_3651_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
return v___x_3653_;
}
else
{
lean_object* v_val_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_dec(v_constName_3643_);
v_val_3654_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3652_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_val_3654_);
lean_dec(v___x_3652_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set_tag(v___x_3656_, 0);
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_val_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
return v_res_3668_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3671_ = l_Lean_stringToMessageData(v___x_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3672_, lean_object* v_baseName_3673_, lean_object* v_splitterName_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_){
_start:
{
lean_object* v___x_3680_; uint8_t v_foApprox_3681_; uint8_t v_ctxApprox_3682_; uint8_t v_quasiPatternApprox_3683_; uint8_t v_constApprox_3684_; uint8_t v_isDefEqStuckEx_3685_; uint8_t v_unificationHints_3686_; uint8_t v_proofIrrelevance_3687_; uint8_t v_assignSyntheticOpaque_3688_; uint8_t v_offsetCnstrs_3689_; uint8_t v_transparency_3690_; uint8_t v_univApprox_3691_; uint8_t v_iota_3692_; uint8_t v_beta_3693_; uint8_t v_proj_3694_; uint8_t v_zeta_3695_; uint8_t v_zetaDelta_3696_; uint8_t v_zetaUnused_3697_; uint8_t v_zetaHave_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3761_; 
v___x_3680_ = l_Lean_Meta_Context_config(v_a_3675_);
v_foApprox_3681_ = lean_ctor_get_uint8(v___x_3680_, 0);
v_ctxApprox_3682_ = lean_ctor_get_uint8(v___x_3680_, 1);
v_quasiPatternApprox_3683_ = lean_ctor_get_uint8(v___x_3680_, 2);
v_constApprox_3684_ = lean_ctor_get_uint8(v___x_3680_, 3);
v_isDefEqStuckEx_3685_ = lean_ctor_get_uint8(v___x_3680_, 4);
v_unificationHints_3686_ = lean_ctor_get_uint8(v___x_3680_, 5);
v_proofIrrelevance_3687_ = lean_ctor_get_uint8(v___x_3680_, 6);
v_assignSyntheticOpaque_3688_ = lean_ctor_get_uint8(v___x_3680_, 7);
v_offsetCnstrs_3689_ = lean_ctor_get_uint8(v___x_3680_, 8);
v_transparency_3690_ = lean_ctor_get_uint8(v___x_3680_, 9);
v_univApprox_3691_ = lean_ctor_get_uint8(v___x_3680_, 11);
v_iota_3692_ = lean_ctor_get_uint8(v___x_3680_, 12);
v_beta_3693_ = lean_ctor_get_uint8(v___x_3680_, 13);
v_proj_3694_ = lean_ctor_get_uint8(v___x_3680_, 14);
v_zeta_3695_ = lean_ctor_get_uint8(v___x_3680_, 15);
v_zetaDelta_3696_ = lean_ctor_get_uint8(v___x_3680_, 16);
v_zetaUnused_3697_ = lean_ctor_get_uint8(v___x_3680_, 17);
v_zetaHave_3698_ = lean_ctor_get_uint8(v___x_3680_, 18);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3700_ = v___x_3680_;
v_isShared_3701_ = v_isSharedCheck_3761_;
goto v_resetjp_3699_;
}
else
{
lean_dec(v___x_3680_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3761_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
uint8_t v_trackZetaDelta_3702_; lean_object* v_zetaDeltaSet_3703_; lean_object* v_lctx_3704_; lean_object* v_localInstances_3705_; lean_object* v_defEqCtx_x3f_3706_; lean_object* v_synthPendingDepth_3707_; lean_object* v_canUnfold_x3f_3708_; uint8_t v_univApprox_3709_; uint8_t v_inTypeClassResolution_3710_; uint8_t v_cacheInferType_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3759_; 
v_trackZetaDelta_3702_ = lean_ctor_get_uint8(v_a_3675_, sizeof(void*)*7);
v_zetaDeltaSet_3703_ = lean_ctor_get(v_a_3675_, 1);
v_lctx_3704_ = lean_ctor_get(v_a_3675_, 2);
v_localInstances_3705_ = lean_ctor_get(v_a_3675_, 3);
v_defEqCtx_x3f_3706_ = lean_ctor_get(v_a_3675_, 4);
v_synthPendingDepth_3707_ = lean_ctor_get(v_a_3675_, 5);
v_canUnfold_x3f_3708_ = lean_ctor_get(v_a_3675_, 6);
v_univApprox_3709_ = lean_ctor_get_uint8(v_a_3675_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3710_ = lean_ctor_get_uint8(v_a_3675_, sizeof(void*)*7 + 2);
v_cacheInferType_3711_ = lean_ctor_get_uint8(v_a_3675_, sizeof(void*)*7 + 3);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_a_3675_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; 
v_unused_3760_ = lean_ctor_get(v_a_3675_, 0);
lean_dec(v_unused_3760_);
v___x_3713_ = v_a_3675_;
v_isShared_3714_ = v_isSharedCheck_3759_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_canUnfold_x3f_3708_);
lean_inc(v_synthPendingDepth_3707_);
lean_inc(v_defEqCtx_x3f_3706_);
lean_inc(v_localInstances_3705_);
lean_inc(v_lctx_3704_);
lean_inc(v_zetaDeltaSet_3703_);
lean_dec(v_a_3675_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3759_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
uint8_t v___x_3715_; lean_object* v___x_3717_; 
v___x_3715_ = 2;
if (v_isShared_3701_ == 0)
{
v___x_3717_ = v___x_3700_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 0, v_foApprox_3681_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 1, v_ctxApprox_3682_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 2, v_quasiPatternApprox_3683_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 3, v_constApprox_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 4, v_isDefEqStuckEx_3685_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 5, v_unificationHints_3686_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 6, v_proofIrrelevance_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 7, v_assignSyntheticOpaque_3688_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 8, v_offsetCnstrs_3689_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 9, v_transparency_3690_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 11, v_univApprox_3691_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 12, v_iota_3692_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 13, v_beta_3693_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 14, v_proj_3694_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 15, v_zeta_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 16, v_zetaDelta_3696_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 17, v_zetaUnused_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3758_, 18, v_zetaHave_3698_);
v___x_3717_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
uint64_t v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3721_; 
lean_ctor_set_uint8(v___x_3717_, 10, v___x_3715_);
v___x_3718_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3717_);
v___x_3719_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set_uint64(v___x_3719_, sizeof(void*)*1, v___x_3718_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 0, v___x_3719_);
v___x_3721_ = v___x_3713_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_zetaDeltaSet_3703_);
lean_ctor_set(v_reuseFailAlloc_3757_, 2, v_lctx_3704_);
lean_ctor_set(v_reuseFailAlloc_3757_, 3, v_localInstances_3705_);
lean_ctor_set(v_reuseFailAlloc_3757_, 4, v_defEqCtx_x3f_3706_);
lean_ctor_set(v_reuseFailAlloc_3757_, 5, v_synthPendingDepth_3707_);
lean_ctor_set(v_reuseFailAlloc_3757_, 6, v_canUnfold_x3f_3708_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*7, v_trackZetaDelta_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*7 + 1, v_univApprox_3709_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3710_);
lean_ctor_set_uint8(v_reuseFailAlloc_3757_, sizeof(void*)*7 + 3, v_cacheInferType_3711_);
v___x_3721_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; 
lean_inc(v_matchDeclName_3672_);
v___x_3722_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3672_, v___x_3721_, v_a_3676_, v_a_3677_, v_a_3678_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; lean_object* v_a_3725_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
lean_inc(v_matchDeclName_3672_);
v___x_3724_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_3672_, v_a_3678_);
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref(v___x_3724_);
if (lean_obj_tag(v_a_3725_) == 1)
{
lean_object* v_val_3726_; lean_object* v_numParams_3727_; lean_object* v_numDiscrs_3728_; lean_object* v_altInfos_3729_; lean_object* v_uElimPos_x3f_3730_; lean_object* v_discrInfos_3731_; lean_object* v_overlaps_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___f_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___f_3740_; uint8_t v___x_3741_; lean_object* v___x_3742_; 
v_val_3726_ = lean_ctor_get(v_a_3725_, 0);
lean_inc(v_val_3726_);
lean_dec_ref(v_a_3725_);
v_numParams_3727_ = lean_ctor_get(v_val_3726_, 0);
lean_inc(v_numParams_3727_);
v_numDiscrs_3728_ = lean_ctor_get(v_val_3726_, 1);
lean_inc(v_numDiscrs_3728_);
v_altInfos_3729_ = lean_ctor_get(v_val_3726_, 2);
lean_inc_ref(v_altInfos_3729_);
v_uElimPos_x3f_3730_ = lean_ctor_get(v_val_3726_, 3);
lean_inc(v_uElimPos_x3f_3730_);
v_discrInfos_3731_ = lean_ctor_get(v_val_3726_, 4);
lean_inc_ref(v_discrInfos_3731_);
v_overlaps_3732_ = lean_ctor_get(v_val_3726_, 5);
lean_inc_ref_n(v_overlaps_3732_, 2);
v___x_3733_ = l_Lean_instInhabitedExpr;
v___x_3734_ = l_Lean_ConstantInfo_levelParams(v_a_3723_);
v___x_3735_ = lean_box(0);
lean_inc(v___x_3734_);
v___x_3736_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_3734_, v___x_3735_);
lean_inc(v_splitterName_3674_);
v___f_3737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3737_, 0, v_overlaps_3732_);
lean_closure_set(v___f_3737_, 1, v_splitterName_3674_);
v___x_3738_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3731_);
v___x_3739_ = l_Lean_ConstantInfo_type(v_a_3723_);
lean_inc_ref(v___x_3739_);
v___f_3740_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3740_, 0, v_splitterName_3674_);
lean_closure_set(v___f_3740_, 1, v_matchDeclName_3672_);
lean_closure_set(v___f_3740_, 2, v_numParams_3727_);
lean_closure_set(v___f_3740_, 3, v_val_3726_);
lean_closure_set(v___f_3740_, 4, v___x_3733_);
lean_closure_set(v___f_3740_, 5, v_numDiscrs_3728_);
lean_closure_set(v___f_3740_, 6, v_baseName_3673_);
lean_closure_set(v___f_3740_, 7, v_a_3723_);
lean_closure_set(v___f_3740_, 8, v___x_3736_);
lean_closure_set(v___f_3740_, 9, v___x_3734_);
lean_closure_set(v___f_3740_, 10, v___x_3738_);
lean_closure_set(v___f_3740_, 11, v_uElimPos_x3f_3730_);
lean_closure_set(v___f_3740_, 12, v_discrInfos_3731_);
lean_closure_set(v___f_3740_, 13, v_overlaps_3732_);
lean_closure_set(v___f_3740_, 14, v___f_3737_);
lean_closure_set(v___f_3740_, 15, v___x_3739_);
lean_closure_set(v___f_3740_, 16, v_altInfos_3729_);
v___x_3741_ = 0;
v___x_3742_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3739_, v___f_3740_, v___x_3741_, v___x_3741_, v___x_3721_, v_a_3676_, v_a_3677_, v_a_3678_);
lean_dec_ref(v___x_3721_);
return v___x_3742_;
}
else
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
lean_dec(v_a_3725_);
lean_dec(v_a_3723_);
lean_dec(v_splitterName_3674_);
lean_dec(v_baseName_3673_);
v___x_3743_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3744_ = l_Lean_MessageData_ofName(v_matchDeclName_3672_);
v___x_3745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3743_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3747_, v___x_3721_, v_a_3676_, v_a_3677_, v_a_3678_);
lean_dec_ref(v___x_3721_);
return v___x_3748_;
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec_ref(v___x_3721_);
lean_dec(v_splitterName_3674_);
lean_dec(v_baseName_3673_);
lean_dec(v_matchDeclName_3672_);
v_a_3749_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3722_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3722_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3762_, lean_object* v_baseName_3763_, lean_object* v_splitterName_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3762_, v_baseName_3763_, v_splitterName_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
return v_res_3770_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3771_, lean_object* v_ys_3772_, lean_object* v_hsz_3773_, lean_object* v_x_3774_, lean_object* v_x_3775_){
_start:
{
uint8_t v___x_3776_; 
v___x_3776_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3771_, v_ys_3772_, v_x_3774_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3777_, lean_object* v_ys_3778_, lean_object* v_hsz_3779_, lean_object* v_x_3780_, lean_object* v_x_3781_){
_start:
{
uint8_t v_res_3782_; lean_object* v_r_3783_; 
v_res_3782_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3777_, v_ys_3778_, v_hsz_3779_, v_x_3780_, v_x_3781_);
lean_dec_ref(v_ys_3778_);
lean_dec_ref(v_xs_3777_);
v_r_3783_ = lean_box(v_res_3782_);
return v_r_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3784_, lean_object* v_R_3785_, lean_object* v_a_3786_, lean_object* v_b_3787_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3786_, v_b_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3789_, lean_object* v_val_3790_, lean_object* v_baseName_3791_, lean_object* v___x_3792_, lean_object* v_a_3793_, lean_object* v___x_3794_, lean_object* v___x_3795_, lean_object* v___x_3796_, lean_object* v_matchDeclName_3797_, lean_object* v___x_3798_, lean_object* v___x_3799_, lean_object* v___x_3800_, lean_object* v_inst_3801_, lean_object* v_R_3802_, lean_object* v_a_3803_, lean_object* v_b_3804_, lean_object* v_c_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v___x_3811_; 
v___x_3811_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3789_, v_val_3790_, v_baseName_3791_, v___x_3792_, v_a_3793_, v___x_3794_, v___x_3795_, v___x_3796_, v_matchDeclName_3797_, v___x_3798_, v___x_3799_, v___x_3800_, v_a_3803_, v_b_3804_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3812_ = _args[0];
lean_object* v_val_3813_ = _args[1];
lean_object* v_baseName_3814_ = _args[2];
lean_object* v___x_3815_ = _args[3];
lean_object* v_a_3816_ = _args[4];
lean_object* v___x_3817_ = _args[5];
lean_object* v___x_3818_ = _args[6];
lean_object* v___x_3819_ = _args[7];
lean_object* v_matchDeclName_3820_ = _args[8];
lean_object* v___x_3821_ = _args[9];
lean_object* v___x_3822_ = _args[10];
lean_object* v___x_3823_ = _args[11];
lean_object* v_inst_3824_ = _args[12];
lean_object* v_R_3825_ = _args[13];
lean_object* v_a_3826_ = _args[14];
lean_object* v_b_3827_ = _args[15];
lean_object* v_c_3828_ = _args[16];
lean_object* v___y_3829_ = _args[17];
lean_object* v___y_3830_ = _args[18];
lean_object* v___y_3831_ = _args[19];
lean_object* v___y_3832_ = _args[20];
lean_object* v___y_3833_ = _args[21];
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3812_, v_val_3813_, v_baseName_3814_, v___x_3815_, v_a_3816_, v___x_3817_, v___x_3818_, v___x_3819_, v_matchDeclName_3820_, v___x_3821_, v___x_3822_, v___x_3823_, v_inst_3824_, v_R_3825_, v_a_3826_, v_b_3827_, v_c_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v_upperBound_3812_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3835_, lean_object* v_constName_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v___x_3842_; 
v___x_3842_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3843_, lean_object* v_constName_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3843_, v_constName_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3851_, lean_object* v_ref_3852_, lean_object* v_constName_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3852_, v_constName_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3860_, lean_object* v_ref_3861_, lean_object* v_constName_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3860_, v_ref_3861_, v_constName_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v_ref_3861_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3869_, lean_object* v_ref_3870_, lean_object* v_msg_3871_, lean_object* v_declHint_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3870_, v_msg_3871_, v_declHint_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3879_, lean_object* v_ref_3880_, lean_object* v_msg_3881_, lean_object* v_declHint_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3879_, v_ref_3880_, v_msg_3881_, v_declHint_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v_ref_3880_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3889_, lean_object* v_declHint_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3889_, v_declHint_3890_, v___y_3894_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3897_, lean_object* v_declHint_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3897_, v_declHint_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3905_, lean_object* v_ref_3906_, lean_object* v_msg_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3906_, v_msg_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3914_, lean_object* v_ref_3915_, lean_object* v_msg_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3914_, v_ref_3915_, v_msg_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v_ref_3915_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3923_, lean_object* v_vals_3924_, lean_object* v_i_3925_, lean_object* v_k_3926_){
_start:
{
lean_object* v___x_3927_; uint8_t v___x_3928_; 
v___x_3927_ = lean_array_get_size(v_keys_3923_);
v___x_3928_ = lean_nat_dec_lt(v_i_3925_, v___x_3927_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; 
lean_dec(v_i_3925_);
v___x_3929_ = lean_box(0);
return v___x_3929_;
}
else
{
lean_object* v_k_x27_3930_; uint8_t v___x_3931_; 
v_k_x27_3930_ = lean_array_fget_borrowed(v_keys_3923_, v_i_3925_);
v___x_3931_ = lean_name_eq(v_k_3926_, v_k_x27_3930_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = lean_unsigned_to_nat(1u);
v___x_3933_ = lean_nat_add(v_i_3925_, v___x_3932_);
lean_dec(v_i_3925_);
v_i_3925_ = v___x_3933_;
goto _start;
}
else
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = lean_array_fget_borrowed(v_vals_3924_, v_i_3925_);
lean_dec(v_i_3925_);
lean_inc(v___x_3935_);
v___x_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3935_);
return v___x_3936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3937_, lean_object* v_vals_3938_, lean_object* v_i_3939_, lean_object* v_k_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3937_, v_vals_3938_, v_i_3939_, v_k_3940_);
lean_dec(v_k_3940_);
lean_dec_ref(v_vals_3938_);
lean_dec_ref(v_keys_3937_);
return v_res_3941_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_3942_; size_t v___x_3943_; size_t v___x_3944_; 
v___x_3942_ = ((size_t)5ULL);
v___x_3943_ = ((size_t)1ULL);
v___x_3944_ = lean_usize_shift_left(v___x_3943_, v___x_3942_);
return v___x_3944_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_3945_; size_t v___x_3946_; size_t v___x_3947_; 
v___x_3945_ = ((size_t)1ULL);
v___x_3946_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0);
v___x_3947_ = lean_usize_sub(v___x_3946_, v___x_3945_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3948_, size_t v_x_3949_, lean_object* v_x_3950_){
_start:
{
if (lean_obj_tag(v_x_3948_) == 0)
{
lean_object* v_es_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3972_; 
v_es_3951_ = lean_ctor_get(v_x_3948_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v_x_3948_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3953_ = v_x_3948_;
v_isShared_3954_ = v_isSharedCheck_3972_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_es_3951_);
lean_dec(v_x_3948_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3972_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3955_; size_t v___x_3956_; size_t v___x_3957_; size_t v___x_3958_; lean_object* v_j_3959_; lean_object* v___x_3960_; 
v___x_3955_ = lean_box(2);
v___x_3956_ = ((size_t)5ULL);
v___x_3957_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1);
v___x_3958_ = lean_usize_land(v_x_3949_, v___x_3957_);
v_j_3959_ = lean_usize_to_nat(v___x_3958_);
v___x_3960_ = lean_array_get(v___x_3955_, v_es_3951_, v_j_3959_);
lean_dec(v_j_3959_);
lean_dec_ref(v_es_3951_);
switch(lean_obj_tag(v___x_3960_))
{
case 0:
{
lean_object* v_key_3961_; lean_object* v_val_3962_; uint8_t v___x_3963_; 
v_key_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_key_3961_);
v_val_3962_ = lean_ctor_get(v___x_3960_, 1);
lean_inc(v_val_3962_);
lean_dec_ref(v___x_3960_);
v___x_3963_ = lean_name_eq(v_x_3950_, v_key_3961_);
lean_dec(v_key_3961_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; 
lean_dec(v_val_3962_);
lean_del_object(v___x_3953_);
v___x_3964_ = lean_box(0);
return v___x_3964_;
}
else
{
lean_object* v___x_3966_; 
if (v_isShared_3954_ == 0)
{
lean_ctor_set_tag(v___x_3953_, 1);
lean_ctor_set(v___x_3953_, 0, v_val_3962_);
v___x_3966_ = v___x_3953_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_val_3962_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
case 1:
{
lean_object* v_node_3968_; size_t v___x_3969_; 
lean_del_object(v___x_3953_);
v_node_3968_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_node_3968_);
lean_dec_ref(v___x_3960_);
v___x_3969_ = lean_usize_shift_right(v_x_3949_, v___x_3956_);
v_x_3948_ = v_node_3968_;
v_x_3949_ = v___x_3969_;
goto _start;
}
default: 
{
lean_object* v___x_3971_; 
lean_del_object(v___x_3953_);
v___x_3971_ = lean_box(0);
return v___x_3971_;
}
}
}
}
else
{
lean_object* v_ks_3973_; lean_object* v_vs_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v_ks_3973_ = lean_ctor_get(v_x_3948_, 0);
lean_inc_ref(v_ks_3973_);
v_vs_3974_ = lean_ctor_get(v_x_3948_, 1);
lean_inc_ref(v_vs_3974_);
lean_dec_ref(v_x_3948_);
v___x_3975_ = lean_unsigned_to_nat(0u);
v___x_3976_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3973_, v_vs_3974_, v___x_3975_, v_x_3950_);
lean_dec_ref(v_vs_3974_);
lean_dec_ref(v_ks_3973_);
return v___x_3976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3977_, lean_object* v_x_3978_, lean_object* v_x_3979_){
_start:
{
size_t v_x_715__boxed_3980_; lean_object* v_res_3981_; 
v_x_715__boxed_3980_ = lean_unbox_usize(v_x_3978_);
lean_dec(v_x_3978_);
v_res_3981_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3977_, v_x_715__boxed_3980_, v_x_3979_);
lean_dec(v_x_3979_);
return v_res_3981_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3982_; uint64_t v___x_3983_; 
v___x_3982_ = lean_unsigned_to_nat(1723u);
v___x_3983_ = lean_uint64_of_nat(v___x_3982_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3984_, lean_object* v_x_3985_){
_start:
{
uint64_t v___y_3987_; 
if (lean_obj_tag(v_x_3985_) == 0)
{
uint64_t v___x_3990_; 
v___x_3990_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0);
v___y_3987_ = v___x_3990_;
goto v___jp_3986_;
}
else
{
uint64_t v_hash_3991_; 
v_hash_3991_ = lean_ctor_get_uint64(v_x_3985_, sizeof(void*)*2);
v___y_3987_ = v_hash_3991_;
goto v___jp_3986_;
}
v___jp_3986_:
{
size_t v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_uint64_to_usize(v___y_3987_);
v___x_3989_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3984_, v___x_3988_, v_x_3985_);
return v___x_3989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3992_, lean_object* v_x_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3992_, v_x_3993_);
lean_dec(v_x_3993_);
return v_res_3994_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_4002_ = l_Lean_stringToMessageData(v___x_4001_);
return v___x_4002_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_4005_ = l_Lean_stringToMessageData(v___x_4004_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_){
_start:
{
lean_object* v___x_4012_; lean_object* v_env_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4012_ = lean_st_ref_get(v_a_4010_);
v_env_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc_ref(v_env_4013_);
lean_dec(v___x_4012_);
lean_inc_n(v_matchDeclName_4006_, 3);
v___x_4014_ = l_Lean_mkPrivateName(v_env_4013_, v_matchDeclName_4006_);
lean_dec_ref(v_env_4013_);
v___x_4015_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_4014_);
v___x_4016_ = l_Lean_Name_append(v___x_4014_, v___x_4015_);
lean_inc_n(v___x_4016_, 2);
v___x_4017_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_4017_, 0, v_matchDeclName_4006_);
lean_closure_set(v___x_4017_, 1, v___x_4014_);
lean_closure_set(v___x_4017_, 2, v___x_4016_);
v___x_4018_ = l_Lean_Meta_realizeConst(v_matchDeclName_4006_, v___x_4016_, v___x_4017_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4047_; 
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4047_ == 0)
{
lean_object* v_unused_4048_; 
v_unused_4048_ = lean_ctor_get(v___x_4018_, 0);
lean_dec(v_unused_4048_);
v___x_4020_ = v___x_4018_;
v_isShared_4021_ = v_isSharedCheck_4047_;
goto v_resetjp_4019_;
}
else
{
lean_dec(v___x_4018_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4047_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v_env_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v_map_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4045_; 
v___x_4022_ = lean_st_ref_get(v_a_4010_);
v_env_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc_ref(v_env_4023_);
lean_dec(v___x_4022_);
v___x_4024_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_4025_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_4026_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_4027_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4024_, v___x_4025_, v_env_4023_, v___x_4026_, v___x_4016_);
v_map_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4045_ == 0)
{
lean_object* v_unused_4046_; 
v_unused_4046_ = lean_ctor_get(v___x_4027_, 1);
lean_dec(v_unused_4046_);
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4045_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_map_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4045_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_4028_, v_matchDeclName_4006_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4036_; 
lean_del_object(v___x_4020_);
v___x_4033_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_4034_ = l_Lean_MessageData_ofName(v_matchDeclName_4006_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set_tag(v___x_4030_, 7);
lean_ctor_set(v___x_4030_, 1, v___x_4034_);
lean_ctor_set(v___x_4030_, 0, v___x_4033_);
v___x_4036_ = v___x_4030_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4037_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_4038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4036_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
v___x_4039_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_4038_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
return v___x_4039_;
}
}
else
{
lean_object* v_val_4041_; lean_object* v___x_4043_; 
lean_del_object(v___x_4030_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
lean_dec(v_matchDeclName_4006_);
v_val_4041_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_val_4041_);
lean_dec_ref(v___x_4032_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v_val_4041_);
v___x_4043_ = v___x_4020_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_val_4041_);
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
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec(v___x_4016_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
lean_dec(v_matchDeclName_4006_);
v_a_4049_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4018_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4018_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = lean_get_match_equations_for(v_matchDeclName_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4064_, lean_object* v_x_4065_, lean_object* v_x_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4065_, v_x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4068_, lean_object* v_x_4069_, lean_object* v_x_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4068_, v_x_4069_, v_x_4070_);
lean_dec(v_x_4070_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4072_, lean_object* v_x_4073_, size_t v_x_4074_, lean_object* v_x_4075_){
_start:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4073_, v_x_4074_, v_x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4077_, lean_object* v_x_4078_, lean_object* v_x_4079_, lean_object* v_x_4080_){
_start:
{
size_t v_x_931__boxed_4081_; lean_object* v_res_4082_; 
v_x_931__boxed_4081_ = lean_unbox_usize(v_x_4079_);
lean_dec(v_x_4079_);
v_res_4082_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4077_, v_x_4078_, v_x_931__boxed_4081_, v_x_4080_);
lean_dec(v_x_4080_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4083_, lean_object* v_keys_4084_, lean_object* v_vals_4085_, lean_object* v_heq_4086_, lean_object* v_i_4087_, lean_object* v_k_4088_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4084_, v_vals_4085_, v_i_4087_, v_k_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4090_, lean_object* v_keys_4091_, lean_object* v_vals_4092_, lean_object* v_heq_4093_, lean_object* v_i_4094_, lean_object* v_k_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4090_, v_keys_4091_, v_vals_4092_, v_heq_4093_, v_i_4094_, v_k_4095_);
lean_dec(v_k_4095_);
lean_dec_ref(v_vals_4092_);
lean_dec_ref(v_keys_4091_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4097_, lean_object* v_k_4098_, uint8_t v_cleanupAnnotations_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v___f_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___f_4105_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4105_, 0, v_k_4098_);
v___x_4106_ = 0;
v___x_4107_ = lean_box(0);
v___x_4108_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4106_, v___x_4107_, v_type_4097_, v___f_4105_, v_cleanupAnnotations_4099_, v___x_4106_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4108_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4108_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
v_a_4117_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4108_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4108_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4125_, lean_object* v_k_4126_, lean_object* v_cleanupAnnotations_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4133_; lean_object* v_res_4134_; 
v_cleanupAnnotations_boxed_4133_ = lean_unbox(v_cleanupAnnotations_4127_);
v_res_4134_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4125_, v_k_4126_, v_cleanupAnnotations_boxed_4133_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4135_, lean_object* v_type_4136_, lean_object* v_k_4137_, uint8_t v_cleanupAnnotations_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4136_, v_k_4137_, v_cleanupAnnotations_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4145_, lean_object* v_type_4146_, lean_object* v_k_4147_, lean_object* v_cleanupAnnotations_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4154_; lean_object* v_res_4155_; 
v_cleanupAnnotations_boxed_4154_ = lean_unbox(v_cleanupAnnotations_4148_);
v_res_4155_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4145_, v_type_4146_, v_k_4147_, v_cleanupAnnotations_boxed_4154_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v_msg_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_){
_start:
{
lean_object* v___f_4162_; lean_object* v___x_19931__overap_4163_; lean_object* v___x_4164_; 
v___f_4162_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_19931__overap_4163_ = lean_panic_fn_borrowed(v___f_4162_, v_msg_4156_);
lean_inc(v___y_4160_);
lean_inc_ref(v___y_4159_);
lean_inc(v___y_4158_);
lean_inc_ref(v___y_4157_);
v___x_4164_ = lean_apply_5(v___x_19931__overap_4163_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, lean_box(0));
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v_msg_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_msg_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4172_){
_start:
{
uint8_t v_foApprox_4173_; uint8_t v_ctxApprox_4174_; uint8_t v_quasiPatternApprox_4175_; uint8_t v_constApprox_4176_; uint8_t v_isDefEqStuckEx_4177_; uint8_t v_unificationHints_4178_; uint8_t v_proofIrrelevance_4179_; uint8_t v_assignSyntheticOpaque_4180_; uint8_t v_offsetCnstrs_4181_; uint8_t v_transparency_4182_; uint8_t v_univApprox_4183_; uint8_t v_iota_4184_; uint8_t v_beta_4185_; uint8_t v_proj_4186_; uint8_t v_zeta_4187_; uint8_t v_zetaDelta_4188_; uint8_t v_zetaUnused_4189_; uint8_t v_zetaHave_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4198_; 
v_foApprox_4173_ = lean_ctor_get_uint8(v_c_4172_, 0);
v_ctxApprox_4174_ = lean_ctor_get_uint8(v_c_4172_, 1);
v_quasiPatternApprox_4175_ = lean_ctor_get_uint8(v_c_4172_, 2);
v_constApprox_4176_ = lean_ctor_get_uint8(v_c_4172_, 3);
v_isDefEqStuckEx_4177_ = lean_ctor_get_uint8(v_c_4172_, 4);
v_unificationHints_4178_ = lean_ctor_get_uint8(v_c_4172_, 5);
v_proofIrrelevance_4179_ = lean_ctor_get_uint8(v_c_4172_, 6);
v_assignSyntheticOpaque_4180_ = lean_ctor_get_uint8(v_c_4172_, 7);
v_offsetCnstrs_4181_ = lean_ctor_get_uint8(v_c_4172_, 8);
v_transparency_4182_ = lean_ctor_get_uint8(v_c_4172_, 9);
v_univApprox_4183_ = lean_ctor_get_uint8(v_c_4172_, 11);
v_iota_4184_ = lean_ctor_get_uint8(v_c_4172_, 12);
v_beta_4185_ = lean_ctor_get_uint8(v_c_4172_, 13);
v_proj_4186_ = lean_ctor_get_uint8(v_c_4172_, 14);
v_zeta_4187_ = lean_ctor_get_uint8(v_c_4172_, 15);
v_zetaDelta_4188_ = lean_ctor_get_uint8(v_c_4172_, 16);
v_zetaUnused_4189_ = lean_ctor_get_uint8(v_c_4172_, 17);
v_zetaHave_4190_ = lean_ctor_get_uint8(v_c_4172_, 18);
v_isSharedCheck_4198_ = !lean_is_exclusive(v_c_4172_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4192_ = v_c_4172_;
v_isShared_4193_ = v_isSharedCheck_4198_;
goto v_resetjp_4191_;
}
else
{
lean_dec(v_c_4172_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4198_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
uint8_t v___x_4194_; lean_object* v___x_4196_; 
v___x_4194_ = 2;
if (v_isShared_4193_ == 0)
{
v___x_4196_ = v___x_4192_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 0, v_foApprox_4173_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 1, v_ctxApprox_4174_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 2, v_quasiPatternApprox_4175_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 3, v_constApprox_4176_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 4, v_isDefEqStuckEx_4177_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 5, v_unificationHints_4178_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 6, v_proofIrrelevance_4179_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 7, v_assignSyntheticOpaque_4180_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 8, v_offsetCnstrs_4181_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 9, v_transparency_4182_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 11, v_univApprox_4183_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 12, v_iota_4184_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 13, v_beta_4185_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 14, v_proj_4186_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 15, v_zeta_4187_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 16, v_zetaDelta_4188_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 17, v_zetaUnused_4189_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, 18, v_zetaHave_4190_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_ctor_set_uint8(v___x_4196_, 10, v___x_4194_);
return v___x_4196_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4199_, lean_object* v_t_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v_dummy_4206_; lean_object* v_nargs_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_dummy_4206_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4207_ = l_Lean_Expr_getAppNumArgs(v_t_4200_);
lean_inc(v_nargs_4207_);
v___x_4208_ = lean_mk_array(v_nargs_4207_, v_dummy_4206_);
v___x_4209_ = lean_unsigned_to_nat(1u);
v___x_4210_ = lean_nat_sub(v_nargs_4207_, v___x_4209_);
lean_dec(v_nargs_4207_);
v___x_4211_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4200_, v___x_4208_, v___x_4210_);
v___x_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4213_, lean_object* v_t_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4213_, v_t_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec_ref(v_x_4213_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4221_, lean_object* v_x_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v_snd_4221_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4229_, lean_object* v_x_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
lean_object* v_res_4236_; 
v_res_4236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4229_, v_x_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec_ref(v_x_4230_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4237_, size_t v_i_4238_, lean_object* v_bs_4239_){
_start:
{
uint8_t v___x_4240_; 
v___x_4240_ = lean_usize_dec_lt(v_i_4238_, v_sz_4237_);
if (v___x_4240_ == 0)
{
return v_bs_4239_;
}
else
{
lean_object* v_v_4241_; lean_object* v_fst_4242_; lean_object* v_snd_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4257_; 
v_v_4241_ = lean_array_uget(v_bs_4239_, v_i_4238_);
v_fst_4242_ = lean_ctor_get(v_v_4241_, 0);
v_snd_4243_ = lean_ctor_get(v_v_4241_, 1);
v_isSharedCheck_4257_ = !lean_is_exclusive(v_v_4241_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4245_ = v_v_4241_;
v_isShared_4246_ = v_isSharedCheck_4257_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_snd_4243_);
lean_inc(v_fst_4242_);
lean_dec(v_v_4241_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4257_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4247_; lean_object* v_bs_x27_4248_; lean_object* v___f_4249_; lean_object* v___x_4251_; 
v___x_4247_ = lean_unsigned_to_nat(0u);
v_bs_x27_4248_ = lean_array_uset(v_bs_4239_, v_i_4238_, v___x_4247_);
v___f_4249_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4249_, 0, v_snd_4243_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 1, v___f_4249_);
v___x_4251_ = v___x_4245_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_fst_4242_);
lean_ctor_set(v_reuseFailAlloc_4256_, 1, v___f_4249_);
v___x_4251_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
size_t v___x_4252_; size_t v___x_4253_; lean_object* v___x_4254_; 
v___x_4252_ = ((size_t)1ULL);
v___x_4253_ = lean_usize_add(v_i_4238_, v___x_4252_);
v___x_4254_ = lean_array_uset(v_bs_x27_4248_, v_i_4238_, v___x_4251_);
v_i_4238_ = v___x_4253_;
v_bs_4239_ = v___x_4254_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4258_, lean_object* v_i_4259_, lean_object* v_bs_4260_){
_start:
{
size_t v_sz_boxed_4261_; size_t v_i_boxed_4262_; lean_object* v_res_4263_; 
v_sz_boxed_4261_ = lean_unbox_usize(v_sz_4258_);
lean_dec(v_sz_4258_);
v_i_boxed_4262_ = lean_unbox_usize(v_i_4259_);
lean_dec(v_i_4259_);
v_res_4263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4261_, v_i_boxed_4262_, v_bs_4260_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4264_, size_t v_i_4265_, lean_object* v_bs_4266_){
_start:
{
uint8_t v___x_4267_; 
v___x_4267_ = lean_usize_dec_lt(v_i_4265_, v_sz_4264_);
if (v___x_4267_ == 0)
{
return v_bs_4266_;
}
else
{
lean_object* v_v_4268_; lean_object* v_fst_4269_; lean_object* v_snd_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4286_; 
v_v_4268_ = lean_array_uget(v_bs_4266_, v_i_4265_);
v_fst_4269_ = lean_ctor_get(v_v_4268_, 0);
v_snd_4270_ = lean_ctor_get(v_v_4268_, 1);
v_isSharedCheck_4286_ = !lean_is_exclusive(v_v_4268_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4272_ = v_v_4268_;
v_isShared_4273_ = v_isSharedCheck_4286_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_snd_4270_);
lean_inc(v_fst_4269_);
lean_dec(v_v_4268_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4286_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4274_; lean_object* v_bs_x27_4275_; uint8_t v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4279_; 
v___x_4274_ = lean_unsigned_to_nat(0u);
v_bs_x27_4275_ = lean_array_uset(v_bs_4266_, v_i_4265_, v___x_4274_);
v___x_4276_ = 0;
v___x_4277_ = lean_box(v___x_4276_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v___x_4277_);
v___x_4279_ = v___x_4272_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v___x_4277_);
lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_snd_4270_);
v___x_4279_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
lean_object* v___x_4280_; size_t v___x_4281_; size_t v___x_4282_; lean_object* v___x_4283_; 
v___x_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4280_, 0, v_fst_4269_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
v___x_4281_ = ((size_t)1ULL);
v___x_4282_ = lean_usize_add(v_i_4265_, v___x_4281_);
v___x_4283_ = lean_array_uset(v_bs_x27_4275_, v_i_4265_, v___x_4280_);
v_i_4265_ = v___x_4282_;
v_bs_4266_ = v___x_4283_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4287_, lean_object* v_i_4288_, lean_object* v_bs_4289_){
_start:
{
size_t v_sz_boxed_4290_; size_t v_i_boxed_4291_; lean_object* v_res_4292_; 
v_sz_boxed_4290_ = lean_unbox_usize(v_sz_4287_);
lean_dec(v_sz_4287_);
v_i_boxed_4291_ = lean_unbox_usize(v_i_4288_);
lean_dec(v_i_4288_);
v_res_4292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4290_, v_i_boxed_4291_, v_bs_4289_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4293_, lean_object* v_a_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v___x_4300_; lean_object* v___x_21853__overap_4301_; lean_object* v___x_4302_; 
v___x_4300_ = l_Lean_instInhabitedExpr;
v___x_21853__overap_4301_ = l_instInhabitedOfMonad___redArg(v___x_4293_, v___x_4300_);
lean_inc(v___y_4298_);
lean_inc_ref(v___y_4297_);
lean_inc(v___y_4296_);
lean_inc_ref(v___y_4295_);
v___x_4302_ = lean_apply_5(v___x_21853__overap_4301_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, lean_box(0));
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4303_, lean_object* v_a_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4303_, v_a_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec_ref(v_a_4304_);
return v_res_4310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = l_instMonadEIO(lean_box(0));
return v___x_4311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4312_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4313_ = l_StateRefT_x27_instMonad___redArg(v___x_4312_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4318_, lean_object* v_declInfos_4319_, lean_object* v_k_4320_, lean_object* v_kind_4321_, lean_object* v_x_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
uint8_t v_kind_boxed_4328_; lean_object* v_res_4329_; 
v_kind_boxed_4328_ = lean_unbox(v_kind_4321_);
v_res_4329_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4318_, v_declInfos_4319_, v_k_4320_, v_kind_boxed_4328_, v_x_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4330_, lean_object* v_k_4331_, uint8_t v_kind_4332_, lean_object* v_acc_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v___x_4339_; lean_object* v_toApplicative_4340_; lean_object* v_toFunctor_4341_; lean_object* v_toSeq_4342_; lean_object* v_toSeqLeft_4343_; lean_object* v_toSeqRight_4344_; lean_object* v___f_4345_; lean_object* v___f_4346_; lean_object* v___f_4347_; lean_object* v___f_4348_; lean_object* v___x_4349_; lean_object* v___f_4350_; lean_object* v___f_4351_; lean_object* v___f_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v_toApplicative_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4405_; 
v___x_4339_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4340_ = lean_ctor_get(v___x_4339_, 0);
v_toFunctor_4341_ = lean_ctor_get(v_toApplicative_4340_, 0);
v_toSeq_4342_ = lean_ctor_get(v_toApplicative_4340_, 2);
v_toSeqLeft_4343_ = lean_ctor_get(v_toApplicative_4340_, 3);
v_toSeqRight_4344_ = lean_ctor_get(v_toApplicative_4340_, 4);
v___f_4345_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4346_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4341_, 2);
v___f_4347_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4347_, 0, v_toFunctor_4341_);
v___f_4348_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4348_, 0, v_toFunctor_4341_);
v___x_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___f_4347_);
lean_ctor_set(v___x_4349_, 1, v___f_4348_);
lean_inc(v_toSeqRight_4344_);
v___f_4350_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4350_, 0, v_toSeqRight_4344_);
lean_inc(v_toSeqLeft_4343_);
v___f_4351_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4351_, 0, v_toSeqLeft_4343_);
lean_inc(v_toSeq_4342_);
v___f_4352_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4352_, 0, v_toSeq_4342_);
v___x_4353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4349_);
lean_ctor_set(v___x_4353_, 1, v___f_4345_);
lean_ctor_set(v___x_4353_, 2, v___f_4352_);
lean_ctor_set(v___x_4353_, 3, v___f_4351_);
lean_ctor_set(v___x_4353_, 4, v___f_4350_);
v___x_4354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4353_);
lean_ctor_set(v___x_4354_, 1, v___f_4346_);
v___x_4355_ = l_StateRefT_x27_instMonad___redArg(v___x_4354_);
v_toApplicative_4356_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4405_ == 0)
{
lean_object* v_unused_4406_; 
v_unused_4406_ = lean_ctor_get(v___x_4355_, 1);
lean_dec(v_unused_4406_);
v___x_4358_ = v___x_4355_;
v_isShared_4359_ = v_isSharedCheck_4405_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_toApplicative_4356_);
lean_dec(v___x_4355_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4405_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v_toFunctor_4360_; lean_object* v_toSeq_4361_; lean_object* v_toSeqLeft_4362_; lean_object* v_toSeqRight_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4403_; 
v_toFunctor_4360_ = lean_ctor_get(v_toApplicative_4356_, 0);
v_toSeq_4361_ = lean_ctor_get(v_toApplicative_4356_, 2);
v_toSeqLeft_4362_ = lean_ctor_get(v_toApplicative_4356_, 3);
v_toSeqRight_4363_ = lean_ctor_get(v_toApplicative_4356_, 4);
v_isSharedCheck_4403_ = !lean_is_exclusive(v_toApplicative_4356_);
if (v_isSharedCheck_4403_ == 0)
{
lean_object* v_unused_4404_; 
v_unused_4404_ = lean_ctor_get(v_toApplicative_4356_, 1);
lean_dec(v_unused_4404_);
v___x_4365_ = v_toApplicative_4356_;
v_isShared_4366_ = v_isSharedCheck_4403_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_toSeqRight_4363_);
lean_inc(v_toSeqLeft_4362_);
lean_inc(v_toSeq_4361_);
lean_inc(v_toFunctor_4360_);
lean_dec(v_toApplicative_4356_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4403_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___f_4367_; lean_object* v___f_4368_; lean_object* v___f_4369_; lean_object* v___f_4370_; lean_object* v___x_4371_; lean_object* v___f_4372_; lean_object* v___f_4373_; lean_object* v___f_4374_; lean_object* v___x_4376_; 
v___f_4367_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4368_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4360_);
v___f_4369_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4369_, 0, v_toFunctor_4360_);
v___f_4370_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4370_, 0, v_toFunctor_4360_);
v___x_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___f_4369_);
lean_ctor_set(v___x_4371_, 1, v___f_4370_);
v___f_4372_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4372_, 0, v_toSeqRight_4363_);
v___f_4373_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4373_, 0, v_toSeqLeft_4362_);
v___f_4374_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4374_, 0, v_toSeq_4361_);
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 4, v___f_4372_);
lean_ctor_set(v___x_4365_, 3, v___f_4373_);
lean_ctor_set(v___x_4365_, 2, v___f_4374_);
lean_ctor_set(v___x_4365_, 1, v___f_4367_);
lean_ctor_set(v___x_4365_, 0, v___x_4371_);
v___x_4376_ = v___x_4365_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4371_);
lean_ctor_set(v_reuseFailAlloc_4402_, 1, v___f_4367_);
lean_ctor_set(v_reuseFailAlloc_4402_, 2, v___f_4374_);
lean_ctor_set(v_reuseFailAlloc_4402_, 3, v___f_4373_);
lean_ctor_set(v_reuseFailAlloc_4402_, 4, v___f_4372_);
v___x_4376_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
lean_object* v___x_4378_; 
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 1, v___f_4368_);
lean_ctor_set(v___x_4358_, 0, v___x_4376_);
v___x_4378_ = v___x_4358_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4376_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v___f_4368_);
v___x_4378_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; uint8_t v___x_4381_; 
v___x_4379_ = lean_array_get_size(v_acc_4333_);
v___x_4380_ = lean_array_get_size(v_declInfos_4330_);
v___x_4381_ = lean_nat_dec_lt(v___x_4379_, v___x_4380_);
if (v___x_4381_ == 0)
{
lean_object* v___x_4382_; 
lean_dec_ref(v___x_4378_);
lean_dec_ref(v_declInfos_4330_);
lean_inc(v___y_4337_);
lean_inc_ref(v___y_4336_);
lean_inc(v___y_4335_);
lean_inc_ref(v___y_4334_);
v___x_4382_ = lean_apply_6(v_k_4331_, v_acc_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, lean_box(0));
return v___x_4382_;
}
else
{
lean_object* v___f_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; lean_object* v___f_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v_snd_4391_; lean_object* v_fst_4392_; lean_object* v_fst_4393_; lean_object* v_snd_4394_; lean_object* v___x_4395_; 
v___f_4383_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4383_, 0, v___x_4378_);
v___x_4384_ = lean_box(0);
v___x_4385_ = 0;
v___f_4386_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4386_, 0, v___f_4383_);
v___x_4387_ = lean_box(v___x_4385_);
v___x_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
lean_ctor_set(v___x_4388_, 1, v___f_4386_);
v___x_4389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4384_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = lean_array_get(v___x_4389_, v_declInfos_4330_, v___x_4379_);
lean_dec_ref(v___x_4389_);
v_snd_4391_ = lean_ctor_get(v___x_4390_, 1);
lean_inc(v_snd_4391_);
v_fst_4392_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_fst_4392_);
lean_dec(v___x_4390_);
v_fst_4393_ = lean_ctor_get(v_snd_4391_, 0);
lean_inc(v_fst_4393_);
v_snd_4394_ = lean_ctor_get(v_snd_4391_, 1);
lean_inc(v_snd_4394_);
lean_dec(v_snd_4391_);
lean_inc(v___y_4337_);
lean_inc_ref(v___y_4336_);
lean_inc(v___y_4335_);
lean_inc_ref(v___y_4334_);
lean_inc_ref(v_acc_4333_);
v___x_4395_ = lean_apply_6(v_snd_4394_, v_acc_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, lean_box(0));
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4397_; lean_object* v___f_4398_; uint8_t v___x_4399_; lean_object* v___x_4400_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref(v___x_4395_);
v___x_4397_ = lean_box(v_kind_4332_);
v___f_4398_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4398_, 0, v_acc_4333_);
lean_closure_set(v___f_4398_, 1, v_declInfos_4330_);
lean_closure_set(v___f_4398_, 2, v_k_4331_);
lean_closure_set(v___f_4398_, 3, v___x_4397_);
v___x_4399_ = lean_unbox(v_fst_4393_);
lean_dec(v_fst_4393_);
v___x_4400_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4392_, v___x_4399_, v_a_4396_, v___f_4398_, v_kind_4332_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
return v___x_4400_;
}
else
{
lean_dec(v_fst_4393_);
lean_dec(v_fst_4392_);
lean_dec_ref(v_acc_4333_);
lean_dec_ref(v_k_4331_);
lean_dec_ref(v_declInfos_4330_);
return v___x_4395_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4407_, lean_object* v_declInfos_4408_, lean_object* v_k_4409_, uint8_t v_kind_4410_, lean_object* v_x_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4417_ = lean_array_push(v_acc_4407_, v_x_4411_);
v___x_4418_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4408_, v_k_4409_, v_kind_4410_, v___x_4417_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4419_, lean_object* v_k_4420_, lean_object* v_kind_4421_, lean_object* v_acc_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
uint8_t v_kind_boxed_4428_; lean_object* v_res_4429_; 
v_kind_boxed_4428_ = lean_unbox(v_kind_4421_);
v_res_4429_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4419_, v_k_4420_, v_kind_boxed_4428_, v_acc_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4430_, lean_object* v_k_4431_, uint8_t v_kind_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
v___x_4438_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4439_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4430_, v_k_4431_, v_kind_4432_, v___x_4438_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4440_, lean_object* v_k_4441_, lean_object* v_kind_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
uint8_t v_kind_boxed_4448_; lean_object* v_res_4449_; 
v_kind_boxed_4448_ = lean_unbox(v_kind_4442_);
v_res_4449_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4440_, v_k_4441_, v_kind_boxed_4448_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4450_, lean_object* v_k_4451_, uint8_t v_kind_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
size_t v_sz_4458_; size_t v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v_sz_4458_ = lean_array_size(v_declInfos_4450_);
v___x_4459_ = ((size_t)0ULL);
v___x_4460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4458_, v___x_4459_, v_declInfos_4450_);
v___x_4461_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4460_, v_k_4451_, v_kind_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
return v___x_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4462_, lean_object* v_k_4463_, lean_object* v_kind_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
uint8_t v_kind_boxed_4470_; lean_object* v_res_4471_; 
v_kind_boxed_4470_ = lean_unbox(v_kind_4464_);
v_res_4471_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4462_, v_k_4463_, v_kind_boxed_4470_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4472_, lean_object* v_k_4473_, uint8_t v_kind_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
size_t v_sz_4480_; size_t v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v_sz_4480_ = lean_array_size(v_declInfos_4472_);
v___x_4481_ = ((size_t)0ULL);
v___x_4482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4480_, v___x_4481_, v_declInfos_4472_);
v___x_4483_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4482_, v_k_4473_, v_kind_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
return v___x_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4484_, lean_object* v_k_4485_, lean_object* v_kind_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
uint8_t v_kind_boxed_4492_; lean_object* v_res_4493_; 
v_kind_boxed_4492_ = lean_unbox(v_kind_4486_);
v_res_4493_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4484_, v_k_4485_, v_kind_boxed_4492_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(lean_object* v_a_4497_, lean_object* v_b_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_array_4504_; lean_object* v_start_4505_; lean_object* v_stop_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4564_; 
v_array_4504_ = lean_ctor_get(v_a_4497_, 0);
v_start_4505_ = lean_ctor_get(v_a_4497_, 1);
v_stop_4506_ = lean_ctor_get(v_a_4497_, 2);
v_isSharedCheck_4564_ = !lean_is_exclusive(v_a_4497_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4508_ = v_a_4497_;
v_isShared_4509_ = v_isSharedCheck_4564_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_stop_4506_);
lean_inc(v_start_4505_);
lean_inc(v_array_4504_);
lean_dec(v_a_4497_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4564_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
uint8_t v___x_4510_; 
v___x_4510_ = lean_nat_dec_lt(v_start_4505_, v_stop_4506_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; 
lean_del_object(v___x_4508_);
lean_dec(v_stop_4506_);
lean_dec(v_start_4505_);
lean_dec_ref(v_array_4504_);
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v_b_4498_);
return v___x_4511_;
}
else
{
lean_object* v_snd_4512_; lean_object* v_fst_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4563_; 
v_snd_4512_ = lean_ctor_get(v_b_4498_, 1);
v_fst_4513_ = lean_ctor_get(v_b_4498_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v_b_4498_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4515_ = v_b_4498_;
v_isShared_4516_ = v_isSharedCheck_4563_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_snd_4512_);
lean_inc(v_fst_4513_);
lean_dec(v_b_4498_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4563_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v_array_4517_; lean_object* v_start_4518_; lean_object* v_stop_4519_; uint8_t v___x_4520_; 
v_array_4517_ = lean_ctor_get(v_snd_4512_, 0);
v_start_4518_ = lean_ctor_get(v_snd_4512_, 1);
v_stop_4519_ = lean_ctor_get(v_snd_4512_, 2);
v___x_4520_ = lean_nat_dec_lt(v_start_4518_, v_stop_4519_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4522_; 
lean_del_object(v___x_4508_);
lean_dec(v_stop_4506_);
lean_dec(v_start_4505_);
lean_dec_ref(v_array_4504_);
if (v_isShared_4516_ == 0)
{
v___x_4522_ = v___x_4515_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_fst_4513_);
lean_ctor_set(v_reuseFailAlloc_4524_, 1, v_snd_4512_);
v___x_4522_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4523_; 
v___x_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
return v___x_4523_;
}
}
else
{
lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4559_; 
lean_inc(v_stop_4519_);
lean_inc(v_start_4518_);
lean_inc_ref(v_array_4517_);
v_isSharedCheck_4559_ = !lean_is_exclusive(v_snd_4512_);
if (v_isSharedCheck_4559_ == 0)
{
lean_object* v_unused_4560_; lean_object* v_unused_4561_; lean_object* v_unused_4562_; 
v_unused_4560_ = lean_ctor_get(v_snd_4512_, 2);
lean_dec(v_unused_4560_);
v_unused_4561_ = lean_ctor_get(v_snd_4512_, 1);
lean_dec(v_unused_4561_);
v_unused_4562_ = lean_ctor_get(v_snd_4512_, 0);
lean_dec(v_unused_4562_);
v___x_4526_ = v_snd_4512_;
v_isShared_4527_ = v_isSharedCheck_4559_;
goto v_resetjp_4525_;
}
else
{
lean_dec(v_snd_4512_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4559_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4528_ = lean_array_fget_borrowed(v_array_4504_, v_start_4505_);
v___x_4529_ = lean_array_fget_borrowed(v_array_4517_, v_start_4518_);
lean_inc(v___x_4529_);
lean_inc(v___x_4528_);
v___x_4530_ = l_Lean_Meta_mkEqHEq(v___x_4528_, v___x_4529_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v_a_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4535_; 
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
lean_inc(v_a_4531_);
lean_dec_ref(v___x_4530_);
v___x_4532_ = lean_unsigned_to_nat(1u);
v___x_4533_ = lean_nat_add(v_start_4505_, v___x_4532_);
lean_dec(v_start_4505_);
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 2, v_stop_4506_);
lean_ctor_set(v___x_4526_, 1, v___x_4533_);
lean_ctor_set(v___x_4526_, 0, v_array_4504_);
v___x_4535_ = v___x_4526_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_array_4504_);
lean_ctor_set(v_reuseFailAlloc_4550_, 1, v___x_4533_);
lean_ctor_set(v_reuseFailAlloc_4550_, 2, v_stop_4506_);
v___x_4535_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
lean_object* v___x_4536_; lean_object* v___x_4538_; 
v___x_4536_ = lean_nat_add(v_start_4518_, v___x_4532_);
lean_dec(v_start_4518_);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 2, v_stop_4519_);
lean_ctor_set(v___x_4508_, 1, v___x_4536_);
lean_ctor_set(v___x_4508_, 0, v_array_4517_);
v___x_4538_ = v___x_4508_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_array_4517_);
lean_ctor_set(v_reuseFailAlloc_4549_, 1, v___x_4536_);
lean_ctor_set(v_reuseFailAlloc_4549_, 2, v_stop_4519_);
v___x_4538_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4544_; 
v___x_4539_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__1));
v___x_4540_ = lean_array_get_size(v_fst_4513_);
v___x_4541_ = lean_nat_add(v___x_4540_, v___x_4532_);
v___x_4542_ = lean_name_append_index_after(v___x_4539_, v___x_4541_);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 1, v_a_4531_);
lean_ctor_set(v___x_4515_, 0, v___x_4542_);
v___x_4544_ = v___x_4515_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4542_);
lean_ctor_set(v_reuseFailAlloc_4548_, 1, v_a_4531_);
v___x_4544_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4545_ = lean_array_push(v_fst_4513_, v___x_4544_);
v___x_4546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
lean_ctor_set(v___x_4546_, 1, v___x_4538_);
v_a_4497_ = v___x_4535_;
v_b_4498_ = v___x_4546_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_del_object(v___x_4526_);
lean_dec(v_stop_4519_);
lean_dec(v_start_4518_);
lean_dec_ref(v_array_4517_);
lean_del_object(v___x_4515_);
lean_dec(v_fst_4513_);
lean_del_object(v___x_4508_);
lean_dec(v_stop_4506_);
lean_dec(v_start_4505_);
lean_dec_ref(v_array_4504_);
v_a_4551_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4530_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4530_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___boxed(lean_object* v_a_4565_, lean_object* v_b_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_4565_, v_b_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v___x_4573_, lean_object* v_a_4574_, lean_object* v___x_4575_, lean_object* v_as_4576_, size_t v_sz_4577_, size_t v_i_4578_, lean_object* v_b_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_){
_start:
{
uint8_t v___x_4585_; 
v___x_4585_ = lean_usize_dec_lt(v_i_4578_, v_sz_4577_);
if (v___x_4585_ == 0)
{
lean_object* v___x_4586_; 
lean_dec(v___x_4575_);
v___x_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4586_, 0, v_b_4579_);
return v___x_4586_;
}
else
{
lean_object* v___x_4587_; lean_object* v_a_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4587_ = l_Lean_instInhabitedExpr;
v_a_4588_ = lean_array_uget_borrowed(v_as_4576_, v_i_4578_);
v___x_4589_ = lean_array_get_borrowed(v___x_4587_, v___x_4573_, v_a_4588_);
lean_inc(v___x_4589_);
v___x_4590_ = l_Lean_Meta_instantiateForall(v___x_4589_, v_a_4574_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v___x_4592_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc(v_a_4591_);
lean_dec_ref(v___x_4590_);
lean_inc(v___x_4575_);
v___x_4592_ = l_Lean_Meta_Match_simpH_x3f(v_a_4591_, v___x_4575_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; lean_object* v_a_4595_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref(v___x_4592_);
if (lean_obj_tag(v_a_4593_) == 1)
{
lean_object* v_val_4599_; lean_object* v___x_4600_; 
v_val_4599_ = lean_ctor_get(v_a_4593_, 0);
lean_inc(v_val_4599_);
lean_dec_ref(v_a_4593_);
v___x_4600_ = lean_array_push(v_b_4579_, v_val_4599_);
v_a_4595_ = v___x_4600_;
goto v___jp_4594_;
}
else
{
lean_dec(v_a_4593_);
v_a_4595_ = v_b_4579_;
goto v___jp_4594_;
}
v___jp_4594_:
{
size_t v___x_4596_; size_t v___x_4597_; 
v___x_4596_ = ((size_t)1ULL);
v___x_4597_ = lean_usize_add(v_i_4578_, v___x_4596_);
v_i_4578_ = v___x_4597_;
v_b_4579_ = v_a_4595_;
goto _start;
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec_ref(v_b_4579_);
lean_dec(v___x_4575_);
v_a_4601_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4592_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4592_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
else
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4616_; 
lean_dec_ref(v_b_4579_);
lean_dec(v___x_4575_);
v_a_4609_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4611_ = v___x_4590_;
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4590_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4614_; 
if (v_isShared_4612_ == 0)
{
v___x_4614_ = v___x_4611_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_a_4609_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v___x_4617_, lean_object* v_a_4618_, lean_object* v___x_4619_, lean_object* v_as_4620_, lean_object* v_sz_4621_, lean_object* v_i_4622_, lean_object* v_b_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
size_t v_sz_boxed_4629_; size_t v_i_boxed_4630_; lean_object* v_res_4631_; 
v_sz_boxed_4629_ = lean_unbox_usize(v_sz_4621_);
lean_dec(v_sz_4621_);
v_i_boxed_4630_ = lean_unbox_usize(v_i_4622_);
lean_dec(v_i_4622_);
v_res_4631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v___x_4617_, v_a_4618_, v___x_4619_, v_as_4620_, v_sz_boxed_4629_, v_i_boxed_4630_, v_b_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec_ref(v_as_4620_);
lean_dec_ref(v_a_4618_);
lean_dec_ref(v___x_4617_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4632_, lean_object* v_args_4633_, lean_object* v___x_4634_, lean_object* v_overlaps_4635_, lean_object* v_a_4636_, lean_object* v_fst_4637_, lean_object* v_a_4638_, lean_object* v___x_4639_, lean_object* v___x_4640_, lean_object* v___x_4641_, lean_object* v___x_4642_, lean_object* v_altVars_4643_, uint8_t v___x_4644_, uint8_t v___x_4645_, lean_object* v_a_4646_, lean_object* v___x_4647_, lean_object* v___x_4648_, lean_object* v___x_4649_, lean_object* v___x_4650_, lean_object* v___x_4651_, lean_object* v___x_4652_, lean_object* v___x_4653_, lean_object* v_matchDeclName_4654_, lean_object* v___x_4655_, lean_object* v___x_4656_, lean_object* v___x_4657_, lean_object* v_heqs_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4664_ = l_Lean_mkAppN(v___y_4632_, v_args_4633_);
lean_inc_ref(v_heqs_4658_);
v___x_4665_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4664_, v_heqs_4658_, v___x_4634_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4667_; size_t v_sz_4668_; size_t v___x_4669_; lean_object* v___x_4670_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref(v___x_4665_);
v___x_4667_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4635_, v_a_4636_);
v_sz_4668_ = lean_array_size(v___x_4667_);
v___x_4669_ = ((size_t)0ULL);
lean_inc_ref(v___x_4640_);
v___x_4670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_fst_4637_, v_a_4638_, v___x_4639_, v___x_4667_, v_sz_4668_, v___x_4669_, v___x_4640_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
lean_dec_ref(v___x_4667_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4675_; lean_object* v___y_4676_; lean_object* v_options_4783_; uint8_t v_hasTrace_4784_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref(v___x_4670_);
v_options_4783_ = lean_ctor_get(v___y_4661_, 2);
v_hasTrace_4784_ = lean_ctor_get_uint8(v_options_4783_, sizeof(void*)*1);
if (v_hasTrace_4784_ == 0)
{
v___y_4673_ = v___y_4659_;
v___y_4674_ = v___y_4660_;
v___y_4675_ = v___y_4661_;
v___y_4676_ = v___y_4662_;
goto v___jp_4672_;
}
else
{
lean_object* v_inheritedTraceOptions_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v_inheritedTraceOptions_4785_ = lean_ctor_get(v___y_4661_, 13);
v___x_4786_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4787_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4788_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4785_, v_options_4783_, v___x_4787_);
if (v___x_4788_ == 0)
{
v___y_4673_ = v___y_4659_;
v___y_4674_ = v___y_4660_;
v___y_4675_ = v___y_4661_;
v___y_4676_ = v___y_4662_;
goto v___jp_4672_;
}
else
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4789_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4671_);
v___x_4790_ = lean_array_to_list(v_a_4671_);
v___x_4791_ = lean_box(0);
v___x_4792_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4790_, v___x_4791_);
v___x_4793_ = l_Lean_MessageData_ofList(v___x_4792_);
v___x_4794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4789_);
lean_ctor_set(v___x_4794_, 1, v___x_4793_);
v___x_4795_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4786_, v___x_4794_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_dec_ref(v___x_4795_);
v___y_4673_ = v___y_4659_;
v___y_4674_ = v___y_4660_;
v___y_4675_ = v___y_4661_;
v___y_4676_ = v___y_4662_;
goto v___jp_4672_;
}
else
{
lean_object* v_a_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4803_; 
lean_dec(v_a_4671_);
lean_dec(v_a_4666_);
lean_dec_ref(v_heqs_4658_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
lean_dec(v_matchDeclName_4654_);
lean_dec_ref(v___x_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4648_);
lean_dec(v___x_4647_);
lean_dec_ref(v___x_4642_);
lean_dec(v___x_4641_);
lean_dec_ref(v___x_4640_);
lean_dec_ref(v_a_4638_);
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4798_ = v___x_4795_;
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_a_4796_);
lean_dec(v___x_4795_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4801_; 
if (v_isShared_4799_ == 0)
{
v___x_4801_ = v___x_4798_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_a_4796_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
}
v___jp_4672_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; size_t v_sz_4684_; lean_object* v___x_4685_; 
v___x_4677_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4678_ = l_Array_reverse___redArg(v_a_4638_);
v___x_4679_ = lean_array_get_size(v___x_4678_);
v___x_4680_ = l_Array_toSubarray___redArg(v___x_4678_, v___x_4641_, v___x_4679_);
lean_inc_ref(v___x_4642_);
v___x_4681_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4642_, v___x_4640_);
v___x_4682_ = l_Array_reverse___redArg(v___x_4681_);
v___x_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4677_);
lean_ctor_set(v___x_4683_, 1, v___x_4680_);
v_sz_4684_ = lean_array_size(v___x_4682_);
v___x_4685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4682_, v_sz_4684_, v___x_4669_, v___x_4683_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
lean_dec_ref(v___x_4682_);
if (lean_obj_tag(v___x_4685_) == 0)
{
lean_object* v_a_4686_; lean_object* v_fst_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4773_; 
v_a_4686_ = lean_ctor_get(v___x_4685_, 0);
lean_inc(v_a_4686_);
lean_dec_ref(v___x_4685_);
v_fst_4687_ = lean_ctor_get(v_a_4686_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v_a_4686_);
if (v_isSharedCheck_4773_ == 0)
{
lean_object* v_unused_4774_; 
v_unused_4774_ = lean_ctor_get(v_a_4686_, 1);
lean_dec(v_unused_4774_);
v___x_4689_ = v_a_4686_;
v_isShared_4690_ = v_isSharedCheck_4773_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_fst_4687_);
lean_dec(v_a_4686_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4773_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; uint8_t v___x_4693_; lean_object* v___x_4694_; 
v___x_4691_ = l_Subarray_copy___redArg(v___x_4642_);
lean_inc_ref(v___x_4691_);
v___x_4692_ = l_Array_append___redArg(v___x_4691_, v_altVars_4643_);
v___x_4693_ = 1;
v___x_4694_ = l_Lean_Meta_mkForallFVars(v___x_4692_, v_fst_4687_, v___x_4644_, v___x_4645_, v___x_4645_, v___x_4693_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
lean_dec_ref(v___x_4692_);
if (lean_obj_tag(v___x_4694_) == 0)
{
lean_object* v_a_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v_a_4695_ = lean_ctor_get(v___x_4694_, 0);
lean_inc(v_a_4695_);
lean_dec_ref(v___x_4694_);
v___x_4696_ = l_Lean_ConstantInfo_name(v_a_4646_);
v___x_4697_ = l_Lean_mkConst(v___x_4696_, v___x_4647_);
lean_inc_ref(v___x_4648_);
v___x_4698_ = l_Subarray_copy___redArg(v___x_4648_);
v___x_4699_ = lean_mk_empty_array_with_capacity(v___x_4649_);
v___x_4700_ = lean_array_push(v___x_4699_, v___x_4650_);
v___x_4701_ = l_Array_append___redArg(v___x_4698_, v___x_4700_);
lean_dec_ref(v___x_4700_);
v___x_4702_ = l_Array_append___redArg(v___x_4701_, v___x_4691_);
lean_dec_ref(v___x_4691_);
v___x_4703_ = l_Subarray_copy___redArg(v___x_4651_);
v___x_4704_ = l_Array_append___redArg(v___x_4702_, v___x_4703_);
lean_dec_ref(v___x_4703_);
v___x_4705_ = l_Lean_mkAppN(v___x_4697_, v___x_4704_);
v___x_4706_ = l_Lean_Meta_mkHEq(v___x_4705_, v_a_4666_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4708_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
lean_inc(v_a_4707_);
lean_dec_ref(v___x_4706_);
v___x_4708_ = l_Lean_mkArrowN(v_a_4671_, v_a_4707_, v___y_4675_, v___y_4676_);
lean_dec(v_a_4671_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4709_);
lean_dec_ref(v___x_4708_);
v___x_4710_ = l_Array_append___redArg(v___x_4704_, v_altVars_4643_);
v___x_4711_ = l_Array_append___redArg(v___x_4710_, v_heqs_4658_);
v___x_4712_ = l_Lean_Meta_mkForallFVars(v___x_4711_, v_a_4709_, v___x_4644_, v___x_4645_, v___x_4645_, v___x_4693_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
lean_dec_ref(v___x_4711_);
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_a_4713_; lean_object* v___x_4714_; 
v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
lean_inc(v_a_4713_);
lean_dec_ref(v___x_4712_);
v___x_4714_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4713_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4772_; 
v_a_4715_ = lean_ctor_get(v___x_4714_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4717_ = v___x_4714_;
v_isShared_4718_ = v_isSharedCheck_4772_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v___x_4714_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4772_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v_start_4719_; lean_object* v_stop_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4770_; 
v_start_4719_ = lean_ctor_get(v___x_4648_, 1);
v_stop_4720_ = lean_ctor_get(v___x_4648_, 2);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4648_);
if (v_isSharedCheck_4770_ == 0)
{
lean_object* v_unused_4771_; 
v_unused_4771_ = lean_ctor_get(v___x_4648_, 0);
lean_dec(v_unused_4771_);
v___x_4722_ = v___x_4648_;
v_isShared_4723_ = v_isSharedCheck_4770_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_stop_4720_);
lean_inc(v_start_4719_);
lean_dec(v___x_4648_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4770_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4724_ = lean_nat_sub(v_stop_4720_, v_start_4719_);
lean_dec(v_start_4719_);
lean_dec(v_stop_4720_);
v___x_4725_ = lean_nat_add(v___x_4724_, v___x_4649_);
lean_dec(v___x_4724_);
v___x_4726_ = lean_nat_add(v___x_4725_, v___x_4652_);
lean_dec(v___x_4725_);
v___x_4727_ = lean_nat_add(v___x_4726_, v___x_4653_);
lean_dec(v___x_4726_);
v___x_4728_ = lean_array_get_size(v_altVars_4643_);
v___x_4729_ = lean_nat_add(v___x_4727_, v___x_4728_);
lean_dec(v___x_4727_);
v___x_4730_ = lean_array_get_size(v_heqs_4658_);
lean_dec_ref(v_heqs_4658_);
lean_inc(v_a_4715_);
v___x_4731_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4654_, v_a_4715_, v___x_4729_, v___x_4730_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4769_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4734_ = v___x_4731_;
v_isShared_4735_ = v_isSharedCheck_4769_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4731_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4769_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4736_; lean_object* v_env_4737_; uint8_t v___x_4738_; 
v___x_4736_ = lean_st_ref_get(v___y_4676_);
v_env_4737_ = lean_ctor_get(v___x_4736_, 0);
lean_inc_ref(v_env_4737_);
lean_dec(v___x_4736_);
lean_inc(v___x_4655_);
v___x_4738_ = l_Lean_Environment_contains(v_env_4737_, v___x_4655_, v___x_4645_);
if (v___x_4738_ == 0)
{
lean_object* v___x_4740_; 
lean_del_object(v___x_4734_);
lean_inc(v___x_4655_);
if (v_isShared_4723_ == 0)
{
lean_ctor_set(v___x_4722_, 2, v_a_4715_);
lean_ctor_set(v___x_4722_, 1, v___x_4656_);
lean_ctor_set(v___x_4722_, 0, v___x_4655_);
v___x_4740_ = v___x_4722_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4765_, 1, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4765_, 2, v_a_4715_);
v___x_4740_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
lean_object* v___x_4742_; 
if (v_isShared_4690_ == 0)
{
lean_ctor_set_tag(v___x_4689_, 1);
lean_ctor_set(v___x_4689_, 1, v___x_4657_);
lean_ctor_set(v___x_4689_, 0, v___x_4655_);
v___x_4742_ = v___x_4689_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4764_, 1, v___x_4657_);
v___x_4742_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
lean_object* v___x_4743_; lean_object* v___x_4745_; 
v___x_4743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4740_);
lean_ctor_set(v___x_4743_, 1, v_a_4732_);
lean_ctor_set(v___x_4743_, 2, v___x_4742_);
if (v_isShared_4718_ == 0)
{
lean_ctor_set_tag(v___x_4717_, 2);
lean_ctor_set(v___x_4717_, 0, v___x_4743_);
v___x_4745_ = v___x_4717_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v___x_4743_);
v___x_4745_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
lean_object* v___x_4746_; 
v___x_4746_ = l_Lean_addDecl(v___x_4745_, v___x_4644_, v___y_4675_, v___y_4676_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; 
v_unused_4754_ = lean_ctor_get(v___x_4746_, 0);
lean_dec(v_unused_4754_);
v___x_4748_ = v___x_4746_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_dec(v___x_4746_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
lean_ctor_set(v___x_4748_, 0, v_a_4695_);
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4695_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
lean_dec(v_a_4695_);
v_a_4755_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4746_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4746_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4767_; 
lean_dec(v_a_4732_);
lean_del_object(v___x_4722_);
lean_del_object(v___x_4717_);
lean_dec(v_a_4715_);
lean_del_object(v___x_4689_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 0, v_a_4695_);
v___x_4767_ = v___x_4734_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4695_);
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
lean_del_object(v___x_4722_);
lean_del_object(v___x_4717_);
lean_dec(v_a_4715_);
lean_dec(v_a_4695_);
lean_del_object(v___x_4689_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
return v___x_4731_;
}
}
}
}
else
{
lean_dec(v_a_4695_);
lean_del_object(v___x_4689_);
lean_dec_ref(v_heqs_4658_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
lean_dec(v_matchDeclName_4654_);
lean_dec_ref(v___x_4648_);
return v___x_4714_;
}
}
else
{
lean_dec(v_a_4695_);
lean_del_object(v___x_4689_);
lean_dec_ref(v_heqs_4658_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
lean_dec(v_matchDeclName_4654_);
lean_dec_ref(v___x_4648_);
return v___x_4712_;
}
}
else
{
lean_dec_ref(v___x_4704_);
lean_dec(v_a_4695_);
lean_del_object(v___x_4689_);
lean_dec_ref(v_heqs_4658_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
lean_dec(v_matchDeclName_4654_);
lean_dec_ref(v___x_4648_);
return v___x_4708_;
}
}
else
{
lean_dec_ref(v___x_4704_);
lean_dec(v_a_4695_);
lean_del_object(v___x_4689_);
lean_dec(v_a_4671_);
lean_dec_ref(v_heqs_4658_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
lean_dec(v_matchDeclName_4654_);
lean_dec_ref(v___x_4648_);
return v___x_4706_;
}
}
else
{
lean_dec_ref(v___x_4691_);
lean_del_object(v___x_4689_);
lean_dec(v_a_4671_);
lean_dec(v_a_4666_);
lean_dec_ref(v_heqs_4658_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
lean_dec(v_matchDeclName_4654_);
lean_dec_ref(v___x_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4648_);
lean_dec(v___x_4647_);
return v___x_4694_;
}
}
}
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4782_; 
lean_dec(v_a_4671_);
lean_dec(v_a_4666_);
lean_dec_ref(v_heqs_4658_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
lean_dec(v_matchDeclName_4654_);
lean_dec_ref(v___x_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4648_);
lean_dec(v___x_4647_);
lean_dec_ref(v___x_4642_);
v_a_4775_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4777_ = v___x_4685_;
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v___x_4685_);
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
}
else
{
lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4811_; 
lean_dec(v_a_4666_);
lean_dec_ref(v_heqs_4658_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
lean_dec(v_matchDeclName_4654_);
lean_dec_ref(v___x_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4648_);
lean_dec(v___x_4647_);
lean_dec_ref(v___x_4642_);
lean_dec(v___x_4641_);
lean_dec_ref(v___x_4640_);
lean_dec_ref(v_a_4638_);
v_a_4804_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4806_ = v___x_4670_;
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v___x_4670_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4809_; 
if (v_isShared_4807_ == 0)
{
v___x_4809_ = v___x_4806_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_a_4804_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4658_);
lean_dec(v___x_4657_);
lean_dec(v___x_4656_);
lean_dec(v___x_4655_);
lean_dec(v_matchDeclName_4654_);
lean_dec_ref(v___x_4651_);
lean_dec_ref(v___x_4650_);
lean_dec_ref(v___x_4648_);
lean_dec(v___x_4647_);
lean_dec_ref(v___x_4642_);
lean_dec(v___x_4641_);
lean_dec_ref(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec_ref(v_a_4638_);
return v___x_4665_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4812_ = _args[0];
lean_object* v_args_4813_ = _args[1];
lean_object* v___x_4814_ = _args[2];
lean_object* v_overlaps_4815_ = _args[3];
lean_object* v_a_4816_ = _args[4];
lean_object* v_fst_4817_ = _args[5];
lean_object* v_a_4818_ = _args[6];
lean_object* v___x_4819_ = _args[7];
lean_object* v___x_4820_ = _args[8];
lean_object* v___x_4821_ = _args[9];
lean_object* v___x_4822_ = _args[10];
lean_object* v_altVars_4823_ = _args[11];
lean_object* v___x_4824_ = _args[12];
lean_object* v___x_4825_ = _args[13];
lean_object* v_a_4826_ = _args[14];
lean_object* v___x_4827_ = _args[15];
lean_object* v___x_4828_ = _args[16];
lean_object* v___x_4829_ = _args[17];
lean_object* v___x_4830_ = _args[18];
lean_object* v___x_4831_ = _args[19];
lean_object* v___x_4832_ = _args[20];
lean_object* v___x_4833_ = _args[21];
lean_object* v_matchDeclName_4834_ = _args[22];
lean_object* v___x_4835_ = _args[23];
lean_object* v___x_4836_ = _args[24];
lean_object* v___x_4837_ = _args[25];
lean_object* v_heqs_4838_ = _args[26];
lean_object* v___y_4839_ = _args[27];
lean_object* v___y_4840_ = _args[28];
lean_object* v___y_4841_ = _args[29];
lean_object* v___y_4842_ = _args[30];
lean_object* v___y_4843_ = _args[31];
_start:
{
uint8_t v___x_22593__boxed_4844_; uint8_t v___x_22594__boxed_4845_; lean_object* v_res_4846_; 
v___x_22593__boxed_4844_ = lean_unbox(v___x_4824_);
v___x_22594__boxed_4845_ = lean_unbox(v___x_4825_);
v_res_4846_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4812_, v_args_4813_, v___x_4814_, v_overlaps_4815_, v_a_4816_, v_fst_4817_, v_a_4818_, v___x_4819_, v___x_4820_, v___x_4821_, v___x_4822_, v_altVars_4823_, v___x_22593__boxed_4844_, v___x_22594__boxed_4845_, v_a_4826_, v___x_4827_, v___x_4828_, v___x_4829_, v___x_4830_, v___x_4831_, v___x_4832_, v___x_4833_, v_matchDeclName_4834_, v___x_4835_, v___x_4836_, v___x_4837_, v_heqs_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
lean_dec(v___y_4842_);
lean_dec_ref(v___y_4841_);
lean_dec(v___y_4840_);
lean_dec_ref(v___y_4839_);
lean_dec(v___x_4833_);
lean_dec(v___x_4832_);
lean_dec(v___x_4829_);
lean_dec_ref(v_a_4826_);
lean_dec_ref(v_altVars_4823_);
lean_dec(v_fst_4817_);
lean_dec(v_a_4816_);
lean_dec_ref(v_overlaps_4815_);
lean_dec_ref(v_args_4813_);
return v_res_4846_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
v___x_4849_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4850_ = lean_unsigned_to_nat(8u);
v___x_4851_ = lean_unsigned_to_nat(295u);
v___x_4852_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4853_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4854_ = l_mkPanicMessageWithDecl(v___x_4853_, v___x_4852_, v___x_4851_, v___x_4850_, v___x_4849_);
return v___x_4854_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4855_, lean_object* v___x_4856_, lean_object* v___x_4857_, lean_object* v___y_4858_, lean_object* v___x_4859_, lean_object* v_overlaps_4860_, lean_object* v_a_4861_, lean_object* v_fst_4862_, lean_object* v___x_4863_, lean_object* v_a_4864_, lean_object* v___x_4865_, lean_object* v___x_4866_, lean_object* v___x_4867_, lean_object* v___x_4868_, lean_object* v___x_4869_, lean_object* v___x_4870_, lean_object* v_matchDeclName_4871_, lean_object* v___x_4872_, lean_object* v___x_4873_, lean_object* v___x_4874_, lean_object* v_altVars_4875_, lean_object* v_args_4876_, lean_object* v___mask_4877_, lean_object* v_altResultType_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
uint8_t v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = 0;
v___x_4885_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4878_, v___f_4855_, v___x_4884_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v_start_4887_; lean_object* v_stop_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; uint8_t v___x_4891_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_a_4886_);
lean_dec_ref(v___x_4885_);
v_start_4887_ = lean_ctor_get(v___x_4856_, 1);
v_stop_4888_ = lean_ctor_get(v___x_4856_, 2);
v___x_4889_ = lean_array_get_size(v_a_4886_);
v___x_4890_ = lean_nat_sub(v_stop_4888_, v_start_4887_);
v___x_4891_ = lean_nat_dec_eq(v___x_4889_, v___x_4890_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; lean_object* v___x_4893_; 
lean_dec(v___x_4890_);
lean_dec(v_a_4886_);
lean_dec_ref(v_args_4876_);
lean_dec_ref(v_altVars_4875_);
lean_dec(v___x_4874_);
lean_dec(v___x_4873_);
lean_dec(v___x_4872_);
lean_dec(v_matchDeclName_4871_);
lean_dec(v___x_4870_);
lean_dec_ref(v___x_4869_);
lean_dec_ref(v___x_4868_);
lean_dec(v___x_4867_);
lean_dec_ref(v___x_4866_);
lean_dec(v___x_4865_);
lean_dec_ref(v_a_4864_);
lean_dec_ref(v___x_4863_);
lean_dec(v_fst_4862_);
lean_dec(v_a_4861_);
lean_dec_ref(v_overlaps_4860_);
lean_dec(v___x_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___x_4857_);
lean_dec_ref(v___x_4856_);
v___x_4892_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4893_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4892_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
return v___x_4893_;
}
else
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4894_ = lean_mk_empty_array_with_capacity(v___x_4857_);
lean_inc(v___x_4857_);
lean_inc(v_a_4886_);
v___x_4895_ = l_Array_toSubarray___redArg(v_a_4886_, v___x_4857_, v___x_4889_);
v___x_4896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4894_);
lean_ctor_set(v___x_4896_, 1, v___x_4895_);
lean_inc_ref(v___x_4856_);
v___x_4897_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v___x_4856_, v___x_4896_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; lean_object* v_fst_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___f_4902_; uint8_t v___x_4903_; lean_object* v___x_4904_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4898_);
lean_dec_ref(v___x_4897_);
v_fst_4899_ = lean_ctor_get(v_a_4898_, 0);
lean_inc(v_fst_4899_);
lean_dec(v_a_4898_);
v___x_4900_ = lean_box(v___x_4884_);
v___x_4901_ = lean_box(v___x_4891_);
v___f_4902_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4902_, 0, v___y_4858_);
lean_closure_set(v___f_4902_, 1, v_args_4876_);
lean_closure_set(v___f_4902_, 2, v___x_4859_);
lean_closure_set(v___f_4902_, 3, v_overlaps_4860_);
lean_closure_set(v___f_4902_, 4, v_a_4861_);
lean_closure_set(v___f_4902_, 5, v_fst_4862_);
lean_closure_set(v___f_4902_, 6, v_a_4886_);
lean_closure_set(v___f_4902_, 7, v___x_4889_);
lean_closure_set(v___f_4902_, 8, v___x_4863_);
lean_closure_set(v___f_4902_, 9, v___x_4857_);
lean_closure_set(v___f_4902_, 10, v___x_4856_);
lean_closure_set(v___f_4902_, 11, v_altVars_4875_);
lean_closure_set(v___f_4902_, 12, v___x_4900_);
lean_closure_set(v___f_4902_, 13, v___x_4901_);
lean_closure_set(v___f_4902_, 14, v_a_4864_);
lean_closure_set(v___f_4902_, 15, v___x_4865_);
lean_closure_set(v___f_4902_, 16, v___x_4866_);
lean_closure_set(v___f_4902_, 17, v___x_4867_);
lean_closure_set(v___f_4902_, 18, v___x_4868_);
lean_closure_set(v___f_4902_, 19, v___x_4869_);
lean_closure_set(v___f_4902_, 20, v___x_4890_);
lean_closure_set(v___f_4902_, 21, v___x_4870_);
lean_closure_set(v___f_4902_, 22, v_matchDeclName_4871_);
lean_closure_set(v___f_4902_, 23, v___x_4872_);
lean_closure_set(v___f_4902_, 24, v___x_4873_);
lean_closure_set(v___f_4902_, 25, v___x_4874_);
v___x_4903_ = 0;
v___x_4904_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4899_, v___f_4902_, v___x_4903_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
return v___x_4904_;
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
lean_dec(v___x_4890_);
lean_dec(v_a_4886_);
lean_dec_ref(v_args_4876_);
lean_dec_ref(v_altVars_4875_);
lean_dec(v___x_4874_);
lean_dec(v___x_4873_);
lean_dec(v___x_4872_);
lean_dec(v_matchDeclName_4871_);
lean_dec(v___x_4870_);
lean_dec_ref(v___x_4869_);
lean_dec_ref(v___x_4868_);
lean_dec(v___x_4867_);
lean_dec_ref(v___x_4866_);
lean_dec(v___x_4865_);
lean_dec_ref(v_a_4864_);
lean_dec_ref(v___x_4863_);
lean_dec(v_fst_4862_);
lean_dec(v_a_4861_);
lean_dec_ref(v_overlaps_4860_);
lean_dec(v___x_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___x_4857_);
lean_dec_ref(v___x_4856_);
v_a_4905_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4897_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4897_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
else
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
lean_dec_ref(v_args_4876_);
lean_dec_ref(v_altVars_4875_);
lean_dec(v___x_4874_);
lean_dec(v___x_4873_);
lean_dec(v___x_4872_);
lean_dec(v_matchDeclName_4871_);
lean_dec(v___x_4870_);
lean_dec_ref(v___x_4869_);
lean_dec_ref(v___x_4868_);
lean_dec(v___x_4867_);
lean_dec_ref(v___x_4866_);
lean_dec(v___x_4865_);
lean_dec_ref(v_a_4864_);
lean_dec_ref(v___x_4863_);
lean_dec(v_fst_4862_);
lean_dec(v_a_4861_);
lean_dec_ref(v_overlaps_4860_);
lean_dec(v___x_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___x_4857_);
lean_dec_ref(v___x_4856_);
v_a_4913_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___x_4885_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4885_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4921_ = _args[0];
lean_object* v___x_4922_ = _args[1];
lean_object* v___x_4923_ = _args[2];
lean_object* v___y_4924_ = _args[3];
lean_object* v___x_4925_ = _args[4];
lean_object* v_overlaps_4926_ = _args[5];
lean_object* v_a_4927_ = _args[6];
lean_object* v_fst_4928_ = _args[7];
lean_object* v___x_4929_ = _args[8];
lean_object* v_a_4930_ = _args[9];
lean_object* v___x_4931_ = _args[10];
lean_object* v___x_4932_ = _args[11];
lean_object* v___x_4933_ = _args[12];
lean_object* v___x_4934_ = _args[13];
lean_object* v___x_4935_ = _args[14];
lean_object* v___x_4936_ = _args[15];
lean_object* v_matchDeclName_4937_ = _args[16];
lean_object* v___x_4938_ = _args[17];
lean_object* v___x_4939_ = _args[18];
lean_object* v___x_4940_ = _args[19];
lean_object* v_altVars_4941_ = _args[20];
lean_object* v_args_4942_ = _args[21];
lean_object* v___mask_4943_ = _args[22];
lean_object* v_altResultType_4944_ = _args[23];
lean_object* v___y_4945_ = _args[24];
lean_object* v___y_4946_ = _args[25];
lean_object* v___y_4947_ = _args[26];
lean_object* v___y_4948_ = _args[27];
lean_object* v___y_4949_ = _args[28];
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4921_, v___x_4922_, v___x_4923_, v___y_4924_, v___x_4925_, v_overlaps_4926_, v_a_4927_, v_fst_4928_, v___x_4929_, v_a_4930_, v___x_4931_, v___x_4932_, v___x_4933_, v___x_4934_, v___x_4935_, v___x_4936_, v_matchDeclName_4937_, v___x_4938_, v___x_4939_, v___x_4940_, v_altVars_4941_, v_args_4942_, v___mask_4943_, v_altResultType_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
lean_dec_ref(v___mask_4943_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4952_, lean_object* v_val_4953_, lean_object* v_matchDeclName_4954_, lean_object* v___x_4955_, lean_object* v___x_4956_, lean_object* v_a_4957_, lean_object* v___x_4958_, lean_object* v___x_4959_, lean_object* v___x_4960_, lean_object* v___x_4961_, lean_object* v___x_4962_, lean_object* v___x_4963_, lean_object* v_a_4964_, lean_object* v_b_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_){
_start:
{
uint8_t v___x_4971_; 
v___x_4971_ = lean_nat_dec_lt(v_a_4964_, v_upperBound_4952_);
if (v___x_4971_ == 0)
{
lean_object* v___x_4972_; 
lean_dec(v_a_4964_);
lean_dec(v___x_4963_);
lean_dec(v___x_4962_);
lean_dec_ref(v___x_4961_);
lean_dec_ref(v___x_4960_);
lean_dec_ref(v___x_4959_);
lean_dec(v___x_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v___x_4956_);
lean_dec_ref(v___x_4955_);
lean_dec(v_matchDeclName_4954_);
lean_dec_ref(v_val_4953_);
v___x_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4972_, 0, v_b_4965_);
return v___x_4972_;
}
else
{
lean_object* v_snd_4973_; lean_object* v_fst_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_5037_; 
v_snd_4973_ = lean_ctor_get(v_b_4965_, 1);
v_fst_4974_ = lean_ctor_get(v_b_4965_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v_b_4965_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_4976_ = v_b_4965_;
v_isShared_4977_ = v_isSharedCheck_5037_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_snd_4973_);
lean_inc(v_fst_4974_);
lean_dec(v_b_4965_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_5037_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v_fst_4978_; lean_object* v_snd_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_5036_; 
v_fst_4978_ = lean_ctor_get(v_snd_4973_, 0);
v_snd_4979_ = lean_ctor_get(v_snd_4973_, 1);
v_isSharedCheck_5036_ = !lean_is_exclusive(v_snd_4973_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_4981_ = v_snd_4973_;
v_isShared_4982_ = v_isSharedCheck_5036_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_snd_4979_);
lean_inc(v_fst_4978_);
lean_dec(v_snd_4973_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_5036_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v_altInfos_4983_; lean_object* v_overlaps_4984_; lean_object* v_start_4985_; lean_object* v_stop_4986_; lean_object* v___f_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___y_4999_; lean_object* v___x_5031_; uint8_t v___x_5032_; 
v_altInfos_4983_ = lean_ctor_get(v_val_4953_, 2);
v_overlaps_4984_ = lean_ctor_get(v_val_4953_, 5);
v_start_4985_ = lean_ctor_get(v___x_4961_, 1);
v_stop_4986_ = lean_ctor_get(v___x_4961_, 2);
v___f_4987_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4988_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4989_ = lean_unsigned_to_nat(0u);
v___x_4990_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4991_ = lean_unsigned_to_nat(1u);
v___x_4992_ = lean_box(0);
v___x_4993_ = lean_array_get_borrowed(v___x_4988_, v_altInfos_4983_, v_a_4964_);
v___x_4994_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4954_);
v___x_4995_ = l_Lean_Name_str___override(v_matchDeclName_4954_, v___x_4994_);
lean_inc(v_snd_4979_);
v___x_4996_ = lean_name_append_index_after(v___x_4995_, v_snd_4979_);
lean_inc(v___x_4996_);
v___x_4997_ = lean_array_push(v_fst_4974_, v___x_4996_);
v___x_5031_ = lean_nat_sub(v_stop_4986_, v_start_4985_);
v___x_5032_ = lean_nat_dec_lt(v_a_4964_, v___x_5031_);
lean_dec(v___x_5031_);
if (v___x_5032_ == 0)
{
lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5033_ = l_Lean_instInhabitedExpr;
v___x_5034_ = l_outOfBounds___redArg(v___x_5033_);
v___y_4999_ = v___x_5034_;
goto v___jp_4998_;
}
else
{
lean_object* v___x_5035_; 
v___x_5035_ = l_Subarray_get___redArg(v___x_4961_, v_a_4964_);
v___y_4999_ = v___x_5035_;
goto v___jp_4998_;
}
v___jp_4998_:
{
lean_object* v___x_5000_; 
lean_inc(v___y_4969_);
lean_inc_ref(v___y_4968_);
lean_inc(v___y_4967_);
lean_inc_ref(v___y_4966_);
lean_inc_ref(v___y_4999_);
v___x_5000_ = lean_infer_type(v___y_4999_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v_a_5001_; lean_object* v___f_5002_; lean_object* v___x_5003_; 
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
lean_inc(v_a_5001_);
lean_dec_ref(v___x_5000_);
lean_inc(v___x_4963_);
lean_inc(v_matchDeclName_4954_);
lean_inc(v___x_4962_);
lean_inc_ref(v___x_4961_);
lean_inc_ref(v___x_4960_);
lean_inc_ref(v___x_4959_);
lean_inc(v___x_4958_);
lean_inc_ref(v_a_4957_);
lean_inc(v_fst_4978_);
lean_inc(v_a_4964_);
lean_inc_ref(v_overlaps_4984_);
lean_inc(v___x_4956_);
lean_inc_ref(v___x_4955_);
v___f_5002_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 29, 20);
lean_closure_set(v___f_5002_, 0, v___f_4987_);
lean_closure_set(v___f_5002_, 1, v___x_4955_);
lean_closure_set(v___f_5002_, 2, v___x_4989_);
lean_closure_set(v___f_5002_, 3, v___y_4999_);
lean_closure_set(v___f_5002_, 4, v___x_4956_);
lean_closure_set(v___f_5002_, 5, v_overlaps_4984_);
lean_closure_set(v___f_5002_, 6, v_a_4964_);
lean_closure_set(v___f_5002_, 7, v_fst_4978_);
lean_closure_set(v___f_5002_, 8, v___x_4990_);
lean_closure_set(v___f_5002_, 9, v_a_4957_);
lean_closure_set(v___f_5002_, 10, v___x_4958_);
lean_closure_set(v___f_5002_, 11, v___x_4959_);
lean_closure_set(v___f_5002_, 12, v___x_4991_);
lean_closure_set(v___f_5002_, 13, v___x_4960_);
lean_closure_set(v___f_5002_, 14, v___x_4961_);
lean_closure_set(v___f_5002_, 15, v___x_4962_);
lean_closure_set(v___f_5002_, 16, v_matchDeclName_4954_);
lean_closure_set(v___f_5002_, 17, v___x_4996_);
lean_closure_set(v___f_5002_, 18, v___x_4963_);
lean_closure_set(v___f_5002_, 19, v___x_4992_);
lean_inc(v___x_4993_);
v___x_5003_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_5001_, v___x_4993_, v___f_5002_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5008_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
lean_inc(v_a_5004_);
lean_dec_ref(v___x_5003_);
v___x_5005_ = lean_array_push(v_fst_4978_, v_a_5004_);
v___x_5006_ = lean_nat_add(v_snd_4979_, v___x_4991_);
lean_dec(v_snd_4979_);
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 1, v___x_5006_);
lean_ctor_set(v___x_4981_, 0, v___x_5005_);
v___x_5008_ = v___x_4981_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5005_);
lean_ctor_set(v_reuseFailAlloc_5014_, 1, v___x_5006_);
v___x_5008_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
lean_object* v___x_5010_; 
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 1, v___x_5008_);
lean_ctor_set(v___x_4976_, 0, v___x_4997_);
v___x_5010_ = v___x_4976_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_4997_);
lean_ctor_set(v_reuseFailAlloc_5013_, 1, v___x_5008_);
v___x_5010_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
lean_object* v___x_5011_; 
v___x_5011_ = lean_nat_add(v_a_4964_, v___x_4991_);
lean_dec(v_a_4964_);
v_a_4964_ = v___x_5011_;
v_b_4965_ = v___x_5010_;
goto _start;
}
}
}
else
{
lean_object* v_a_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5022_; 
lean_dec_ref(v___x_4997_);
lean_del_object(v___x_4981_);
lean_dec(v_snd_4979_);
lean_dec(v_fst_4978_);
lean_del_object(v___x_4976_);
lean_dec(v_a_4964_);
lean_dec(v___x_4963_);
lean_dec(v___x_4962_);
lean_dec_ref(v___x_4961_);
lean_dec_ref(v___x_4960_);
lean_dec_ref(v___x_4959_);
lean_dec(v___x_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v___x_4956_);
lean_dec_ref(v___x_4955_);
lean_dec(v_matchDeclName_4954_);
lean_dec_ref(v_val_4953_);
v_a_5015_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5017_ = v___x_5003_;
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_a_5015_);
lean_dec(v___x_5003_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5022_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5020_; 
if (v_isShared_5018_ == 0)
{
v___x_5020_ = v___x_5017_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5015_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
}
else
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5030_; 
lean_dec_ref(v___y_4999_);
lean_dec_ref(v___x_4997_);
lean_dec(v___x_4996_);
lean_del_object(v___x_4981_);
lean_dec(v_snd_4979_);
lean_dec(v_fst_4978_);
lean_del_object(v___x_4976_);
lean_dec(v_a_4964_);
lean_dec(v___x_4963_);
lean_dec(v___x_4962_);
lean_dec_ref(v___x_4961_);
lean_dec_ref(v___x_4960_);
lean_dec_ref(v___x_4959_);
lean_dec(v___x_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v___x_4956_);
lean_dec_ref(v___x_4955_);
lean_dec(v_matchDeclName_4954_);
lean_dec_ref(v_val_4953_);
v_a_5023_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5025_ = v___x_5000_;
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v___x_5000_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5030_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v___x_5028_; 
if (v_isShared_5026_ == 0)
{
v___x_5028_ = v___x_5025_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_a_5023_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
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
lean_object* v_upperBound_5038_ = _args[0];
lean_object* v_val_5039_ = _args[1];
lean_object* v_matchDeclName_5040_ = _args[2];
lean_object* v___x_5041_ = _args[3];
lean_object* v___x_5042_ = _args[4];
lean_object* v_a_5043_ = _args[5];
lean_object* v___x_5044_ = _args[6];
lean_object* v___x_5045_ = _args[7];
lean_object* v___x_5046_ = _args[8];
lean_object* v___x_5047_ = _args[9];
lean_object* v___x_5048_ = _args[10];
lean_object* v___x_5049_ = _args[11];
lean_object* v_a_5050_ = _args[12];
lean_object* v_b_5051_ = _args[13];
lean_object* v___y_5052_ = _args[14];
lean_object* v___y_5053_ = _args[15];
lean_object* v___y_5054_ = _args[16];
lean_object* v___y_5055_ = _args[17];
lean_object* v___y_5056_ = _args[18];
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5038_, v_val_5039_, v_matchDeclName_5040_, v___x_5041_, v___x_5042_, v_a_5043_, v___x_5044_, v___x_5045_, v___x_5046_, v___x_5047_, v___x_5048_, v___x_5049_, v_a_5050_, v_b_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v_upperBound_5038_);
return v_res_5057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5064_, lean_object* v___x_5065_, lean_object* v_matchDeclName_5066_, lean_object* v___x_5067_, lean_object* v_a_5068_, lean_object* v___x_5069_, lean_object* v___x_5070_, lean_object* v_xs_5071_, lean_object* v___matchResultType_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_){
_start:
{
lean_object* v_numParams_5078_; lean_object* v_numDiscrs_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v_lower_5085_; lean_object* v_upper_5086_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; uint8_t v___x_5117_; 
v_numParams_5078_ = lean_ctor_get(v_val_5064_, 0);
v_numDiscrs_5079_ = lean_ctor_get(v_val_5064_, 1);
v___x_5080_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5078_);
lean_inc_ref(v_xs_5071_);
v___x_5081_ = l_Array_toSubarray___redArg(v_xs_5071_, v___x_5080_, v_numParams_5078_);
v___x_5082_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5064_);
v___x_5083_ = lean_array_get(v___x_5065_, v_xs_5071_, v___x_5082_);
lean_dec(v___x_5082_);
v___x_5114_ = lean_array_get_size(v_xs_5071_);
v___x_5115_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5064_);
v___x_5116_ = lean_nat_sub(v___x_5114_, v___x_5115_);
lean_dec(v___x_5115_);
v___x_5117_ = lean_nat_dec_le(v___x_5116_, v___x_5080_);
if (v___x_5117_ == 0)
{
v_lower_5085_ = v___x_5116_;
v_upper_5086_ = v___x_5114_;
goto v___jp_5084_;
}
else
{
lean_dec(v___x_5116_);
v_lower_5085_ = v___x_5080_;
v_upper_5086_ = v___x_5114_;
goto v___jp_5084_;
}
v___jp_5084_:
{
lean_object* v___x_5087_; lean_object* v_start_5088_; lean_object* v_stop_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
lean_inc_ref(v_xs_5071_);
v___x_5087_ = l_Array_toSubarray___redArg(v_xs_5071_, v_lower_5085_, v_upper_5086_);
v_start_5088_ = lean_ctor_get(v___x_5087_, 1);
lean_inc(v_start_5088_);
v_stop_5089_ = lean_ctor_get(v___x_5087_, 2);
lean_inc(v_stop_5089_);
v___x_5090_ = lean_unsigned_to_nat(1u);
v___x_5091_ = lean_nat_add(v_numParams_5078_, v___x_5090_);
v___x_5092_ = lean_nat_add(v___x_5091_, v_numDiscrs_5079_);
v___x_5093_ = lean_nat_sub(v_stop_5089_, v_start_5088_);
lean_dec(v_start_5088_);
lean_dec(v_stop_5089_);
v___x_5094_ = l_Array_toSubarray___redArg(v_xs_5071_, v___x_5091_, v___x_5092_);
v___x_5095_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5093_);
v___x_5096_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5093_, v_val_5064_, v_matchDeclName_5066_, v___x_5094_, v___x_5067_, v_a_5068_, v___x_5069_, v___x_5081_, v___x_5083_, v___x_5087_, v___x_5093_, v___x_5070_, v___x_5080_, v___x_5095_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
lean_dec(v___x_5093_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5104_; 
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5104_ == 0)
{
lean_object* v_unused_5105_; 
v_unused_5105_ = lean_ctor_get(v___x_5096_, 0);
lean_dec(v_unused_5105_);
v___x_5098_ = v___x_5096_;
v_isShared_5099_ = v_isSharedCheck_5104_;
goto v_resetjp_5097_;
}
else
{
lean_dec(v___x_5096_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5104_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5100_; lean_object* v___x_5102_; 
v___x_5100_ = lean_box(0);
if (v_isShared_5099_ == 0)
{
lean_ctor_set(v___x_5098_, 0, v___x_5100_);
v___x_5102_ = v___x_5098_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5100_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
else
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5113_; 
v_a_5106_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5108_ = v___x_5096_;
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5096_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5111_; 
if (v_isShared_5109_ == 0)
{
v___x_5111_ = v___x_5108_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
return v___x_5111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5118_, lean_object* v___x_5119_, lean_object* v_matchDeclName_5120_, lean_object* v___x_5121_, lean_object* v_a_5122_, lean_object* v___x_5123_, lean_object* v___x_5124_, lean_object* v_xs_5125_, lean_object* v___matchResultType_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
lean_object* v_res_5132_; 
v_res_5132_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5118_, v___x_5119_, v_matchDeclName_5120_, v___x_5121_, v_a_5122_, v___x_5123_, v___x_5124_, v_xs_5125_, v___matchResultType_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
lean_dec_ref(v___matchResultType_5126_);
lean_dec_ref(v___x_5119_);
return v_res_5132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_){
_start:
{
uint8_t v_trackZetaDelta_5139_; lean_object* v_zetaDeltaSet_5140_; lean_object* v_lctx_5141_; lean_object* v_localInstances_5142_; lean_object* v_defEqCtx_x3f_5143_; lean_object* v_synthPendingDepth_5144_; lean_object* v_canUnfold_x3f_5145_; uint8_t v_univApprox_5146_; uint8_t v_inTypeClassResolution_5147_; uint8_t v_cacheInferType_5148_; lean_object* v___x_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5192_; 
v_trackZetaDelta_5139_ = lean_ctor_get_uint8(v_a_5134_, sizeof(void*)*7);
v_zetaDeltaSet_5140_ = lean_ctor_get(v_a_5134_, 1);
lean_inc(v_zetaDeltaSet_5140_);
v_lctx_5141_ = lean_ctor_get(v_a_5134_, 2);
lean_inc_ref(v_lctx_5141_);
v_localInstances_5142_ = lean_ctor_get(v_a_5134_, 3);
lean_inc_ref(v_localInstances_5142_);
v_defEqCtx_x3f_5143_ = lean_ctor_get(v_a_5134_, 4);
lean_inc(v_defEqCtx_x3f_5143_);
v_synthPendingDepth_5144_ = lean_ctor_get(v_a_5134_, 5);
lean_inc(v_synthPendingDepth_5144_);
v_canUnfold_x3f_5145_ = lean_ctor_get(v_a_5134_, 6);
lean_inc(v_canUnfold_x3f_5145_);
v_univApprox_5146_ = lean_ctor_get_uint8(v_a_5134_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5147_ = lean_ctor_get_uint8(v_a_5134_, sizeof(void*)*7 + 2);
v_cacheInferType_5148_ = lean_ctor_get_uint8(v_a_5134_, sizeof(void*)*7 + 3);
v___x_5149_ = l_Lean_Meta_Context_config(v_a_5134_);
v_isSharedCheck_5192_ = !lean_is_exclusive(v_a_5134_);
if (v_isSharedCheck_5192_ == 0)
{
lean_object* v_unused_5193_; lean_object* v_unused_5194_; lean_object* v_unused_5195_; lean_object* v_unused_5196_; lean_object* v_unused_5197_; lean_object* v_unused_5198_; lean_object* v_unused_5199_; 
v_unused_5193_ = lean_ctor_get(v_a_5134_, 6);
lean_dec(v_unused_5193_);
v_unused_5194_ = lean_ctor_get(v_a_5134_, 5);
lean_dec(v_unused_5194_);
v_unused_5195_ = lean_ctor_get(v_a_5134_, 4);
lean_dec(v_unused_5195_);
v_unused_5196_ = lean_ctor_get(v_a_5134_, 3);
lean_dec(v_unused_5196_);
v_unused_5197_ = lean_ctor_get(v_a_5134_, 2);
lean_dec(v_unused_5197_);
v_unused_5198_ = lean_ctor_get(v_a_5134_, 1);
lean_dec(v_unused_5198_);
v_unused_5199_ = lean_ctor_get(v_a_5134_, 0);
lean_dec(v_unused_5199_);
v___x_5151_ = v_a_5134_;
v_isShared_5152_ = v_isSharedCheck_5192_;
goto v_resetjp_5150_;
}
else
{
lean_dec(v_a_5134_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5192_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5153_; uint64_t v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5157_; 
v___x_5153_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5149_);
v___x_5154_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5153_);
v___x_5155_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5155_, 0, v___x_5153_);
lean_ctor_set_uint64(v___x_5155_, sizeof(void*)*1, v___x_5154_);
lean_inc(v_canUnfold_x3f_5145_);
lean_inc(v_synthPendingDepth_5144_);
lean_inc(v_defEqCtx_x3f_5143_);
lean_inc_ref(v_localInstances_5142_);
lean_inc_ref(v_lctx_5141_);
lean_inc(v_zetaDeltaSet_5140_);
if (v_isShared_5152_ == 0)
{
lean_ctor_set(v___x_5151_, 0, v___x_5155_);
v___x_5157_ = v___x_5151_;
goto v_reusejp_5156_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5155_);
lean_ctor_set(v_reuseFailAlloc_5191_, 1, v_zetaDeltaSet_5140_);
lean_ctor_set(v_reuseFailAlloc_5191_, 2, v_lctx_5141_);
lean_ctor_set(v_reuseFailAlloc_5191_, 3, v_localInstances_5142_);
lean_ctor_set(v_reuseFailAlloc_5191_, 4, v_defEqCtx_x3f_5143_);
lean_ctor_set(v_reuseFailAlloc_5191_, 5, v_synthPendingDepth_5144_);
lean_ctor_set(v_reuseFailAlloc_5191_, 6, v_canUnfold_x3f_5145_);
lean_ctor_set_uint8(v_reuseFailAlloc_5191_, sizeof(void*)*7, v_trackZetaDelta_5139_);
lean_ctor_set_uint8(v_reuseFailAlloc_5191_, sizeof(void*)*7 + 1, v_univApprox_5146_);
lean_ctor_set_uint8(v_reuseFailAlloc_5191_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5147_);
lean_ctor_set_uint8(v_reuseFailAlloc_5191_, sizeof(void*)*7 + 3, v_cacheInferType_5148_);
v___x_5157_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5156_;
}
v_reusejp_5156_:
{
lean_object* v___x_5158_; lean_object* v___x_5159_; uint64_t v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; 
v___x_5158_ = l_Lean_Meta_Context_config(v___x_5157_);
lean_dec_ref(v___x_5157_);
v___x_5159_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5158_);
v___x_5160_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5159_);
v___x_5161_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5161_, 0, v___x_5159_);
lean_ctor_set_uint64(v___x_5161_, sizeof(void*)*1, v___x_5160_);
v___x_5162_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5162_, 0, v___x_5161_);
lean_ctor_set(v___x_5162_, 1, v_zetaDeltaSet_5140_);
lean_ctor_set(v___x_5162_, 2, v_lctx_5141_);
lean_ctor_set(v___x_5162_, 3, v_localInstances_5142_);
lean_ctor_set(v___x_5162_, 4, v_defEqCtx_x3f_5143_);
lean_ctor_set(v___x_5162_, 5, v_synthPendingDepth_5144_);
lean_ctor_set(v___x_5162_, 6, v_canUnfold_x3f_5145_);
lean_ctor_set_uint8(v___x_5162_, sizeof(void*)*7, v_trackZetaDelta_5139_);
lean_ctor_set_uint8(v___x_5162_, sizeof(void*)*7 + 1, v_univApprox_5146_);
lean_ctor_set_uint8(v___x_5162_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5147_);
lean_ctor_set_uint8(v___x_5162_, sizeof(void*)*7 + 3, v_cacheInferType_5148_);
lean_inc(v_matchDeclName_5133_);
v___x_5163_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5133_, v___x_5162_, v_a_5135_, v_a_5136_, v_a_5137_);
if (lean_obj_tag(v___x_5163_) == 0)
{
lean_object* v_a_5164_; lean_object* v___x_5165_; lean_object* v_a_5166_; 
v_a_5164_ = lean_ctor_get(v___x_5163_, 0);
lean_inc(v_a_5164_);
lean_dec_ref(v___x_5163_);
lean_inc(v_matchDeclName_5133_);
v___x_5165_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5133_, v_a_5137_);
v_a_5166_ = lean_ctor_get(v___x_5165_, 0);
lean_inc(v_a_5166_);
lean_dec_ref(v___x_5165_);
if (lean_obj_tag(v_a_5166_) == 1)
{
lean_object* v_val_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___f_5173_; lean_object* v___x_5174_; uint8_t v___x_5175_; lean_object* v___x_5176_; 
v_val_5167_ = lean_ctor_get(v_a_5166_, 0);
lean_inc(v_val_5167_);
lean_dec_ref(v_a_5166_);
v___x_5168_ = l_Lean_instInhabitedExpr;
v___x_5169_ = l_Lean_ConstantInfo_levelParams(v_a_5164_);
v___x_5170_ = lean_box(0);
lean_inc(v___x_5169_);
v___x_5171_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_5169_, v___x_5170_);
v___x_5172_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5167_);
lean_inc(v_a_5164_);
v___f_5173_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5173_, 0, v_val_5167_);
lean_closure_set(v___f_5173_, 1, v___x_5168_);
lean_closure_set(v___f_5173_, 2, v_matchDeclName_5133_);
lean_closure_set(v___f_5173_, 3, v___x_5172_);
lean_closure_set(v___f_5173_, 4, v_a_5164_);
lean_closure_set(v___f_5173_, 5, v___x_5171_);
lean_closure_set(v___f_5173_, 6, v___x_5169_);
v___x_5174_ = l_Lean_ConstantInfo_type(v_a_5164_);
lean_dec(v_a_5164_);
v___x_5175_ = 0;
v___x_5176_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5174_, v___f_5173_, v___x_5175_, v___x_5175_, v___x_5162_, v_a_5135_, v_a_5136_, v_a_5137_);
lean_dec_ref(v___x_5162_);
return v___x_5176_;
}
else
{
lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
lean_dec(v_a_5166_);
lean_dec(v_a_5164_);
v___x_5177_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5178_ = l_Lean_MessageData_ofName(v_matchDeclName_5133_);
v___x_5179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5177_);
lean_ctor_set(v___x_5179_, 1, v___x_5178_);
v___x_5180_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5179_);
lean_ctor_set(v___x_5181_, 1, v___x_5180_);
v___x_5182_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5181_, v___x_5162_, v_a_5135_, v_a_5136_, v_a_5137_);
lean_dec_ref(v___x_5162_);
return v___x_5182_;
}
}
else
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
lean_dec_ref(v___x_5162_);
lean_dec(v_matchDeclName_5133_);
v_a_5183_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5185_ = v___x_5163_;
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5163_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
v___x_5188_ = v___x_5185_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_a_5183_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5200_, lean_object* v_a_5201_, lean_object* v_a_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_);
lean_dec(v_a_5204_);
lean_dec_ref(v_a_5203_);
lean_dec(v_a_5202_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_inst_5207_, lean_object* v_R_5208_, lean_object* v_a_5209_, lean_object* v_b_5210_, lean_object* v_c_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
lean_object* v___x_5217_; 
v___x_5217_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_5209_, v_b_5210_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_inst_5218_, lean_object* v_R_5219_, lean_object* v_a_5220_, lean_object* v_b_5221_, lean_object* v_c_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
lean_object* v_res_5228_; 
v_res_5228_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_inst_5218_, v_R_5219_, v_a_5220_, v_b_5221_, v_c_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
return v_res_5228_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5229_, lean_object* v_val_5230_, lean_object* v_matchDeclName_5231_, lean_object* v___x_5232_, lean_object* v___x_5233_, lean_object* v_a_5234_, lean_object* v___x_5235_, lean_object* v___x_5236_, lean_object* v___x_5237_, lean_object* v___x_5238_, lean_object* v___x_5239_, lean_object* v___x_5240_, lean_object* v_inst_5241_, lean_object* v_R_5242_, lean_object* v_a_5243_, lean_object* v_b_5244_, lean_object* v_c_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
lean_object* v___x_5251_; 
v___x_5251_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5229_, v_val_5230_, v_matchDeclName_5231_, v___x_5232_, v___x_5233_, v_a_5234_, v___x_5235_, v___x_5236_, v___x_5237_, v___x_5238_, v___x_5239_, v___x_5240_, v_a_5243_, v_b_5244_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5252_ = _args[0];
lean_object* v_val_5253_ = _args[1];
lean_object* v_matchDeclName_5254_ = _args[2];
lean_object* v___x_5255_ = _args[3];
lean_object* v___x_5256_ = _args[4];
lean_object* v_a_5257_ = _args[5];
lean_object* v___x_5258_ = _args[6];
lean_object* v___x_5259_ = _args[7];
lean_object* v___x_5260_ = _args[8];
lean_object* v___x_5261_ = _args[9];
lean_object* v___x_5262_ = _args[10];
lean_object* v___x_5263_ = _args[11];
lean_object* v_inst_5264_ = _args[12];
lean_object* v_R_5265_ = _args[13];
lean_object* v_a_5266_ = _args[14];
lean_object* v_b_5267_ = _args[15];
lean_object* v_c_5268_ = _args[16];
lean_object* v___y_5269_ = _args[17];
lean_object* v___y_5270_ = _args[18];
lean_object* v___y_5271_ = _args[19];
lean_object* v___y_5272_ = _args[20];
lean_object* v___y_5273_ = _args[21];
_start:
{
lean_object* v_res_5274_; 
v_res_5274_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5252_, v_val_5253_, v_matchDeclName_5254_, v___x_5255_, v___x_5256_, v_a_5257_, v___x_5258_, v___x_5259_, v___x_5260_, v___x_5261_, v___x_5262_, v___x_5263_, v_inst_5264_, v_R_5265_, v_a_5266_, v_b_5267_, v_c_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v_upperBound_5252_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5275_, lean_object* v_matchDeclName_5276_, lean_object* v_a_5277_, lean_object* v_b_5278_){
_start:
{
uint8_t v___x_5280_; 
v___x_5280_ = lean_nat_dec_lt(v_a_5277_, v_upperBound_5275_);
if (v___x_5280_ == 0)
{
lean_object* v___x_5281_; 
lean_dec(v_a_5277_);
lean_dec(v_matchDeclName_5276_);
v___x_5281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5281_, 0, v_b_5278_);
return v___x_5281_;
}
else
{
lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; 
v___x_5282_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5276_);
v___x_5283_ = l_Lean_Name_str___override(v_matchDeclName_5276_, v___x_5282_);
v___x_5284_ = lean_unsigned_to_nat(1u);
v___x_5285_ = lean_nat_add(v_a_5277_, v___x_5284_);
lean_dec(v_a_5277_);
lean_inc(v___x_5285_);
v___x_5286_ = lean_name_append_index_after(v___x_5283_, v___x_5285_);
v___x_5287_ = lean_array_push(v_b_5278_, v___x_5286_);
v_a_5277_ = v___x_5285_;
v_b_5278_ = v___x_5287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5289_, lean_object* v_matchDeclName_5290_, lean_object* v_a_5291_, lean_object* v_b_5292_, lean_object* v___y_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5289_, v_matchDeclName_5290_, v_a_5291_, v_b_5292_);
lean_dec(v_upperBound_5289_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5295_, lean_object* v_a_5296_, lean_object* v_a_5297_, lean_object* v_a_5298_, lean_object* v_a_5299_){
_start:
{
lean_object* v___x_5301_; lean_object* v_firstEqnName_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5301_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5295_, 3);
v_firstEqnName_5302_ = l_Lean_Name_str___override(v_matchDeclName_5295_, v___x_5301_);
v___x_5303_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5303_, 0, v_matchDeclName_5295_);
v___x_5304_ = l_Lean_Meta_realizeConst(v_matchDeclName_5295_, v_firstEqnName_5302_, v___x_5303_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
if (lean_obj_tag(v___x_5304_) == 0)
{
lean_object* v___x_5305_; lean_object* v_a_5306_; 
lean_dec_ref(v___x_5304_);
lean_inc(v_matchDeclName_5295_);
v___x_5305_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5295_, v_a_5299_);
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
lean_inc(v_a_5306_);
lean_dec_ref(v___x_5305_);
if (lean_obj_tag(v_a_5306_) == 1)
{
lean_object* v_val_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; 
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec(v_a_5297_);
lean_dec_ref(v_a_5296_);
v_val_5307_ = lean_ctor_get(v_a_5306_, 0);
lean_inc(v_val_5307_);
lean_dec_ref(v_a_5306_);
v___x_5308_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5307_);
lean_dec(v_val_5307_);
v___x_5309_ = lean_unsigned_to_nat(0u);
v___x_5310_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5308_, v_matchDeclName_5295_, v___x_5309_, v___x_5310_);
lean_dec(v___x_5308_);
return v___x_5311_;
}
else
{
lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; 
lean_dec(v_a_5306_);
v___x_5312_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5313_ = l_Lean_MessageData_ofName(v_matchDeclName_5295_);
v___x_5314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5314_, 0, v___x_5312_);
lean_ctor_set(v___x_5314_, 1, v___x_5313_);
v___x_5315_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5316_, 0, v___x_5314_);
lean_ctor_set(v___x_5316_, 1, v___x_5315_);
v___x_5317_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5316_, v_a_5296_, v_a_5297_, v_a_5298_, v_a_5299_);
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec(v_a_5297_);
lean_dec_ref(v_a_5296_);
return v___x_5317_;
}
}
else
{
lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5325_; 
lean_dec(v_a_5299_);
lean_dec_ref(v_a_5298_);
lean_dec(v_a_5297_);
lean_dec_ref(v_a_5296_);
lean_dec(v_matchDeclName_5295_);
v_a_5318_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5320_ = v___x_5304_;
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v___x_5304_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5318_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = lean_get_congr_match_equations_for(v_matchDeclName_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5333_, lean_object* v_matchDeclName_5334_, lean_object* v_inst_5335_, lean_object* v_R_5336_, lean_object* v_a_5337_, lean_object* v_b_5338_, lean_object* v_c_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
lean_object* v___x_5345_; 
v___x_5345_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5333_, v_matchDeclName_5334_, v_a_5337_, v_b_5338_);
return v___x_5345_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5346_, lean_object* v_matchDeclName_5347_, lean_object* v_inst_5348_, lean_object* v_R_5349_, lean_object* v_a_5350_, lean_object* v_b_5351_, lean_object* v_c_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5346_, v_matchDeclName_5347_, v_inst_5348_, v_R_5349_, v_a_5350_, v_b_5351_, v_c_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_);
lean_dec(v___y_5356_);
lean_dec_ref(v___y_5355_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec(v_upperBound_5346_);
return v_res_5358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
v___x_5409_ = lean_unsigned_to_nat(3248161880u);
v___x_5410_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5411_ = l_Lean_Name_num___override(v___x_5410_, v___x_5409_);
return v___x_5411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5413_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5414_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5415_ = l_Lean_Name_str___override(v___x_5414_, v___x_5413_);
return v___x_5415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5417_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5418_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5419_ = l_Lean_Name_str___override(v___x_5418_, v___x_5417_);
return v___x_5419_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; 
v___x_5420_ = lean_unsigned_to_nat(2u);
v___x_5421_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5422_ = l_Lean_Name_num___override(v___x_5421_, v___x_5420_);
return v___x_5422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5424_; uint8_t v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; 
v___x_5424_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5425_ = 0;
v___x_5426_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5427_ = l_Lean_registerTraceClass(v___x_5424_, v___x_5425_, v___x_5426_);
return v___x_5427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5428_){
_start:
{
lean_object* v_res_5429_; 
v_res_5429_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5430_, lean_object* v_n_5431_){
_start:
{
if (lean_obj_tag(v_n_5431_) == 1)
{
lean_object* v_pre_5432_; lean_object* v_str_5433_; uint8_t v___y_5435_; uint8_t v___x_5441_; 
v_pre_5432_ = lean_ctor_get(v_n_5431_, 0);
lean_inc(v_pre_5432_);
v_str_5433_ = lean_ctor_get(v_n_5431_, 1);
lean_inc_ref_n(v_str_5433_, 2);
lean_dec_ref(v_n_5431_);
v___x_5441_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5433_);
if (v___x_5441_ == 0)
{
lean_object* v___x_5442_; uint8_t v___x_5443_; 
v___x_5442_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5443_ = lean_string_dec_eq(v_str_5433_, v___x_5442_);
lean_dec_ref(v_str_5433_);
v___y_5435_ = v___x_5443_;
goto v___jp_5434_;
}
else
{
lean_dec_ref(v_str_5433_);
v___y_5435_ = v___x_5441_;
goto v___jp_5434_;
}
v___jp_5434_:
{
if (v___y_5435_ == 0)
{
lean_object* v___x_5436_; 
lean_dec(v_pre_5432_);
lean_dec_ref(v_env_5430_);
v___x_5436_ = lean_box(0);
return v___x_5436_;
}
else
{
lean_object* v___x_5437_; 
v___x_5437_ = lean_private_to_user_name(v_pre_5432_);
if (lean_obj_tag(v___x_5437_) == 0)
{
lean_dec_ref(v_env_5430_);
return v___x_5437_;
}
else
{
lean_object* v_val_5438_; uint8_t v___x_5439_; 
v_val_5438_ = lean_ctor_get(v___x_5437_, 0);
lean_inc(v_val_5438_);
v___x_5439_ = lean_is_matcher(v_env_5430_, v_val_5438_);
if (v___x_5439_ == 0)
{
lean_object* v___x_5440_; 
lean_dec_ref(v___x_5437_);
v___x_5440_ = lean_box(0);
return v___x_5440_;
}
else
{
return v___x_5437_;
}
}
}
}
}
else
{
lean_object* v___x_5444_; 
lean_dec(v_n_5431_);
lean_dec_ref(v_env_5430_);
v___x_5444_ = lean_box(0);
return v___x_5444_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5445_, lean_object* v_x2_5446_){
_start:
{
lean_object* v___x_5447_; 
v___x_5447_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5445_, v_x2_5446_);
if (lean_obj_tag(v___x_5447_) == 0)
{
uint8_t v___x_5448_; 
v___x_5448_ = 0;
return v___x_5448_;
}
else
{
uint8_t v___x_5449_; 
lean_dec_ref(v___x_5447_);
v___x_5449_ = 1;
return v___x_5449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5450_, lean_object* v_x2_5451_){
_start:
{
uint8_t v_res_5452_; lean_object* v_r_5453_; 
v_res_5452_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5450_, v_x2_5451_);
v_r_5453_ = lean_box(v_res_5452_);
return v_r_5453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5456_; lean_object* v___x_5457_; 
v___f_5456_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5457_ = l_Lean_registerReservedNamePredicate(v___f_5456_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5458_){
_start:
{
lean_object* v_res_5459_; 
v_res_5459_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5459_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5466_; uint64_t v___x_5467_; 
v___x_5466_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5467_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5466_);
return v___x_5467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; 
v___x_5468_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5469_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5470_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5470_, 0, v___x_5469_);
lean_ctor_set_uint64(v___x_5470_, sizeof(void*)*1, v___x_5468_);
return v___x_5470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; 
v___x_5473_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5474_ = lean_unsigned_to_nat(0u);
v___x_5475_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5475_, 0, v___x_5474_);
lean_ctor_set(v___x_5475_, 1, v___x_5474_);
lean_ctor_set(v___x_5475_, 2, v___x_5474_);
lean_ctor_set(v___x_5475_, 3, v___x_5474_);
lean_ctor_set(v___x_5475_, 4, v___x_5473_);
lean_ctor_set(v___x_5475_, 5, v___x_5473_);
lean_ctor_set(v___x_5475_, 6, v___x_5473_);
lean_ctor_set(v___x_5475_, 7, v___x_5473_);
lean_ctor_set(v___x_5475_, 8, v___x_5473_);
lean_ctor_set(v___x_5475_, 9, v___x_5473_);
return v___x_5475_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5476_; lean_object* v___x_5477_; 
v___x_5476_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5477_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5477_, 0, v___x_5476_);
lean_ctor_set(v___x_5477_, 1, v___x_5476_);
lean_ctor_set(v___x_5477_, 2, v___x_5476_);
lean_ctor_set(v___x_5477_, 3, v___x_5476_);
lean_ctor_set(v___x_5477_, 4, v___x_5476_);
lean_ctor_set(v___x_5477_, 5, v___x_5476_);
return v___x_5477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5478_; lean_object* v___x_5479_; 
v___x_5478_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5479_, 0, v___x_5478_);
lean_ctor_set(v___x_5479_, 1, v___x_5478_);
lean_ctor_set(v___x_5479_, 2, v___x_5478_);
lean_ctor_set(v___x_5479_, 3, v___x_5478_);
lean_ctor_set(v___x_5479_, 4, v___x_5478_);
return v___x_5479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5480_, lean_object* v_name_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_){
_start:
{
lean_object* v___x_5485_; lean_object* v_env_5486_; lean_object* v___x_5487_; 
v___x_5485_ = lean_st_ref_get(v___y_5483_);
v_env_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc_ref(v_env_5486_);
lean_dec(v___x_5485_);
v___x_5487_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5486_, v_name_5481_);
if (lean_obj_tag(v___x_5487_) == 1)
{
lean_object* v_val_5488_; uint8_t v___x_5489_; uint8_t v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; 
v_val_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_val_5488_);
lean_dec_ref(v___x_5487_);
v___x_5489_ = 0;
v___x_5490_ = 1;
v___x_5491_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5492_ = lean_unsigned_to_nat(0u);
v___x_5493_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5494_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5495_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5496_ = lean_box(0);
lean_inc(v___x_5480_);
v___x_5497_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5497_, 0, v___x_5491_);
lean_ctor_set(v___x_5497_, 1, v___x_5480_);
lean_ctor_set(v___x_5497_, 2, v___x_5494_);
lean_ctor_set(v___x_5497_, 3, v___x_5495_);
lean_ctor_set(v___x_5497_, 4, v___x_5496_);
lean_ctor_set(v___x_5497_, 5, v___x_5492_);
lean_ctor_set(v___x_5497_, 6, v___x_5496_);
lean_ctor_set_uint8(v___x_5497_, sizeof(void*)*7, v___x_5489_);
lean_ctor_set_uint8(v___x_5497_, sizeof(void*)*7 + 1, v___x_5489_);
lean_ctor_set_uint8(v___x_5497_, sizeof(void*)*7 + 2, v___x_5489_);
lean_ctor_set_uint8(v___x_5497_, sizeof(void*)*7 + 3, v___x_5490_);
v___x_5498_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5499_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5500_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5501_, 0, v___x_5498_);
lean_ctor_set(v___x_5501_, 1, v___x_5499_);
lean_ctor_set(v___x_5501_, 2, v___x_5480_);
lean_ctor_set(v___x_5501_, 3, v___x_5493_);
lean_ctor_set(v___x_5501_, 4, v___x_5500_);
v___x_5502_ = lean_st_mk_ref(v___x_5501_);
lean_inc(v___y_5483_);
lean_inc_ref(v___y_5482_);
lean_inc(v___x_5502_);
v___x_5503_ = lean_get_match_equations_for(v_val_5488_, v___x_5497_, v___x_5502_, v___y_5482_, v___y_5483_);
if (lean_obj_tag(v___x_5503_) == 0)
{
lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5512_; 
v_isSharedCheck_5512_ = !lean_is_exclusive(v___x_5503_);
if (v_isSharedCheck_5512_ == 0)
{
lean_object* v_unused_5513_; 
v_unused_5513_ = lean_ctor_get(v___x_5503_, 0);
lean_dec(v_unused_5513_);
v___x_5505_ = v___x_5503_;
v_isShared_5506_ = v_isSharedCheck_5512_;
goto v_resetjp_5504_;
}
else
{
lean_dec(v___x_5503_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5512_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5510_; 
v___x_5507_ = lean_st_ref_get(v___x_5502_);
lean_dec(v___x_5502_);
lean_dec(v___x_5507_);
v___x_5508_ = lean_box(v___x_5490_);
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 0, v___x_5508_);
v___x_5510_ = v___x_5505_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v___x_5508_);
v___x_5510_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
return v___x_5510_;
}
}
}
else
{
lean_dec(v___x_5502_);
if (lean_obj_tag(v___x_5503_) == 0)
{
lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5521_; 
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5503_);
if (v_isSharedCheck_5521_ == 0)
{
lean_object* v_unused_5522_; 
v_unused_5522_ = lean_ctor_get(v___x_5503_, 0);
lean_dec(v_unused_5522_);
v___x_5515_ = v___x_5503_;
v_isShared_5516_ = v_isSharedCheck_5521_;
goto v_resetjp_5514_;
}
else
{
lean_dec(v___x_5503_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5521_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5517_; lean_object* v___x_5519_; 
v___x_5517_ = lean_box(v___x_5490_);
if (v_isShared_5516_ == 0)
{
lean_ctor_set_tag(v___x_5515_, 0);
lean_ctor_set(v___x_5515_, 0, v___x_5517_);
v___x_5519_ = v___x_5515_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5517_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
return v___x_5519_;
}
}
}
else
{
lean_object* v_a_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5530_; 
v_a_5523_ = lean_ctor_get(v___x_5503_, 0);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5503_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5525_ = v___x_5503_;
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
else
{
lean_inc(v_a_5523_);
lean_dec(v___x_5503_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5528_; 
if (v_isShared_5526_ == 0)
{
v___x_5528_ = v___x_5525_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
}
else
{
uint8_t v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
lean_dec(v___x_5487_);
lean_dec(v___x_5480_);
v___x_5531_ = 0;
v___x_5532_ = lean_box(v___x_5531_);
v___x_5533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5533_, 0, v___x_5532_);
return v___x_5533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5534_, lean_object* v_name_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_){
_start:
{
lean_object* v_res_5539_; 
v_res_5539_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5534_, v_name_5535_, v___y_5536_, v___y_5537_);
lean_dec(v___y_5537_);
lean_dec_ref(v___y_5536_);
return v_res_5539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5543_; lean_object* v___x_5544_; 
v___f_5543_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5544_ = l_Lean_registerReservedNameAction(v___f_5543_);
return v___x_5544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5545_){
_start:
{
lean_object* v_res_5546_; 
v_res_5546_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5547_, lean_object* v_n_5548_){
_start:
{
if (lean_obj_tag(v_n_5548_) == 1)
{
lean_object* v_pre_5549_; lean_object* v_str_5550_; uint8_t v___x_5551_; 
v_pre_5549_ = lean_ctor_get(v_n_5548_, 0);
lean_inc(v_pre_5549_);
v_str_5550_ = lean_ctor_get(v_n_5548_, 1);
lean_inc_ref(v_str_5550_);
lean_dec_ref(v_n_5548_);
v___x_5551_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5550_);
if (v___x_5551_ == 0)
{
lean_object* v___x_5552_; 
lean_dec(v_pre_5549_);
lean_dec_ref(v_env_5547_);
v___x_5552_ = lean_box(0);
return v___x_5552_;
}
else
{
uint8_t v___x_5553_; 
lean_inc(v_pre_5549_);
v___x_5553_ = lean_is_matcher(v_env_5547_, v_pre_5549_);
if (v___x_5553_ == 0)
{
lean_object* v___x_5554_; 
lean_dec(v_pre_5549_);
v___x_5554_ = lean_box(0);
return v___x_5554_;
}
else
{
lean_object* v___x_5555_; 
v___x_5555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5555_, 0, v_pre_5549_);
return v___x_5555_;
}
}
}
else
{
lean_object* v___x_5556_; 
lean_dec(v_n_5548_);
lean_dec_ref(v_env_5547_);
v___x_5556_ = lean_box(0);
return v___x_5556_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5557_, lean_object* v_x2_5558_){
_start:
{
lean_object* v___x_5559_; 
v___x_5559_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5557_, v_x2_5558_);
if (lean_obj_tag(v___x_5559_) == 0)
{
uint8_t v___x_5560_; 
v___x_5560_ = 0;
return v___x_5560_;
}
else
{
uint8_t v___x_5561_; 
lean_dec_ref(v___x_5559_);
v___x_5561_ = 1;
return v___x_5561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5562_, lean_object* v_x2_5563_){
_start:
{
uint8_t v_res_5564_; lean_object* v_r_5565_; 
v_res_5564_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5562_, v_x2_5563_);
v_r_5565_ = lean_box(v_res_5564_);
return v_r_5565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5568_; lean_object* v___x_5569_; 
v___f_5568_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5569_ = l_Lean_registerReservedNamePredicate(v___f_5568_);
return v___x_5569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5570_){
_start:
{
lean_object* v_res_5571_; 
v_res_5571_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5572_, lean_object* v_name_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_){
_start:
{
lean_object* v___x_5577_; lean_object* v_env_5578_; lean_object* v___x_5579_; 
v___x_5577_ = lean_st_ref_get(v___y_5575_);
v_env_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc_ref(v_env_5578_);
lean_dec(v___x_5577_);
v___x_5579_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5578_, v_name_5573_);
if (lean_obj_tag(v___x_5579_) == 1)
{
lean_object* v_val_5580_; uint8_t v___x_5581_; uint8_t v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; 
v_val_5580_ = lean_ctor_get(v___x_5579_, 0);
lean_inc(v_val_5580_);
lean_dec_ref(v___x_5579_);
v___x_5581_ = 0;
v___x_5582_ = 1;
v___x_5583_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5584_ = lean_unsigned_to_nat(32u);
v___x_5585_ = lean_mk_empty_array_with_capacity(v___x_5584_);
lean_dec_ref(v___x_5585_);
v___x_5586_ = lean_unsigned_to_nat(0u);
v___x_5587_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5588_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5589_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5590_ = lean_box(0);
lean_inc(v___x_5572_);
v___x_5591_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5591_, 0, v___x_5583_);
lean_ctor_set(v___x_5591_, 1, v___x_5572_);
lean_ctor_set(v___x_5591_, 2, v___x_5588_);
lean_ctor_set(v___x_5591_, 3, v___x_5589_);
lean_ctor_set(v___x_5591_, 4, v___x_5590_);
lean_ctor_set(v___x_5591_, 5, v___x_5586_);
lean_ctor_set(v___x_5591_, 6, v___x_5590_);
lean_ctor_set_uint8(v___x_5591_, sizeof(void*)*7, v___x_5581_);
lean_ctor_set_uint8(v___x_5591_, sizeof(void*)*7 + 1, v___x_5581_);
lean_ctor_set_uint8(v___x_5591_, sizeof(void*)*7 + 2, v___x_5581_);
lean_ctor_set_uint8(v___x_5591_, sizeof(void*)*7 + 3, v___x_5582_);
v___x_5592_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5593_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5594_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5595_, 0, v___x_5592_);
lean_ctor_set(v___x_5595_, 1, v___x_5593_);
lean_ctor_set(v___x_5595_, 2, v___x_5572_);
lean_ctor_set(v___x_5595_, 3, v___x_5587_);
lean_ctor_set(v___x_5595_, 4, v___x_5594_);
v___x_5596_ = lean_st_mk_ref(v___x_5595_);
lean_inc(v___y_5575_);
lean_inc_ref(v___y_5574_);
lean_inc(v___x_5596_);
v___x_5597_ = lean_get_congr_match_equations_for(v_val_5580_, v___x_5591_, v___x_5596_, v___y_5574_, v___y_5575_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5606_; 
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5606_ == 0)
{
lean_object* v_unused_5607_; 
v_unused_5607_ = lean_ctor_get(v___x_5597_, 0);
lean_dec(v_unused_5607_);
v___x_5599_ = v___x_5597_;
v_isShared_5600_ = v_isSharedCheck_5606_;
goto v_resetjp_5598_;
}
else
{
lean_dec(v___x_5597_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5606_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5604_; 
v___x_5601_ = lean_st_ref_get(v___x_5596_);
lean_dec(v___x_5596_);
lean_dec(v___x_5601_);
v___x_5602_ = lean_box(v___x_5582_);
if (v_isShared_5600_ == 0)
{
lean_ctor_set(v___x_5599_, 0, v___x_5602_);
v___x_5604_ = v___x_5599_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v___x_5602_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
}
}
}
else
{
lean_dec(v___x_5596_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5615_; 
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5615_ == 0)
{
lean_object* v_unused_5616_; 
v_unused_5616_ = lean_ctor_get(v___x_5597_, 0);
lean_dec(v_unused_5616_);
v___x_5609_ = v___x_5597_;
v_isShared_5610_ = v_isSharedCheck_5615_;
goto v_resetjp_5608_;
}
else
{
lean_dec(v___x_5597_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5615_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5611_; lean_object* v___x_5613_; 
v___x_5611_ = lean_box(v___x_5582_);
if (v_isShared_5610_ == 0)
{
lean_ctor_set_tag(v___x_5609_, 0);
lean_ctor_set(v___x_5609_, 0, v___x_5611_);
v___x_5613_ = v___x_5609_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v___x_5611_);
v___x_5613_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
return v___x_5613_;
}
}
}
else
{
lean_object* v_a_5617_; lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5624_; 
v_a_5617_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5624_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5624_ == 0)
{
v___x_5619_ = v___x_5597_;
v_isShared_5620_ = v_isSharedCheck_5624_;
goto v_resetjp_5618_;
}
else
{
lean_inc(v_a_5617_);
lean_dec(v___x_5597_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5624_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v___x_5622_; 
if (v_isShared_5620_ == 0)
{
v___x_5622_ = v___x_5619_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_a_5617_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
}
}
else
{
uint8_t v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; 
lean_dec(v___x_5579_);
lean_dec(v___x_5572_);
v___x_5625_ = 0;
v___x_5626_ = lean_box(v___x_5625_);
v___x_5627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5627_, 0, v___x_5626_);
return v___x_5627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5628_, lean_object* v_name_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_){
_start:
{
lean_object* v_res_5633_; 
v_res_5633_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5628_, v_name_5629_, v___y_5630_, v___y_5631_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
return v_res_5633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5637_; lean_object* v___x_5638_; 
v___f_5637_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5638_ = l_Lean_registerReservedNameAction(v___f_5637_);
return v___x_5638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5639_){
_start:
{
lean_object* v_res_5640_; 
v_res_5640_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5640_;
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
