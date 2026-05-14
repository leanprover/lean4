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
lean_object* v_ref_1311_; lean_object* v___x_1312_; lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1358_; 
v_ref_1311_ = lean_ctor_get(v___y_1308_, 5);
v___x_1312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1358_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1358_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1317_; lean_object* v_traceState_1318_; lean_object* v_env_1319_; lean_object* v_nextMacroScope_1320_; lean_object* v_ngen_1321_; lean_object* v_auxDeclNGen_1322_; lean_object* v_cache_1323_; lean_object* v_messages_1324_; lean_object* v_infoState_1325_; lean_object* v_snapshotTasks_1326_; lean_object* v_newDecls_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1357_; 
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
v_newDecls_1327_ = lean_ctor_get(v___x_1317_, 9);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1329_ = v___x_1317_;
v_isShared_1330_ = v_isSharedCheck_1357_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_newDecls_1327_);
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
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1357_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
uint64_t v_tid_1331_; lean_object* v_traces_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1356_; 
v_tid_1331_ = lean_ctor_get_uint64(v_traceState_1318_, sizeof(void*)*1);
v_traces_1332_ = lean_ctor_get(v_traceState_1318_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_traceState_1318_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1334_ = v_traceState_1318_;
v_isShared_1335_ = v_isSharedCheck_1356_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_traces_1332_);
lean_dec(v_traceState_1318_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1356_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; double v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0);
v___x_1338_ = 0;
v___x_1339_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1));
v___x_1340_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1340_, 0, v_cls_1304_);
lean_ctor_set(v___x_1340_, 1, v___x_1336_);
lean_ctor_set(v___x_1340_, 2, v___x_1339_);
lean_ctor_set_float(v___x_1340_, sizeof(void*)*3, v___x_1337_);
lean_ctor_set_float(v___x_1340_, sizeof(void*)*3 + 8, v___x_1337_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*3 + 16, v___x_1338_);
v___x_1341_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2));
v___x_1342_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v_a_1313_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
lean_inc(v_ref_1311_);
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v_ref_1311_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = l_Lean_PersistentArray_push___redArg(v_traces_1332_, v___x_1343_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1344_);
v___x_1346_ = v___x_1334_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1344_);
lean_ctor_set_uint64(v_reuseFailAlloc_1355_, sizeof(void*)*1, v_tid_1331_);
v___x_1346_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1348_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 4, v___x_1346_);
v___x_1348_ = v___x_1329_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_env_1319_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_nextMacroScope_1320_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_ngen_1321_);
lean_ctor_set(v_reuseFailAlloc_1354_, 3, v_auxDeclNGen_1322_);
lean_ctor_set(v_reuseFailAlloc_1354_, 4, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1354_, 5, v_cache_1323_);
lean_ctor_set(v_reuseFailAlloc_1354_, 6, v_messages_1324_);
lean_ctor_set(v_reuseFailAlloc_1354_, 7, v_infoState_1325_);
lean_ctor_set(v_reuseFailAlloc_1354_, 8, v_snapshotTasks_1326_);
lean_ctor_set(v_reuseFailAlloc_1354_, 9, v_newDecls_1327_);
v___x_1348_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1349_ = lean_st_ref_set(v___y_1309_, v___x_1348_);
v___x_1350_ = lean_box(0);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1350_);
v___x_1352_ = v___x_1315_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object* v_cls_1359_, lean_object* v_msg_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1359_, v_msg_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
return v_res_1366_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0));
v___x_1369_ = l_Lean_stringToMessageData(v___x_1368_);
return v___x_1369_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2));
v___x_1372_ = l_Lean_stringToMessageData(v___x_1371_);
return v___x_1372_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4));
v___x_1375_ = l_Lean_stringToMessageData(v___x_1374_);
return v___x_1375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
return v___x_1378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16(void){
_start:
{
lean_object* v_cls_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_cls_1392_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1393_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15));
v___x_1394_ = l_Lean_Name_append(v___x_1393_, v_cls_1392_);
return v___x_1394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18(void){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17));
v___x_1397_ = l_Lean_stringToMessageData(v___x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1398_, lean_object* v_mvarId_1399_, lean_object* v_depth_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v_a_1411_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; uint8_t v___y_1448_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; uint8_t v___y_1473_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v_a_1497_; lean_object* v___y_1501_; uint8_t v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; uint8_t v___y_1509_; lean_object* v___y_1544_; uint8_t v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v_a_1551_; lean_object* v___y_1555_; uint8_t v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; uint8_t v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; uint8_t v___y_1574_; lean_object* v___y_1598_; uint8_t v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; uint8_t v___y_1606_; lean_object* v___y_1623_; uint8_t v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; uint8_t v___y_1631_; lean_object* v___y_1648_; uint8_t v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; uint8_t v___y_1656_; lean_object* v___y_1674_; uint8_t v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; uint8_t v___y_1682_; lean_object* v___y_1703_; uint8_t v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; uint8_t v___y_1711_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v_fileName_1762_; lean_object* v_fileMap_1763_; lean_object* v_options_1764_; lean_object* v_currRecDepth_1765_; lean_object* v_maxRecDepth_1766_; lean_object* v_ref_1767_; lean_object* v_currNamespace_1768_; lean_object* v_openDecls_1769_; lean_object* v_initHeartbeats_1770_; lean_object* v_maxHeartbeats_1771_; lean_object* v_quotContext_1772_; lean_object* v_currMacroScope_1773_; uint8_t v_diag_1774_; lean_object* v_cancelTk_x3f_1775_; uint8_t v_suppressElabErrors_1776_; lean_object* v_inheritedTraceOptions_1777_; lean_object* v_cls_1778_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_fileName_1762_ = lean_ctor_get(v_a_1403_, 0);
v_fileMap_1763_ = lean_ctor_get(v_a_1403_, 1);
v_options_1764_ = lean_ctor_get(v_a_1403_, 2);
v_currRecDepth_1765_ = lean_ctor_get(v_a_1403_, 3);
v_maxRecDepth_1766_ = lean_ctor_get(v_a_1403_, 4);
v_ref_1767_ = lean_ctor_get(v_a_1403_, 5);
v_currNamespace_1768_ = lean_ctor_get(v_a_1403_, 6);
v_openDecls_1769_ = lean_ctor_get(v_a_1403_, 7);
v_initHeartbeats_1770_ = lean_ctor_get(v_a_1403_, 8);
v_maxHeartbeats_1771_ = lean_ctor_get(v_a_1403_, 9);
v_quotContext_1772_ = lean_ctor_get(v_a_1403_, 10);
v_currMacroScope_1773_ = lean_ctor_get(v_a_1403_, 11);
v_diag_1774_ = lean_ctor_get_uint8(v_a_1403_, sizeof(void*)*14);
v_cancelTk_x3f_1775_ = lean_ctor_get(v_a_1403_, 12);
v_suppressElabErrors_1776_ = lean_ctor_get_uint8(v_a_1403_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1777_ = lean_ctor_get(v_a_1403_, 13);
v_cls_1778_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_nat_dec_eq(v_maxRecDepth_1766_, v___x_1790_);
if (v___x_1791_ == 0)
{
uint8_t v___x_1792_; 
v___x_1792_ = lean_nat_dec_eq(v_currRecDepth_1765_, v_maxRecDepth_1766_);
if (v___x_1792_ == 0)
{
goto v___jp_1779_;
}
else
{
lean_object* v___x_1793_; 
lean_dec(v_mvarId_1399_);
lean_dec(v_matchDeclName_1398_);
lean_inc(v_ref_1767_);
v___x_1793_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1767_);
return v___x_1793_;
}
}
else
{
goto v___jp_1779_;
}
v___jp_1406_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_array_get_size(v_a_1411_);
v___x_1414_ = lean_box(0);
v___x_1415_ = lean_nat_dec_lt(v___x_1412_, v___x_1413_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_dec_ref(v_a_1411_);
lean_dec_ref(v___y_1408_);
lean_dec(v_matchDeclName_1398_);
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
return v___x_1416_;
}
else
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_le(v___x_1413_, v___x_1413_);
if (v___x_1417_ == 0)
{
if (v___x_1415_ == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref(v_a_1411_);
lean_dec_ref(v___y_1408_);
lean_dec(v_matchDeclName_1398_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1414_);
return v___x_1418_;
}
else
{
size_t v___x_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = lean_usize_of_nat(v___x_1413_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1400_, v_matchDeclName_1398_, v_a_1411_, v___x_1419_, v___x_1420_, v___x_1414_, v___y_1407_, v___y_1410_, v___y_1408_, v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec_ref(v_a_1411_);
return v___x_1421_;
}
}
else
{
size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = lean_usize_of_nat(v___x_1413_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1400_, v_matchDeclName_1398_, v_a_1411_, v___x_1422_, v___x_1423_, v___x_1414_, v___y_1407_, v___y_1410_, v___y_1408_, v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec_ref(v_a_1411_);
return v___x_1424_;
}
}
}
v___jp_1425_:
{
if (lean_obj_tag(v___y_1430_) == 0)
{
lean_object* v_a_1431_; 
v_a_1431_ = lean_ctor_get(v___y_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___y_1430_);
v___y_1407_ = v___y_1426_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
v___y_1410_ = v___y_1429_;
v_a_1411_ = v_a_1431_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec_ref(v___y_1427_);
lean_dec(v_matchDeclName_1398_);
v_a_1432_ = lean_ctor_get(v___y_1430_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___y_1430_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___y_1430_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___y_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
v___jp_1440_:
{
if (v___y_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec_ref(v___y_1445_);
v___x_1449_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1443_, v___y_1447_, v___y_1446_);
lean_dec_ref(v___y_1443_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1463_; 
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1449_, 0);
lean_dec(v_unused_1464_);
v___x_1451_ = v___x_1449_;
v_isShared_1452_ = v_isSharedCheck_1463_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v___x_1449_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1463_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1453_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1398_);
v___x_1454_ = l_Lean_MessageData_ofName(v_matchDeclName_1398_);
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
lean_ctor_set(v___x_1451_, 0, v___y_1441_);
v___x_1459_ = v___x_1451_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___y_1441_);
v___x_1459_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1457_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1460_, v___y_1442_, v___y_1447_, v___y_1444_, v___y_1446_);
v___y_1426_ = v___y_1442_;
v___y_1427_ = v___y_1444_;
v___y_1428_ = v___y_1446_;
v___y_1429_ = v___y_1447_;
v___y_1430_ = v___x_1461_;
goto v___jp_1425_;
}
}
}
else
{
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1441_);
lean_dec(v_matchDeclName_1398_);
return v___x_1449_;
}
}
else
{
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1441_);
v___y_1426_ = v___y_1442_;
v___y_1427_ = v___y_1444_;
v___y_1428_ = v___y_1446_;
v___y_1429_ = v___y_1447_;
v___y_1430_ = v___y_1445_;
goto v___jp_1425_;
}
}
v___jp_1465_:
{
if (v___y_1473_ == 0)
{
lean_object* v___x_1474_; 
lean_dec_ref(v___y_1470_);
v___x_1474_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1467_, v___y_1472_, v___y_1471_);
lean_dec_ref(v___y_1467_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v___x_1475_; 
lean_dec_ref(v___x_1474_);
v___x_1475_ = l_Lean_Meta_saveState___redArg(v___y_1472_, v___y_1471_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1475_);
lean_inc(v___y_1466_);
v___x_1477_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1466_, v___y_1468_, v___y_1472_, v___y_1469_, v___y_1471_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_dec(v_a_1476_);
lean_dec(v___y_1466_);
v___y_1426_ = v___y_1468_;
v___y_1427_ = v___y_1469_;
v___y_1428_ = v___y_1471_;
v___y_1429_ = v___y_1472_;
v___y_1430_ = v___x_1477_;
goto v___jp_1425_;
}
else
{
lean_object* v_a_1478_; uint8_t v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
v___x_1479_ = l_Lean_Exception_isInterrupt(v_a_1478_);
if (v___x_1479_ == 0)
{
uint8_t v___x_1480_; 
v___x_1480_ = l_Lean_Exception_isRuntime(v_a_1478_);
v___y_1441_ = v___y_1466_;
v___y_1442_ = v___y_1468_;
v___y_1443_ = v_a_1476_;
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___x_1477_;
v___y_1446_ = v___y_1471_;
v___y_1447_ = v___y_1472_;
v___y_1448_ = v___x_1480_;
goto v___jp_1440_;
}
else
{
lean_dec(v_a_1478_);
v___y_1441_ = v___y_1466_;
v___y_1442_ = v___y_1468_;
v___y_1443_ = v_a_1476_;
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___x_1477_;
v___y_1446_ = v___y_1471_;
v___y_1447_ = v___y_1472_;
v___y_1448_ = v___x_1479_;
goto v___jp_1440_;
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1466_);
lean_dec(v_matchDeclName_1398_);
v_a_1481_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1475_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1475_);
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
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1466_);
lean_dec(v_matchDeclName_1398_);
return v___x_1474_;
}
}
else
{
lean_object* v___x_1489_; 
lean_dec_ref(v___y_1469_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec(v_matchDeclName_1398_);
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___y_1470_);
return v___x_1489_;
}
}
v___jp_1490_:
{
uint8_t v___x_1498_; 
v___x_1498_ = l_Lean_Exception_isInterrupt(v_a_1497_);
if (v___x_1498_ == 0)
{
uint8_t v___x_1499_; 
lean_inc_ref(v_a_1497_);
v___x_1499_ = l_Lean_Exception_isRuntime(v_a_1497_);
v___y_1466_ = v___y_1492_;
v___y_1467_ = v___y_1491_;
v___y_1468_ = v___y_1493_;
v___y_1469_ = v___y_1494_;
v___y_1470_ = v_a_1497_;
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___y_1496_;
v___y_1473_ = v___x_1499_;
goto v___jp_1465_;
}
else
{
v___y_1466_ = v___y_1492_;
v___y_1467_ = v___y_1491_;
v___y_1468_ = v___y_1493_;
v___y_1469_ = v___y_1494_;
v___y_1470_ = v_a_1497_;
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___y_1496_;
v___y_1473_ = v___x_1498_;
goto v___jp_1465_;
}
}
v___jp_1500_:
{
if (v___y_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_dec_ref(v___y_1506_);
v___x_1510_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1505_, v___y_1508_, v___y_1507_);
lean_dec_ref(v___y_1505_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v___x_1511_; 
lean_dec_ref(v___x_1510_);
v___x_1511_ = l_Lean_Meta_saveState___redArg(v___y_1508_, v___y_1507_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref(v___x_1511_);
v___x_1513_ = lean_box(0);
lean_inc(v___y_1501_);
v___x_1514_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1501_, v___x_1513_, v___y_1502_, v___y_1503_, v___y_1508_, v___y_1504_, v___y_1507_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref(v___x_1514_);
if (lean_obj_tag(v_a_1515_) == 1)
{
lean_object* v_val_1516_; lean_object* v_fst_1517_; lean_object* v_snd_1518_; lean_object* v_mvarId_1519_; lean_object* v_fvarId_1520_; lean_object* v___x_1521_; 
v_val_1516_ = lean_ctor_get(v_a_1515_, 0);
lean_inc(v_val_1516_);
lean_dec_ref(v_a_1515_);
v_fst_1517_ = lean_ctor_get(v_val_1516_, 0);
lean_inc(v_fst_1517_);
v_snd_1518_ = lean_ctor_get(v_val_1516_, 1);
lean_inc(v_snd_1518_);
lean_dec(v_val_1516_);
v_mvarId_1519_ = lean_ctor_get(v_fst_1517_, 0);
lean_inc(v_mvarId_1519_);
v_fvarId_1520_ = lean_ctor_get(v_fst_1517_, 1);
lean_inc(v_fvarId_1520_);
lean_dec(v_fst_1517_);
v___x_1521_ = l_Lean_Meta_trySubst(v_mvarId_1519_, v_fvarId_1520_, v___y_1503_, v___y_1508_, v___y_1504_, v___y_1507_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v_mvarId_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v_a_1512_);
lean_dec(v___y_1501_);
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref(v___x_1521_);
v_mvarId_1523_ = lean_ctor_get(v_snd_1518_, 0);
lean_inc(v_mvarId_1523_);
lean_dec(v_snd_1518_);
v___x_1524_ = lean_unsigned_to_nat(2u);
v___x_1525_ = lean_mk_empty_array_with_capacity(v___x_1524_);
v___x_1526_ = lean_array_push(v___x_1525_, v_a_1522_);
v___x_1527_ = lean_array_push(v___x_1526_, v_mvarId_1523_);
v___y_1407_ = v___y_1503_;
v___y_1408_ = v___y_1504_;
v___y_1409_ = v___y_1507_;
v___y_1410_ = v___y_1508_;
v_a_1411_ = v___x_1527_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1528_; 
lean_dec(v_snd_1518_);
v_a_1528_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1528_);
lean_dec_ref(v___x_1521_);
v___y_1491_ = v_a_1512_;
v___y_1492_ = v___y_1501_;
v___y_1493_ = v___y_1503_;
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1507_;
v___y_1496_ = v___y_1508_;
v_a_1497_ = v_a_1528_;
goto v___jp_1490_;
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_a_1515_);
v___x_1529_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1530_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1529_, v___y_1503_, v___y_1508_, v___y_1504_, v___y_1507_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; 
lean_dec(v_a_1512_);
lean_dec(v___y_1501_);
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref(v___x_1530_);
v___y_1407_ = v___y_1503_;
v___y_1408_ = v___y_1504_;
v___y_1409_ = v___y_1507_;
v___y_1410_ = v___y_1508_;
v_a_1411_ = v_a_1531_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1532_; 
v_a_1532_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1532_);
lean_dec_ref(v___x_1530_);
v___y_1491_ = v_a_1512_;
v___y_1492_ = v___y_1501_;
v___y_1493_ = v___y_1503_;
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1507_;
v___y_1496_ = v___y_1508_;
v_a_1497_ = v_a_1532_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v_a_1533_; 
v_a_1533_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v___x_1514_);
v___y_1491_ = v_a_1512_;
v___y_1492_ = v___y_1501_;
v___y_1493_ = v___y_1503_;
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1507_;
v___y_1496_ = v___y_1508_;
v_a_1497_ = v_a_1533_;
goto v___jp_1490_;
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1501_);
lean_dec(v_matchDeclName_1398_);
v_a_1534_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1511_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1511_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1501_);
lean_dec(v_matchDeclName_1398_);
return v___x_1510_;
}
}
else
{
lean_object* v___x_1542_; 
lean_dec_ref(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1501_);
lean_dec(v_matchDeclName_1398_);
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___y_1506_);
return v___x_1542_;
}
}
v___jp_1543_:
{
uint8_t v___x_1552_; 
v___x_1552_ = l_Lean_Exception_isInterrupt(v_a_1551_);
if (v___x_1552_ == 0)
{
uint8_t v___x_1553_; 
lean_inc_ref(v_a_1551_);
v___x_1553_ = l_Lean_Exception_isRuntime(v_a_1551_);
v___y_1501_ = v___y_1544_;
v___y_1502_ = v___y_1545_;
v___y_1503_ = v___y_1546_;
v___y_1504_ = v___y_1548_;
v___y_1505_ = v___y_1547_;
v___y_1506_ = v_a_1551_;
v___y_1507_ = v___y_1549_;
v___y_1508_ = v___y_1550_;
v___y_1509_ = v___x_1553_;
goto v___jp_1500_;
}
else
{
v___y_1501_ = v___y_1544_;
v___y_1502_ = v___y_1545_;
v___y_1503_ = v___y_1546_;
v___y_1504_ = v___y_1548_;
v___y_1505_ = v___y_1547_;
v___y_1506_ = v_a_1551_;
v___y_1507_ = v___y_1549_;
v___y_1508_ = v___y_1550_;
v___y_1509_ = v___x_1552_;
goto v___jp_1500_;
}
}
v___jp_1554_:
{
if (lean_obj_tag(v___y_1562_) == 0)
{
lean_object* v_a_1563_; 
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1555_);
v_a_1563_ = lean_ctor_get(v___y_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref(v___y_1562_);
v___y_1407_ = v___y_1557_;
v___y_1408_ = v___y_1559_;
v___y_1409_ = v___y_1560_;
v___y_1410_ = v___y_1561_;
v_a_1411_ = v_a_1563_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1564_; 
v_a_1564_ = lean_ctor_get(v___y_1562_, 0);
lean_inc(v_a_1564_);
lean_dec_ref(v___y_1562_);
v___y_1544_ = v___y_1555_;
v___y_1545_ = v___y_1556_;
v___y_1546_ = v___y_1557_;
v___y_1547_ = v___y_1558_;
v___y_1548_ = v___y_1559_;
v___y_1549_ = v___y_1560_;
v___y_1550_ = v___y_1561_;
v_a_1551_ = v_a_1564_;
goto v___jp_1543_;
}
}
v___jp_1565_:
{
if (v___y_1574_ == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref(v___y_1566_);
v___x_1575_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1568_, v___y_1573_, v___y_1572_);
lean_dec_ref(v___y_1568_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref(v___x_1575_);
v___x_1576_ = l_Lean_Meta_saveState___redArg(v___y_1573_, v___y_1572_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref(v___x_1576_);
lean_inc(v___y_1567_);
v___x_1578_ = l_Lean_Meta_simpIfTarget(v___y_1567_, v___y_1569_, v___y_1569_, v___y_1570_, v___y_1573_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; uint8_t v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v___x_1578_);
v___x_1580_ = l_Lean_instBEqMVarId_beq(v_a_1579_, v___y_1567_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_box(0);
v___x_1582_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1579_, v___x_1581_, v___y_1570_, v___y_1573_, v___y_1571_, v___y_1572_);
v___y_1555_ = v___y_1567_;
v___y_1556_ = v___y_1569_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v_a_1577_;
v___y_1559_ = v___y_1571_;
v___y_1560_ = v___y_1572_;
v___y_1561_ = v___y_1573_;
v___y_1562_ = v___x_1582_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1584_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1583_, v___y_1570_, v___y_1573_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1579_, v_a_1585_, v___y_1570_, v___y_1573_, v___y_1571_, v___y_1572_);
v___y_1555_ = v___y_1567_;
v___y_1556_ = v___y_1569_;
v___y_1557_ = v___y_1570_;
v___y_1558_ = v_a_1577_;
v___y_1559_ = v___y_1571_;
v___y_1560_ = v___y_1572_;
v___y_1561_ = v___y_1573_;
v___y_1562_ = v___x_1586_;
goto v___jp_1554_;
}
else
{
lean_object* v_a_1587_; 
lean_dec(v_a_1579_);
v_a_1587_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1584_);
v___y_1544_ = v___y_1567_;
v___y_1545_ = v___y_1569_;
v___y_1546_ = v___y_1570_;
v___y_1547_ = v_a_1577_;
v___y_1548_ = v___y_1571_;
v___y_1549_ = v___y_1572_;
v___y_1550_ = v___y_1573_;
v_a_1551_ = v_a_1587_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v_a_1588_; 
v_a_1588_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v___x_1578_);
v___y_1544_ = v___y_1567_;
v___y_1545_ = v___y_1569_;
v___y_1546_ = v___y_1570_;
v___y_1547_ = v_a_1577_;
v___y_1548_ = v___y_1571_;
v___y_1549_ = v___y_1572_;
v___y_1550_ = v___y_1573_;
v_a_1551_ = v_a_1588_;
goto v___jp_1543_;
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1567_);
lean_dec(v_matchDeclName_1398_);
v_a_1589_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1576_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1576_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1567_);
lean_dec(v_matchDeclName_1398_);
return v___x_1575_;
}
}
else
{
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
v___y_1426_ = v___y_1570_;
v___y_1427_ = v___y_1571_;
v___y_1428_ = v___y_1572_;
v___y_1429_ = v___y_1573_;
v___y_1430_ = v___y_1566_;
goto v___jp_1425_;
}
}
v___jp_1597_:
{
if (v___y_1606_ == 0)
{
lean_object* v___x_1607_; 
lean_dec_ref(v___y_1600_);
v___x_1607_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1603_, v___y_1605_, v___y_1604_);
lean_dec_ref(v___y_1603_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref(v___x_1607_);
v___x_1608_ = l_Lean_Meta_saveState___redArg(v___y_1605_, v___y_1604_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1610_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref(v___x_1608_);
lean_inc(v___y_1598_);
v___x_1610_ = l_Lean_Meta_splitSparseCasesOn(v___y_1598_, v___y_1601_, v___y_1605_, v___y_1602_, v___y_1604_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_dec(v_a_1609_);
lean_dec(v___y_1598_);
v___y_1426_ = v___y_1601_;
v___y_1427_ = v___y_1602_;
v___y_1428_ = v___y_1604_;
v___y_1429_ = v___y_1605_;
v___y_1430_ = v___x_1610_;
goto v___jp_1425_;
}
else
{
lean_object* v_a_1611_; uint8_t v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
v___x_1612_ = l_Lean_Exception_isInterrupt(v_a_1611_);
if (v___x_1612_ == 0)
{
uint8_t v___x_1613_; 
v___x_1613_ = l_Lean_Exception_isRuntime(v_a_1611_);
v___y_1566_ = v___x_1610_;
v___y_1567_ = v___y_1598_;
v___y_1568_ = v_a_1609_;
v___y_1569_ = v___y_1599_;
v___y_1570_ = v___y_1601_;
v___y_1571_ = v___y_1602_;
v___y_1572_ = v___y_1604_;
v___y_1573_ = v___y_1605_;
v___y_1574_ = v___x_1613_;
goto v___jp_1565_;
}
else
{
lean_dec(v_a_1611_);
v___y_1566_ = v___x_1610_;
v___y_1567_ = v___y_1598_;
v___y_1568_ = v_a_1609_;
v___y_1569_ = v___y_1599_;
v___y_1570_ = v___y_1601_;
v___y_1571_ = v___y_1602_;
v___y_1572_ = v___y_1604_;
v___y_1573_ = v___y_1605_;
v___y_1574_ = v___x_1612_;
goto v___jp_1565_;
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1598_);
lean_dec(v_matchDeclName_1398_);
v_a_1614_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1608_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1608_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1598_);
lean_dec(v_matchDeclName_1398_);
return v___x_1607_;
}
}
else
{
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1598_);
v___y_1426_ = v___y_1601_;
v___y_1427_ = v___y_1602_;
v___y_1428_ = v___y_1604_;
v___y_1429_ = v___y_1605_;
v___y_1430_ = v___y_1600_;
goto v___jp_1425_;
}
}
v___jp_1622_:
{
if (v___y_1631_ == 0)
{
lean_object* v___x_1632_; 
lean_dec_ref(v___y_1627_);
v___x_1632_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1628_, v___y_1630_, v___y_1629_);
lean_dec_ref(v___y_1628_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1633_; 
lean_dec_ref(v___x_1632_);
v___x_1633_ = l_Lean_Meta_saveState___redArg(v___y_1630_, v___y_1629_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref(v___x_1633_);
lean_inc(v___y_1623_);
v___x_1635_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1623_, v___y_1625_, v___y_1630_, v___y_1626_, v___y_1629_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_dec(v_a_1634_);
lean_dec(v___y_1623_);
v___y_1426_ = v___y_1625_;
v___y_1427_ = v___y_1626_;
v___y_1428_ = v___y_1629_;
v___y_1429_ = v___y_1630_;
v___y_1430_ = v___x_1635_;
goto v___jp_1425_;
}
else
{
lean_object* v_a_1636_; uint8_t v___x_1637_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
v___x_1637_ = l_Lean_Exception_isInterrupt(v_a_1636_);
if (v___x_1637_ == 0)
{
uint8_t v___x_1638_; 
v___x_1638_ = l_Lean_Exception_isRuntime(v_a_1636_);
v___y_1598_ = v___y_1623_;
v___y_1599_ = v___y_1624_;
v___y_1600_ = v___x_1635_;
v___y_1601_ = v___y_1625_;
v___y_1602_ = v___y_1626_;
v___y_1603_ = v_a_1634_;
v___y_1604_ = v___y_1629_;
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___x_1638_;
goto v___jp_1597_;
}
else
{
lean_dec(v_a_1636_);
v___y_1598_ = v___y_1623_;
v___y_1599_ = v___y_1624_;
v___y_1600_ = v___x_1635_;
v___y_1601_ = v___y_1625_;
v___y_1602_ = v___y_1626_;
v___y_1603_ = v_a_1634_;
v___y_1604_ = v___y_1629_;
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___x_1637_;
goto v___jp_1597_;
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1623_);
lean_dec(v_matchDeclName_1398_);
v_a_1639_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1633_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1633_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1623_);
lean_dec(v_matchDeclName_1398_);
return v___x_1632_;
}
}
else
{
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1623_);
v___y_1426_ = v___y_1625_;
v___y_1427_ = v___y_1626_;
v___y_1428_ = v___y_1629_;
v___y_1429_ = v___y_1630_;
v___y_1430_ = v___y_1627_;
goto v___jp_1425_;
}
}
v___jp_1647_:
{
if (v___y_1656_ == 0)
{
lean_object* v___x_1657_; 
lean_dec_ref(v___y_1653_);
v___x_1657_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1651_, v___y_1655_, v___y_1654_);
lean_dec_ref(v___y_1651_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref(v___x_1657_);
v___x_1658_ = l_Lean_Meta_saveState___redArg(v___y_1655_, v___y_1654_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref(v___x_1658_);
lean_inc(v___y_1648_);
v___x_1660_ = l_Lean_Meta_casesOnStuckLHS(v___y_1648_, v___y_1650_, v___y_1655_, v___y_1652_, v___y_1654_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_dec(v_a_1659_);
lean_dec(v___y_1648_);
v___y_1426_ = v___y_1650_;
v___y_1427_ = v___y_1652_;
v___y_1428_ = v___y_1654_;
v___y_1429_ = v___y_1655_;
v___y_1430_ = v___x_1660_;
goto v___jp_1425_;
}
else
{
lean_object* v_a_1661_; uint8_t v___x_1662_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
v___x_1662_ = l_Lean_Exception_isInterrupt(v_a_1661_);
if (v___x_1662_ == 0)
{
uint8_t v___x_1663_; 
v___x_1663_ = l_Lean_Exception_isRuntime(v_a_1661_);
v___y_1623_ = v___y_1648_;
v___y_1624_ = v___y_1649_;
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1652_;
v___y_1627_ = v___x_1660_;
v___y_1628_ = v_a_1659_;
v___y_1629_ = v___y_1654_;
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___x_1663_;
goto v___jp_1622_;
}
else
{
lean_dec(v_a_1661_);
v___y_1623_ = v___y_1648_;
v___y_1624_ = v___y_1649_;
v___y_1625_ = v___y_1650_;
v___y_1626_ = v___y_1652_;
v___y_1627_ = v___x_1660_;
v___y_1628_ = v_a_1659_;
v___y_1629_ = v___y_1654_;
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___x_1662_;
goto v___jp_1622_;
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1648_);
lean_dec(v_matchDeclName_1398_);
v_a_1664_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1658_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1658_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1648_);
lean_dec(v_matchDeclName_1398_);
return v___x_1657_;
}
}
else
{
lean_object* v___x_1672_; 
lean_dec_ref(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1648_);
lean_dec(v_matchDeclName_1398_);
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___y_1653_);
return v___x_1672_;
}
}
v___jp_1673_:
{
if (v___y_1682_ == 0)
{
lean_object* v___x_1683_; 
lean_dec_ref(v___y_1677_);
v___x_1683_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1679_, v___y_1681_, v___y_1680_);
lean_dec_ref(v___y_1679_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref(v___x_1683_);
v___x_1684_ = l_Lean_Meta_saveState___redArg(v___y_1681_, v___y_1680_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1686_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref(v___x_1684_);
lean_inc(v___y_1674_);
v___x_1686_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1674_, v___y_1676_, v___y_1681_, v___y_1678_, v___y_1680_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec(v_a_1685_);
lean_dec(v___y_1674_);
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_mk_empty_array_with_capacity(v___x_1688_);
v___x_1690_ = lean_array_push(v___x_1689_, v_a_1687_);
v___y_1407_ = v___y_1676_;
v___y_1408_ = v___y_1678_;
v___y_1409_ = v___y_1680_;
v___y_1410_ = v___y_1681_;
v_a_1411_ = v___x_1690_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1691_; uint8_t v___x_1692_; 
v_a_1691_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1686_);
v___x_1692_ = l_Lean_Exception_isInterrupt(v_a_1691_);
if (v___x_1692_ == 0)
{
uint8_t v___x_1693_; 
lean_inc(v_a_1691_);
v___x_1693_ = l_Lean_Exception_isRuntime(v_a_1691_);
v___y_1648_ = v___y_1674_;
v___y_1649_ = v___y_1675_;
v___y_1650_ = v___y_1676_;
v___y_1651_ = v_a_1685_;
v___y_1652_ = v___y_1678_;
v___y_1653_ = v_a_1691_;
v___y_1654_ = v___y_1680_;
v___y_1655_ = v___y_1681_;
v___y_1656_ = v___x_1693_;
goto v___jp_1647_;
}
else
{
v___y_1648_ = v___y_1674_;
v___y_1649_ = v___y_1675_;
v___y_1650_ = v___y_1676_;
v___y_1651_ = v_a_1685_;
v___y_1652_ = v___y_1678_;
v___y_1653_ = v_a_1691_;
v___y_1654_ = v___y_1680_;
v___y_1655_ = v___y_1681_;
v___y_1656_ = v___x_1692_;
goto v___jp_1647_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1674_);
lean_dec(v_matchDeclName_1398_);
v_a_1694_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1684_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1684_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1674_);
lean_dec(v_matchDeclName_1398_);
return v___x_1683_;
}
}
else
{
lean_dec_ref(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1674_);
lean_dec(v_matchDeclName_1398_);
return v___y_1677_;
}
}
v___jp_1702_:
{
if (v___y_1711_ == 0)
{
lean_object* v___x_1712_; 
lean_dec_ref(v___y_1708_);
v___x_1712_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1706_, v___y_1710_, v___y_1709_);
lean_dec_ref(v___y_1706_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec_ref(v___x_1712_);
v___x_1713_ = lean_unsigned_to_nat(16u);
v___x_1714_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*1, v___y_1704_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*1 + 1, v___y_1704_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*1 + 2, v___y_1704_);
v___x_1715_ = l_Lean_Meta_saveState___redArg(v___y_1710_, v___y_1709_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1717_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref(v___x_1715_);
lean_inc(v___y_1703_);
v___x_1717_ = l_Lean_MVarId_contradiction(v___y_1703_, v___x_1714_, v___y_1705_, v___y_1710_, v___y_1707_, v___y_1709_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v___x_1718_; 
lean_dec_ref(v___x_1717_);
lean_dec(v_a_1716_);
lean_dec(v___y_1703_);
v___x_1718_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1407_ = v___y_1705_;
v___y_1408_ = v___y_1707_;
v___y_1409_ = v___y_1709_;
v___y_1410_ = v___y_1710_;
v_a_1411_ = v___x_1718_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1719_; uint8_t v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1719_);
v___x_1720_ = l_Lean_Exception_isInterrupt(v_a_1719_);
if (v___x_1720_ == 0)
{
uint8_t v___x_1721_; 
v___x_1721_ = l_Lean_Exception_isRuntime(v_a_1719_);
v___y_1674_ = v___y_1703_;
v___y_1675_ = v___y_1704_;
v___y_1676_ = v___y_1705_;
v___y_1677_ = v___x_1717_;
v___y_1678_ = v___y_1707_;
v___y_1679_ = v_a_1716_;
v___y_1680_ = v___y_1709_;
v___y_1681_ = v___y_1710_;
v___y_1682_ = v___x_1721_;
goto v___jp_1673_;
}
else
{
lean_dec(v_a_1719_);
v___y_1674_ = v___y_1703_;
v___y_1675_ = v___y_1704_;
v___y_1676_ = v___y_1705_;
v___y_1677_ = v___x_1717_;
v___y_1678_ = v___y_1707_;
v___y_1679_ = v_a_1716_;
v___y_1680_ = v___y_1709_;
v___y_1681_ = v___y_1710_;
v___y_1682_ = v___x_1720_;
goto v___jp_1673_;
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec_ref(v___x_1714_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1703_);
lean_dec(v_matchDeclName_1398_);
v_a_1722_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1715_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1715_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
else
{
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1703_);
lean_dec(v_matchDeclName_1398_);
return v___x_1712_;
}
}
else
{
lean_dec_ref(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1703_);
lean_dec(v_matchDeclName_1398_);
return v___y_1708_;
}
}
v___jp_1730_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1736_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1399_, v___x_1735_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1738_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = l_Lean_Meta_saveState___redArg(v___y_1732_, v___y_1734_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; uint8_t v___x_1740_; lean_object* v___x_1741_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___x_1738_);
v___x_1740_ = 1;
lean_inc(v_a_1737_);
v___x_1741_ = l_Lean_MVarId_refl(v_a_1737_, v___x_1740_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v___x_1742_; 
lean_dec_ref(v___x_1741_);
lean_dec(v_a_1739_);
lean_dec(v_a_1737_);
v___x_1742_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1407_ = v___y_1731_;
v___y_1408_ = v___y_1733_;
v___y_1409_ = v___y_1734_;
v___y_1410_ = v___y_1732_;
v_a_1411_ = v___x_1742_;
goto v___jp_1406_;
}
else
{
lean_object* v_a_1743_; uint8_t v___x_1744_; 
v_a_1743_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1743_);
v___x_1744_ = l_Lean_Exception_isInterrupt(v_a_1743_);
if (v___x_1744_ == 0)
{
uint8_t v___x_1745_; 
v___x_1745_ = l_Lean_Exception_isRuntime(v_a_1743_);
v___y_1703_ = v_a_1737_;
v___y_1704_ = v___x_1740_;
v___y_1705_ = v___y_1731_;
v___y_1706_ = v_a_1739_;
v___y_1707_ = v___y_1733_;
v___y_1708_ = v___x_1741_;
v___y_1709_ = v___y_1734_;
v___y_1710_ = v___y_1732_;
v___y_1711_ = v___x_1745_;
goto v___jp_1702_;
}
else
{
lean_dec(v_a_1743_);
v___y_1703_ = v_a_1737_;
v___y_1704_ = v___x_1740_;
v___y_1705_ = v___y_1731_;
v___y_1706_ = v_a_1739_;
v___y_1707_ = v___y_1733_;
v___y_1708_ = v___x_1741_;
v___y_1709_ = v___y_1734_;
v___y_1710_ = v___y_1732_;
v___y_1711_ = v___x_1744_;
goto v___jp_1702_;
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_a_1737_);
lean_dec_ref(v___y_1733_);
lean_dec(v_matchDeclName_1398_);
v_a_1746_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1738_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1738_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v___y_1733_);
lean_dec(v_matchDeclName_1398_);
v_a_1754_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1736_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1736_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
v___jp_1779_:
{
uint8_t v_hasTrace_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_hasTrace_1780_ = lean_ctor_get_uint8(v_options_1764_, sizeof(void*)*1);
v___x_1781_ = lean_unsigned_to_nat(1u);
v___x_1782_ = lean_nat_add(v_currRecDepth_1765_, v___x_1781_);
lean_inc_ref(v_inheritedTraceOptions_1777_);
lean_inc(v_cancelTk_x3f_1775_);
lean_inc(v_currMacroScope_1773_);
lean_inc(v_quotContext_1772_);
lean_inc(v_maxHeartbeats_1771_);
lean_inc(v_initHeartbeats_1770_);
lean_inc(v_openDecls_1769_);
lean_inc(v_currNamespace_1768_);
lean_inc(v_ref_1767_);
lean_inc(v_maxRecDepth_1766_);
lean_inc_ref(v_options_1764_);
lean_inc_ref(v_fileMap_1763_);
lean_inc_ref(v_fileName_1762_);
v___x_1783_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1783_, 0, v_fileName_1762_);
lean_ctor_set(v___x_1783_, 1, v_fileMap_1763_);
lean_ctor_set(v___x_1783_, 2, v_options_1764_);
lean_ctor_set(v___x_1783_, 3, v___x_1782_);
lean_ctor_set(v___x_1783_, 4, v_maxRecDepth_1766_);
lean_ctor_set(v___x_1783_, 5, v_ref_1767_);
lean_ctor_set(v___x_1783_, 6, v_currNamespace_1768_);
lean_ctor_set(v___x_1783_, 7, v_openDecls_1769_);
lean_ctor_set(v___x_1783_, 8, v_initHeartbeats_1770_);
lean_ctor_set(v___x_1783_, 9, v_maxHeartbeats_1771_);
lean_ctor_set(v___x_1783_, 10, v_quotContext_1772_);
lean_ctor_set(v___x_1783_, 11, v_currMacroScope_1773_);
lean_ctor_set(v___x_1783_, 12, v_cancelTk_x3f_1775_);
lean_ctor_set(v___x_1783_, 13, v_inheritedTraceOptions_1777_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*14, v_diag_1774_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*14 + 1, v_suppressElabErrors_1776_);
if (v_hasTrace_1780_ == 0)
{
v___y_1731_ = v_a_1401_;
v___y_1732_ = v_a_1402_;
v___y_1733_ = v___x_1783_;
v___y_1734_ = v_a_1404_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1785_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1777_, v_options_1764_, v___x_1784_);
if (v___x_1785_ == 0)
{
v___y_1731_ = v_a_1401_;
v___y_1732_ = v_a_1402_;
v___y_1733_ = v___x_1783_;
v___y_1734_ = v_a_1404_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1786_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1399_);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_mvarId_1399_);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1778_, v___x_1788_, v_a_1401_, v_a_1402_, v___x_1783_, v_a_1404_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_dec_ref(v___x_1789_);
v___y_1731_ = v_a_1401_;
v___y_1732_ = v_a_1402_;
v___y_1733_ = v___x_1783_;
v___y_1734_ = v_a_1404_;
goto v___jp_1730_;
}
else
{
lean_dec_ref(v___x_1783_);
lean_dec(v_mvarId_1399_);
lean_dec(v_matchDeclName_1398_);
return v___x_1789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1794_, lean_object* v_matchDeclName_1795_, lean_object* v_as_1796_, size_t v_i_1797_, size_t v_stop_1798_, lean_object* v_b_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
uint8_t v___x_1805_; 
v___x_1805_ = lean_usize_dec_eq(v_i_1797_, v_stop_1798_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1806_ = lean_array_uget_borrowed(v_as_1796_, v_i_1797_);
v___x_1807_ = lean_unsigned_to_nat(1u);
v___x_1808_ = lean_nat_add(v_depth_1794_, v___x_1807_);
lean_inc(v___x_1806_);
lean_inc(v_matchDeclName_1795_);
v___x_1809_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1795_, v___x_1806_, v___x_1808_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___x_1808_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; size_t v___x_1811_; size_t v___x_1812_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref(v___x_1809_);
v___x_1811_ = ((size_t)1ULL);
v___x_1812_ = lean_usize_add(v_i_1797_, v___x_1811_);
v_i_1797_ = v___x_1812_;
v_b_1799_ = v_a_1810_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1795_);
return v___x_1809_;
}
}
else
{
lean_object* v___x_1814_; 
lean_dec(v_matchDeclName_1795_);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_b_1799_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1815_, lean_object* v_matchDeclName_1816_, lean_object* v_as_1817_, lean_object* v_i_1818_, lean_object* v_stop_1819_, lean_object* v_b_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
size_t v_i_boxed_1826_; size_t v_stop_boxed_1827_; lean_object* v_res_1828_; 
v_i_boxed_1826_ = lean_unbox_usize(v_i_1818_);
lean_dec(v_i_1818_);
v_stop_boxed_1827_ = lean_unbox_usize(v_stop_1819_);
lean_dec(v_stop_1819_);
v_res_1828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1815_, v_matchDeclName_1816_, v_as_1817_, v_i_boxed_1826_, v_stop_boxed_1827_, v_b_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec_ref(v_as_1817_);
lean_dec(v_depth_1815_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1829_, lean_object* v_mvarId_1830_, lean_object* v_depth_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1829_, v_mvarId_1830_, v_depth_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_depth_1831_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v___x_1841_; 
v___x_1841_ = l_Lean_Expr_hasMVar(v_e_1838_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_e_1838_);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; lean_object* v_mctx_1844_; lean_object* v___x_1845_; lean_object* v_fst_1846_; lean_object* v_snd_1847_; lean_object* v___x_1848_; lean_object* v_cache_1849_; lean_object* v_zetaDeltaFVarIds_1850_; lean_object* v_postponed_1851_; lean_object* v_diag_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1861_; 
v___x_1843_ = lean_st_ref_get(v___y_1839_);
v_mctx_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc_ref(v_mctx_1844_);
lean_dec(v___x_1843_);
v___x_1845_ = l_Lean_instantiateMVarsCore(v_mctx_1844_, v_e_1838_);
v_fst_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_fst_1846_);
v_snd_1847_ = lean_ctor_get(v___x_1845_, 1);
lean_inc(v_snd_1847_);
lean_dec_ref(v___x_1845_);
v___x_1848_ = lean_st_ref_take(v___y_1839_);
v_cache_1849_ = lean_ctor_get(v___x_1848_, 1);
v_zetaDeltaFVarIds_1850_ = lean_ctor_get(v___x_1848_, 2);
v_postponed_1851_ = lean_ctor_get(v___x_1848_, 3);
v_diag_1852_ = lean_ctor_get(v___x_1848_, 4);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; 
v_unused_1862_ = lean_ctor_get(v___x_1848_, 0);
lean_dec(v_unused_1862_);
v___x_1854_ = v___x_1848_;
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_diag_1852_);
lean_inc(v_postponed_1851_);
lean_inc(v_zetaDeltaFVarIds_1850_);
lean_inc(v_cache_1849_);
lean_dec(v___x_1848_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_snd_1847_);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_snd_1847_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_cache_1849_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_zetaDeltaFVarIds_1850_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_postponed_1851_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v_diag_1852_);
v___x_1857_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_st_ref_set(v___y_1839_, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_fst_1846_);
return v___x_1859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1863_, v___y_1864_);
lean_dec(v___y_1864_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1867_, v___y_1869_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1881_, lean_object* v_localInsts_1882_, lean_object* v_x_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1881_, v_localInsts_1882_, v_x_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1889_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1889_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1906_, lean_object* v_localInsts_1907_, lean_object* v_x_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1906_, v_localInsts_1907_, v_x_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1915_, lean_object* v_lctx_1916_, lean_object* v_localInsts_1917_, lean_object* v_x_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1916_, v_localInsts_1917_, v_x_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1925_, lean_object* v_lctx_1926_, lean_object* v_localInsts_1927_, lean_object* v_x_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1925_, v_lctx_1926_, v_localInsts_1927_, v_x_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1934_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1935_, lean_object* v_x_1936_){
_start:
{
uint8_t v___x_1937_; 
v___x_1937_ = lean_name_eq(v_x_1936_, v_matchDeclName_1935_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1938_, lean_object* v_x_1939_){
_start:
{
uint8_t v_res_1940_; lean_object* v_r_1941_; 
v_res_1940_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1938_, v_x_1939_);
lean_dec(v_x_1939_);
lean_dec(v_matchDeclName_1938_);
v_r_1941_ = lean_box(v_res_1940_);
return v_r_1941_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1942_, lean_object* v_a_1943_, lean_object* v_b_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_nat_dec_lt(v_a_1943_, v_upperBound_1942_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
lean_dec(v_a_1943_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_b_1944_);
return v___x_1951_;
}
else
{
uint8_t v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = 0;
v___x_1953_ = l_Lean_Meta_introSubstEq(v_b_1944_, v___x_1952_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_snd_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref(v___x_1953_);
v_snd_1955_ = lean_ctor_get(v_a_1954_, 1);
lean_inc(v_snd_1955_);
lean_dec(v_a_1954_);
v___x_1956_ = lean_unsigned_to_nat(1u);
v___x_1957_ = lean_nat_add(v_a_1943_, v___x_1956_);
lean_dec(v_a_1943_);
v_a_1943_ = v___x_1957_;
v_b_1944_ = v_snd_1955_;
goto _start;
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v_a_1943_);
v_a_1959_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1953_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1953_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1967_, lean_object* v_a_1968_, lean_object* v_b_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1967_, v_a_1968_, v_b_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v_upperBound_1967_);
return v_res_1975_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1978_ = l_Lean_stringToMessageData(v___x_1977_);
return v___x_1978_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1981_ = l_Lean_stringToMessageData(v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1982_, lean_object* v___f_1983_, lean_object* v_matchDeclName_1984_, lean_object* v___x_1985_, uint8_t v___x_1986_, lean_object* v_heqPos_1987_, lean_object* v_heqNum_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2145_; 
v___x_1994_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1982_, v___y_1990_);
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2145_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2145_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_box(0);
v___x_2000_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1995_, v___x_1999_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2144_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2144_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2144_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v_mvarId_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v_options_2069_; lean_object* v_inheritedTraceOptions_2070_; uint8_t v_hasTrace_2071_; lean_object* v___x_2072_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; 
v_options_2069_ = lean_ctor_get(v___y_1991_, 2);
v_inheritedTraceOptions_2070_ = lean_ctor_get(v___y_1991_, 13);
v_hasTrace_2071_ = lean_ctor_get_uint8(v_options_2069_, sizeof(void*)*1);
v___x_2072_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2071_ == 0)
{
v___y_2074_ = v___y_1989_;
v___y_2075_ = v___y_1990_;
v___y_2076_ = v___y_1991_;
v___y_2077_ = v___y_1992_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2070_, v_options_2069_, v___x_2129_);
if (v___x_2130_ == 0)
{
v___y_2074_ = v___y_1989_;
v___y_2075_ = v___y_1990_;
v___y_2076_ = v___y_1991_;
v___y_2077_ = v___y_1992_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2131_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2132_ = l_Lean_Expr_mvarId_x21(v_a_2001_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2131_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2072_, v___x_2134_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_dec_ref(v___x_2135_);
v___y_2074_ = v___y_1989_;
v___y_2075_ = v___y_1990_;
v___y_2076_ = v___y_1991_;
v___y_2077_ = v___y_1992_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_del_object(v___x_2003_);
lean_dec(v_a_2001_);
lean_del_object(v___x_1997_);
lean_dec(v_heqPos_1987_);
lean_dec(v___x_1985_);
lean_dec(v_matchDeclName_1984_);
lean_dec_ref(v___f_1983_);
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
v___jp_2005_:
{
if (v___y_2012_ == 0)
{
lean_object* v___x_2013_; 
lean_dec_ref(v___y_2009_);
lean_del_object(v___x_2003_);
v___x_2013_ = l_Lean_MVarId_deltaTarget(v___y_2011_, v___f_1983_, v___y_2007_, v___y_2008_, v___y_2010_, v___y_2006_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_2013_);
v___x_2015_ = l_Lean_MVarId_heqOfEq(v_a_2014_, v___y_2007_, v___y_2008_, v___y_2010_, v___y_2006_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_2015_);
v___x_2017_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1984_, v_a_2016_, v___x_1985_, v___y_2007_, v___y_2008_, v___y_2010_, v___y_2006_);
lean_dec(v___x_1985_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v___x_2018_; 
lean_dec_ref(v___x_2017_);
v___x_2018_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2001_, v___y_2008_);
return v___x_2018_;
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_a_2001_);
v_a_2019_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2017_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2017_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_a_2001_);
lean_dec(v___x_1985_);
lean_dec(v_matchDeclName_1984_);
v_a_2027_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2015_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2015_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v_a_2001_);
lean_dec(v___x_1985_);
lean_dec(v_matchDeclName_1984_);
v_a_2035_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2013_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2013_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v___x_2044_; 
lean_dec(v___y_2011_);
lean_dec(v_a_2001_);
lean_dec(v___x_1985_);
lean_dec(v_matchDeclName_1984_);
lean_dec_ref(v___f_1983_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 1);
lean_ctor_set(v___x_2003_, 0, v___y_2009_);
v___x_2044_ = v___x_2003_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___y_2009_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
v___jp_2046_:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_MVarId_intros(v_mvarId_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v_snd_2054_; uint8_t v___x_2055_; lean_object* v___x_2056_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
v_snd_2054_ = lean_ctor_get(v_a_2053_, 1);
lean_inc_n(v_snd_2054_, 2);
lean_dec(v_a_2053_);
v___x_2055_ = 1;
v___x_2056_ = l_Lean_MVarId_refl(v_snd_2054_, v___x_2055_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2057_; 
lean_dec_ref(v___x_2056_);
lean_dec(v_snd_2054_);
lean_del_object(v___x_2003_);
lean_dec(v___x_1985_);
lean_dec(v_matchDeclName_1984_);
lean_dec_ref(v___f_1983_);
v___x_2057_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2001_, v___y_2049_);
return v___x_2057_;
}
else
{
lean_object* v_a_2058_; uint8_t v___x_2059_; 
v_a_2058_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2056_);
v___x_2059_ = l_Lean_Exception_isInterrupt(v_a_2058_);
if (v___x_2059_ == 0)
{
uint8_t v___x_2060_; 
lean_inc(v_a_2058_);
v___x_2060_ = l_Lean_Exception_isRuntime(v_a_2058_);
v___y_2006_ = v___y_2051_;
v___y_2007_ = v___y_2048_;
v___y_2008_ = v___y_2049_;
v___y_2009_ = v_a_2058_;
v___y_2010_ = v___y_2050_;
v___y_2011_ = v_snd_2054_;
v___y_2012_ = v___x_2060_;
goto v___jp_2005_;
}
else
{
v___y_2006_ = v___y_2051_;
v___y_2007_ = v___y_2048_;
v___y_2008_ = v___y_2049_;
v___y_2009_ = v_a_2058_;
v___y_2010_ = v___y_2050_;
v___y_2011_ = v_snd_2054_;
v___y_2012_ = v___x_2059_;
goto v___jp_2005_;
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_del_object(v___x_2003_);
lean_dec(v_a_2001_);
lean_dec(v___x_1985_);
lean_dec(v_matchDeclName_1984_);
lean_dec_ref(v___f_1983_);
v_a_2061_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2052_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2052_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
v___jp_2073_:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Expr_mvarId_x21(v_a_2001_);
if (v___x_1986_ == 0)
{
lean_del_object(v___x_1997_);
lean_dec(v_heqPos_1987_);
v_mvarId_2047_ = v___x_2078_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
v___y_2051_ = v___y_2077_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_box(0);
v___x_2080_ = 0;
v___x_2081_ = l_Lean_Meta_introNCore(v___x_2078_, v_heqPos_1987_, v___x_2079_, v___x_2080_, v___x_2080_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v_snd_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2119_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref(v___x_2081_);
v_snd_2083_ = lean_ctor_get(v_a_2082_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_a_2082_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v_a_2082_, 0);
lean_dec(v_unused_2120_);
v___x_2085_ = v_a_2082_;
v_isShared_2086_ = v_isSharedCheck_2119_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_snd_2083_);
lean_dec(v_a_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2119_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; 
lean_inc(v___x_1985_);
v___x_2087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1988_, v___x_1985_, v_snd_2083_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_options_2088_; uint8_t v_hasTrace_2089_; 
v_options_2088_ = lean_ctor_get(v___y_2076_, 2);
v_hasTrace_2089_ = lean_ctor_get_uint8(v_options_2088_, sizeof(void*)*1);
if (v_hasTrace_2089_ == 0)
{
lean_object* v_a_2090_; 
lean_del_object(v___x_2085_);
lean_del_object(v___x_1997_);
v_a_2090_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v___x_2087_);
v_mvarId_2047_ = v_a_2090_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
v___y_2051_ = v___y_2077_;
goto v___jp_2046_;
}
else
{
lean_object* v_a_2091_; lean_object* v_inheritedTraceOptions_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_a_2091_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2087_);
v_inheritedTraceOptions_2092_ = lean_ctor_get(v___y_2076_, 13);
v___x_2093_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2094_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2092_, v_options_2088_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_del_object(v___x_2085_);
lean_del_object(v___x_1997_);
v_mvarId_2047_ = v_a_2091_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
v___y_2051_ = v___y_2077_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2091_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 1);
lean_ctor_set(v___x_1997_, 0, v_a_2091_);
v___x_2097_ = v___x_1997_;
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
if (v_isShared_2086_ == 0)
{
lean_ctor_set_tag(v___x_2085_, 7);
lean_ctor_set(v___x_2085_, 1, v___x_2097_);
lean_ctor_set(v___x_2085_, 0, v___x_2095_);
v___x_2099_ = v___x_2085_;
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
v___x_2100_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2072_, v___x_2099_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_dec_ref(v___x_2100_);
v_mvarId_2047_ = v_a_2091_;
v___y_2048_ = v___y_2074_;
v___y_2049_ = v___y_2075_;
v___y_2050_ = v___y_2076_;
v___y_2051_ = v___y_2077_;
goto v___jp_2046_;
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec(v_a_2091_);
lean_del_object(v___x_2003_);
lean_dec(v_a_2001_);
lean_dec(v___x_1985_);
lean_dec(v_matchDeclName_1984_);
lean_dec_ref(v___f_1983_);
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
lean_del_object(v___x_2085_);
lean_del_object(v___x_2003_);
lean_dec(v_a_2001_);
lean_del_object(v___x_1997_);
lean_dec(v___x_1985_);
lean_dec(v_matchDeclName_1984_);
lean_dec_ref(v___f_1983_);
v_a_2111_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2087_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2087_);
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
lean_del_object(v___x_2003_);
lean_dec(v_a_2001_);
lean_del_object(v___x_1997_);
lean_dec(v___x_1985_);
lean_dec(v_matchDeclName_1984_);
lean_dec_ref(v___f_1983_);
v_a_2121_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2081_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2081_);
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
lean_del_object(v___x_1997_);
lean_dec(v_heqPos_1987_);
lean_dec(v___x_1985_);
lean_dec(v_matchDeclName_1984_);
lean_dec_ref(v___f_1983_);
return v___x_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2146_, lean_object* v___f_2147_, lean_object* v_matchDeclName_2148_, lean_object* v___x_2149_, lean_object* v___x_2150_, lean_object* v_heqPos_2151_, lean_object* v_heqNum_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
uint8_t v___x_6050__boxed_2158_; lean_object* v_res_2159_; 
v___x_6050__boxed_2158_ = lean_unbox(v___x_2150_);
v_res_2159_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2146_, v___f_2147_, v_matchDeclName_2148_, v___x_2149_, v___x_6050__boxed_2158_, v_heqPos_2151_, v_heqNum_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
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
lean_dec_ref(v___x_2340_);
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
lean_object* v___f_2495_; lean_object* v___x_14711__overap_2496_; lean_object* v___x_2497_; 
v___f_2495_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14711__overap_2496_ = lean_panic_fn_borrowed(v___f_2495_, v_msg_2489_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
v___x_2497_ = lean_apply_5(v___x_14711__overap_2496_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, lean_box(0));
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
lean_dec_ref(v___x_2603_);
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
lean_dec_ref(v___x_2691_);
v___x_2693_ = l_Lean_mkArrow(v_a_2692_, v_fst_2674_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v___x_2693_);
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
lean_dec_ref(v___x_2755_);
v___x_2757_ = lean_array_get_size(v___x_2740_);
v___x_2758_ = l_Lean_Meta_Match_simpH_x3f(v_a_2756_, v___x_2757_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v_a_2761_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2758_);
if (lean_obj_tag(v_a_2759_) == 1)
{
lean_object* v_val_2765_; lean_object* v___x_2766_; 
v_val_2765_ = lean_ctor_get(v_a_2759_, 0);
lean_inc(v_val_2765_);
lean_dec_ref(v_a_2759_);
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
lean_dec_ref(v___x_2836_);
v___x_2838_ = l_Lean_mkArrowN(v_a_2806_, v_a_2837_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref(v___x_2838_);
v___x_2840_ = l_Array_append___redArg(v___x_2831_, v_ys_2807_);
v___x_2841_ = l_Array_append___redArg(v___x_2840_, v_alts_2819_);
v___x_2842_ = l_Lean_Meta_mkForallFVars(v___x_2841_, v_a_2839_, v___x_2808_, v___x_2809_, v___x_2809_, v___x_2810_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec_ref(v___x_2841_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref(v___x_2842_);
v___x_2844_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2843_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc_n(v_a_2845_, 2);
lean_dec_ref(v___x_2844_);
lean_inc(v___x_2812_);
v___x_2846_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2811_, v_a_2845_, v___x_2812_, v___x_2812_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref(v___x_2846_);
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
uint8_t v___x_18946__boxed_2939_; uint8_t v___x_18947__boxed_2940_; uint8_t v___x_18948__boxed_2941_; lean_object* v_res_2942_; 
v___x_18946__boxed_2939_ = lean_unbox(v___x_2922_);
v___x_18947__boxed_2940_ = lean_unbox(v___x_2923_);
v___x_18948__boxed_2941_ = lean_unbox(v___x_2924_);
v_res_2942_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2911_, v_a_2912_, v_a_2913_, v___x_2914_, v___x_2915_, v___x_2916_, v___x_2917_, v___x_2918_, v_rhsArgs_2919_, v_a_2920_, v_ys_2921_, v___x_18946__boxed_2939_, v___x_18947__boxed_2940_, v___x_18948__boxed_2941_, v_matchDeclName_2925_, v___x_2926_, v___x_2927_, v___x_2928_, v___x_2929_, v___x_2930_, v_argMask_2931_, v_a_2932_, v_alts_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
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
lean_object* v_a_2992_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; uint8_t v___y_2998_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; uint8_t v___y_3046_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v_options_3057_; uint8_t v_hasTrace_3058_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref(v___x_2991_);
v_options_3057_ = lean_ctor_get(v___y_2980_, 2);
v_hasTrace_3058_ = lean_ctor_get_uint8(v_options_3057_, sizeof(void*)*1);
if (v_hasTrace_3058_ == 0)
{
v___y_3049_ = v___y_2978_;
v___y_3050_ = v___y_2979_;
v___y_3051_ = v___y_2980_;
v___y_3052_ = v___y_2981_;
goto v___jp_3048_;
}
else
{
lean_object* v_inheritedTraceOptions_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v_inheritedTraceOptions_3059_ = lean_ctor_get(v___y_2980_, 13);
v___x_3060_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3061_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_3062_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3059_, v_options_3057_, v___x_3061_);
if (v___x_3062_ == 0)
{
v___y_3049_ = v___y_2978_;
v___y_3050_ = v___y_2979_;
v___y_3051_ = v___y_2980_;
v___y_3052_ = v___y_2981_;
goto v___jp_3048_;
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3063_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_2992_);
v___x_3064_ = lean_array_to_list(v_a_2992_);
v___x_3065_ = lean_box(0);
v___x_3066_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3064_, v___x_3065_);
v___x_3067_ = l_Lean_MessageData_ofList(v___x_3066_);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3063_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3060_, v___x_3068_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_dec_ref(v___x_3069_);
v___y_3049_ = v___y_2978_;
v___y_3050_ = v___y_2979_;
v___y_3051_ = v___y_2980_;
v___y_3052_ = v___y_2981_;
goto v___jp_3048_;
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
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
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
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
v___x_3007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3004_, v_sz_3006_, v___x_2990_, v___x_3005_, v___y_2994_, v___y_2996_, v___y_2997_, v___y_2995_);
lean_dec_ref(v___x_3004_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v_fst_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; uint8_t v___x_3013_; lean_object* v___x_3014_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref(v___x_3007_);
v_fst_3009_ = lean_ctor_get(v_a_3008_, 0);
lean_inc(v_fst_3009_);
lean_dec(v_a_3008_);
v___x_3010_ = l_Subarray_copy___redArg(v___x_2960_);
lean_inc_ref(v___x_3010_);
v___x_3011_ = l_Array_append___redArg(v___x_3010_, v_ys_2973_);
v___x_3012_ = 0;
v___x_3013_ = 1;
v___x_3014_ = l_Lean_Meta_mkForallFVars(v___x_3011_, v_fst_3009_, v___x_3012_, v___x_2961_, v___x_2961_, v___x_3013_, v___y_2994_, v___y_2996_, v___y_2997_, v___y_2995_);
lean_dec_ref(v___x_3011_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___f_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref(v___x_3014_);
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
v___x_3024_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2972_, v___x_3010_, v___x_2987_, v___x_3023_, v___f_3022_, v___y_2994_, v___y_2996_, v___y_2997_, v___y_2995_);
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
if (v___y_3046_ == 0)
{
v___y_2994_ = v___y_3042_;
v___y_2995_ = v___y_3043_;
v___y_2996_ = v___y_3044_;
v___y_2997_ = v___y_3045_;
v___y_2998_ = v___y_3046_;
goto v___jp_2993_;
}
else
{
uint8_t v___x_3047_; 
v___x_3047_ = lean_nat_dec_eq(v___x_2972_, v___x_2959_);
v___y_2994_ = v___y_3042_;
v___y_2995_ = v___y_3043_;
v___y_2996_ = v___y_3044_;
v___y_2997_ = v___y_3045_;
v___y_2998_ = v___x_3047_;
goto v___jp_2993_;
}
}
v___jp_3048_:
{
lean_object* v___x_3053_; uint8_t v___x_3054_; 
v___x_3053_ = lean_array_get_size(v_ys_2973_);
v___x_3054_ = lean_nat_dec_eq(v___x_3053_, v___x_2959_);
if (v___x_3054_ == 0)
{
v___y_3042_ = v___y_3049_;
v___y_3043_ = v___y_3052_;
v___y_3044_ = v___y_3050_;
v___y_3045_ = v___y_3051_;
v___y_3046_ = v___x_3054_;
goto v___jp_3041_;
}
else
{
lean_object* v___x_3055_; uint8_t v___x_3056_; 
v___x_3055_ = lean_array_get_size(v_a_2992_);
v___x_3056_ = lean_nat_dec_eq(v___x_3055_, v___x_2959_);
v___y_3042_ = v___y_3049_;
v___y_3043_ = v___y_3052_;
v___y_3044_ = v___y_3050_;
v___y_3045_ = v___y_3051_;
v___y_3046_ = v___x_3056_;
goto v___jp_3041_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
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
v_a_3078_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_2991_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_2991_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3086_ = _args[0];
lean_object* v_overlaps_3087_ = _args[1];
lean_object* v_a_3088_ = _args[2];
lean_object* v_fst_3089_ = _args[3];
lean_object* v___x_3090_ = _args[4];
lean_object* v___x_3091_ = _args[5];
lean_object* v___x_3092_ = _args[6];
lean_object* v___x_3093_ = _args[7];
lean_object* v___x_3094_ = _args[8];
lean_object* v_a_3095_ = _args[9];
lean_object* v___x_3096_ = _args[10];
lean_object* v___x_3097_ = _args[11];
lean_object* v___x_3098_ = _args[12];
lean_object* v_matchDeclName_3099_ = _args[13];
lean_object* v___x_3100_ = _args[14];
lean_object* v___x_3101_ = _args[15];
lean_object* v___x_3102_ = _args[16];
lean_object* v___x_3103_ = _args[17];
lean_object* v___x_3104_ = _args[18];
lean_object* v_ys_3105_ = _args[19];
lean_object* v___eqs_3106_ = _args[20];
lean_object* v_rhsArgs_3107_ = _args[21];
lean_object* v_argMask_3108_ = _args[22];
lean_object* v_altResultType_3109_ = _args[23];
lean_object* v___y_3110_ = _args[24];
lean_object* v___y_3111_ = _args[25];
lean_object* v___y_3112_ = _args[26];
lean_object* v___y_3113_ = _args[27];
lean_object* v___y_3114_ = _args[28];
_start:
{
uint8_t v___x_19214__boxed_3115_; lean_object* v_res_3116_; 
v___x_19214__boxed_3115_ = lean_unbox(v___x_3093_);
v_res_3116_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3086_, v_overlaps_3087_, v_a_3088_, v_fst_3089_, v___x_3090_, v___x_3091_, v___x_3092_, v___x_19214__boxed_3115_, v___x_3094_, v_a_3095_, v___x_3096_, v___x_3097_, v___x_3098_, v_matchDeclName_3099_, v___x_3100_, v___x_3101_, v___x_3102_, v___x_3103_, v___x_3104_, v_ys_3105_, v___eqs_3106_, v_rhsArgs_3107_, v_argMask_3108_, v_altResultType_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec_ref(v___eqs_3106_);
lean_dec(v___x_3104_);
lean_dec(v_fst_3089_);
lean_dec_ref(v_overlaps_3087_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3117_, lean_object* v_val_3118_, lean_object* v_baseName_3119_, lean_object* v___x_3120_, lean_object* v_a_3121_, lean_object* v___x_3122_, lean_object* v___x_3123_, lean_object* v___x_3124_, lean_object* v_matchDeclName_3125_, lean_object* v___x_3126_, lean_object* v___x_3127_, lean_object* v___x_3128_, lean_object* v_a_3129_, lean_object* v_b_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_nat_dec_lt(v_a_3129_, v_upperBound_3117_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; 
lean_dec(v_a_3129_);
lean_dec(v___x_3128_);
lean_dec_ref(v___x_3127_);
lean_dec(v___x_3126_);
lean_dec(v_matchDeclName_3125_);
lean_dec_ref(v___x_3124_);
lean_dec_ref(v___x_3123_);
lean_dec(v___x_3122_);
lean_dec_ref(v_a_3121_);
lean_dec_ref(v___x_3120_);
lean_dec(v_baseName_3119_);
lean_dec_ref(v_val_3118_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v_b_3130_);
return v___x_3137_;
}
else
{
lean_object* v_snd_3138_; lean_object* v_snd_3139_; lean_object* v_snd_3140_; lean_object* v_fst_3141_; lean_object* v_fst_3142_; lean_object* v_fst_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3226_; 
v_snd_3138_ = lean_ctor_get(v_b_3130_, 1);
lean_inc(v_snd_3138_);
v_snd_3139_ = lean_ctor_get(v_snd_3138_, 1);
lean_inc(v_snd_3139_);
v_snd_3140_ = lean_ctor_get(v_snd_3139_, 1);
lean_inc(v_snd_3140_);
v_fst_3141_ = lean_ctor_get(v_b_3130_, 0);
lean_inc(v_fst_3141_);
lean_dec_ref(v_b_3130_);
v_fst_3142_ = lean_ctor_get(v_snd_3138_, 0);
lean_inc(v_fst_3142_);
lean_dec(v_snd_3138_);
v_fst_3143_ = lean_ctor_get(v_snd_3139_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_snd_3139_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v_snd_3139_, 1);
lean_dec(v_unused_3227_);
v___x_3145_ = v_snd_3139_;
v_isShared_3146_ = v_isSharedCheck_3226_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_fst_3143_);
lean_dec(v_snd_3139_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3226_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v_fst_3147_; lean_object* v_snd_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3225_; 
v_fst_3147_ = lean_ctor_get(v_snd_3140_, 0);
v_snd_3148_ = lean_ctor_get(v_snd_3140_, 1);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_snd_3140_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3150_ = v_snd_3140_;
v_isShared_3151_ = v_isSharedCheck_3225_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_snd_3148_);
lean_inc(v_fst_3147_);
lean_dec(v_snd_3140_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3225_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v_altInfos_3152_; lean_object* v_overlaps_3153_; lean_object* v_start_3154_; lean_object* v_stop_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___f_3167_; lean_object* v___x_3168_; lean_object* v___y_3170_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v_altInfos_3152_ = lean_ctor_get(v_val_3118_, 2);
v_overlaps_3153_ = lean_ctor_get(v_val_3118_, 5);
v_start_3154_ = lean_ctor_get(v___x_3127_, 1);
v_stop_3155_ = lean_ctor_get(v___x_3127_, 2);
v___x_3156_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3157_ = l_Lean_instInhabitedExpr;
v___x_3158_ = lean_unsigned_to_nat(0u);
v___x_3159_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3160_ = lean_box(0);
v___x_3161_ = lean_unsigned_to_nat(1u);
v___x_3162_ = lean_array_get_borrowed(v___x_3156_, v_altInfos_3152_, v_a_3129_);
v___x_3163_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3119_);
v___x_3164_ = l_Lean_Name_str___override(v_baseName_3119_, v___x_3163_);
lean_inc(v_fst_3143_);
v___x_3165_ = lean_name_append_index_after(v___x_3164_, v_fst_3143_);
v___x_3166_ = lean_box(v___x_3136_);
lean_inc(v___x_3128_);
lean_inc_ref(v___x_3127_);
lean_inc(v___x_3126_);
lean_inc(v___x_3165_);
lean_inc(v_matchDeclName_3125_);
lean_inc_ref(v___x_3124_);
lean_inc_ref(v___x_3123_);
lean_inc(v___x_3122_);
lean_inc_ref(v_a_3121_);
lean_inc_ref(v___x_3120_);
lean_inc(v_fst_3142_);
lean_inc(v_a_3129_);
lean_inc_ref(v_overlaps_3153_);
v___f_3167_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3167_, 0, v___x_3161_);
lean_closure_set(v___f_3167_, 1, v_overlaps_3153_);
lean_closure_set(v___f_3167_, 2, v_a_3129_);
lean_closure_set(v___f_3167_, 3, v_fst_3142_);
lean_closure_set(v___f_3167_, 4, v___x_3159_);
lean_closure_set(v___f_3167_, 5, v___x_3158_);
lean_closure_set(v___f_3167_, 6, v___x_3120_);
lean_closure_set(v___f_3167_, 7, v___x_3166_);
lean_closure_set(v___f_3167_, 8, v___x_3157_);
lean_closure_set(v___f_3167_, 9, v_a_3121_);
lean_closure_set(v___f_3167_, 10, v___x_3122_);
lean_closure_set(v___f_3167_, 11, v___x_3123_);
lean_closure_set(v___f_3167_, 12, v___x_3124_);
lean_closure_set(v___f_3167_, 13, v_matchDeclName_3125_);
lean_closure_set(v___f_3167_, 14, v___x_3165_);
lean_closure_set(v___f_3167_, 15, v___x_3126_);
lean_closure_set(v___f_3167_, 16, v___x_3160_);
lean_closure_set(v___f_3167_, 17, v___x_3127_);
lean_closure_set(v___f_3167_, 18, v___x_3128_);
v___x_3168_ = lean_array_push(v_fst_3141_, v___x_3165_);
v___x_3221_ = lean_nat_sub(v_stop_3155_, v_start_3154_);
v___x_3222_ = lean_nat_dec_lt(v_a_3129_, v___x_3221_);
lean_dec(v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; 
v___x_3223_ = l_outOfBounds___redArg(v___x_3157_);
v___y_3170_ = v___x_3223_;
goto v___jp_3169_;
}
else
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Subarray_get___redArg(v___x_3127_, v_a_3129_);
v___y_3170_ = v___x_3224_;
goto v___jp_3169_;
}
v___jp_3169_:
{
lean_object* v___x_3171_; 
lean_inc(v___y_3134_);
lean_inc_ref(v___y_3133_);
lean_inc(v___y_3132_);
lean_inc_ref(v___y_3131_);
v___x_3171_ = lean_infer_type(v___y_3170_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3173_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref(v___x_3171_);
lean_inc(v___x_3128_);
lean_inc(v___x_3162_);
v___x_3173_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3172_, v___x_3162_, v___x_3128_, v___f_3167_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v_snd_3175_; lean_object* v_fst_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3204_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref(v___x_3173_);
v_snd_3175_ = lean_ctor_get(v_a_3174_, 1);
v_fst_3176_ = lean_ctor_get(v_a_3174_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_a_3174_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3178_ = v_a_3174_;
v_isShared_3179_ = v_isSharedCheck_3204_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_snd_3175_);
lean_inc(v_fst_3176_);
lean_dec(v_a_3174_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3204_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v_fst_3180_; lean_object* v_snd_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3203_; 
v_fst_3180_ = lean_ctor_get(v_snd_3175_, 0);
v_snd_3181_ = lean_ctor_get(v_snd_3175_, 1);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_snd_3175_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3183_ = v_snd_3175_;
v_isShared_3184_ = v_isSharedCheck_3203_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_snd_3181_);
lean_inc(v_fst_3180_);
lean_dec(v_snd_3175_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3203_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3185_ = lean_array_push(v_fst_3142_, v_fst_3176_);
v___x_3186_ = lean_array_push(v_fst_3147_, v_fst_3180_);
v___x_3187_ = lean_array_push(v_snd_3148_, v_snd_3181_);
v___x_3188_ = lean_nat_add(v_fst_3143_, v___x_3161_);
lean_dec(v_fst_3143_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 1, v___x_3187_);
lean_ctor_set(v___x_3183_, 0, v___x_3186_);
v___x_3190_ = v___x_3183_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3187_);
v___x_3190_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3192_; 
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 1, v___x_3190_);
lean_ctor_set(v___x_3178_, 0, v___x_3188_);
v___x_3192_ = v___x_3178_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3194_; 
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 1, v___x_3192_);
lean_ctor_set(v___x_3150_, 0, v___x_3185_);
v___x_3194_ = v___x_3150_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3196_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 1, v___x_3194_);
lean_ctor_set(v___x_3145_, 0, v___x_3168_);
v___x_3196_ = v___x_3145_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_nat_add(v_a_3129_, v___x_3161_);
lean_dec(v_a_3129_);
v_a_3129_ = v___x_3197_;
v_b_3130_ = v___x_3196_;
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
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v___x_3168_);
lean_del_object(v___x_3150_);
lean_dec(v_snd_3148_);
lean_dec(v_fst_3147_);
lean_del_object(v___x_3145_);
lean_dec(v_fst_3143_);
lean_dec(v_fst_3142_);
lean_dec(v_a_3129_);
lean_dec(v___x_3128_);
lean_dec_ref(v___x_3127_);
lean_dec(v___x_3126_);
lean_dec(v_matchDeclName_3125_);
lean_dec_ref(v___x_3124_);
lean_dec_ref(v___x_3123_);
lean_dec(v___x_3122_);
lean_dec_ref(v_a_3121_);
lean_dec_ref(v___x_3120_);
lean_dec(v_baseName_3119_);
lean_dec_ref(v_val_3118_);
v_a_3205_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3173_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3173_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref(v___x_3168_);
lean_dec_ref(v___f_3167_);
lean_del_object(v___x_3150_);
lean_dec(v_snd_3148_);
lean_dec(v_fst_3147_);
lean_del_object(v___x_3145_);
lean_dec(v_fst_3143_);
lean_dec(v_fst_3142_);
lean_dec(v_a_3129_);
lean_dec(v___x_3128_);
lean_dec_ref(v___x_3127_);
lean_dec(v___x_3126_);
lean_dec(v_matchDeclName_3125_);
lean_dec_ref(v___x_3124_);
lean_dec_ref(v___x_3123_);
lean_dec(v___x_3122_);
lean_dec_ref(v_a_3121_);
lean_dec_ref(v___x_3120_);
lean_dec(v_baseName_3119_);
lean_dec_ref(v_val_3118_);
v_a_3213_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3171_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3171_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
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
lean_object* v_upperBound_3228_ = _args[0];
lean_object* v_val_3229_ = _args[1];
lean_object* v_baseName_3230_ = _args[2];
lean_object* v___x_3231_ = _args[3];
lean_object* v_a_3232_ = _args[4];
lean_object* v___x_3233_ = _args[5];
lean_object* v___x_3234_ = _args[6];
lean_object* v___x_3235_ = _args[7];
lean_object* v_matchDeclName_3236_ = _args[8];
lean_object* v___x_3237_ = _args[9];
lean_object* v___x_3238_ = _args[10];
lean_object* v___x_3239_ = _args[11];
lean_object* v_a_3240_ = _args[12];
lean_object* v_b_3241_ = _args[13];
lean_object* v___y_3242_ = _args[14];
lean_object* v___y_3243_ = _args[15];
lean_object* v___y_3244_ = _args[16];
lean_object* v___y_3245_ = _args[17];
lean_object* v___y_3246_ = _args[18];
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3228_, v_val_3229_, v_baseName_3230_, v___x_3231_, v_a_3232_, v___x_3233_, v___x_3234_, v___x_3235_, v_matchDeclName_3236_, v___x_3237_, v___x_3238_, v___x_3239_, v_a_3240_, v_b_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v_upperBound_3228_);
return v_res_3247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3251_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3252_ = lean_unsigned_to_nat(6u);
v___x_3253_ = lean_unsigned_to_nat(233u);
v___x_3254_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3255_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3256_ = l_mkPanicMessageWithDecl(v___x_3255_, v___x_3254_, v___x_3253_, v___x_3252_, v___x_3251_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3269_, lean_object* v_matchDeclName_3270_, lean_object* v_numParams_3271_, lean_object* v_val_3272_, lean_object* v___x_3273_, lean_object* v_numDiscrs_3274_, lean_object* v_baseName_3275_, lean_object* v_a_3276_, lean_object* v___x_3277_, lean_object* v___x_3278_, lean_object* v___x_3279_, lean_object* v_uElimPos_x3f_3280_, lean_object* v_discrInfos_3281_, lean_object* v_overlaps_3282_, lean_object* v___f_3283_, lean_object* v___x_3284_, lean_object* v_altInfos_3285_, lean_object* v_xs_3286_, lean_object* v___matchResultType_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; uint8_t v___y_3305_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v_lower_3313_; lean_object* v_upper_3314_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3307_ = lean_box(0);
v___x_3308_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3271_);
lean_inc_ref(v_xs_3286_);
v___x_3309_ = l_Array_toSubarray___redArg(v_xs_3286_, v___x_3308_, v_numParams_3271_);
v___x_3310_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3272_);
v___x_3311_ = lean_array_get(v___x_3273_, v_xs_3286_, v___x_3310_);
lean_dec(v___x_3310_);
v___x_3367_ = lean_array_get_size(v_xs_3286_);
v___x_3368_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3272_);
v___x_3369_ = lean_nat_sub(v___x_3367_, v___x_3368_);
lean_dec(v___x_3368_);
v___x_3370_ = lean_nat_dec_le(v___x_3369_, v___x_3308_);
if (v___x_3370_ == 0)
{
v_lower_3313_ = v___x_3369_;
v_upper_3314_ = v___x_3367_;
goto v___jp_3312_;
}
else
{
lean_dec(v___x_3369_);
v_lower_3313_ = v___x_3308_;
v_upper_3314_ = v___x_3367_;
goto v___jp_3312_;
}
v___jp_3293_:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3295_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3294_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
return v___x_3295_;
}
v___jp_3296_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3299_, 0, v___y_3298_);
lean_ctor_set(v___x_3299_, 1, v_splitterName_3269_);
lean_ctor_set(v___x_3299_, 2, v___y_3297_);
v___x_3300_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3270_, v___x_3299_, v___y_3291_);
return v___x_3300_;
}
v___jp_3301_:
{
lean_object* v___x_3306_; 
lean_inc(v_matchDeclName_3270_);
v___x_3306_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3270_, v___y_3305_, v___y_3304_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_dec_ref(v___x_3306_);
v___y_3297_ = v___y_3302_;
v___y_3298_ = v___y_3303_;
goto v___jp_3296_;
}
else
{
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v_matchDeclName_3270_);
lean_dec(v_splitterName_3269_);
return v___x_3306_;
}
}
v___jp_3312_:
{
lean_object* v___x_3315_; lean_object* v_start_3316_; lean_object* v_stop_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_inc_ref(v_xs_3286_);
v___x_3315_ = l_Array_toSubarray___redArg(v_xs_3286_, v_lower_3313_, v_upper_3314_);
v_start_3316_ = lean_ctor_get(v___x_3315_, 1);
lean_inc(v_start_3316_);
v_stop_3317_ = lean_ctor_get(v___x_3315_, 2);
lean_inc(v_stop_3317_);
v___x_3318_ = lean_unsigned_to_nat(1u);
v___x_3319_ = lean_nat_add(v_numParams_3271_, v___x_3318_);
v___x_3320_ = lean_nat_add(v___x_3319_, v_numDiscrs_3274_);
v___x_3321_ = lean_nat_sub(v_stop_3317_, v_start_3316_);
lean_dec(v_start_3316_);
lean_dec(v_stop_3317_);
v___x_3322_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3323_ = l_Array_toSubarray___redArg(v_xs_3286_, v___x_3319_, v___x_3320_);
lean_inc(v___x_3278_);
lean_inc(v_matchDeclName_3270_);
lean_inc(v___x_3277_);
v___x_3324_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3321_, v_val_3272_, v_baseName_3275_, v___x_3323_, v_a_3276_, v___x_3277_, v___x_3309_, v___x_3311_, v_matchDeclName_3270_, v___x_3278_, v___x_3315_, v___x_3279_, v___x_3308_, v___x_3322_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___x_3321_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v_snd_3326_; lean_object* v_snd_3327_; lean_object* v_snd_3328_; lean_object* v_fst_3329_; lean_object* v_fst_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3357_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref(v___x_3324_);
v_snd_3326_ = lean_ctor_get(v_a_3325_, 1);
v_snd_3327_ = lean_ctor_get(v_snd_3326_, 1);
v_snd_3328_ = lean_ctor_get(v_snd_3327_, 1);
lean_inc(v_snd_3328_);
v_fst_3329_ = lean_ctor_get(v_a_3325_, 0);
lean_inc(v_fst_3329_);
lean_dec(v_a_3325_);
v_fst_3330_ = lean_ctor_get(v_snd_3328_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_snd_3328_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v_snd_3328_, 1);
lean_dec(v_unused_3358_);
v___x_3332_ = v_snd_3328_;
v_isShared_3333_ = v_isSharedCheck_3357_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_fst_3330_);
lean_dec(v_snd_3328_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3357_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; uint8_t v___x_3335_; 
lean_inc_ref(v_overlaps_3282_);
lean_inc(v_fst_3330_);
v___x_3334_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3334_, 0, v_numParams_3271_);
lean_ctor_set(v___x_3334_, 1, v_numDiscrs_3274_);
lean_ctor_set(v___x_3334_, 2, v_fst_3330_);
lean_ctor_set(v___x_3334_, 3, v_uElimPos_x3f_3280_);
lean_ctor_set(v___x_3334_, 4, v_discrInfos_3281_);
lean_ctor_set(v___x_3334_, 5, v_overlaps_3282_);
v___x_3335_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3282_);
lean_dec_ref(v_overlaps_3282_);
if (v___x_3335_ == 0)
{
uint8_t v___x_3336_; 
lean_del_object(v___x_3332_);
lean_dec(v_fst_3330_);
lean_dec_ref(v___x_3284_);
lean_dec(v___x_3278_);
lean_dec(v___x_3277_);
v___x_3336_ = 1;
v___y_3302_ = v___x_3334_;
v___y_3303_ = v_fst_3329_;
v___y_3304_ = v___f_3283_;
v___y_3305_ = v___x_3336_;
goto v___jp_3301_;
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3338_ = lean_find_expr(v___x_3337_, v___x_3284_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
lean_dec_ref(v___f_3283_);
v___x_3339_ = lean_array_get_size(v_altInfos_3285_);
v___x_3340_ = lean_array_get_size(v_fst_3330_);
v___x_3341_ = lean_nat_dec_eq(v___x_3339_, v___x_3340_);
if (v___x_3341_ == 0)
{
lean_dec_ref(v___x_3334_);
lean_del_object(v___x_3332_);
lean_dec(v_fst_3330_);
lean_dec(v_fst_3329_);
lean_dec_ref(v___x_3284_);
lean_dec(v___x_3278_);
lean_dec(v___x_3277_);
lean_dec(v_matchDeclName_3270_);
lean_dec(v_splitterName_3269_);
goto v___jp_3293_;
}
else
{
uint8_t v___x_3342_; 
v___x_3342_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3285_, v_fst_3330_, v___x_3339_);
lean_dec(v_fst_3330_);
if (v___x_3342_ == 0)
{
lean_dec_ref(v___x_3334_);
lean_del_object(v___x_3332_);
lean_dec(v_fst_3329_);
lean_dec_ref(v___x_3284_);
lean_dec(v___x_3278_);
lean_dec(v___x_3277_);
lean_dec(v_matchDeclName_3270_);
lean_dec(v_splitterName_3269_);
goto v___jp_3293_;
}
else
{
uint8_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3349_; 
v___x_3343_ = 0;
lean_inc_n(v_splitterName_3269_, 2);
v___x_3344_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3344_, 0, v_splitterName_3269_);
lean_ctor_set(v___x_3344_, 1, v___x_3278_);
lean_ctor_set(v___x_3344_, 2, v___x_3284_);
lean_inc(v_matchDeclName_3270_);
v___x_3345_ = l_Lean_mkConst(v_matchDeclName_3270_, v___x_3277_);
v___x_3346_ = lean_box(1);
v___x_3347_ = 1;
if (v_isShared_3333_ == 0)
{
lean_ctor_set_tag(v___x_3332_, 1);
lean_ctor_set(v___x_3332_, 1, v___x_3307_);
lean_ctor_set(v___x_3332_, 0, v_splitterName_3269_);
v___x_3349_ = v___x_3332_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_splitterName_3269_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3307_);
v___x_3349_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3350_, 0, v___x_3344_);
lean_ctor_set(v___x_3350_, 1, v___x_3345_);
lean_ctor_set(v___x_3350_, 2, v___x_3346_);
lean_ctor_set(v___x_3350_, 3, v___x_3349_);
lean_ctor_set_uint8(v___x_3350_, sizeof(void*)*4, v___x_3347_);
v___x_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_inc_ref(v___x_3351_);
v___x_3352_ = l_Lean_addDecl(v___x_3351_, v___x_3343_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3352_) == 0)
{
uint8_t v___x_3353_; lean_object* v___x_3354_; 
lean_dec_ref(v___x_3352_);
v___x_3353_ = 0;
lean_inc(v_splitterName_3269_);
v___x_3354_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3269_, v___x_3353_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v___x_3355_; 
lean_dec_ref(v___x_3354_);
v___x_3355_ = l_Lean_compileDecl(v___x_3351_, v___x_3343_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_dec_ref(v___x_3355_);
v___y_3297_ = v___x_3334_;
v___y_3298_ = v_fst_3329_;
goto v___jp_3296_;
}
else
{
lean_dec_ref(v___x_3334_);
lean_dec(v_fst_3329_);
lean_dec(v_matchDeclName_3270_);
lean_dec(v_splitterName_3269_);
return v___x_3355_;
}
}
else
{
lean_dec_ref(v___x_3351_);
lean_dec_ref(v___x_3334_);
lean_dec(v_fst_3329_);
lean_dec(v_matchDeclName_3270_);
lean_dec(v_splitterName_3269_);
return v___x_3354_;
}
}
else
{
lean_dec_ref(v___x_3351_);
lean_dec_ref(v___x_3334_);
lean_dec(v_fst_3329_);
lean_dec(v_matchDeclName_3270_);
lean_dec(v_splitterName_3269_);
return v___x_3352_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3338_);
lean_del_object(v___x_3332_);
lean_dec(v_fst_3330_);
lean_dec_ref(v___x_3284_);
lean_dec(v___x_3278_);
lean_dec(v___x_3277_);
v___y_3302_ = v___x_3334_;
v___y_3303_ = v_fst_3329_;
v___y_3304_ = v___f_3283_;
v___y_3305_ = v___x_3335_;
goto v___jp_3301_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec_ref(v___x_3284_);
lean_dec_ref(v___f_3283_);
lean_dec_ref(v_overlaps_3282_);
lean_dec_ref(v_discrInfos_3281_);
lean_dec(v_uElimPos_x3f_3280_);
lean_dec(v___x_3278_);
lean_dec(v___x_3277_);
lean_dec(v_numDiscrs_3274_);
lean_dec(v_numParams_3271_);
lean_dec(v_matchDeclName_3270_);
lean_dec(v_splitterName_3269_);
v_a_3359_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3324_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3324_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3371_ = _args[0];
lean_object* v_matchDeclName_3372_ = _args[1];
lean_object* v_numParams_3373_ = _args[2];
lean_object* v_val_3374_ = _args[3];
lean_object* v___x_3375_ = _args[4];
lean_object* v_numDiscrs_3376_ = _args[5];
lean_object* v_baseName_3377_ = _args[6];
lean_object* v_a_3378_ = _args[7];
lean_object* v___x_3379_ = _args[8];
lean_object* v___x_3380_ = _args[9];
lean_object* v___x_3381_ = _args[10];
lean_object* v_uElimPos_x3f_3382_ = _args[11];
lean_object* v_discrInfos_3383_ = _args[12];
lean_object* v_overlaps_3384_ = _args[13];
lean_object* v___f_3385_ = _args[14];
lean_object* v___x_3386_ = _args[15];
lean_object* v_altInfos_3387_ = _args[16];
lean_object* v_xs_3388_ = _args[17];
lean_object* v___matchResultType_3389_ = _args[18];
lean_object* v___y_3390_ = _args[19];
lean_object* v___y_3391_ = _args[20];
lean_object* v___y_3392_ = _args[21];
lean_object* v___y_3393_ = _args[22];
lean_object* v___y_3394_ = _args[23];
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3371_, v_matchDeclName_3372_, v_numParams_3373_, v_val_3374_, v___x_3375_, v_numDiscrs_3376_, v_baseName_3377_, v_a_3378_, v___x_3379_, v___x_3380_, v___x_3381_, v_uElimPos_x3f_3382_, v_discrInfos_3383_, v_overlaps_3384_, v___f_3385_, v___x_3386_, v_altInfos_3387_, v_xs_3388_, v___matchResultType_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec_ref(v___matchResultType_3389_);
lean_dec_ref(v_altInfos_3387_);
lean_dec_ref(v___x_3375_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
if (lean_obj_tag(v_a_3396_) == 0)
{
lean_object* v___x_3398_; 
v___x_3398_ = l_List_reverse___redArg(v_a_3397_);
return v___x_3398_;
}
else
{
lean_object* v_head_3399_; lean_object* v_tail_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3409_; 
v_head_3399_ = lean_ctor_get(v_a_3396_, 0);
v_tail_3400_ = lean_ctor_get(v_a_3396_, 1);
v_isSharedCheck_3409_ = !lean_is_exclusive(v_a_3396_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3402_ = v_a_3396_;
v_isShared_3403_ = v_isSharedCheck_3409_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_tail_3400_);
lean_inc(v_head_3399_);
lean_dec(v_a_3396_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3409_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3404_; lean_object* v___x_3406_; 
v___x_3404_ = l_Lean_mkLevelParam(v_head_3399_);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 1, v_a_3397_);
lean_ctor_set(v___x_3402_, 0, v___x_3404_);
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3404_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_a_3397_);
v___x_3406_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
v_a_3396_ = v_tail_3400_;
v_a_3397_ = v___x_3406_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
return v___x_3412_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3413_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3414_ = lean_unsigned_to_nat(0u);
v___x_3415_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
lean_ctor_set(v___x_3415_, 2, v___x_3414_);
lean_ctor_set(v___x_3415_, 3, v___x_3414_);
lean_ctor_set(v___x_3415_, 4, v___x_3413_);
lean_ctor_set(v___x_3415_, 5, v___x_3413_);
lean_ctor_set(v___x_3415_, 6, v___x_3413_);
lean_ctor_set(v___x_3415_, 7, v___x_3413_);
lean_ctor_set(v___x_3415_, 8, v___x_3413_);
lean_ctor_set(v___x_3415_, 9, v___x_3413_);
return v___x_3415_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3416_ = lean_box(1);
v___x_3417_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3418_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3418_);
lean_ctor_set(v___x_3419_, 1, v___x_3417_);
lean_ctor_set(v___x_3419_, 2, v___x_3416_);
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_3422_ = l_Lean_stringToMessageData(v___x_3421_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_3425_ = l_Lean_stringToMessageData(v___x_3424_);
return v___x_3425_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
return v___x_3434_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_3437_ = l_Lean_stringToMessageData(v___x_3436_);
return v___x_3437_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_3440_ = l_Lean_stringToMessageData(v___x_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3441_, lean_object* v_declHint_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; lean_object* v_env_3446_; uint8_t v___x_3447_; 
v___x_3445_ = lean_st_ref_get(v___y_3443_);
v_env_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc_ref(v_env_3446_);
lean_dec(v___x_3445_);
v___x_3447_ = l_Lean_Name_isAnonymous(v_declHint_3442_);
if (v___x_3447_ == 0)
{
uint8_t v_isExporting_3448_; 
v_isExporting_3448_ = lean_ctor_get_uint8(v_env_3446_, sizeof(void*)*8);
if (v_isExporting_3448_ == 0)
{
lean_object* v___x_3449_; 
lean_dec_ref(v_env_3446_);
lean_dec(v_declHint_3442_);
v___x_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3449_, 0, v_msg_3441_);
return v___x_3449_;
}
else
{
lean_object* v___x_3450_; uint8_t v___x_3451_; 
lean_inc_ref(v_env_3446_);
v___x_3450_ = l_Lean_Environment_setExporting(v_env_3446_, v___x_3447_);
lean_inc(v_declHint_3442_);
lean_inc_ref(v___x_3450_);
v___x_3451_ = l_Lean_Environment_contains(v___x_3450_, v_declHint_3442_, v_isExporting_3448_);
if (v___x_3451_ == 0)
{
lean_object* v___x_3452_; 
lean_dec_ref(v___x_3450_);
lean_dec_ref(v_env_3446_);
lean_dec(v_declHint_3442_);
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v_msg_3441_);
return v___x_3452_;
}
else
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v_c_3458_; lean_object* v___x_3459_; 
v___x_3453_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3454_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3455_ = l_Lean_Options_empty;
v___x_3456_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3450_);
lean_ctor_set(v___x_3456_, 1, v___x_3453_);
lean_ctor_set(v___x_3456_, 2, v___x_3454_);
lean_ctor_set(v___x_3456_, 3, v___x_3455_);
lean_inc(v_declHint_3442_);
v___x_3457_ = l_Lean_MessageData_ofConstName(v_declHint_3442_, v___x_3447_);
v_c_3458_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3458_, 0, v___x_3456_);
lean_ctor_set(v_c_3458_, 1, v___x_3457_);
v___x_3459_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3446_, v_declHint_3442_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_dec_ref(v_env_3446_);
lean_dec(v_declHint_3442_);
v___x_3460_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
lean_ctor_set(v___x_3461_, 1, v_c_3458_);
v___x_3462_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_3463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3461_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = l_Lean_MessageData_note(v___x_3463_);
v___x_3465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3465_, 0, v_msg_3441_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
return v___x_3466_;
}
else
{
lean_object* v_val_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3502_; 
v_val_3467_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3469_ = v___x_3459_;
v_isShared_3470_ = v_isSharedCheck_3502_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_val_3467_);
lean_dec(v___x_3459_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3502_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v_mod_3474_; uint8_t v___x_3475_; 
v___x_3471_ = lean_box(0);
v___x_3472_ = l_Lean_Environment_header(v_env_3446_);
lean_dec_ref(v_env_3446_);
v___x_3473_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3472_);
v_mod_3474_ = lean_array_get(v___x_3471_, v___x_3473_, v_val_3467_);
lean_dec(v_val_3467_);
lean_dec_ref(v___x_3473_);
v___x_3475_ = l_Lean_isPrivateName(v_declHint_3442_);
lean_dec(v_declHint_3442_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3487_; 
v___x_3476_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_3477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
lean_ctor_set(v___x_3477_, 1, v_c_3458_);
v___x_3478_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_3479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3477_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v___x_3480_ = l_Lean_MessageData_ofName(v_mod_3474_);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3479_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = l_Lean_MessageData_note(v___x_3483_);
v___x_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3485_, 0, v_msg_3441_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set_tag(v___x_3469_, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3485_);
v___x_3487_ = v___x_3469_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3489_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v_c_3458_);
v___x_3491_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_3492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = l_Lean_MessageData_ofName(v_mod_3474_);
v___x_3494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3492_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_3496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3494_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v___x_3497_ = l_Lean_MessageData_note(v___x_3496_);
v___x_3498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3498_, 0, v_msg_3441_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set_tag(v___x_3469_, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3498_);
v___x_3500_ = v___x_3469_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3503_; 
lean_dec_ref(v_env_3446_);
lean_dec(v_declHint_3442_);
v___x_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3503_, 0, v_msg_3441_);
return v___x_3503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3504_, lean_object* v_declHint_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3504_, v_declHint_3505_, v___y_3506_);
lean_dec(v___y_3506_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3509_, lean_object* v_declHint_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v___x_3516_; lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3526_; 
v___x_3516_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3509_, v_declHint_3510_, v___y_3514_);
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3526_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3526_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v___x_3521_ = l_Lean_unknownIdentifierMessageTag;
v___x_3522_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
lean_ctor_set(v___x_3522_, 1, v_a_3517_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3522_);
v___x_3524_ = v___x_3519_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3527_, lean_object* v_declHint_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3527_, v_declHint_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3535_, lean_object* v_msg_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_fileName_3542_; lean_object* v_fileMap_3543_; lean_object* v_options_3544_; lean_object* v_currRecDepth_3545_; lean_object* v_maxRecDepth_3546_; lean_object* v_ref_3547_; lean_object* v_currNamespace_3548_; lean_object* v_openDecls_3549_; lean_object* v_initHeartbeats_3550_; lean_object* v_maxHeartbeats_3551_; lean_object* v_quotContext_3552_; lean_object* v_currMacroScope_3553_; uint8_t v_diag_3554_; lean_object* v_cancelTk_x3f_3555_; uint8_t v_suppressElabErrors_3556_; lean_object* v_inheritedTraceOptions_3557_; lean_object* v_ref_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v_fileName_3542_ = lean_ctor_get(v___y_3539_, 0);
v_fileMap_3543_ = lean_ctor_get(v___y_3539_, 1);
v_options_3544_ = lean_ctor_get(v___y_3539_, 2);
v_currRecDepth_3545_ = lean_ctor_get(v___y_3539_, 3);
v_maxRecDepth_3546_ = lean_ctor_get(v___y_3539_, 4);
v_ref_3547_ = lean_ctor_get(v___y_3539_, 5);
v_currNamespace_3548_ = lean_ctor_get(v___y_3539_, 6);
v_openDecls_3549_ = lean_ctor_get(v___y_3539_, 7);
v_initHeartbeats_3550_ = lean_ctor_get(v___y_3539_, 8);
v_maxHeartbeats_3551_ = lean_ctor_get(v___y_3539_, 9);
v_quotContext_3552_ = lean_ctor_get(v___y_3539_, 10);
v_currMacroScope_3553_ = lean_ctor_get(v___y_3539_, 11);
v_diag_3554_ = lean_ctor_get_uint8(v___y_3539_, sizeof(void*)*14);
v_cancelTk_x3f_3555_ = lean_ctor_get(v___y_3539_, 12);
v_suppressElabErrors_3556_ = lean_ctor_get_uint8(v___y_3539_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3557_ = lean_ctor_get(v___y_3539_, 13);
v_ref_3558_ = l_Lean_replaceRef(v_ref_3535_, v_ref_3547_);
lean_inc_ref(v_inheritedTraceOptions_3557_);
lean_inc(v_cancelTk_x3f_3555_);
lean_inc(v_currMacroScope_3553_);
lean_inc(v_quotContext_3552_);
lean_inc(v_maxHeartbeats_3551_);
lean_inc(v_initHeartbeats_3550_);
lean_inc(v_openDecls_3549_);
lean_inc(v_currNamespace_3548_);
lean_inc(v_maxRecDepth_3546_);
lean_inc(v_currRecDepth_3545_);
lean_inc_ref(v_options_3544_);
lean_inc_ref(v_fileMap_3543_);
lean_inc_ref(v_fileName_3542_);
v___x_3559_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3559_, 0, v_fileName_3542_);
lean_ctor_set(v___x_3559_, 1, v_fileMap_3543_);
lean_ctor_set(v___x_3559_, 2, v_options_3544_);
lean_ctor_set(v___x_3559_, 3, v_currRecDepth_3545_);
lean_ctor_set(v___x_3559_, 4, v_maxRecDepth_3546_);
lean_ctor_set(v___x_3559_, 5, v_ref_3558_);
lean_ctor_set(v___x_3559_, 6, v_currNamespace_3548_);
lean_ctor_set(v___x_3559_, 7, v_openDecls_3549_);
lean_ctor_set(v___x_3559_, 8, v_initHeartbeats_3550_);
lean_ctor_set(v___x_3559_, 9, v_maxHeartbeats_3551_);
lean_ctor_set(v___x_3559_, 10, v_quotContext_3552_);
lean_ctor_set(v___x_3559_, 11, v_currMacroScope_3553_);
lean_ctor_set(v___x_3559_, 12, v_cancelTk_x3f_3555_);
lean_ctor_set(v___x_3559_, 13, v_inheritedTraceOptions_3557_);
lean_ctor_set_uint8(v___x_3559_, sizeof(void*)*14, v_diag_3554_);
lean_ctor_set_uint8(v___x_3559_, sizeof(void*)*14 + 1, v_suppressElabErrors_3556_);
v___x_3560_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3536_, v___y_3537_, v___y_3538_, v___x_3559_, v___y_3540_);
lean_dec_ref(v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3561_, lean_object* v_msg_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3561_, v_msg_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v_ref_3561_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3569_, lean_object* v_msg_3570_, lean_object* v_declHint_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v___x_3577_; lean_object* v_a_3578_; lean_object* v___x_3579_; 
v___x_3577_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3570_, v_declHint_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref(v___x_3577_);
v___x_3579_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3569_, v_a_3578_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3580_, lean_object* v_msg_3581_, lean_object* v_declHint_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3580_, v_msg_3581_, v_declHint_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v_ref_3580_);
return v_res_3588_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3591_ = l_Lean_stringToMessageData(v___x_3590_);
return v___x_3591_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3594_ = l_Lean_stringToMessageData(v___x_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3595_, lean_object* v_constName_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; uint8_t v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3602_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3603_ = 0;
lean_inc(v_constName_3596_);
v___x_3604_ = l_Lean_MessageData_ofConstName(v_constName_3596_, v___x_3603_);
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3602_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3595_, v___x_3607_, v_constName_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3609_, lean_object* v_constName_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3609_, v_constName_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v_ref_3609_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_ref_3623_; lean_object* v___x_3624_; 
v_ref_3623_ = lean_ctor_get(v___y_3620_, 5);
v___x_3624_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3623_, v_constName_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v___x_3638_; lean_object* v_env_3639_; uint8_t v___x_3640_; lean_object* v___x_3641_; 
v___x_3638_ = lean_st_ref_get(v___y_3636_);
v_env_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc_ref(v_env_3639_);
lean_dec(v___x_3638_);
v___x_3640_ = 0;
lean_inc(v_constName_3632_);
v___x_3641_ = l_Lean_Environment_find_x3f(v_env_3639_, v_constName_3632_, v___x_3640_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
return v___x_3642_;
}
else
{
lean_object* v_val_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_dec(v_constName_3632_);
v_val_3643_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3641_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_val_3643_);
lean_dec(v___x_3641_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 0);
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_val_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
return v_res_3657_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3660_ = l_Lean_stringToMessageData(v___x_3659_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3661_, lean_object* v_baseName_3662_, lean_object* v_splitterName_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v___x_3669_; uint8_t v_foApprox_3670_; uint8_t v_ctxApprox_3671_; uint8_t v_quasiPatternApprox_3672_; uint8_t v_constApprox_3673_; uint8_t v_isDefEqStuckEx_3674_; uint8_t v_unificationHints_3675_; uint8_t v_proofIrrelevance_3676_; uint8_t v_assignSyntheticOpaque_3677_; uint8_t v_offsetCnstrs_3678_; uint8_t v_transparency_3679_; uint8_t v_univApprox_3680_; uint8_t v_iota_3681_; uint8_t v_beta_3682_; uint8_t v_proj_3683_; uint8_t v_zeta_3684_; uint8_t v_zetaDelta_3685_; uint8_t v_zetaUnused_3686_; uint8_t v_zetaHave_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3750_; 
v___x_3669_ = l_Lean_Meta_Context_config(v_a_3664_);
v_foApprox_3670_ = lean_ctor_get_uint8(v___x_3669_, 0);
v_ctxApprox_3671_ = lean_ctor_get_uint8(v___x_3669_, 1);
v_quasiPatternApprox_3672_ = lean_ctor_get_uint8(v___x_3669_, 2);
v_constApprox_3673_ = lean_ctor_get_uint8(v___x_3669_, 3);
v_isDefEqStuckEx_3674_ = lean_ctor_get_uint8(v___x_3669_, 4);
v_unificationHints_3675_ = lean_ctor_get_uint8(v___x_3669_, 5);
v_proofIrrelevance_3676_ = lean_ctor_get_uint8(v___x_3669_, 6);
v_assignSyntheticOpaque_3677_ = lean_ctor_get_uint8(v___x_3669_, 7);
v_offsetCnstrs_3678_ = lean_ctor_get_uint8(v___x_3669_, 8);
v_transparency_3679_ = lean_ctor_get_uint8(v___x_3669_, 9);
v_univApprox_3680_ = lean_ctor_get_uint8(v___x_3669_, 11);
v_iota_3681_ = lean_ctor_get_uint8(v___x_3669_, 12);
v_beta_3682_ = lean_ctor_get_uint8(v___x_3669_, 13);
v_proj_3683_ = lean_ctor_get_uint8(v___x_3669_, 14);
v_zeta_3684_ = lean_ctor_get_uint8(v___x_3669_, 15);
v_zetaDelta_3685_ = lean_ctor_get_uint8(v___x_3669_, 16);
v_zetaUnused_3686_ = lean_ctor_get_uint8(v___x_3669_, 17);
v_zetaHave_3687_ = lean_ctor_get_uint8(v___x_3669_, 18);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3689_ = v___x_3669_;
v_isShared_3690_ = v_isSharedCheck_3750_;
goto v_resetjp_3688_;
}
else
{
lean_dec(v___x_3669_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3750_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
uint8_t v_trackZetaDelta_3691_; lean_object* v_zetaDeltaSet_3692_; lean_object* v_lctx_3693_; lean_object* v_localInstances_3694_; lean_object* v_defEqCtx_x3f_3695_; lean_object* v_synthPendingDepth_3696_; lean_object* v_canUnfold_x3f_3697_; uint8_t v_univApprox_3698_; uint8_t v_inTypeClassResolution_3699_; uint8_t v_cacheInferType_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3748_; 
v_trackZetaDelta_3691_ = lean_ctor_get_uint8(v_a_3664_, sizeof(void*)*7);
v_zetaDeltaSet_3692_ = lean_ctor_get(v_a_3664_, 1);
v_lctx_3693_ = lean_ctor_get(v_a_3664_, 2);
v_localInstances_3694_ = lean_ctor_get(v_a_3664_, 3);
v_defEqCtx_x3f_3695_ = lean_ctor_get(v_a_3664_, 4);
v_synthPendingDepth_3696_ = lean_ctor_get(v_a_3664_, 5);
v_canUnfold_x3f_3697_ = lean_ctor_get(v_a_3664_, 6);
v_univApprox_3698_ = lean_ctor_get_uint8(v_a_3664_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3699_ = lean_ctor_get_uint8(v_a_3664_, sizeof(void*)*7 + 2);
v_cacheInferType_3700_ = lean_ctor_get_uint8(v_a_3664_, sizeof(void*)*7 + 3);
v_isSharedCheck_3748_ = !lean_is_exclusive(v_a_3664_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; 
v_unused_3749_ = lean_ctor_get(v_a_3664_, 0);
lean_dec(v_unused_3749_);
v___x_3702_ = v_a_3664_;
v_isShared_3703_ = v_isSharedCheck_3748_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_canUnfold_x3f_3697_);
lean_inc(v_synthPendingDepth_3696_);
lean_inc(v_defEqCtx_x3f_3695_);
lean_inc(v_localInstances_3694_);
lean_inc(v_lctx_3693_);
lean_inc(v_zetaDeltaSet_3692_);
lean_dec(v_a_3664_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3748_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
uint8_t v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = 2;
if (v_isShared_3690_ == 0)
{
v___x_3706_ = v___x_3689_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 0, v_foApprox_3670_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 1, v_ctxApprox_3671_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 2, v_quasiPatternApprox_3672_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 3, v_constApprox_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 4, v_isDefEqStuckEx_3674_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 5, v_unificationHints_3675_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 6, v_proofIrrelevance_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 7, v_assignSyntheticOpaque_3677_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 8, v_offsetCnstrs_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 9, v_transparency_3679_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 11, v_univApprox_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 12, v_iota_3681_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 13, v_beta_3682_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 14, v_proj_3683_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 15, v_zeta_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 16, v_zetaDelta_3685_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 17, v_zetaUnused_3686_);
lean_ctor_set_uint8(v_reuseFailAlloc_3747_, 18, v_zetaHave_3687_);
v___x_3706_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
uint64_t v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
lean_ctor_set_uint8(v___x_3706_, 10, v___x_3704_);
v___x_3707_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3706_);
v___x_3708_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3708_, 0, v___x_3706_);
lean_ctor_set_uint64(v___x_3708_, sizeof(void*)*1, v___x_3707_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3708_);
v___x_3710_ = v___x_3702_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_zetaDeltaSet_3692_);
lean_ctor_set(v_reuseFailAlloc_3746_, 2, v_lctx_3693_);
lean_ctor_set(v_reuseFailAlloc_3746_, 3, v_localInstances_3694_);
lean_ctor_set(v_reuseFailAlloc_3746_, 4, v_defEqCtx_x3f_3695_);
lean_ctor_set(v_reuseFailAlloc_3746_, 5, v_synthPendingDepth_3696_);
lean_ctor_set(v_reuseFailAlloc_3746_, 6, v_canUnfold_x3f_3697_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, sizeof(void*)*7, v_trackZetaDelta_3691_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, sizeof(void*)*7 + 1, v_univApprox_3698_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3699_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, sizeof(void*)*7 + 3, v_cacheInferType_3700_);
v___x_3710_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3711_; 
lean_inc(v_matchDeclName_3661_);
v___x_3711_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3661_, v___x_3710_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3713_; lean_object* v_a_3714_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref(v___x_3711_);
lean_inc(v_matchDeclName_3661_);
v___x_3713_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_3661_, v_a_3667_);
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref(v___x_3713_);
if (lean_obj_tag(v_a_3714_) == 1)
{
lean_object* v_val_3715_; lean_object* v_numParams_3716_; lean_object* v_numDiscrs_3717_; lean_object* v_altInfos_3718_; lean_object* v_uElimPos_x3f_3719_; lean_object* v_discrInfos_3720_; lean_object* v_overlaps_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___f_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___f_3729_; uint8_t v___x_3730_; lean_object* v___x_3731_; 
v_val_3715_ = lean_ctor_get(v_a_3714_, 0);
lean_inc(v_val_3715_);
lean_dec_ref(v_a_3714_);
v_numParams_3716_ = lean_ctor_get(v_val_3715_, 0);
lean_inc(v_numParams_3716_);
v_numDiscrs_3717_ = lean_ctor_get(v_val_3715_, 1);
lean_inc(v_numDiscrs_3717_);
v_altInfos_3718_ = lean_ctor_get(v_val_3715_, 2);
lean_inc_ref(v_altInfos_3718_);
v_uElimPos_x3f_3719_ = lean_ctor_get(v_val_3715_, 3);
lean_inc(v_uElimPos_x3f_3719_);
v_discrInfos_3720_ = lean_ctor_get(v_val_3715_, 4);
lean_inc_ref(v_discrInfos_3720_);
v_overlaps_3721_ = lean_ctor_get(v_val_3715_, 5);
lean_inc_ref_n(v_overlaps_3721_, 2);
v___x_3722_ = l_Lean_instInhabitedExpr;
v___x_3723_ = l_Lean_ConstantInfo_levelParams(v_a_3712_);
v___x_3724_ = lean_box(0);
lean_inc(v___x_3723_);
v___x_3725_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_3723_, v___x_3724_);
lean_inc(v_splitterName_3663_);
v___f_3726_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3726_, 0, v_overlaps_3721_);
lean_closure_set(v___f_3726_, 1, v_splitterName_3663_);
v___x_3727_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3720_);
v___x_3728_ = l_Lean_ConstantInfo_type(v_a_3712_);
lean_inc_ref(v___x_3728_);
v___f_3729_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3729_, 0, v_splitterName_3663_);
lean_closure_set(v___f_3729_, 1, v_matchDeclName_3661_);
lean_closure_set(v___f_3729_, 2, v_numParams_3716_);
lean_closure_set(v___f_3729_, 3, v_val_3715_);
lean_closure_set(v___f_3729_, 4, v___x_3722_);
lean_closure_set(v___f_3729_, 5, v_numDiscrs_3717_);
lean_closure_set(v___f_3729_, 6, v_baseName_3662_);
lean_closure_set(v___f_3729_, 7, v_a_3712_);
lean_closure_set(v___f_3729_, 8, v___x_3725_);
lean_closure_set(v___f_3729_, 9, v___x_3723_);
lean_closure_set(v___f_3729_, 10, v___x_3727_);
lean_closure_set(v___f_3729_, 11, v_uElimPos_x3f_3719_);
lean_closure_set(v___f_3729_, 12, v_discrInfos_3720_);
lean_closure_set(v___f_3729_, 13, v_overlaps_3721_);
lean_closure_set(v___f_3729_, 14, v___f_3726_);
lean_closure_set(v___f_3729_, 15, v___x_3728_);
lean_closure_set(v___f_3729_, 16, v_altInfos_3718_);
v___x_3730_ = 0;
v___x_3731_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3728_, v___f_3729_, v___x_3730_, v___x_3730_, v___x_3710_, v_a_3665_, v_a_3666_, v_a_3667_);
lean_dec_ref(v___x_3710_);
return v___x_3731_;
}
else
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_dec(v_a_3714_);
lean_dec(v_a_3712_);
lean_dec(v_splitterName_3663_);
lean_dec(v_baseName_3662_);
v___x_3732_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3733_ = l_Lean_MessageData_ofName(v_matchDeclName_3661_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3736_, v___x_3710_, v_a_3665_, v_a_3666_, v_a_3667_);
lean_dec_ref(v___x_3710_);
return v___x_3737_;
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec_ref(v___x_3710_);
lean_dec(v_splitterName_3663_);
lean_dec(v_baseName_3662_);
lean_dec(v_matchDeclName_3661_);
v_a_3738_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3711_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3711_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3751_, lean_object* v_baseName_3752_, lean_object* v_splitterName_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3751_, v_baseName_3752_, v_splitterName_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec(v_a_3755_);
return v_res_3759_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3760_, lean_object* v_ys_3761_, lean_object* v_hsz_3762_, lean_object* v_x_3763_, lean_object* v_x_3764_){
_start:
{
uint8_t v___x_3765_; 
v___x_3765_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3760_, v_ys_3761_, v_x_3763_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3766_, lean_object* v_ys_3767_, lean_object* v_hsz_3768_, lean_object* v_x_3769_, lean_object* v_x_3770_){
_start:
{
uint8_t v_res_3771_; lean_object* v_r_3772_; 
v_res_3771_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3766_, v_ys_3767_, v_hsz_3768_, v_x_3769_, v_x_3770_);
lean_dec_ref(v_ys_3767_);
lean_dec_ref(v_xs_3766_);
v_r_3772_ = lean_box(v_res_3771_);
return v_r_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3773_, lean_object* v_R_3774_, lean_object* v_a_3775_, lean_object* v_b_3776_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3775_, v_b_3776_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3778_, lean_object* v_val_3779_, lean_object* v_baseName_3780_, lean_object* v___x_3781_, lean_object* v_a_3782_, lean_object* v___x_3783_, lean_object* v___x_3784_, lean_object* v___x_3785_, lean_object* v_matchDeclName_3786_, lean_object* v___x_3787_, lean_object* v___x_3788_, lean_object* v___x_3789_, lean_object* v_inst_3790_, lean_object* v_R_3791_, lean_object* v_a_3792_, lean_object* v_b_3793_, lean_object* v_c_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3778_, v_val_3779_, v_baseName_3780_, v___x_3781_, v_a_3782_, v___x_3783_, v___x_3784_, v___x_3785_, v_matchDeclName_3786_, v___x_3787_, v___x_3788_, v___x_3789_, v_a_3792_, v_b_3793_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3801_ = _args[0];
lean_object* v_val_3802_ = _args[1];
lean_object* v_baseName_3803_ = _args[2];
lean_object* v___x_3804_ = _args[3];
lean_object* v_a_3805_ = _args[4];
lean_object* v___x_3806_ = _args[5];
lean_object* v___x_3807_ = _args[6];
lean_object* v___x_3808_ = _args[7];
lean_object* v_matchDeclName_3809_ = _args[8];
lean_object* v___x_3810_ = _args[9];
lean_object* v___x_3811_ = _args[10];
lean_object* v___x_3812_ = _args[11];
lean_object* v_inst_3813_ = _args[12];
lean_object* v_R_3814_ = _args[13];
lean_object* v_a_3815_ = _args[14];
lean_object* v_b_3816_ = _args[15];
lean_object* v_c_3817_ = _args[16];
lean_object* v___y_3818_ = _args[17];
lean_object* v___y_3819_ = _args[18];
lean_object* v___y_3820_ = _args[19];
lean_object* v___y_3821_ = _args[20];
lean_object* v___y_3822_ = _args[21];
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3801_, v_val_3802_, v_baseName_3803_, v___x_3804_, v_a_3805_, v___x_3806_, v___x_3807_, v___x_3808_, v_matchDeclName_3809_, v___x_3810_, v___x_3811_, v___x_3812_, v_inst_3813_, v_R_3814_, v_a_3815_, v_b_3816_, v_c_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v_upperBound_3801_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3824_, lean_object* v_constName_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v___x_3831_; 
v___x_3831_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3832_, lean_object* v_constName_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3832_, v_constName_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3840_, lean_object* v_ref_3841_, lean_object* v_constName_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3841_, v_constName_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3849_, lean_object* v_ref_3850_, lean_object* v_constName_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3849_, v_ref_3850_, v_constName_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v_ref_3850_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3858_, lean_object* v_ref_3859_, lean_object* v_msg_3860_, lean_object* v_declHint_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3859_, v_msg_3860_, v_declHint_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3868_, lean_object* v_ref_3869_, lean_object* v_msg_3870_, lean_object* v_declHint_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3868_, v_ref_3869_, v_msg_3870_, v_declHint_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v_ref_3869_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3878_, lean_object* v_declHint_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3878_, v_declHint_3879_, v___y_3883_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3886_, lean_object* v_declHint_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3886_, v_declHint_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3894_, lean_object* v_ref_3895_, lean_object* v_msg_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3895_, v_msg_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3903_, lean_object* v_ref_3904_, lean_object* v_msg_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3903_, v_ref_3904_, v_msg_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v_ref_3904_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3912_, lean_object* v_vals_3913_, lean_object* v_i_3914_, lean_object* v_k_3915_){
_start:
{
lean_object* v___x_3916_; uint8_t v___x_3917_; 
v___x_3916_ = lean_array_get_size(v_keys_3912_);
v___x_3917_ = lean_nat_dec_lt(v_i_3914_, v___x_3916_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; 
lean_dec(v_i_3914_);
v___x_3918_ = lean_box(0);
return v___x_3918_;
}
else
{
lean_object* v_k_x27_3919_; uint8_t v___x_3920_; 
v_k_x27_3919_ = lean_array_fget_borrowed(v_keys_3912_, v_i_3914_);
v___x_3920_ = lean_name_eq(v_k_3915_, v_k_x27_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = lean_unsigned_to_nat(1u);
v___x_3922_ = lean_nat_add(v_i_3914_, v___x_3921_);
lean_dec(v_i_3914_);
v_i_3914_ = v___x_3922_;
goto _start;
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3924_ = lean_array_fget_borrowed(v_vals_3913_, v_i_3914_);
lean_dec(v_i_3914_);
lean_inc(v___x_3924_);
v___x_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3926_, lean_object* v_vals_3927_, lean_object* v_i_3928_, lean_object* v_k_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3926_, v_vals_3927_, v_i_3928_, v_k_3929_);
lean_dec(v_k_3929_);
lean_dec_ref(v_vals_3927_);
lean_dec_ref(v_keys_3926_);
return v_res_3930_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_3931_; size_t v___x_3932_; size_t v___x_3933_; 
v___x_3931_ = ((size_t)5ULL);
v___x_3932_ = ((size_t)1ULL);
v___x_3933_ = lean_usize_shift_left(v___x_3932_, v___x_3931_);
return v___x_3933_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_3934_; size_t v___x_3935_; size_t v___x_3936_; 
v___x_3934_ = ((size_t)1ULL);
v___x_3935_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0);
v___x_3936_ = lean_usize_sub(v___x_3935_, v___x_3934_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3937_, size_t v_x_3938_, lean_object* v_x_3939_){
_start:
{
if (lean_obj_tag(v_x_3937_) == 0)
{
lean_object* v_es_3940_; lean_object* v___x_3941_; size_t v___x_3942_; size_t v___x_3943_; size_t v___x_3944_; lean_object* v_j_3945_; lean_object* v___x_3946_; 
v_es_3940_ = lean_ctor_get(v_x_3937_, 0);
v___x_3941_ = lean_box(2);
v___x_3942_ = ((size_t)5ULL);
v___x_3943_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1);
v___x_3944_ = lean_usize_land(v_x_3938_, v___x_3943_);
v_j_3945_ = lean_usize_to_nat(v___x_3944_);
v___x_3946_ = lean_array_get_borrowed(v___x_3941_, v_es_3940_, v_j_3945_);
lean_dec(v_j_3945_);
switch(lean_obj_tag(v___x_3946_))
{
case 0:
{
lean_object* v_key_3947_; lean_object* v_val_3948_; uint8_t v___x_3949_; 
v_key_3947_ = lean_ctor_get(v___x_3946_, 0);
v_val_3948_ = lean_ctor_get(v___x_3946_, 1);
v___x_3949_ = lean_name_eq(v_x_3939_, v_key_3947_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; 
v___x_3950_ = lean_box(0);
return v___x_3950_;
}
else
{
lean_object* v___x_3951_; 
lean_inc(v_val_3948_);
v___x_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3951_, 0, v_val_3948_);
return v___x_3951_;
}
}
case 1:
{
lean_object* v_node_3952_; size_t v___x_3953_; 
v_node_3952_ = lean_ctor_get(v___x_3946_, 0);
v___x_3953_ = lean_usize_shift_right(v_x_3938_, v___x_3942_);
v_x_3937_ = v_node_3952_;
v_x_3938_ = v___x_3953_;
goto _start;
}
default: 
{
lean_object* v___x_3955_; 
v___x_3955_ = lean_box(0);
return v___x_3955_;
}
}
}
else
{
lean_object* v_ks_3956_; lean_object* v_vs_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v_ks_3956_ = lean_ctor_get(v_x_3937_, 0);
v_vs_3957_ = lean_ctor_get(v_x_3937_, 1);
v___x_3958_ = lean_unsigned_to_nat(0u);
v___x_3959_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3956_, v_vs_3957_, v___x_3958_, v_x_3939_);
return v___x_3959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3960_, lean_object* v_x_3961_, lean_object* v_x_3962_){
_start:
{
size_t v_x_716__boxed_3963_; lean_object* v_res_3964_; 
v_x_716__boxed_3963_ = lean_unbox_usize(v_x_3961_);
lean_dec(v_x_3961_);
v_res_3964_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3960_, v_x_716__boxed_3963_, v_x_3962_);
lean_dec(v_x_3962_);
lean_dec_ref(v_x_3960_);
return v_res_3964_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3965_; uint64_t v___x_3966_; 
v___x_3965_ = lean_unsigned_to_nat(1723u);
v___x_3966_ = lean_uint64_of_nat(v___x_3965_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3967_, lean_object* v_x_3968_){
_start:
{
uint64_t v___y_3970_; 
if (lean_obj_tag(v_x_3968_) == 0)
{
uint64_t v___x_3973_; 
v___x_3973_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0);
v___y_3970_ = v___x_3973_;
goto v___jp_3969_;
}
else
{
uint64_t v_hash_3974_; 
v_hash_3974_ = lean_ctor_get_uint64(v_x_3968_, sizeof(void*)*2);
v___y_3970_ = v_hash_3974_;
goto v___jp_3969_;
}
v___jp_3969_:
{
size_t v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = lean_uint64_to_usize(v___y_3970_);
v___x_3972_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3967_, v___x_3971_, v_x_3968_);
return v___x_3972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3975_, lean_object* v_x_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3975_, v_x_3976_);
lean_dec(v_x_3976_);
lean_dec_ref(v_x_3975_);
return v_res_3977_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3984_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3985_ = l_Lean_stringToMessageData(v___x_3984_);
return v___x_3985_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3987_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3988_ = l_Lean_stringToMessageData(v___x_3987_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v___x_3995_; lean_object* v_env_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3995_ = lean_st_ref_get(v_a_3993_);
v_env_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc_ref(v_env_3996_);
lean_dec(v___x_3995_);
lean_inc_n(v_matchDeclName_3989_, 3);
v___x_3997_ = l_Lean_mkPrivateName(v_env_3996_, v_matchDeclName_3989_);
lean_dec_ref(v_env_3996_);
v___x_3998_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_3997_);
v___x_3999_ = l_Lean_Name_append(v___x_3997_, v___x_3998_);
lean_inc_n(v___x_3999_, 2);
v___x_4000_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_4000_, 0, v_matchDeclName_3989_);
lean_closure_set(v___x_4000_, 1, v___x_3997_);
lean_closure_set(v___x_4000_, 2, v___x_3999_);
v___x_4001_ = l_Lean_Meta_realizeConst(v_matchDeclName_3989_, v___x_3999_, v___x_4000_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4030_; 
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4030_ == 0)
{
lean_object* v_unused_4031_; 
v_unused_4031_ = lean_ctor_get(v___x_4001_, 0);
lean_dec(v_unused_4031_);
v___x_4003_ = v___x_4001_;
v_isShared_4004_ = v_isSharedCheck_4030_;
goto v_resetjp_4002_;
}
else
{
lean_dec(v___x_4001_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4030_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4005_; lean_object* v_env_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v_map_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4028_; 
v___x_4005_ = lean_st_ref_get(v_a_3993_);
v_env_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc_ref(v_env_4006_);
lean_dec(v___x_4005_);
v___x_4007_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_4008_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_4009_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_4010_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4007_, v___x_4008_, v_env_4006_, v___x_4009_, v___x_3999_);
v_map_4011_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4028_ == 0)
{
lean_object* v_unused_4029_; 
v_unused_4029_ = lean_ctor_get(v___x_4010_, 1);
lean_dec(v_unused_4029_);
v___x_4013_ = v___x_4010_;
v_isShared_4014_ = v_isSharedCheck_4028_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_map_4011_);
lean_dec(v___x_4010_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4028_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_4011_, v_matchDeclName_3989_);
lean_dec_ref(v_map_4011_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4019_; 
lean_del_object(v___x_4003_);
v___x_4016_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_4017_ = l_Lean_MessageData_ofName(v_matchDeclName_3989_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set_tag(v___x_4013_, 7);
lean_ctor_set(v___x_4013_, 1, v___x_4017_);
lean_ctor_set(v___x_4013_, 0, v___x_4016_);
v___x_4019_ = v___x_4013_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_4016_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v___x_4017_);
v___x_4019_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4020_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_4021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4019_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
v___x_4022_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_4021_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
lean_dec(v_a_3991_);
lean_dec_ref(v_a_3990_);
return v___x_4022_;
}
}
else
{
lean_object* v_val_4024_; lean_object* v___x_4026_; 
lean_del_object(v___x_4013_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
lean_dec(v_a_3991_);
lean_dec_ref(v_a_3990_);
lean_dec(v_matchDeclName_3989_);
v_val_4024_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_val_4024_);
lean_dec_ref(v___x_4015_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 0, v_val_4024_);
v___x_4026_ = v___x_4003_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_val_4024_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_dec(v___x_3999_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
lean_dec(v_a_3991_);
lean_dec_ref(v_a_3990_);
lean_dec(v_matchDeclName_3989_);
v_a_4032_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4001_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4001_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = lean_get_match_equations_for(v_matchDeclName_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4047_, lean_object* v_x_4048_, lean_object* v_x_4049_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4048_, v_x_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4051_, lean_object* v_x_4052_, lean_object* v_x_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4051_, v_x_4052_, v_x_4053_);
lean_dec(v_x_4053_);
lean_dec_ref(v_x_4052_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4055_, lean_object* v_x_4056_, size_t v_x_4057_, lean_object* v_x_4058_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4056_, v_x_4057_, v_x_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4060_, lean_object* v_x_4061_, lean_object* v_x_4062_, lean_object* v_x_4063_){
_start:
{
size_t v_x_920__boxed_4064_; lean_object* v_res_4065_; 
v_x_920__boxed_4064_ = lean_unbox_usize(v_x_4062_);
lean_dec(v_x_4062_);
v_res_4065_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4060_, v_x_4061_, v_x_920__boxed_4064_, v_x_4063_);
lean_dec(v_x_4063_);
lean_dec_ref(v_x_4061_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4066_, lean_object* v_keys_4067_, lean_object* v_vals_4068_, lean_object* v_heq_4069_, lean_object* v_i_4070_, lean_object* v_k_4071_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4067_, v_vals_4068_, v_i_4070_, v_k_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4073_, lean_object* v_keys_4074_, lean_object* v_vals_4075_, lean_object* v_heq_4076_, lean_object* v_i_4077_, lean_object* v_k_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4073_, v_keys_4074_, v_vals_4075_, v_heq_4076_, v_i_4077_, v_k_4078_);
lean_dec(v_k_4078_);
lean_dec_ref(v_vals_4075_);
lean_dec_ref(v_keys_4074_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4080_, lean_object* v_k_4081_, uint8_t v_cleanupAnnotations_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v___f_4088_; uint8_t v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___f_4088_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4088_, 0, v_k_4081_);
v___x_4089_ = 0;
v___x_4090_ = lean_box(0);
v___x_4091_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4089_, v___x_4090_, v_type_4080_, v___f_4088_, v_cleanupAnnotations_4082_, v___x_4089_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4091_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4091_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
v_a_4100_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4091_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4091_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4108_, lean_object* v_k_4109_, lean_object* v_cleanupAnnotations_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4116_; lean_object* v_res_4117_; 
v_cleanupAnnotations_boxed_4116_ = lean_unbox(v_cleanupAnnotations_4110_);
v_res_4117_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4108_, v_k_4109_, v_cleanupAnnotations_boxed_4116_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4118_, lean_object* v_type_4119_, lean_object* v_k_4120_, uint8_t v_cleanupAnnotations_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4119_, v_k_4120_, v_cleanupAnnotations_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4128_, lean_object* v_type_4129_, lean_object* v_k_4130_, lean_object* v_cleanupAnnotations_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4137_; lean_object* v_res_4138_; 
v_cleanupAnnotations_boxed_4137_ = lean_unbox(v_cleanupAnnotations_4131_);
v_res_4138_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4128_, v_type_4129_, v_k_4130_, v_cleanupAnnotations_boxed_4137_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v_msg_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v___f_4145_; lean_object* v___x_19935__overap_4146_; lean_object* v___x_4147_; 
v___f_4145_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_19935__overap_4146_ = lean_panic_fn_borrowed(v___f_4145_, v_msg_4139_);
lean_inc(v___y_4143_);
lean_inc_ref(v___y_4142_);
lean_inc(v___y_4141_);
lean_inc_ref(v___y_4140_);
v___x_4147_ = lean_apply_5(v___x_19935__overap_4146_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, lean_box(0));
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v_msg_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_msg_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4155_){
_start:
{
uint8_t v_foApprox_4156_; uint8_t v_ctxApprox_4157_; uint8_t v_quasiPatternApprox_4158_; uint8_t v_constApprox_4159_; uint8_t v_isDefEqStuckEx_4160_; uint8_t v_unificationHints_4161_; uint8_t v_proofIrrelevance_4162_; uint8_t v_assignSyntheticOpaque_4163_; uint8_t v_offsetCnstrs_4164_; uint8_t v_transparency_4165_; uint8_t v_univApprox_4166_; uint8_t v_iota_4167_; uint8_t v_beta_4168_; uint8_t v_proj_4169_; uint8_t v_zeta_4170_; uint8_t v_zetaDelta_4171_; uint8_t v_zetaUnused_4172_; uint8_t v_zetaHave_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4181_; 
v_foApprox_4156_ = lean_ctor_get_uint8(v_c_4155_, 0);
v_ctxApprox_4157_ = lean_ctor_get_uint8(v_c_4155_, 1);
v_quasiPatternApprox_4158_ = lean_ctor_get_uint8(v_c_4155_, 2);
v_constApprox_4159_ = lean_ctor_get_uint8(v_c_4155_, 3);
v_isDefEqStuckEx_4160_ = lean_ctor_get_uint8(v_c_4155_, 4);
v_unificationHints_4161_ = lean_ctor_get_uint8(v_c_4155_, 5);
v_proofIrrelevance_4162_ = lean_ctor_get_uint8(v_c_4155_, 6);
v_assignSyntheticOpaque_4163_ = lean_ctor_get_uint8(v_c_4155_, 7);
v_offsetCnstrs_4164_ = lean_ctor_get_uint8(v_c_4155_, 8);
v_transparency_4165_ = lean_ctor_get_uint8(v_c_4155_, 9);
v_univApprox_4166_ = lean_ctor_get_uint8(v_c_4155_, 11);
v_iota_4167_ = lean_ctor_get_uint8(v_c_4155_, 12);
v_beta_4168_ = lean_ctor_get_uint8(v_c_4155_, 13);
v_proj_4169_ = lean_ctor_get_uint8(v_c_4155_, 14);
v_zeta_4170_ = lean_ctor_get_uint8(v_c_4155_, 15);
v_zetaDelta_4171_ = lean_ctor_get_uint8(v_c_4155_, 16);
v_zetaUnused_4172_ = lean_ctor_get_uint8(v_c_4155_, 17);
v_zetaHave_4173_ = lean_ctor_get_uint8(v_c_4155_, 18);
v_isSharedCheck_4181_ = !lean_is_exclusive(v_c_4155_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4175_ = v_c_4155_;
v_isShared_4176_ = v_isSharedCheck_4181_;
goto v_resetjp_4174_;
}
else
{
lean_dec(v_c_4155_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4181_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
uint8_t v___x_4177_; lean_object* v___x_4179_; 
v___x_4177_ = 2;
if (v_isShared_4176_ == 0)
{
v___x_4179_ = v___x_4175_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 0, v_foApprox_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 1, v_ctxApprox_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 2, v_quasiPatternApprox_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 3, v_constApprox_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 4, v_isDefEqStuckEx_4160_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 5, v_unificationHints_4161_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 6, v_proofIrrelevance_4162_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 7, v_assignSyntheticOpaque_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 8, v_offsetCnstrs_4164_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 9, v_transparency_4165_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 11, v_univApprox_4166_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 12, v_iota_4167_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 13, v_beta_4168_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 14, v_proj_4169_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 15, v_zeta_4170_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 16, v_zetaDelta_4171_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 17, v_zetaUnused_4172_);
lean_ctor_set_uint8(v_reuseFailAlloc_4180_, 18, v_zetaHave_4173_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_ctor_set_uint8(v___x_4179_, 10, v___x_4177_);
return v___x_4179_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4182_, lean_object* v_t_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v_dummy_4189_; lean_object* v_nargs_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v_dummy_4189_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4190_ = l_Lean_Expr_getAppNumArgs(v_t_4183_);
lean_inc(v_nargs_4190_);
v___x_4191_ = lean_mk_array(v_nargs_4190_, v_dummy_4189_);
v___x_4192_ = lean_unsigned_to_nat(1u);
v___x_4193_ = lean_nat_sub(v_nargs_4190_, v___x_4192_);
lean_dec(v_nargs_4190_);
v___x_4194_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4183_, v___x_4191_, v___x_4193_);
v___x_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4196_, lean_object* v_t_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4196_, v_t_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec_ref(v_x_4196_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4204_, lean_object* v_x_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4211_, 0, v_snd_4204_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4212_, lean_object* v_x_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4212_, v_x_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec_ref(v_x_4213_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4220_, size_t v_i_4221_, lean_object* v_bs_4222_){
_start:
{
uint8_t v___x_4223_; 
v___x_4223_ = lean_usize_dec_lt(v_i_4221_, v_sz_4220_);
if (v___x_4223_ == 0)
{
return v_bs_4222_;
}
else
{
lean_object* v_v_4224_; lean_object* v_fst_4225_; lean_object* v_snd_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4240_; 
v_v_4224_ = lean_array_uget(v_bs_4222_, v_i_4221_);
v_fst_4225_ = lean_ctor_get(v_v_4224_, 0);
v_snd_4226_ = lean_ctor_get(v_v_4224_, 1);
v_isSharedCheck_4240_ = !lean_is_exclusive(v_v_4224_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4228_ = v_v_4224_;
v_isShared_4229_ = v_isSharedCheck_4240_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_snd_4226_);
lean_inc(v_fst_4225_);
lean_dec(v_v_4224_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4240_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4230_; lean_object* v_bs_x27_4231_; lean_object* v___f_4232_; lean_object* v___x_4234_; 
v___x_4230_ = lean_unsigned_to_nat(0u);
v_bs_x27_4231_ = lean_array_uset(v_bs_4222_, v_i_4221_, v___x_4230_);
v___f_4232_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4232_, 0, v_snd_4226_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 1, v___f_4232_);
v___x_4234_ = v___x_4228_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_fst_4225_);
lean_ctor_set(v_reuseFailAlloc_4239_, 1, v___f_4232_);
v___x_4234_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
size_t v___x_4235_; size_t v___x_4236_; lean_object* v___x_4237_; 
v___x_4235_ = ((size_t)1ULL);
v___x_4236_ = lean_usize_add(v_i_4221_, v___x_4235_);
v___x_4237_ = lean_array_uset(v_bs_x27_4231_, v_i_4221_, v___x_4234_);
v_i_4221_ = v___x_4236_;
v_bs_4222_ = v___x_4237_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4241_, lean_object* v_i_4242_, lean_object* v_bs_4243_){
_start:
{
size_t v_sz_boxed_4244_; size_t v_i_boxed_4245_; lean_object* v_res_4246_; 
v_sz_boxed_4244_ = lean_unbox_usize(v_sz_4241_);
lean_dec(v_sz_4241_);
v_i_boxed_4245_ = lean_unbox_usize(v_i_4242_);
lean_dec(v_i_4242_);
v_res_4246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4244_, v_i_boxed_4245_, v_bs_4243_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4247_, size_t v_i_4248_, lean_object* v_bs_4249_){
_start:
{
uint8_t v___x_4250_; 
v___x_4250_ = lean_usize_dec_lt(v_i_4248_, v_sz_4247_);
if (v___x_4250_ == 0)
{
return v_bs_4249_;
}
else
{
lean_object* v_v_4251_; lean_object* v_fst_4252_; lean_object* v_snd_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4269_; 
v_v_4251_ = lean_array_uget(v_bs_4249_, v_i_4248_);
v_fst_4252_ = lean_ctor_get(v_v_4251_, 0);
v_snd_4253_ = lean_ctor_get(v_v_4251_, 1);
v_isSharedCheck_4269_ = !lean_is_exclusive(v_v_4251_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4255_ = v_v_4251_;
v_isShared_4256_ = v_isSharedCheck_4269_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_snd_4253_);
lean_inc(v_fst_4252_);
lean_dec(v_v_4251_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4269_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4257_; lean_object* v_bs_x27_4258_; uint8_t v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4262_; 
v___x_4257_ = lean_unsigned_to_nat(0u);
v_bs_x27_4258_ = lean_array_uset(v_bs_4249_, v_i_4248_, v___x_4257_);
v___x_4259_ = 0;
v___x_4260_ = lean_box(v___x_4259_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set(v___x_4255_, 0, v___x_4260_);
v___x_4262_ = v___x_4255_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4260_);
lean_ctor_set(v_reuseFailAlloc_4268_, 1, v_snd_4253_);
v___x_4262_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
lean_object* v___x_4263_; size_t v___x_4264_; size_t v___x_4265_; lean_object* v___x_4266_; 
v___x_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4263_, 0, v_fst_4252_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = ((size_t)1ULL);
v___x_4265_ = lean_usize_add(v_i_4248_, v___x_4264_);
v___x_4266_ = lean_array_uset(v_bs_x27_4258_, v_i_4248_, v___x_4263_);
v_i_4248_ = v___x_4265_;
v_bs_4249_ = v___x_4266_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4270_, lean_object* v_i_4271_, lean_object* v_bs_4272_){
_start:
{
size_t v_sz_boxed_4273_; size_t v_i_boxed_4274_; lean_object* v_res_4275_; 
v_sz_boxed_4273_ = lean_unbox_usize(v_sz_4270_);
lean_dec(v_sz_4270_);
v_i_boxed_4274_ = lean_unbox_usize(v_i_4271_);
lean_dec(v_i_4271_);
v_res_4275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4273_, v_i_boxed_4274_, v_bs_4272_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4276_, lean_object* v_a_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_21857__overap_4284_; lean_object* v___x_4285_; 
v___x_4283_ = l_Lean_instInhabitedExpr;
v___x_21857__overap_4284_ = l_instInhabitedOfMonad___redArg(v___x_4276_, v___x_4283_);
lean_inc(v___y_4281_);
lean_inc_ref(v___y_4280_);
lean_inc(v___y_4279_);
lean_inc_ref(v___y_4278_);
v___x_4285_ = lean_apply_5(v___x_21857__overap_4284_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, lean_box(0));
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4286_, lean_object* v_a_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4286_, v_a_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec_ref(v_a_4287_);
return v_res_4293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_instMonadEIO(lean_box(0));
return v___x_4294_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4295_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4296_ = l_StateRefT_x27_instMonad___redArg(v___x_4295_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4301_, lean_object* v_declInfos_4302_, lean_object* v_k_4303_, lean_object* v_kind_4304_, lean_object* v_x_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
uint8_t v_kind_boxed_4311_; lean_object* v_res_4312_; 
v_kind_boxed_4311_ = lean_unbox(v_kind_4304_);
v_res_4312_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4301_, v_declInfos_4302_, v_k_4303_, v_kind_boxed_4311_, v_x_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4313_, lean_object* v_k_4314_, uint8_t v_kind_4315_, lean_object* v_acc_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v___x_4322_; lean_object* v_toApplicative_4323_; lean_object* v_toFunctor_4324_; lean_object* v_toSeq_4325_; lean_object* v_toSeqLeft_4326_; lean_object* v_toSeqRight_4327_; lean_object* v___f_4328_; lean_object* v___f_4329_; lean_object* v___f_4330_; lean_object* v___f_4331_; lean_object* v___x_4332_; lean_object* v___f_4333_; lean_object* v___f_4334_; lean_object* v___f_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v_toApplicative_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4388_; 
v___x_4322_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4323_ = lean_ctor_get(v___x_4322_, 0);
v_toFunctor_4324_ = lean_ctor_get(v_toApplicative_4323_, 0);
v_toSeq_4325_ = lean_ctor_get(v_toApplicative_4323_, 2);
v_toSeqLeft_4326_ = lean_ctor_get(v_toApplicative_4323_, 3);
v_toSeqRight_4327_ = lean_ctor_get(v_toApplicative_4323_, 4);
v___f_4328_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4329_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4324_, 2);
v___f_4330_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4330_, 0, v_toFunctor_4324_);
v___f_4331_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4331_, 0, v_toFunctor_4324_);
v___x_4332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___f_4330_);
lean_ctor_set(v___x_4332_, 1, v___f_4331_);
lean_inc(v_toSeqRight_4327_);
v___f_4333_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4333_, 0, v_toSeqRight_4327_);
lean_inc(v_toSeqLeft_4326_);
v___f_4334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4334_, 0, v_toSeqLeft_4326_);
lean_inc(v_toSeq_4325_);
v___f_4335_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4335_, 0, v_toSeq_4325_);
v___x_4336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4332_);
lean_ctor_set(v___x_4336_, 1, v___f_4328_);
lean_ctor_set(v___x_4336_, 2, v___f_4335_);
lean_ctor_set(v___x_4336_, 3, v___f_4334_);
lean_ctor_set(v___x_4336_, 4, v___f_4333_);
v___x_4337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4336_);
lean_ctor_set(v___x_4337_, 1, v___f_4329_);
v___x_4338_ = l_StateRefT_x27_instMonad___redArg(v___x_4337_);
v_toApplicative_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4388_ == 0)
{
lean_object* v_unused_4389_; 
v_unused_4389_ = lean_ctor_get(v___x_4338_, 1);
lean_dec(v_unused_4389_);
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4388_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_toApplicative_4339_);
lean_dec(v___x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4388_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v_toFunctor_4343_; lean_object* v_toSeq_4344_; lean_object* v_toSeqLeft_4345_; lean_object* v_toSeqRight_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4386_; 
v_toFunctor_4343_ = lean_ctor_get(v_toApplicative_4339_, 0);
v_toSeq_4344_ = lean_ctor_get(v_toApplicative_4339_, 2);
v_toSeqLeft_4345_ = lean_ctor_get(v_toApplicative_4339_, 3);
v_toSeqRight_4346_ = lean_ctor_get(v_toApplicative_4339_, 4);
v_isSharedCheck_4386_ = !lean_is_exclusive(v_toApplicative_4339_);
if (v_isSharedCheck_4386_ == 0)
{
lean_object* v_unused_4387_; 
v_unused_4387_ = lean_ctor_get(v_toApplicative_4339_, 1);
lean_dec(v_unused_4387_);
v___x_4348_ = v_toApplicative_4339_;
v_isShared_4349_ = v_isSharedCheck_4386_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_toSeqRight_4346_);
lean_inc(v_toSeqLeft_4345_);
lean_inc(v_toSeq_4344_);
lean_inc(v_toFunctor_4343_);
lean_dec(v_toApplicative_4339_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4386_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___f_4350_; lean_object* v___f_4351_; lean_object* v___f_4352_; lean_object* v___f_4353_; lean_object* v___x_4354_; lean_object* v___f_4355_; lean_object* v___f_4356_; lean_object* v___f_4357_; lean_object* v___x_4359_; 
v___f_4350_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4351_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4343_);
v___f_4352_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4352_, 0, v_toFunctor_4343_);
v___f_4353_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4353_, 0, v_toFunctor_4343_);
v___x_4354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4354_, 0, v___f_4352_);
lean_ctor_set(v___x_4354_, 1, v___f_4353_);
v___f_4355_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4355_, 0, v_toSeqRight_4346_);
v___f_4356_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4356_, 0, v_toSeqLeft_4345_);
v___f_4357_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4357_, 0, v_toSeq_4344_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 4, v___f_4355_);
lean_ctor_set(v___x_4348_, 3, v___f_4356_);
lean_ctor_set(v___x_4348_, 2, v___f_4357_);
lean_ctor_set(v___x_4348_, 1, v___f_4350_);
lean_ctor_set(v___x_4348_, 0, v___x_4354_);
v___x_4359_ = v___x_4348_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4354_);
lean_ctor_set(v_reuseFailAlloc_4385_, 1, v___f_4350_);
lean_ctor_set(v_reuseFailAlloc_4385_, 2, v___f_4357_);
lean_ctor_set(v_reuseFailAlloc_4385_, 3, v___f_4356_);
lean_ctor_set(v_reuseFailAlloc_4385_, 4, v___f_4355_);
v___x_4359_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
lean_object* v___x_4361_; 
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 1, v___f_4351_);
lean_ctor_set(v___x_4341_, 0, v___x_4359_);
v___x_4361_ = v___x_4341_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4384_, 1, v___f_4351_);
v___x_4361_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; 
v___x_4362_ = lean_array_get_size(v_acc_4316_);
v___x_4363_ = lean_array_get_size(v_declInfos_4313_);
v___x_4364_ = lean_nat_dec_lt(v___x_4362_, v___x_4363_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; 
lean_dec_ref(v___x_4361_);
lean_dec_ref(v_declInfos_4313_);
lean_inc(v___y_4320_);
lean_inc_ref(v___y_4319_);
lean_inc(v___y_4318_);
lean_inc_ref(v___y_4317_);
v___x_4365_ = lean_apply_6(v_k_4314_, v_acc_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, lean_box(0));
return v___x_4365_;
}
else
{
lean_object* v___f_4366_; lean_object* v___x_4367_; uint8_t v___x_4368_; lean_object* v___f_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v_snd_4374_; lean_object* v_fst_4375_; lean_object* v_fst_4376_; lean_object* v_snd_4377_; lean_object* v___x_4378_; 
v___f_4366_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4366_, 0, v___x_4361_);
v___x_4367_ = lean_box(0);
v___x_4368_ = 0;
v___f_4369_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4369_, 0, v___f_4366_);
v___x_4370_ = lean_box(v___x_4368_);
v___x_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4370_);
lean_ctor_set(v___x_4371_, 1, v___f_4369_);
v___x_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4367_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = lean_array_get(v___x_4372_, v_declInfos_4313_, v___x_4362_);
lean_dec_ref(v___x_4372_);
v_snd_4374_ = lean_ctor_get(v___x_4373_, 1);
lean_inc(v_snd_4374_);
v_fst_4375_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_fst_4375_);
lean_dec(v___x_4373_);
v_fst_4376_ = lean_ctor_get(v_snd_4374_, 0);
lean_inc(v_fst_4376_);
v_snd_4377_ = lean_ctor_get(v_snd_4374_, 1);
lean_inc(v_snd_4377_);
lean_dec(v_snd_4374_);
lean_inc(v___y_4320_);
lean_inc_ref(v___y_4319_);
lean_inc(v___y_4318_);
lean_inc_ref(v___y_4317_);
lean_inc_ref(v_acc_4316_);
v___x_4378_ = lean_apply_6(v_snd_4377_, v_acc_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, lean_box(0));
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; lean_object* v___x_4380_; lean_object* v___f_4381_; uint8_t v___x_4382_; lean_object* v___x_4383_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref(v___x_4378_);
v___x_4380_ = lean_box(v_kind_4315_);
v___f_4381_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4381_, 0, v_acc_4316_);
lean_closure_set(v___f_4381_, 1, v_declInfos_4313_);
lean_closure_set(v___f_4381_, 2, v_k_4314_);
lean_closure_set(v___f_4381_, 3, v___x_4380_);
v___x_4382_ = lean_unbox(v_fst_4376_);
lean_dec(v_fst_4376_);
v___x_4383_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4375_, v___x_4382_, v_a_4379_, v___f_4381_, v_kind_4315_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
return v___x_4383_;
}
else
{
lean_dec(v_fst_4376_);
lean_dec(v_fst_4375_);
lean_dec_ref(v_acc_4316_);
lean_dec_ref(v_k_4314_);
lean_dec_ref(v_declInfos_4313_);
return v___x_4378_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4390_, lean_object* v_declInfos_4391_, lean_object* v_k_4392_, uint8_t v_kind_4393_, lean_object* v_x_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4400_ = lean_array_push(v_acc_4390_, v_x_4394_);
v___x_4401_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4391_, v_k_4392_, v_kind_4393_, v___x_4400_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4402_, lean_object* v_k_4403_, lean_object* v_kind_4404_, lean_object* v_acc_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
uint8_t v_kind_boxed_4411_; lean_object* v_res_4412_; 
v_kind_boxed_4411_ = lean_unbox(v_kind_4404_);
v_res_4412_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4402_, v_k_4403_, v_kind_boxed_4411_, v_acc_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4413_, lean_object* v_k_4414_, uint8_t v_kind_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4421_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4422_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4413_, v_k_4414_, v_kind_4415_, v___x_4421_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4423_, lean_object* v_k_4424_, lean_object* v_kind_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
uint8_t v_kind_boxed_4431_; lean_object* v_res_4432_; 
v_kind_boxed_4431_ = lean_unbox(v_kind_4425_);
v_res_4432_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4423_, v_k_4424_, v_kind_boxed_4431_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4433_, lean_object* v_k_4434_, uint8_t v_kind_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
size_t v_sz_4441_; size_t v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v_sz_4441_ = lean_array_size(v_declInfos_4433_);
v___x_4442_ = ((size_t)0ULL);
v___x_4443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4441_, v___x_4442_, v_declInfos_4433_);
v___x_4444_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4443_, v_k_4434_, v_kind_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4445_, lean_object* v_k_4446_, lean_object* v_kind_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
uint8_t v_kind_boxed_4453_; lean_object* v_res_4454_; 
v_kind_boxed_4453_ = lean_unbox(v_kind_4447_);
v_res_4454_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4445_, v_k_4446_, v_kind_boxed_4453_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4455_, lean_object* v_k_4456_, uint8_t v_kind_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
size_t v_sz_4463_; size_t v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; 
v_sz_4463_ = lean_array_size(v_declInfos_4455_);
v___x_4464_ = ((size_t)0ULL);
v___x_4465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4463_, v___x_4464_, v_declInfos_4455_);
v___x_4466_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4465_, v_k_4456_, v_kind_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4467_, lean_object* v_k_4468_, lean_object* v_kind_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_){
_start:
{
uint8_t v_kind_boxed_4475_; lean_object* v_res_4476_; 
v_kind_boxed_4475_ = lean_unbox(v_kind_4469_);
v_res_4476_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4467_, v_k_4468_, v_kind_boxed_4475_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(lean_object* v_a_4480_, lean_object* v_b_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v_array_4487_; lean_object* v_start_4488_; lean_object* v_stop_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4547_; 
v_array_4487_ = lean_ctor_get(v_a_4480_, 0);
v_start_4488_ = lean_ctor_get(v_a_4480_, 1);
v_stop_4489_ = lean_ctor_get(v_a_4480_, 2);
v_isSharedCheck_4547_ = !lean_is_exclusive(v_a_4480_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4491_ = v_a_4480_;
v_isShared_4492_ = v_isSharedCheck_4547_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_stop_4489_);
lean_inc(v_start_4488_);
lean_inc(v_array_4487_);
lean_dec(v_a_4480_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4547_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
uint8_t v___x_4493_; 
v___x_4493_ = lean_nat_dec_lt(v_start_4488_, v_stop_4489_);
if (v___x_4493_ == 0)
{
lean_object* v___x_4494_; 
lean_del_object(v___x_4491_);
lean_dec(v_stop_4489_);
lean_dec(v_start_4488_);
lean_dec_ref(v_array_4487_);
v___x_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4494_, 0, v_b_4481_);
return v___x_4494_;
}
else
{
lean_object* v_snd_4495_; lean_object* v_fst_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4546_; 
v_snd_4495_ = lean_ctor_get(v_b_4481_, 1);
v_fst_4496_ = lean_ctor_get(v_b_4481_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v_b_4481_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4498_ = v_b_4481_;
v_isShared_4499_ = v_isSharedCheck_4546_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_snd_4495_);
lean_inc(v_fst_4496_);
lean_dec(v_b_4481_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4546_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v_array_4500_; lean_object* v_start_4501_; lean_object* v_stop_4502_; uint8_t v___x_4503_; 
v_array_4500_ = lean_ctor_get(v_snd_4495_, 0);
v_start_4501_ = lean_ctor_get(v_snd_4495_, 1);
v_stop_4502_ = lean_ctor_get(v_snd_4495_, 2);
v___x_4503_ = lean_nat_dec_lt(v_start_4501_, v_stop_4502_);
if (v___x_4503_ == 0)
{
lean_object* v___x_4505_; 
lean_del_object(v___x_4491_);
lean_dec(v_stop_4489_);
lean_dec(v_start_4488_);
lean_dec_ref(v_array_4487_);
if (v_isShared_4499_ == 0)
{
v___x_4505_ = v___x_4498_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_fst_4496_);
lean_ctor_set(v_reuseFailAlloc_4507_, 1, v_snd_4495_);
v___x_4505_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4506_; 
v___x_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
return v___x_4506_;
}
}
else
{
lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4542_; 
lean_inc(v_stop_4502_);
lean_inc(v_start_4501_);
lean_inc_ref(v_array_4500_);
v_isSharedCheck_4542_ = !lean_is_exclusive(v_snd_4495_);
if (v_isSharedCheck_4542_ == 0)
{
lean_object* v_unused_4543_; lean_object* v_unused_4544_; lean_object* v_unused_4545_; 
v_unused_4543_ = lean_ctor_get(v_snd_4495_, 2);
lean_dec(v_unused_4543_);
v_unused_4544_ = lean_ctor_get(v_snd_4495_, 1);
lean_dec(v_unused_4544_);
v_unused_4545_ = lean_ctor_get(v_snd_4495_, 0);
lean_dec(v_unused_4545_);
v___x_4509_ = v_snd_4495_;
v_isShared_4510_ = v_isSharedCheck_4542_;
goto v_resetjp_4508_;
}
else
{
lean_dec(v_snd_4495_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4542_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4511_ = lean_array_fget_borrowed(v_array_4487_, v_start_4488_);
v___x_4512_ = lean_array_fget_borrowed(v_array_4500_, v_start_4501_);
lean_inc(v___x_4512_);
lean_inc(v___x_4511_);
v___x_4513_ = l_Lean_Meta_mkEqHEq(v___x_4511_, v___x_4512_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4518_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref(v___x_4513_);
v___x_4515_ = lean_unsigned_to_nat(1u);
v___x_4516_ = lean_nat_add(v_start_4488_, v___x_4515_);
lean_dec(v_start_4488_);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 2, v_stop_4489_);
lean_ctor_set(v___x_4509_, 1, v___x_4516_);
lean_ctor_set(v___x_4509_, 0, v_array_4487_);
v___x_4518_ = v___x_4509_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_array_4487_);
lean_ctor_set(v_reuseFailAlloc_4533_, 1, v___x_4516_);
lean_ctor_set(v_reuseFailAlloc_4533_, 2, v_stop_4489_);
v___x_4518_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
lean_object* v___x_4519_; lean_object* v___x_4521_; 
v___x_4519_ = lean_nat_add(v_start_4501_, v___x_4515_);
lean_dec(v_start_4501_);
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 2, v_stop_4502_);
lean_ctor_set(v___x_4491_, 1, v___x_4519_);
lean_ctor_set(v___x_4491_, 0, v_array_4500_);
v___x_4521_ = v___x_4491_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_array_4500_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v___x_4519_);
lean_ctor_set(v_reuseFailAlloc_4532_, 2, v_stop_4502_);
v___x_4521_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4527_; 
v___x_4522_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__1));
v___x_4523_ = lean_array_get_size(v_fst_4496_);
v___x_4524_ = lean_nat_add(v___x_4523_, v___x_4515_);
v___x_4525_ = lean_name_append_index_after(v___x_4522_, v___x_4524_);
if (v_isShared_4499_ == 0)
{
lean_ctor_set(v___x_4498_, 1, v_a_4514_);
lean_ctor_set(v___x_4498_, 0, v___x_4525_);
v___x_4527_ = v___x_4498_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4525_);
lean_ctor_set(v_reuseFailAlloc_4531_, 1, v_a_4514_);
v___x_4527_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4528_ = lean_array_push(v_fst_4496_, v___x_4527_);
v___x_4529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4529_, 0, v___x_4528_);
lean_ctor_set(v___x_4529_, 1, v___x_4521_);
v_a_4480_ = v___x_4518_;
v_b_4481_ = v___x_4529_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_del_object(v___x_4509_);
lean_dec(v_stop_4502_);
lean_dec(v_start_4501_);
lean_dec_ref(v_array_4500_);
lean_del_object(v___x_4498_);
lean_dec(v_fst_4496_);
lean_del_object(v___x_4491_);
lean_dec(v_stop_4489_);
lean_dec(v_start_4488_);
lean_dec_ref(v_array_4487_);
v_a_4534_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4513_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4513_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___boxed(lean_object* v_a_4548_, lean_object* v_b_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_4548_, v_b_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v___x_4556_, lean_object* v_a_4557_, lean_object* v___x_4558_, lean_object* v_as_4559_, size_t v_sz_4560_, size_t v_i_4561_, lean_object* v_b_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
uint8_t v___x_4568_; 
v___x_4568_ = lean_usize_dec_lt(v_i_4561_, v_sz_4560_);
if (v___x_4568_ == 0)
{
lean_object* v___x_4569_; 
lean_dec(v___x_4558_);
v___x_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4569_, 0, v_b_4562_);
return v___x_4569_;
}
else
{
lean_object* v___x_4570_; lean_object* v_a_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v___x_4570_ = l_Lean_instInhabitedExpr;
v_a_4571_ = lean_array_uget_borrowed(v_as_4559_, v_i_4561_);
v___x_4572_ = lean_array_get_borrowed(v___x_4570_, v___x_4556_, v_a_4571_);
lean_inc(v___x_4572_);
v___x_4573_ = l_Lean_Meta_instantiateForall(v___x_4572_, v_a_4557_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
if (lean_obj_tag(v___x_4573_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4575_; 
v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
lean_inc(v_a_4574_);
lean_dec_ref(v___x_4573_);
lean_inc(v___x_4558_);
v___x_4575_ = l_Lean_Meta_Match_simpH_x3f(v_a_4574_, v___x_4558_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v_a_4576_; lean_object* v_a_4578_; 
v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
lean_inc(v_a_4576_);
lean_dec_ref(v___x_4575_);
if (lean_obj_tag(v_a_4576_) == 1)
{
lean_object* v_val_4582_; lean_object* v___x_4583_; 
v_val_4582_ = lean_ctor_get(v_a_4576_, 0);
lean_inc(v_val_4582_);
lean_dec_ref(v_a_4576_);
v___x_4583_ = lean_array_push(v_b_4562_, v_val_4582_);
v_a_4578_ = v___x_4583_;
goto v___jp_4577_;
}
else
{
lean_dec(v_a_4576_);
v_a_4578_ = v_b_4562_;
goto v___jp_4577_;
}
v___jp_4577_:
{
size_t v___x_4579_; size_t v___x_4580_; 
v___x_4579_ = ((size_t)1ULL);
v___x_4580_ = lean_usize_add(v_i_4561_, v___x_4579_);
v_i_4561_ = v___x_4580_;
v_b_4562_ = v_a_4578_;
goto _start;
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_dec_ref(v_b_4562_);
lean_dec(v___x_4558_);
v_a_4584_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4575_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4575_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
lean_dec_ref(v_b_4562_);
lean_dec(v___x_4558_);
v_a_4592_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___x_4573_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___x_4573_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v___x_4600_, lean_object* v_a_4601_, lean_object* v___x_4602_, lean_object* v_as_4603_, lean_object* v_sz_4604_, lean_object* v_i_4605_, lean_object* v_b_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
size_t v_sz_boxed_4612_; size_t v_i_boxed_4613_; lean_object* v_res_4614_; 
v_sz_boxed_4612_ = lean_unbox_usize(v_sz_4604_);
lean_dec(v_sz_4604_);
v_i_boxed_4613_ = lean_unbox_usize(v_i_4605_);
lean_dec(v_i_4605_);
v_res_4614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v___x_4600_, v_a_4601_, v___x_4602_, v_as_4603_, v_sz_boxed_4612_, v_i_boxed_4613_, v_b_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec_ref(v_as_4603_);
lean_dec_ref(v_a_4601_);
lean_dec_ref(v___x_4600_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4615_, lean_object* v_args_4616_, lean_object* v___x_4617_, lean_object* v_overlaps_4618_, lean_object* v_a_4619_, lean_object* v_fst_4620_, lean_object* v_a_4621_, lean_object* v___x_4622_, lean_object* v___x_4623_, lean_object* v___x_4624_, lean_object* v___x_4625_, lean_object* v_altVars_4626_, uint8_t v___x_4627_, uint8_t v___x_4628_, lean_object* v_a_4629_, lean_object* v___x_4630_, lean_object* v___x_4631_, lean_object* v___x_4632_, lean_object* v___x_4633_, lean_object* v___x_4634_, lean_object* v___x_4635_, lean_object* v___x_4636_, lean_object* v_matchDeclName_4637_, lean_object* v___x_4638_, lean_object* v___x_4639_, lean_object* v___x_4640_, lean_object* v_heqs_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4647_ = l_Lean_mkAppN(v___y_4615_, v_args_4616_);
lean_inc_ref(v_heqs_4641_);
v___x_4648_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4647_, v_heqs_4641_, v___x_4617_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v_a_4649_; lean_object* v___x_4650_; size_t v_sz_4651_; size_t v___x_4652_; lean_object* v___x_4653_; 
v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
lean_inc(v_a_4649_);
lean_dec_ref(v___x_4648_);
v___x_4650_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4618_, v_a_4619_);
v_sz_4651_ = lean_array_size(v___x_4650_);
v___x_4652_ = ((size_t)0ULL);
lean_inc_ref(v___x_4623_);
v___x_4653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_fst_4620_, v_a_4621_, v___x_4622_, v___x_4650_, v_sz_4651_, v___x_4652_, v___x_4623_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
lean_dec_ref(v___x_4650_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v_options_4766_; uint8_t v_hasTrace_4767_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc(v_a_4654_);
lean_dec_ref(v___x_4653_);
v_options_4766_ = lean_ctor_get(v___y_4644_, 2);
v_hasTrace_4767_ = lean_ctor_get_uint8(v_options_4766_, sizeof(void*)*1);
if (v_hasTrace_4767_ == 0)
{
v___y_4656_ = v___y_4642_;
v___y_4657_ = v___y_4643_;
v___y_4658_ = v___y_4644_;
v___y_4659_ = v___y_4645_;
goto v___jp_4655_;
}
else
{
lean_object* v_inheritedTraceOptions_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; uint8_t v___x_4771_; 
v_inheritedTraceOptions_4768_ = lean_ctor_get(v___y_4644_, 13);
v___x_4769_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4770_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4771_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4768_, v_options_4766_, v___x_4770_);
if (v___x_4771_ == 0)
{
v___y_4656_ = v___y_4642_;
v___y_4657_ = v___y_4643_;
v___y_4658_ = v___y_4644_;
v___y_4659_ = v___y_4645_;
goto v___jp_4655_;
}
else
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4772_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4654_);
v___x_4773_ = lean_array_to_list(v_a_4654_);
v___x_4774_ = lean_box(0);
v___x_4775_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4773_, v___x_4774_);
v___x_4776_ = l_Lean_MessageData_ofList(v___x_4775_);
v___x_4777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4772_);
lean_ctor_set(v___x_4777_, 1, v___x_4776_);
v___x_4778_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4769_, v___x_4777_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_dec_ref(v___x_4778_);
v___y_4656_ = v___y_4642_;
v___y_4657_ = v___y_4643_;
v___y_4658_ = v___y_4644_;
v___y_4659_ = v___y_4645_;
goto v___jp_4655_;
}
else
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4786_; 
lean_dec(v_a_4654_);
lean_dec(v_a_4649_);
lean_dec_ref(v_heqs_4641_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v_matchDeclName_4637_);
lean_dec_ref(v___x_4634_);
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___x_4631_);
lean_dec(v___x_4630_);
lean_dec_ref(v___x_4625_);
lean_dec(v___x_4624_);
lean_dec_ref(v___x_4623_);
lean_dec_ref(v_a_4621_);
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4781_ = v___x_4778_;
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4778_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4784_; 
if (v_isShared_4782_ == 0)
{
v___x_4784_ = v___x_4781_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4779_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
}
v___jp_4655_:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; size_t v_sz_4667_; lean_object* v___x_4668_; 
v___x_4660_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4661_ = l_Array_reverse___redArg(v_a_4621_);
v___x_4662_ = lean_array_get_size(v___x_4661_);
v___x_4663_ = l_Array_toSubarray___redArg(v___x_4661_, v___x_4624_, v___x_4662_);
lean_inc_ref(v___x_4625_);
v___x_4664_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4625_, v___x_4623_);
v___x_4665_ = l_Array_reverse___redArg(v___x_4664_);
v___x_4666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4660_);
lean_ctor_set(v___x_4666_, 1, v___x_4663_);
v_sz_4667_ = lean_array_size(v___x_4665_);
v___x_4668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4665_, v_sz_4667_, v___x_4652_, v___x_4666_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec_ref(v___x_4665_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; lean_object* v_fst_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4756_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4669_);
lean_dec_ref(v___x_4668_);
v_fst_4670_ = lean_ctor_get(v_a_4669_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_a_4669_);
if (v_isSharedCheck_4756_ == 0)
{
lean_object* v_unused_4757_; 
v_unused_4757_ = lean_ctor_get(v_a_4669_, 1);
lean_dec(v_unused_4757_);
v___x_4672_ = v_a_4669_;
v_isShared_4673_ = v_isSharedCheck_4756_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_fst_4670_);
lean_dec(v_a_4669_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4756_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; lean_object* v___x_4677_; 
v___x_4674_ = l_Subarray_copy___redArg(v___x_4625_);
lean_inc_ref(v___x_4674_);
v___x_4675_ = l_Array_append___redArg(v___x_4674_, v_altVars_4626_);
v___x_4676_ = 1;
v___x_4677_ = l_Lean_Meta_mkForallFVars(v___x_4675_, v_fst_4670_, v___x_4627_, v___x_4628_, v___x_4628_, v___x_4676_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec_ref(v___x_4675_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref(v___x_4677_);
v___x_4679_ = l_Lean_ConstantInfo_name(v_a_4629_);
v___x_4680_ = l_Lean_mkConst(v___x_4679_, v___x_4630_);
lean_inc_ref(v___x_4631_);
v___x_4681_ = l_Subarray_copy___redArg(v___x_4631_);
v___x_4682_ = lean_mk_empty_array_with_capacity(v___x_4632_);
v___x_4683_ = lean_array_push(v___x_4682_, v___x_4633_);
v___x_4684_ = l_Array_append___redArg(v___x_4681_, v___x_4683_);
lean_dec_ref(v___x_4683_);
v___x_4685_ = l_Array_append___redArg(v___x_4684_, v___x_4674_);
lean_dec_ref(v___x_4674_);
v___x_4686_ = l_Subarray_copy___redArg(v___x_4634_);
v___x_4687_ = l_Array_append___redArg(v___x_4685_, v___x_4686_);
lean_dec_ref(v___x_4686_);
v___x_4688_ = l_Lean_mkAppN(v___x_4680_, v___x_4687_);
v___x_4689_ = l_Lean_Meta_mkHEq(v___x_4688_, v_a_4649_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_object* v_a_4690_; lean_object* v___x_4691_; 
v_a_4690_ = lean_ctor_get(v___x_4689_, 0);
lean_inc(v_a_4690_);
lean_dec_ref(v___x_4689_);
v___x_4691_ = l_Lean_mkArrowN(v_a_4654_, v_a_4690_, v___y_4658_, v___y_4659_);
lean_dec(v_a_4654_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_a_4692_);
lean_dec_ref(v___x_4691_);
v___x_4693_ = l_Array_append___redArg(v___x_4687_, v_altVars_4626_);
v___x_4694_ = l_Array_append___redArg(v___x_4693_, v_heqs_4641_);
v___x_4695_ = l_Lean_Meta_mkForallFVars(v___x_4694_, v_a_4692_, v___x_4627_, v___x_4628_, v___x_4628_, v___x_4676_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec_ref(v___x_4694_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v_a_4696_; lean_object* v___x_4697_; 
v_a_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_a_4696_);
lean_dec_ref(v___x_4695_);
v___x_4697_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4696_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4755_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4700_ = v___x_4697_;
v_isShared_4701_ = v_isSharedCheck_4755_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4697_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4755_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v_start_4702_; lean_object* v_stop_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4753_; 
v_start_4702_ = lean_ctor_get(v___x_4631_, 1);
v_stop_4703_ = lean_ctor_get(v___x_4631_, 2);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; 
v_unused_4754_ = lean_ctor_get(v___x_4631_, 0);
lean_dec(v_unused_4754_);
v___x_4705_ = v___x_4631_;
v_isShared_4706_ = v_isSharedCheck_4753_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_stop_4703_);
lean_inc(v_start_4702_);
lean_dec(v___x_4631_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4753_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4707_ = lean_nat_sub(v_stop_4703_, v_start_4702_);
lean_dec(v_start_4702_);
lean_dec(v_stop_4703_);
v___x_4708_ = lean_nat_add(v___x_4707_, v___x_4632_);
lean_dec(v___x_4707_);
v___x_4709_ = lean_nat_add(v___x_4708_, v___x_4635_);
lean_dec(v___x_4708_);
v___x_4710_ = lean_nat_add(v___x_4709_, v___x_4636_);
lean_dec(v___x_4709_);
v___x_4711_ = lean_array_get_size(v_altVars_4626_);
v___x_4712_ = lean_nat_add(v___x_4710_, v___x_4711_);
lean_dec(v___x_4710_);
v___x_4713_ = lean_array_get_size(v_heqs_4641_);
lean_dec_ref(v_heqs_4641_);
lean_inc(v_a_4698_);
v___x_4714_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4637_, v_a_4698_, v___x_4712_, v___x_4713_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4752_; 
v_a_4715_ = lean_ctor_get(v___x_4714_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4717_ = v___x_4714_;
v_isShared_4718_ = v_isSharedCheck_4752_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v___x_4714_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4752_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4719_; lean_object* v_env_4720_; uint8_t v___x_4721_; 
v___x_4719_ = lean_st_ref_get(v___y_4659_);
v_env_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc_ref(v_env_4720_);
lean_dec(v___x_4719_);
lean_inc(v___x_4638_);
v___x_4721_ = l_Lean_Environment_contains(v_env_4720_, v___x_4638_, v___x_4628_);
if (v___x_4721_ == 0)
{
lean_object* v___x_4723_; 
lean_del_object(v___x_4717_);
lean_inc(v___x_4638_);
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 2, v_a_4698_);
lean_ctor_set(v___x_4705_, 1, v___x_4639_);
lean_ctor_set(v___x_4705_, 0, v___x_4638_);
v___x_4723_ = v___x_4705_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v___x_4638_);
lean_ctor_set(v_reuseFailAlloc_4748_, 1, v___x_4639_);
lean_ctor_set(v_reuseFailAlloc_4748_, 2, v_a_4698_);
v___x_4723_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4725_; 
if (v_isShared_4673_ == 0)
{
lean_ctor_set_tag(v___x_4672_, 1);
lean_ctor_set(v___x_4672_, 1, v___x_4640_);
lean_ctor_set(v___x_4672_, 0, v___x_4638_);
v___x_4725_ = v___x_4672_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4638_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v___x_4640_);
v___x_4725_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; lean_object* v___x_4728_; 
v___x_4726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4723_);
lean_ctor_set(v___x_4726_, 1, v_a_4715_);
lean_ctor_set(v___x_4726_, 2, v___x_4725_);
if (v_isShared_4701_ == 0)
{
lean_ctor_set_tag(v___x_4700_, 2);
lean_ctor_set(v___x_4700_, 0, v___x_4726_);
v___x_4728_ = v___x_4700_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4726_);
v___x_4728_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
lean_object* v___x_4729_; 
v___x_4729_ = l_Lean_addDecl(v___x_4728_, v___x_4627_, v___y_4658_, v___y_4659_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4736_ == 0)
{
lean_object* v_unused_4737_; 
v_unused_4737_ = lean_ctor_get(v___x_4729_, 0);
lean_dec(v_unused_4737_);
v___x_4731_ = v___x_4729_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_dec(v___x_4729_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 0, v_a_4678_);
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4678_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_dec(v_a_4678_);
v_a_4738_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4729_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4729_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4750_; 
lean_dec(v_a_4715_);
lean_del_object(v___x_4705_);
lean_del_object(v___x_4700_);
lean_dec(v_a_4698_);
lean_del_object(v___x_4672_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
if (v_isShared_4718_ == 0)
{
lean_ctor_set(v___x_4717_, 0, v_a_4678_);
v___x_4750_ = v___x_4717_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4678_);
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
else
{
lean_del_object(v___x_4705_);
lean_del_object(v___x_4700_);
lean_dec(v_a_4698_);
lean_dec(v_a_4678_);
lean_del_object(v___x_4672_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
return v___x_4714_;
}
}
}
}
else
{
lean_dec(v_a_4678_);
lean_del_object(v___x_4672_);
lean_dec_ref(v_heqs_4641_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v_matchDeclName_4637_);
lean_dec_ref(v___x_4631_);
return v___x_4697_;
}
}
else
{
lean_dec(v_a_4678_);
lean_del_object(v___x_4672_);
lean_dec_ref(v_heqs_4641_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v_matchDeclName_4637_);
lean_dec_ref(v___x_4631_);
return v___x_4695_;
}
}
else
{
lean_dec_ref(v___x_4687_);
lean_dec(v_a_4678_);
lean_del_object(v___x_4672_);
lean_dec_ref(v_heqs_4641_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v_matchDeclName_4637_);
lean_dec_ref(v___x_4631_);
return v___x_4691_;
}
}
else
{
lean_dec_ref(v___x_4687_);
lean_dec(v_a_4678_);
lean_del_object(v___x_4672_);
lean_dec(v_a_4654_);
lean_dec_ref(v_heqs_4641_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v_matchDeclName_4637_);
lean_dec_ref(v___x_4631_);
return v___x_4689_;
}
}
else
{
lean_dec_ref(v___x_4674_);
lean_del_object(v___x_4672_);
lean_dec(v_a_4654_);
lean_dec(v_a_4649_);
lean_dec_ref(v_heqs_4641_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v_matchDeclName_4637_);
lean_dec_ref(v___x_4634_);
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___x_4631_);
lean_dec(v___x_4630_);
return v___x_4677_;
}
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4765_; 
lean_dec(v_a_4654_);
lean_dec(v_a_4649_);
lean_dec_ref(v_heqs_4641_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v_matchDeclName_4637_);
lean_dec_ref(v___x_4634_);
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___x_4631_);
lean_dec(v___x_4630_);
lean_dec_ref(v___x_4625_);
v_a_4758_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4760_ = v___x_4668_;
v_isShared_4761_ = v_isSharedCheck_4765_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4668_);
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
else
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4794_; 
lean_dec(v_a_4649_);
lean_dec_ref(v_heqs_4641_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v_matchDeclName_4637_);
lean_dec_ref(v___x_4634_);
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___x_4631_);
lean_dec(v___x_4630_);
lean_dec_ref(v___x_4625_);
lean_dec(v___x_4624_);
lean_dec_ref(v___x_4623_);
lean_dec_ref(v_a_4621_);
v_a_4787_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4789_ = v___x_4653_;
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4653_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4792_; 
if (v_isShared_4790_ == 0)
{
v___x_4792_ = v___x_4789_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4641_);
lean_dec(v___x_4640_);
lean_dec(v___x_4639_);
lean_dec(v___x_4638_);
lean_dec(v_matchDeclName_4637_);
lean_dec_ref(v___x_4634_);
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___x_4631_);
lean_dec(v___x_4630_);
lean_dec_ref(v___x_4625_);
lean_dec(v___x_4624_);
lean_dec_ref(v___x_4623_);
lean_dec(v___x_4622_);
lean_dec_ref(v_a_4621_);
return v___x_4648_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4795_ = _args[0];
lean_object* v_args_4796_ = _args[1];
lean_object* v___x_4797_ = _args[2];
lean_object* v_overlaps_4798_ = _args[3];
lean_object* v_a_4799_ = _args[4];
lean_object* v_fst_4800_ = _args[5];
lean_object* v_a_4801_ = _args[6];
lean_object* v___x_4802_ = _args[7];
lean_object* v___x_4803_ = _args[8];
lean_object* v___x_4804_ = _args[9];
lean_object* v___x_4805_ = _args[10];
lean_object* v_altVars_4806_ = _args[11];
lean_object* v___x_4807_ = _args[12];
lean_object* v___x_4808_ = _args[13];
lean_object* v_a_4809_ = _args[14];
lean_object* v___x_4810_ = _args[15];
lean_object* v___x_4811_ = _args[16];
lean_object* v___x_4812_ = _args[17];
lean_object* v___x_4813_ = _args[18];
lean_object* v___x_4814_ = _args[19];
lean_object* v___x_4815_ = _args[20];
lean_object* v___x_4816_ = _args[21];
lean_object* v_matchDeclName_4817_ = _args[22];
lean_object* v___x_4818_ = _args[23];
lean_object* v___x_4819_ = _args[24];
lean_object* v___x_4820_ = _args[25];
lean_object* v_heqs_4821_ = _args[26];
lean_object* v___y_4822_ = _args[27];
lean_object* v___y_4823_ = _args[28];
lean_object* v___y_4824_ = _args[29];
lean_object* v___y_4825_ = _args[30];
lean_object* v___y_4826_ = _args[31];
_start:
{
uint8_t v___x_22597__boxed_4827_; uint8_t v___x_22598__boxed_4828_; lean_object* v_res_4829_; 
v___x_22597__boxed_4827_ = lean_unbox(v___x_4807_);
v___x_22598__boxed_4828_ = lean_unbox(v___x_4808_);
v_res_4829_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4795_, v_args_4796_, v___x_4797_, v_overlaps_4798_, v_a_4799_, v_fst_4800_, v_a_4801_, v___x_4802_, v___x_4803_, v___x_4804_, v___x_4805_, v_altVars_4806_, v___x_22597__boxed_4827_, v___x_22598__boxed_4828_, v_a_4809_, v___x_4810_, v___x_4811_, v___x_4812_, v___x_4813_, v___x_4814_, v___x_4815_, v___x_4816_, v_matchDeclName_4817_, v___x_4818_, v___x_4819_, v___x_4820_, v_heqs_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
lean_dec(v___x_4816_);
lean_dec(v___x_4815_);
lean_dec(v___x_4812_);
lean_dec_ref(v_a_4809_);
lean_dec_ref(v_altVars_4806_);
lean_dec(v_fst_4800_);
lean_dec(v_a_4799_);
lean_dec_ref(v_overlaps_4798_);
lean_dec_ref(v_args_4796_);
return v_res_4829_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4832_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4833_ = lean_unsigned_to_nat(8u);
v___x_4834_ = lean_unsigned_to_nat(295u);
v___x_4835_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4836_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4837_ = l_mkPanicMessageWithDecl(v___x_4836_, v___x_4835_, v___x_4834_, v___x_4833_, v___x_4832_);
return v___x_4837_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4838_, lean_object* v___x_4839_, lean_object* v___x_4840_, lean_object* v___y_4841_, lean_object* v___x_4842_, lean_object* v_overlaps_4843_, lean_object* v_a_4844_, lean_object* v_fst_4845_, lean_object* v___x_4846_, lean_object* v_a_4847_, lean_object* v___x_4848_, lean_object* v___x_4849_, lean_object* v___x_4850_, lean_object* v___x_4851_, lean_object* v___x_4852_, lean_object* v___x_4853_, lean_object* v_matchDeclName_4854_, lean_object* v___x_4855_, lean_object* v___x_4856_, lean_object* v___x_4857_, lean_object* v_altVars_4858_, lean_object* v_args_4859_, lean_object* v___mask_4860_, lean_object* v_altResultType_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_){
_start:
{
uint8_t v___x_4867_; lean_object* v___x_4868_; 
v___x_4867_ = 0;
v___x_4868_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4861_, v___f_4838_, v___x_4867_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v_a_4869_; lean_object* v_start_4870_; lean_object* v_stop_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; 
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
lean_inc(v_a_4869_);
lean_dec_ref(v___x_4868_);
v_start_4870_ = lean_ctor_get(v___x_4839_, 1);
v_stop_4871_ = lean_ctor_get(v___x_4839_, 2);
v___x_4872_ = lean_array_get_size(v_a_4869_);
v___x_4873_ = lean_nat_sub(v_stop_4871_, v_start_4870_);
v___x_4874_ = lean_nat_dec_eq(v___x_4872_, v___x_4873_);
if (v___x_4874_ == 0)
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
lean_dec(v___x_4873_);
lean_dec(v_a_4869_);
lean_dec_ref(v_args_4859_);
lean_dec_ref(v_altVars_4858_);
lean_dec(v___x_4857_);
lean_dec(v___x_4856_);
lean_dec(v___x_4855_);
lean_dec(v_matchDeclName_4854_);
lean_dec(v___x_4853_);
lean_dec_ref(v___x_4852_);
lean_dec_ref(v___x_4851_);
lean_dec(v___x_4850_);
lean_dec_ref(v___x_4849_);
lean_dec(v___x_4848_);
lean_dec_ref(v_a_4847_);
lean_dec_ref(v___x_4846_);
lean_dec(v_fst_4845_);
lean_dec(v_a_4844_);
lean_dec_ref(v_overlaps_4843_);
lean_dec(v___x_4842_);
lean_dec_ref(v___y_4841_);
lean_dec(v___x_4840_);
lean_dec_ref(v___x_4839_);
v___x_4875_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4876_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4875_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
return v___x_4876_;
}
else
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4877_ = lean_mk_empty_array_with_capacity(v___x_4840_);
lean_inc(v___x_4840_);
lean_inc(v_a_4869_);
v___x_4878_ = l_Array_toSubarray___redArg(v_a_4869_, v___x_4840_, v___x_4872_);
v___x_4879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4877_);
lean_ctor_set(v___x_4879_, 1, v___x_4878_);
lean_inc_ref(v___x_4839_);
v___x_4880_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v___x_4839_, v___x_4879_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v_fst_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___f_4885_; uint8_t v___x_4886_; lean_object* v___x_4887_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_a_4881_);
lean_dec_ref(v___x_4880_);
v_fst_4882_ = lean_ctor_get(v_a_4881_, 0);
lean_inc(v_fst_4882_);
lean_dec(v_a_4881_);
v___x_4883_ = lean_box(v___x_4867_);
v___x_4884_ = lean_box(v___x_4874_);
v___f_4885_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4885_, 0, v___y_4841_);
lean_closure_set(v___f_4885_, 1, v_args_4859_);
lean_closure_set(v___f_4885_, 2, v___x_4842_);
lean_closure_set(v___f_4885_, 3, v_overlaps_4843_);
lean_closure_set(v___f_4885_, 4, v_a_4844_);
lean_closure_set(v___f_4885_, 5, v_fst_4845_);
lean_closure_set(v___f_4885_, 6, v_a_4869_);
lean_closure_set(v___f_4885_, 7, v___x_4872_);
lean_closure_set(v___f_4885_, 8, v___x_4846_);
lean_closure_set(v___f_4885_, 9, v___x_4840_);
lean_closure_set(v___f_4885_, 10, v___x_4839_);
lean_closure_set(v___f_4885_, 11, v_altVars_4858_);
lean_closure_set(v___f_4885_, 12, v___x_4883_);
lean_closure_set(v___f_4885_, 13, v___x_4884_);
lean_closure_set(v___f_4885_, 14, v_a_4847_);
lean_closure_set(v___f_4885_, 15, v___x_4848_);
lean_closure_set(v___f_4885_, 16, v___x_4849_);
lean_closure_set(v___f_4885_, 17, v___x_4850_);
lean_closure_set(v___f_4885_, 18, v___x_4851_);
lean_closure_set(v___f_4885_, 19, v___x_4852_);
lean_closure_set(v___f_4885_, 20, v___x_4873_);
lean_closure_set(v___f_4885_, 21, v___x_4853_);
lean_closure_set(v___f_4885_, 22, v_matchDeclName_4854_);
lean_closure_set(v___f_4885_, 23, v___x_4855_);
lean_closure_set(v___f_4885_, 24, v___x_4856_);
lean_closure_set(v___f_4885_, 25, v___x_4857_);
v___x_4886_ = 0;
v___x_4887_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4882_, v___f_4885_, v___x_4886_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
return v___x_4887_;
}
else
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
lean_dec(v___x_4873_);
lean_dec(v_a_4869_);
lean_dec_ref(v_args_4859_);
lean_dec_ref(v_altVars_4858_);
lean_dec(v___x_4857_);
lean_dec(v___x_4856_);
lean_dec(v___x_4855_);
lean_dec(v_matchDeclName_4854_);
lean_dec(v___x_4853_);
lean_dec_ref(v___x_4852_);
lean_dec_ref(v___x_4851_);
lean_dec(v___x_4850_);
lean_dec_ref(v___x_4849_);
lean_dec(v___x_4848_);
lean_dec_ref(v_a_4847_);
lean_dec_ref(v___x_4846_);
lean_dec(v_fst_4845_);
lean_dec(v_a_4844_);
lean_dec_ref(v_overlaps_4843_);
lean_dec(v___x_4842_);
lean_dec_ref(v___y_4841_);
lean_dec(v___x_4840_);
lean_dec_ref(v___x_4839_);
v_a_4888_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4880_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4880_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
}
}
else
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
lean_dec_ref(v_args_4859_);
lean_dec_ref(v_altVars_4858_);
lean_dec(v___x_4857_);
lean_dec(v___x_4856_);
lean_dec(v___x_4855_);
lean_dec(v_matchDeclName_4854_);
lean_dec(v___x_4853_);
lean_dec_ref(v___x_4852_);
lean_dec_ref(v___x_4851_);
lean_dec(v___x_4850_);
lean_dec_ref(v___x_4849_);
lean_dec(v___x_4848_);
lean_dec_ref(v_a_4847_);
lean_dec_ref(v___x_4846_);
lean_dec(v_fst_4845_);
lean_dec(v_a_4844_);
lean_dec_ref(v_overlaps_4843_);
lean_dec(v___x_4842_);
lean_dec_ref(v___y_4841_);
lean_dec(v___x_4840_);
lean_dec_ref(v___x_4839_);
v_a_4896_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4868_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4868_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4904_ = _args[0];
lean_object* v___x_4905_ = _args[1];
lean_object* v___x_4906_ = _args[2];
lean_object* v___y_4907_ = _args[3];
lean_object* v___x_4908_ = _args[4];
lean_object* v_overlaps_4909_ = _args[5];
lean_object* v_a_4910_ = _args[6];
lean_object* v_fst_4911_ = _args[7];
lean_object* v___x_4912_ = _args[8];
lean_object* v_a_4913_ = _args[9];
lean_object* v___x_4914_ = _args[10];
lean_object* v___x_4915_ = _args[11];
lean_object* v___x_4916_ = _args[12];
lean_object* v___x_4917_ = _args[13];
lean_object* v___x_4918_ = _args[14];
lean_object* v___x_4919_ = _args[15];
lean_object* v_matchDeclName_4920_ = _args[16];
lean_object* v___x_4921_ = _args[17];
lean_object* v___x_4922_ = _args[18];
lean_object* v___x_4923_ = _args[19];
lean_object* v_altVars_4924_ = _args[20];
lean_object* v_args_4925_ = _args[21];
lean_object* v___mask_4926_ = _args[22];
lean_object* v_altResultType_4927_ = _args[23];
lean_object* v___y_4928_ = _args[24];
lean_object* v___y_4929_ = _args[25];
lean_object* v___y_4930_ = _args[26];
lean_object* v___y_4931_ = _args[27];
lean_object* v___y_4932_ = _args[28];
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4904_, v___x_4905_, v___x_4906_, v___y_4907_, v___x_4908_, v_overlaps_4909_, v_a_4910_, v_fst_4911_, v___x_4912_, v_a_4913_, v___x_4914_, v___x_4915_, v___x_4916_, v___x_4917_, v___x_4918_, v___x_4919_, v_matchDeclName_4920_, v___x_4921_, v___x_4922_, v___x_4923_, v_altVars_4924_, v_args_4925_, v___mask_4926_, v_altResultType_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
lean_dec_ref(v___mask_4926_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4935_, lean_object* v_val_4936_, lean_object* v_matchDeclName_4937_, lean_object* v___x_4938_, lean_object* v___x_4939_, lean_object* v_a_4940_, lean_object* v___x_4941_, lean_object* v___x_4942_, lean_object* v___x_4943_, lean_object* v___x_4944_, lean_object* v___x_4945_, lean_object* v___x_4946_, lean_object* v_a_4947_, lean_object* v_b_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_){
_start:
{
uint8_t v___x_4954_; 
v___x_4954_ = lean_nat_dec_lt(v_a_4947_, v_upperBound_4935_);
if (v___x_4954_ == 0)
{
lean_object* v___x_4955_; 
lean_dec(v_a_4947_);
lean_dec(v___x_4946_);
lean_dec(v___x_4945_);
lean_dec_ref(v___x_4944_);
lean_dec_ref(v___x_4943_);
lean_dec_ref(v___x_4942_);
lean_dec(v___x_4941_);
lean_dec_ref(v_a_4940_);
lean_dec(v___x_4939_);
lean_dec_ref(v___x_4938_);
lean_dec(v_matchDeclName_4937_);
lean_dec_ref(v_val_4936_);
v___x_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4955_, 0, v_b_4948_);
return v___x_4955_;
}
else
{
lean_object* v_snd_4956_; lean_object* v_fst_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_5020_; 
v_snd_4956_ = lean_ctor_get(v_b_4948_, 1);
v_fst_4957_ = lean_ctor_get(v_b_4948_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v_b_4948_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_4959_ = v_b_4948_;
v_isShared_4960_ = v_isSharedCheck_5020_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_snd_4956_);
lean_inc(v_fst_4957_);
lean_dec(v_b_4948_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_5020_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v_fst_4961_; lean_object* v_snd_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_5019_; 
v_fst_4961_ = lean_ctor_get(v_snd_4956_, 0);
v_snd_4962_ = lean_ctor_get(v_snd_4956_, 1);
v_isSharedCheck_5019_ = !lean_is_exclusive(v_snd_4956_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_4964_ = v_snd_4956_;
v_isShared_4965_ = v_isSharedCheck_5019_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_snd_4962_);
lean_inc(v_fst_4961_);
lean_dec(v_snd_4956_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_5019_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v_altInfos_4966_; lean_object* v_overlaps_4967_; lean_object* v_start_4968_; lean_object* v_stop_4969_; lean_object* v___f_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___y_4982_; lean_object* v___x_5014_; uint8_t v___x_5015_; 
v_altInfos_4966_ = lean_ctor_get(v_val_4936_, 2);
v_overlaps_4967_ = lean_ctor_get(v_val_4936_, 5);
v_start_4968_ = lean_ctor_get(v___x_4944_, 1);
v_stop_4969_ = lean_ctor_get(v___x_4944_, 2);
v___f_4970_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4971_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4972_ = lean_unsigned_to_nat(0u);
v___x_4973_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4974_ = lean_unsigned_to_nat(1u);
v___x_4975_ = lean_box(0);
v___x_4976_ = lean_array_get_borrowed(v___x_4971_, v_altInfos_4966_, v_a_4947_);
v___x_4977_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4937_);
v___x_4978_ = l_Lean_Name_str___override(v_matchDeclName_4937_, v___x_4977_);
lean_inc(v_snd_4962_);
v___x_4979_ = lean_name_append_index_after(v___x_4978_, v_snd_4962_);
lean_inc(v___x_4979_);
v___x_4980_ = lean_array_push(v_fst_4957_, v___x_4979_);
v___x_5014_ = lean_nat_sub(v_stop_4969_, v_start_4968_);
v___x_5015_ = lean_nat_dec_lt(v_a_4947_, v___x_5014_);
lean_dec(v___x_5014_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5016_ = l_Lean_instInhabitedExpr;
v___x_5017_ = l_outOfBounds___redArg(v___x_5016_);
v___y_4982_ = v___x_5017_;
goto v___jp_4981_;
}
else
{
lean_object* v___x_5018_; 
v___x_5018_ = l_Subarray_get___redArg(v___x_4944_, v_a_4947_);
v___y_4982_ = v___x_5018_;
goto v___jp_4981_;
}
v___jp_4981_:
{
lean_object* v___x_4983_; 
lean_inc(v___y_4952_);
lean_inc_ref(v___y_4951_);
lean_inc(v___y_4950_);
lean_inc_ref(v___y_4949_);
lean_inc_ref(v___y_4982_);
v___x_4983_ = lean_infer_type(v___y_4982_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v___f_4985_; lean_object* v___x_4986_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref(v___x_4983_);
lean_inc(v___x_4946_);
lean_inc(v_matchDeclName_4937_);
lean_inc(v___x_4945_);
lean_inc_ref(v___x_4944_);
lean_inc_ref(v___x_4943_);
lean_inc_ref(v___x_4942_);
lean_inc(v___x_4941_);
lean_inc_ref(v_a_4940_);
lean_inc(v_fst_4961_);
lean_inc(v_a_4947_);
lean_inc_ref(v_overlaps_4967_);
lean_inc(v___x_4939_);
lean_inc_ref(v___x_4938_);
v___f_4985_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 29, 20);
lean_closure_set(v___f_4985_, 0, v___f_4970_);
lean_closure_set(v___f_4985_, 1, v___x_4938_);
lean_closure_set(v___f_4985_, 2, v___x_4972_);
lean_closure_set(v___f_4985_, 3, v___y_4982_);
lean_closure_set(v___f_4985_, 4, v___x_4939_);
lean_closure_set(v___f_4985_, 5, v_overlaps_4967_);
lean_closure_set(v___f_4985_, 6, v_a_4947_);
lean_closure_set(v___f_4985_, 7, v_fst_4961_);
lean_closure_set(v___f_4985_, 8, v___x_4973_);
lean_closure_set(v___f_4985_, 9, v_a_4940_);
lean_closure_set(v___f_4985_, 10, v___x_4941_);
lean_closure_set(v___f_4985_, 11, v___x_4942_);
lean_closure_set(v___f_4985_, 12, v___x_4974_);
lean_closure_set(v___f_4985_, 13, v___x_4943_);
lean_closure_set(v___f_4985_, 14, v___x_4944_);
lean_closure_set(v___f_4985_, 15, v___x_4945_);
lean_closure_set(v___f_4985_, 16, v_matchDeclName_4937_);
lean_closure_set(v___f_4985_, 17, v___x_4979_);
lean_closure_set(v___f_4985_, 18, v___x_4946_);
lean_closure_set(v___f_4985_, 19, v___x_4975_);
lean_inc(v___x_4976_);
v___x_4986_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4984_, v___x_4976_, v___f_4985_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4991_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref(v___x_4986_);
v___x_4988_ = lean_array_push(v_fst_4961_, v_a_4987_);
v___x_4989_ = lean_nat_add(v_snd_4962_, v___x_4974_);
lean_dec(v_snd_4962_);
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 1, v___x_4989_);
lean_ctor_set(v___x_4964_, 0, v___x_4988_);
v___x_4991_ = v___x_4964_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v___x_4988_);
lean_ctor_set(v_reuseFailAlloc_4997_, 1, v___x_4989_);
v___x_4991_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
lean_object* v___x_4993_; 
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 1, v___x_4991_);
lean_ctor_set(v___x_4959_, 0, v___x_4980_);
v___x_4993_ = v___x_4959_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4980_);
lean_ctor_set(v_reuseFailAlloc_4996_, 1, v___x_4991_);
v___x_4993_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
lean_object* v___x_4994_; 
v___x_4994_ = lean_nat_add(v_a_4947_, v___x_4974_);
lean_dec(v_a_4947_);
v_a_4947_ = v___x_4994_;
v_b_4948_ = v___x_4993_;
goto _start;
}
}
}
else
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
lean_dec_ref(v___x_4980_);
lean_del_object(v___x_4964_);
lean_dec(v_snd_4962_);
lean_dec(v_fst_4961_);
lean_del_object(v___x_4959_);
lean_dec(v_a_4947_);
lean_dec(v___x_4946_);
lean_dec(v___x_4945_);
lean_dec_ref(v___x_4944_);
lean_dec_ref(v___x_4943_);
lean_dec_ref(v___x_4942_);
lean_dec(v___x_4941_);
lean_dec_ref(v_a_4940_);
lean_dec(v___x_4939_);
lean_dec_ref(v___x_4938_);
lean_dec(v_matchDeclName_4937_);
lean_dec_ref(v_val_4936_);
v_a_4998_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4986_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4986_);
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
else
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
lean_dec_ref(v___y_4982_);
lean_dec_ref(v___x_4980_);
lean_dec(v___x_4979_);
lean_del_object(v___x_4964_);
lean_dec(v_snd_4962_);
lean_dec(v_fst_4961_);
lean_del_object(v___x_4959_);
lean_dec(v_a_4947_);
lean_dec(v___x_4946_);
lean_dec(v___x_4945_);
lean_dec_ref(v___x_4944_);
lean_dec_ref(v___x_4943_);
lean_dec_ref(v___x_4942_);
lean_dec(v___x_4941_);
lean_dec_ref(v_a_4940_);
lean_dec(v___x_4939_);
lean_dec_ref(v___x_4938_);
lean_dec(v_matchDeclName_4937_);
lean_dec_ref(v_val_4936_);
v_a_5006_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4983_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4983_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
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
lean_object* v_upperBound_5021_ = _args[0];
lean_object* v_val_5022_ = _args[1];
lean_object* v_matchDeclName_5023_ = _args[2];
lean_object* v___x_5024_ = _args[3];
lean_object* v___x_5025_ = _args[4];
lean_object* v_a_5026_ = _args[5];
lean_object* v___x_5027_ = _args[6];
lean_object* v___x_5028_ = _args[7];
lean_object* v___x_5029_ = _args[8];
lean_object* v___x_5030_ = _args[9];
lean_object* v___x_5031_ = _args[10];
lean_object* v___x_5032_ = _args[11];
lean_object* v_a_5033_ = _args[12];
lean_object* v_b_5034_ = _args[13];
lean_object* v___y_5035_ = _args[14];
lean_object* v___y_5036_ = _args[15];
lean_object* v___y_5037_ = _args[16];
lean_object* v___y_5038_ = _args[17];
lean_object* v___y_5039_ = _args[18];
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5021_, v_val_5022_, v_matchDeclName_5023_, v___x_5024_, v___x_5025_, v_a_5026_, v___x_5027_, v___x_5028_, v___x_5029_, v___x_5030_, v___x_5031_, v___x_5032_, v_a_5033_, v_b_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
lean_dec(v___y_5038_);
lean_dec_ref(v___y_5037_);
lean_dec(v___y_5036_);
lean_dec_ref(v___y_5035_);
lean_dec(v_upperBound_5021_);
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5047_, lean_object* v___x_5048_, lean_object* v_matchDeclName_5049_, lean_object* v___x_5050_, lean_object* v_a_5051_, lean_object* v___x_5052_, lean_object* v___x_5053_, lean_object* v_xs_5054_, lean_object* v___matchResultType_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_){
_start:
{
lean_object* v_numParams_5061_; lean_object* v_numDiscrs_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v_lower_5068_; lean_object* v_upper_5069_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; uint8_t v___x_5100_; 
v_numParams_5061_ = lean_ctor_get(v_val_5047_, 0);
v_numDiscrs_5062_ = lean_ctor_get(v_val_5047_, 1);
v___x_5063_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5061_);
lean_inc_ref(v_xs_5054_);
v___x_5064_ = l_Array_toSubarray___redArg(v_xs_5054_, v___x_5063_, v_numParams_5061_);
v___x_5065_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5047_);
v___x_5066_ = lean_array_get(v___x_5048_, v_xs_5054_, v___x_5065_);
lean_dec(v___x_5065_);
v___x_5097_ = lean_array_get_size(v_xs_5054_);
v___x_5098_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5047_);
v___x_5099_ = lean_nat_sub(v___x_5097_, v___x_5098_);
lean_dec(v___x_5098_);
v___x_5100_ = lean_nat_dec_le(v___x_5099_, v___x_5063_);
if (v___x_5100_ == 0)
{
v_lower_5068_ = v___x_5099_;
v_upper_5069_ = v___x_5097_;
goto v___jp_5067_;
}
else
{
lean_dec(v___x_5099_);
v_lower_5068_ = v___x_5063_;
v_upper_5069_ = v___x_5097_;
goto v___jp_5067_;
}
v___jp_5067_:
{
lean_object* v___x_5070_; lean_object* v_start_5071_; lean_object* v_stop_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
lean_inc_ref(v_xs_5054_);
v___x_5070_ = l_Array_toSubarray___redArg(v_xs_5054_, v_lower_5068_, v_upper_5069_);
v_start_5071_ = lean_ctor_get(v___x_5070_, 1);
lean_inc(v_start_5071_);
v_stop_5072_ = lean_ctor_get(v___x_5070_, 2);
lean_inc(v_stop_5072_);
v___x_5073_ = lean_unsigned_to_nat(1u);
v___x_5074_ = lean_nat_add(v_numParams_5061_, v___x_5073_);
v___x_5075_ = lean_nat_add(v___x_5074_, v_numDiscrs_5062_);
v___x_5076_ = lean_nat_sub(v_stop_5072_, v_start_5071_);
lean_dec(v_start_5071_);
lean_dec(v_stop_5072_);
v___x_5077_ = l_Array_toSubarray___redArg(v_xs_5054_, v___x_5074_, v___x_5075_);
v___x_5078_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5076_);
v___x_5079_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5076_, v_val_5047_, v_matchDeclName_5049_, v___x_5077_, v___x_5050_, v_a_5051_, v___x_5052_, v___x_5064_, v___x_5066_, v___x_5070_, v___x_5076_, v___x_5053_, v___x_5063_, v___x_5078_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_);
lean_dec(v___x_5076_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5087_; 
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5087_ == 0)
{
lean_object* v_unused_5088_; 
v_unused_5088_ = lean_ctor_get(v___x_5079_, 0);
lean_dec(v_unused_5088_);
v___x_5081_ = v___x_5079_;
v_isShared_5082_ = v_isSharedCheck_5087_;
goto v_resetjp_5080_;
}
else
{
lean_dec(v___x_5079_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5087_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5083_; lean_object* v___x_5085_; 
v___x_5083_ = lean_box(0);
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 0, v___x_5083_);
v___x_5085_ = v___x_5081_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v___x_5083_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
else
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5096_; 
v_a_5089_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5096_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5096_ == 0)
{
v___x_5091_ = v___x_5079_;
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5079_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5096_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v___x_5094_; 
if (v_isShared_5092_ == 0)
{
v___x_5094_ = v___x_5091_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5089_);
v___x_5094_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
return v___x_5094_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5101_, lean_object* v___x_5102_, lean_object* v_matchDeclName_5103_, lean_object* v___x_5104_, lean_object* v_a_5105_, lean_object* v___x_5106_, lean_object* v___x_5107_, lean_object* v_xs_5108_, lean_object* v___matchResultType_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
lean_object* v_res_5115_; 
v_res_5115_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5101_, v___x_5102_, v_matchDeclName_5103_, v___x_5104_, v_a_5105_, v___x_5106_, v___x_5107_, v_xs_5108_, v___matchResultType_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec(v___y_5111_);
lean_dec_ref(v___y_5110_);
lean_dec_ref(v___matchResultType_5109_);
lean_dec_ref(v___x_5102_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5116_, lean_object* v_a_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_){
_start:
{
uint8_t v_trackZetaDelta_5122_; lean_object* v_zetaDeltaSet_5123_; lean_object* v_lctx_5124_; lean_object* v_localInstances_5125_; lean_object* v_defEqCtx_x3f_5126_; lean_object* v_synthPendingDepth_5127_; lean_object* v_canUnfold_x3f_5128_; uint8_t v_univApprox_5129_; uint8_t v_inTypeClassResolution_5130_; uint8_t v_cacheInferType_5131_; lean_object* v___x_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5175_; 
v_trackZetaDelta_5122_ = lean_ctor_get_uint8(v_a_5117_, sizeof(void*)*7);
v_zetaDeltaSet_5123_ = lean_ctor_get(v_a_5117_, 1);
lean_inc(v_zetaDeltaSet_5123_);
v_lctx_5124_ = lean_ctor_get(v_a_5117_, 2);
lean_inc_ref(v_lctx_5124_);
v_localInstances_5125_ = lean_ctor_get(v_a_5117_, 3);
lean_inc_ref(v_localInstances_5125_);
v_defEqCtx_x3f_5126_ = lean_ctor_get(v_a_5117_, 4);
lean_inc(v_defEqCtx_x3f_5126_);
v_synthPendingDepth_5127_ = lean_ctor_get(v_a_5117_, 5);
lean_inc(v_synthPendingDepth_5127_);
v_canUnfold_x3f_5128_ = lean_ctor_get(v_a_5117_, 6);
lean_inc(v_canUnfold_x3f_5128_);
v_univApprox_5129_ = lean_ctor_get_uint8(v_a_5117_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5130_ = lean_ctor_get_uint8(v_a_5117_, sizeof(void*)*7 + 2);
v_cacheInferType_5131_ = lean_ctor_get_uint8(v_a_5117_, sizeof(void*)*7 + 3);
v___x_5132_ = l_Lean_Meta_Context_config(v_a_5117_);
v_isSharedCheck_5175_ = !lean_is_exclusive(v_a_5117_);
if (v_isSharedCheck_5175_ == 0)
{
lean_object* v_unused_5176_; lean_object* v_unused_5177_; lean_object* v_unused_5178_; lean_object* v_unused_5179_; lean_object* v_unused_5180_; lean_object* v_unused_5181_; lean_object* v_unused_5182_; 
v_unused_5176_ = lean_ctor_get(v_a_5117_, 6);
lean_dec(v_unused_5176_);
v_unused_5177_ = lean_ctor_get(v_a_5117_, 5);
lean_dec(v_unused_5177_);
v_unused_5178_ = lean_ctor_get(v_a_5117_, 4);
lean_dec(v_unused_5178_);
v_unused_5179_ = lean_ctor_get(v_a_5117_, 3);
lean_dec(v_unused_5179_);
v_unused_5180_ = lean_ctor_get(v_a_5117_, 2);
lean_dec(v_unused_5180_);
v_unused_5181_ = lean_ctor_get(v_a_5117_, 1);
lean_dec(v_unused_5181_);
v_unused_5182_ = lean_ctor_get(v_a_5117_, 0);
lean_dec(v_unused_5182_);
v___x_5134_ = v_a_5117_;
v_isShared_5135_ = v_isSharedCheck_5175_;
goto v_resetjp_5133_;
}
else
{
lean_dec(v_a_5117_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5175_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v___x_5136_; uint64_t v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5140_; 
v___x_5136_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5132_);
v___x_5137_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5136_);
v___x_5138_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5138_, 0, v___x_5136_);
lean_ctor_set_uint64(v___x_5138_, sizeof(void*)*1, v___x_5137_);
lean_inc(v_canUnfold_x3f_5128_);
lean_inc(v_synthPendingDepth_5127_);
lean_inc(v_defEqCtx_x3f_5126_);
lean_inc_ref(v_localInstances_5125_);
lean_inc_ref(v_lctx_5124_);
lean_inc(v_zetaDeltaSet_5123_);
if (v_isShared_5135_ == 0)
{
lean_ctor_set(v___x_5134_, 0, v___x_5138_);
v___x_5140_ = v___x_5134_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5138_);
lean_ctor_set(v_reuseFailAlloc_5174_, 1, v_zetaDeltaSet_5123_);
lean_ctor_set(v_reuseFailAlloc_5174_, 2, v_lctx_5124_);
lean_ctor_set(v_reuseFailAlloc_5174_, 3, v_localInstances_5125_);
lean_ctor_set(v_reuseFailAlloc_5174_, 4, v_defEqCtx_x3f_5126_);
lean_ctor_set(v_reuseFailAlloc_5174_, 5, v_synthPendingDepth_5127_);
lean_ctor_set(v_reuseFailAlloc_5174_, 6, v_canUnfold_x3f_5128_);
lean_ctor_set_uint8(v_reuseFailAlloc_5174_, sizeof(void*)*7, v_trackZetaDelta_5122_);
lean_ctor_set_uint8(v_reuseFailAlloc_5174_, sizeof(void*)*7 + 1, v_univApprox_5129_);
lean_ctor_set_uint8(v_reuseFailAlloc_5174_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5130_);
lean_ctor_set_uint8(v_reuseFailAlloc_5174_, sizeof(void*)*7 + 3, v_cacheInferType_5131_);
v___x_5140_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
lean_object* v___x_5141_; lean_object* v___x_5142_; uint64_t v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; 
v___x_5141_ = l_Lean_Meta_Context_config(v___x_5140_);
lean_dec_ref(v___x_5140_);
v___x_5142_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5141_);
v___x_5143_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5142_);
v___x_5144_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5144_, 0, v___x_5142_);
lean_ctor_set_uint64(v___x_5144_, sizeof(void*)*1, v___x_5143_);
v___x_5145_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5145_, 0, v___x_5144_);
lean_ctor_set(v___x_5145_, 1, v_zetaDeltaSet_5123_);
lean_ctor_set(v___x_5145_, 2, v_lctx_5124_);
lean_ctor_set(v___x_5145_, 3, v_localInstances_5125_);
lean_ctor_set(v___x_5145_, 4, v_defEqCtx_x3f_5126_);
lean_ctor_set(v___x_5145_, 5, v_synthPendingDepth_5127_);
lean_ctor_set(v___x_5145_, 6, v_canUnfold_x3f_5128_);
lean_ctor_set_uint8(v___x_5145_, sizeof(void*)*7, v_trackZetaDelta_5122_);
lean_ctor_set_uint8(v___x_5145_, sizeof(void*)*7 + 1, v_univApprox_5129_);
lean_ctor_set_uint8(v___x_5145_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5130_);
lean_ctor_set_uint8(v___x_5145_, sizeof(void*)*7 + 3, v_cacheInferType_5131_);
lean_inc(v_matchDeclName_5116_);
v___x_5146_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5116_, v___x_5145_, v_a_5118_, v_a_5119_, v_a_5120_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; lean_object* v___x_5148_; lean_object* v_a_5149_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_a_5147_);
lean_dec_ref(v___x_5146_);
lean_inc(v_matchDeclName_5116_);
v___x_5148_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5116_, v_a_5120_);
v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
lean_inc(v_a_5149_);
lean_dec_ref(v___x_5148_);
if (lean_obj_tag(v_a_5149_) == 1)
{
lean_object* v_val_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___f_5156_; lean_object* v___x_5157_; uint8_t v___x_5158_; lean_object* v___x_5159_; 
v_val_5150_ = lean_ctor_get(v_a_5149_, 0);
lean_inc(v_val_5150_);
lean_dec_ref(v_a_5149_);
v___x_5151_ = l_Lean_instInhabitedExpr;
v___x_5152_ = l_Lean_ConstantInfo_levelParams(v_a_5147_);
v___x_5153_ = lean_box(0);
lean_inc(v___x_5152_);
v___x_5154_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_5152_, v___x_5153_);
v___x_5155_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5150_);
lean_inc(v_a_5147_);
v___f_5156_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5156_, 0, v_val_5150_);
lean_closure_set(v___f_5156_, 1, v___x_5151_);
lean_closure_set(v___f_5156_, 2, v_matchDeclName_5116_);
lean_closure_set(v___f_5156_, 3, v___x_5155_);
lean_closure_set(v___f_5156_, 4, v_a_5147_);
lean_closure_set(v___f_5156_, 5, v___x_5154_);
lean_closure_set(v___f_5156_, 6, v___x_5152_);
v___x_5157_ = l_Lean_ConstantInfo_type(v_a_5147_);
lean_dec(v_a_5147_);
v___x_5158_ = 0;
v___x_5159_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5157_, v___f_5156_, v___x_5158_, v___x_5158_, v___x_5145_, v_a_5118_, v_a_5119_, v_a_5120_);
lean_dec_ref(v___x_5145_);
return v___x_5159_;
}
else
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
lean_dec(v_a_5149_);
lean_dec(v_a_5147_);
v___x_5160_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5161_ = l_Lean_MessageData_ofName(v_matchDeclName_5116_);
v___x_5162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5160_);
lean_ctor_set(v___x_5162_, 1, v___x_5161_);
v___x_5163_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5164_, 0, v___x_5162_);
lean_ctor_set(v___x_5164_, 1, v___x_5163_);
v___x_5165_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5164_, v___x_5145_, v_a_5118_, v_a_5119_, v_a_5120_);
lean_dec_ref(v___x_5145_);
return v___x_5165_;
}
}
else
{
lean_object* v_a_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5173_; 
lean_dec_ref(v___x_5145_);
lean_dec(v_matchDeclName_5116_);
v_a_5166_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5173_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5173_ == 0)
{
v___x_5168_ = v___x_5146_;
v_isShared_5169_ = v_isSharedCheck_5173_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_a_5166_);
lean_dec(v___x_5146_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5173_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v___x_5171_; 
if (v_isShared_5169_ == 0)
{
v___x_5171_ = v___x_5168_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
v___x_5171_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
return v___x_5171_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_){
_start:
{
lean_object* v_res_5189_; 
v_res_5189_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_);
lean_dec(v_a_5187_);
lean_dec_ref(v_a_5186_);
lean_dec(v_a_5185_);
return v_res_5189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_inst_5190_, lean_object* v_R_5191_, lean_object* v_a_5192_, lean_object* v_b_5193_, lean_object* v_c_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
lean_object* v___x_5200_; 
v___x_5200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_5192_, v_b_5193_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_);
return v___x_5200_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_inst_5201_, lean_object* v_R_5202_, lean_object* v_a_5203_, lean_object* v_b_5204_, lean_object* v_c_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_inst_5201_, v_R_5202_, v_a_5203_, v_b_5204_, v_c_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_);
lean_dec(v___y_5209_);
lean_dec_ref(v___y_5208_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5212_, lean_object* v_val_5213_, lean_object* v_matchDeclName_5214_, lean_object* v___x_5215_, lean_object* v___x_5216_, lean_object* v_a_5217_, lean_object* v___x_5218_, lean_object* v___x_5219_, lean_object* v___x_5220_, lean_object* v___x_5221_, lean_object* v___x_5222_, lean_object* v___x_5223_, lean_object* v_inst_5224_, lean_object* v_R_5225_, lean_object* v_a_5226_, lean_object* v_b_5227_, lean_object* v_c_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_){
_start:
{
lean_object* v___x_5234_; 
v___x_5234_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5212_, v_val_5213_, v_matchDeclName_5214_, v___x_5215_, v___x_5216_, v_a_5217_, v___x_5218_, v___x_5219_, v___x_5220_, v___x_5221_, v___x_5222_, v___x_5223_, v_a_5226_, v_b_5227_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5235_ = _args[0];
lean_object* v_val_5236_ = _args[1];
lean_object* v_matchDeclName_5237_ = _args[2];
lean_object* v___x_5238_ = _args[3];
lean_object* v___x_5239_ = _args[4];
lean_object* v_a_5240_ = _args[5];
lean_object* v___x_5241_ = _args[6];
lean_object* v___x_5242_ = _args[7];
lean_object* v___x_5243_ = _args[8];
lean_object* v___x_5244_ = _args[9];
lean_object* v___x_5245_ = _args[10];
lean_object* v___x_5246_ = _args[11];
lean_object* v_inst_5247_ = _args[12];
lean_object* v_R_5248_ = _args[13];
lean_object* v_a_5249_ = _args[14];
lean_object* v_b_5250_ = _args[15];
lean_object* v_c_5251_ = _args[16];
lean_object* v___y_5252_ = _args[17];
lean_object* v___y_5253_ = _args[18];
lean_object* v___y_5254_ = _args[19];
lean_object* v___y_5255_ = _args[20];
lean_object* v___y_5256_ = _args[21];
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5235_, v_val_5236_, v_matchDeclName_5237_, v___x_5238_, v___x_5239_, v_a_5240_, v___x_5241_, v___x_5242_, v___x_5243_, v___x_5244_, v___x_5245_, v___x_5246_, v_inst_5247_, v_R_5248_, v_a_5249_, v_b_5250_, v_c_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
lean_dec(v_upperBound_5235_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5258_, lean_object* v_matchDeclName_5259_, lean_object* v_a_5260_, lean_object* v_b_5261_){
_start:
{
uint8_t v___x_5263_; 
v___x_5263_ = lean_nat_dec_lt(v_a_5260_, v_upperBound_5258_);
if (v___x_5263_ == 0)
{
lean_object* v___x_5264_; 
lean_dec(v_a_5260_);
lean_dec(v_matchDeclName_5259_);
v___x_5264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5264_, 0, v_b_5261_);
return v___x_5264_;
}
else
{
lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
v___x_5265_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5259_);
v___x_5266_ = l_Lean_Name_str___override(v_matchDeclName_5259_, v___x_5265_);
v___x_5267_ = lean_unsigned_to_nat(1u);
v___x_5268_ = lean_nat_add(v_a_5260_, v___x_5267_);
lean_dec(v_a_5260_);
lean_inc(v___x_5268_);
v___x_5269_ = lean_name_append_index_after(v___x_5266_, v___x_5268_);
v___x_5270_ = lean_array_push(v_b_5261_, v___x_5269_);
v_a_5260_ = v___x_5268_;
v_b_5261_ = v___x_5270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5272_, lean_object* v_matchDeclName_5273_, lean_object* v_a_5274_, lean_object* v_b_5275_, lean_object* v___y_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5272_, v_matchDeclName_5273_, v_a_5274_, v_b_5275_);
lean_dec(v_upperBound_5272_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_){
_start:
{
lean_object* v___x_5284_; lean_object* v_firstEqnName_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; 
v___x_5284_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5278_, 3);
v_firstEqnName_5285_ = l_Lean_Name_str___override(v_matchDeclName_5278_, v___x_5284_);
v___x_5286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5286_, 0, v_matchDeclName_5278_);
v___x_5287_ = l_Lean_Meta_realizeConst(v_matchDeclName_5278_, v_firstEqnName_5285_, v___x_5286_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_);
if (lean_obj_tag(v___x_5287_) == 0)
{
lean_object* v___x_5288_; lean_object* v_a_5289_; 
lean_dec_ref(v___x_5287_);
lean_inc(v_matchDeclName_5278_);
v___x_5288_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5278_, v_a_5282_);
v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
lean_inc(v_a_5289_);
lean_dec_ref(v___x_5288_);
if (lean_obj_tag(v_a_5289_) == 1)
{
lean_object* v_val_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
lean_dec(v_a_5282_);
lean_dec_ref(v_a_5281_);
lean_dec(v_a_5280_);
lean_dec_ref(v_a_5279_);
v_val_5290_ = lean_ctor_get(v_a_5289_, 0);
lean_inc(v_val_5290_);
lean_dec_ref(v_a_5289_);
v___x_5291_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5290_);
lean_dec(v_val_5290_);
v___x_5292_ = lean_unsigned_to_nat(0u);
v___x_5293_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5294_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5291_, v_matchDeclName_5278_, v___x_5292_, v___x_5293_);
lean_dec(v___x_5291_);
return v___x_5294_;
}
else
{
lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; 
lean_dec(v_a_5289_);
v___x_5295_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5296_ = l_Lean_MessageData_ofName(v_matchDeclName_5278_);
v___x_5297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5297_, 0, v___x_5295_);
lean_ctor_set(v___x_5297_, 1, v___x_5296_);
v___x_5298_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5299_, 0, v___x_5297_);
lean_ctor_set(v___x_5299_, 1, v___x_5298_);
v___x_5300_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5299_, v_a_5279_, v_a_5280_, v_a_5281_, v_a_5282_);
lean_dec(v_a_5282_);
lean_dec_ref(v_a_5281_);
lean_dec(v_a_5280_);
lean_dec_ref(v_a_5279_);
return v___x_5300_;
}
}
else
{
lean_object* v_a_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5308_; 
lean_dec(v_a_5282_);
lean_dec_ref(v_a_5281_);
lean_dec(v_a_5280_);
lean_dec_ref(v_a_5279_);
lean_dec(v_matchDeclName_5278_);
v_a_5301_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5303_ = v___x_5287_;
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_a_5301_);
lean_dec(v___x_5287_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5306_; 
if (v_isShared_5304_ == 0)
{
v___x_5306_ = v___x_5303_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_a_5301_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = lean_get_congr_match_equations_for(v_matchDeclName_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_);
return v_res_5315_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5316_, lean_object* v_matchDeclName_5317_, lean_object* v_inst_5318_, lean_object* v_R_5319_, lean_object* v_a_5320_, lean_object* v_b_5321_, lean_object* v_c_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_){
_start:
{
lean_object* v___x_5328_; 
v___x_5328_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5316_, v_matchDeclName_5317_, v_a_5320_, v_b_5321_);
return v___x_5328_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5329_, lean_object* v_matchDeclName_5330_, lean_object* v_inst_5331_, lean_object* v_R_5332_, lean_object* v_a_5333_, lean_object* v_b_5334_, lean_object* v_c_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_){
_start:
{
lean_object* v_res_5341_; 
v_res_5341_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5329_, v_matchDeclName_5330_, v_inst_5331_, v_R_5332_, v_a_5333_, v_b_5334_, v_c_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec(v_upperBound_5329_);
return v_res_5341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; 
v___x_5392_ = lean_unsigned_to_nat(3248161880u);
v___x_5393_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5394_ = l_Lean_Name_num___override(v___x_5393_, v___x_5392_);
return v___x_5394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5396_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5397_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5398_ = l_Lean_Name_str___override(v___x_5397_, v___x_5396_);
return v___x_5398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5400_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5401_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5402_ = l_Lean_Name_str___override(v___x_5401_, v___x_5400_);
return v___x_5402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
v___x_5403_ = lean_unsigned_to_nat(2u);
v___x_5404_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5405_ = l_Lean_Name_num___override(v___x_5404_, v___x_5403_);
return v___x_5405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5407_; uint8_t v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5407_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5408_ = 0;
v___x_5409_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5410_ = l_Lean_registerTraceClass(v___x_5407_, v___x_5408_, v___x_5409_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5411_){
_start:
{
lean_object* v_res_5412_; 
v_res_5412_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5413_, lean_object* v_n_5414_){
_start:
{
if (lean_obj_tag(v_n_5414_) == 1)
{
lean_object* v_pre_5415_; lean_object* v_str_5416_; uint8_t v___y_5418_; uint8_t v___x_5424_; 
v_pre_5415_ = lean_ctor_get(v_n_5414_, 0);
lean_inc(v_pre_5415_);
v_str_5416_ = lean_ctor_get(v_n_5414_, 1);
lean_inc_ref_n(v_str_5416_, 2);
lean_dec_ref(v_n_5414_);
v___x_5424_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5416_);
if (v___x_5424_ == 0)
{
lean_object* v___x_5425_; uint8_t v___x_5426_; 
v___x_5425_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5426_ = lean_string_dec_eq(v_str_5416_, v___x_5425_);
lean_dec_ref(v_str_5416_);
v___y_5418_ = v___x_5426_;
goto v___jp_5417_;
}
else
{
lean_dec_ref(v_str_5416_);
v___y_5418_ = v___x_5424_;
goto v___jp_5417_;
}
v___jp_5417_:
{
if (v___y_5418_ == 0)
{
lean_object* v___x_5419_; 
lean_dec(v_pre_5415_);
lean_dec_ref(v_env_5413_);
v___x_5419_ = lean_box(0);
return v___x_5419_;
}
else
{
lean_object* v___x_5420_; 
v___x_5420_ = lean_private_to_user_name(v_pre_5415_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_dec_ref(v_env_5413_);
return v___x_5420_;
}
else
{
lean_object* v_val_5421_; uint8_t v___x_5422_; 
v_val_5421_ = lean_ctor_get(v___x_5420_, 0);
lean_inc(v_val_5421_);
v___x_5422_ = lean_is_matcher(v_env_5413_, v_val_5421_);
if (v___x_5422_ == 0)
{
lean_object* v___x_5423_; 
lean_dec_ref(v___x_5420_);
v___x_5423_ = lean_box(0);
return v___x_5423_;
}
else
{
return v___x_5420_;
}
}
}
}
}
else
{
lean_object* v___x_5427_; 
lean_dec(v_n_5414_);
lean_dec_ref(v_env_5413_);
v___x_5427_ = lean_box(0);
return v___x_5427_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5428_, lean_object* v_x2_5429_){
_start:
{
lean_object* v___x_5430_; 
v___x_5430_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5428_, v_x2_5429_);
if (lean_obj_tag(v___x_5430_) == 0)
{
uint8_t v___x_5431_; 
v___x_5431_ = 0;
return v___x_5431_;
}
else
{
uint8_t v___x_5432_; 
lean_dec_ref(v___x_5430_);
v___x_5432_ = 1;
return v___x_5432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5433_, lean_object* v_x2_5434_){
_start:
{
uint8_t v_res_5435_; lean_object* v_r_5436_; 
v_res_5435_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5433_, v_x2_5434_);
v_r_5436_ = lean_box(v_res_5435_);
return v_r_5436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5439_; lean_object* v___x_5440_; 
v___f_5439_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5440_ = l_Lean_registerReservedNamePredicate(v___f_5439_);
return v___x_5440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5441_){
_start:
{
lean_object* v_res_5442_; 
v_res_5442_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5442_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5449_; uint64_t v___x_5450_; 
v___x_5449_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5450_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5449_);
return v___x_5450_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; 
v___x_5451_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5452_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5453_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5453_, 0, v___x_5452_);
lean_ctor_set_uint64(v___x_5453_, sizeof(void*)*1, v___x_5451_);
return v___x_5453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; 
v___x_5456_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5457_ = lean_unsigned_to_nat(0u);
v___x_5458_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_5458_, 0, v___x_5457_);
lean_ctor_set(v___x_5458_, 1, v___x_5457_);
lean_ctor_set(v___x_5458_, 2, v___x_5457_);
lean_ctor_set(v___x_5458_, 3, v___x_5457_);
lean_ctor_set(v___x_5458_, 4, v___x_5456_);
lean_ctor_set(v___x_5458_, 5, v___x_5456_);
lean_ctor_set(v___x_5458_, 6, v___x_5456_);
lean_ctor_set(v___x_5458_, 7, v___x_5456_);
lean_ctor_set(v___x_5458_, 8, v___x_5456_);
lean_ctor_set(v___x_5458_, 9, v___x_5456_);
return v___x_5458_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5459_; lean_object* v___x_5460_; 
v___x_5459_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5460_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5460_, 0, v___x_5459_);
lean_ctor_set(v___x_5460_, 1, v___x_5459_);
lean_ctor_set(v___x_5460_, 2, v___x_5459_);
lean_ctor_set(v___x_5460_, 3, v___x_5459_);
lean_ctor_set(v___x_5460_, 4, v___x_5459_);
lean_ctor_set(v___x_5460_, 5, v___x_5459_);
return v___x_5460_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5461_; lean_object* v___x_5462_; 
v___x_5461_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5462_, 0, v___x_5461_);
lean_ctor_set(v___x_5462_, 1, v___x_5461_);
lean_ctor_set(v___x_5462_, 2, v___x_5461_);
lean_ctor_set(v___x_5462_, 3, v___x_5461_);
lean_ctor_set(v___x_5462_, 4, v___x_5461_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5463_, lean_object* v_name_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
lean_object* v___x_5468_; lean_object* v_env_5469_; lean_object* v___x_5470_; 
v___x_5468_ = lean_st_ref_get(v___y_5466_);
v_env_5469_ = lean_ctor_get(v___x_5468_, 0);
lean_inc_ref(v_env_5469_);
lean_dec(v___x_5468_);
v___x_5470_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5469_, v_name_5464_);
if (lean_obj_tag(v___x_5470_) == 1)
{
lean_object* v_val_5471_; uint8_t v___x_5472_; uint8_t v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; 
v_val_5471_ = lean_ctor_get(v___x_5470_, 0);
lean_inc(v_val_5471_);
lean_dec_ref(v___x_5470_);
v___x_5472_ = 0;
v___x_5473_ = 1;
v___x_5474_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5475_ = lean_unsigned_to_nat(0u);
v___x_5476_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5477_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5478_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5479_ = lean_box(0);
lean_inc(v___x_5463_);
v___x_5480_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5480_, 0, v___x_5474_);
lean_ctor_set(v___x_5480_, 1, v___x_5463_);
lean_ctor_set(v___x_5480_, 2, v___x_5477_);
lean_ctor_set(v___x_5480_, 3, v___x_5478_);
lean_ctor_set(v___x_5480_, 4, v___x_5479_);
lean_ctor_set(v___x_5480_, 5, v___x_5475_);
lean_ctor_set(v___x_5480_, 6, v___x_5479_);
lean_ctor_set_uint8(v___x_5480_, sizeof(void*)*7, v___x_5472_);
lean_ctor_set_uint8(v___x_5480_, sizeof(void*)*7 + 1, v___x_5472_);
lean_ctor_set_uint8(v___x_5480_, sizeof(void*)*7 + 2, v___x_5472_);
lean_ctor_set_uint8(v___x_5480_, sizeof(void*)*7 + 3, v___x_5473_);
v___x_5481_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5482_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5483_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5484_, 0, v___x_5481_);
lean_ctor_set(v___x_5484_, 1, v___x_5482_);
lean_ctor_set(v___x_5484_, 2, v___x_5463_);
lean_ctor_set(v___x_5484_, 3, v___x_5476_);
lean_ctor_set(v___x_5484_, 4, v___x_5483_);
v___x_5485_ = lean_st_mk_ref(v___x_5484_);
lean_inc(v___y_5466_);
lean_inc_ref(v___y_5465_);
lean_inc(v___x_5485_);
v___x_5486_ = lean_get_match_equations_for(v_val_5471_, v___x_5480_, v___x_5485_, v___y_5465_, v___y_5466_);
if (lean_obj_tag(v___x_5486_) == 0)
{
lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5495_; 
v_isSharedCheck_5495_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5495_ == 0)
{
lean_object* v_unused_5496_; 
v_unused_5496_ = lean_ctor_get(v___x_5486_, 0);
lean_dec(v_unused_5496_);
v___x_5488_ = v___x_5486_;
v_isShared_5489_ = v_isSharedCheck_5495_;
goto v_resetjp_5487_;
}
else
{
lean_dec(v___x_5486_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5495_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5493_; 
v___x_5490_ = lean_st_ref_get(v___x_5485_);
lean_dec(v___x_5485_);
lean_dec(v___x_5490_);
v___x_5491_ = lean_box(v___x_5473_);
if (v_isShared_5489_ == 0)
{
lean_ctor_set(v___x_5488_, 0, v___x_5491_);
v___x_5493_ = v___x_5488_;
goto v_reusejp_5492_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v___x_5491_);
v___x_5493_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5492_;
}
v_reusejp_5492_:
{
return v___x_5493_;
}
}
}
else
{
lean_dec(v___x_5485_);
if (lean_obj_tag(v___x_5486_) == 0)
{
lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5504_; 
v_isSharedCheck_5504_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5504_ == 0)
{
lean_object* v_unused_5505_; 
v_unused_5505_ = lean_ctor_get(v___x_5486_, 0);
lean_dec(v_unused_5505_);
v___x_5498_ = v___x_5486_;
v_isShared_5499_ = v_isSharedCheck_5504_;
goto v_resetjp_5497_;
}
else
{
lean_dec(v___x_5486_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5504_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v___x_5500_; lean_object* v___x_5502_; 
v___x_5500_ = lean_box(v___x_5473_);
if (v_isShared_5499_ == 0)
{
lean_ctor_set_tag(v___x_5498_, 0);
lean_ctor_set(v___x_5498_, 0, v___x_5500_);
v___x_5502_ = v___x_5498_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5500_);
v___x_5502_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
return v___x_5502_;
}
}
}
else
{
lean_object* v_a_5506_; lean_object* v___x_5508_; uint8_t v_isShared_5509_; uint8_t v_isSharedCheck_5513_; 
v_a_5506_ = lean_ctor_get(v___x_5486_, 0);
v_isSharedCheck_5513_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5513_ == 0)
{
v___x_5508_ = v___x_5486_;
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
else
{
lean_inc(v_a_5506_);
lean_dec(v___x_5486_);
v___x_5508_ = lean_box(0);
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
v_resetjp_5507_:
{
lean_object* v___x_5511_; 
if (v_isShared_5509_ == 0)
{
v___x_5511_ = v___x_5508_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_a_5506_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
}
}
}
else
{
uint8_t v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; 
lean_dec(v___x_5470_);
lean_dec(v___x_5463_);
v___x_5514_ = 0;
v___x_5515_ = lean_box(v___x_5514_);
v___x_5516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5516_, 0, v___x_5515_);
return v___x_5516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5517_, lean_object* v_name_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_){
_start:
{
lean_object* v_res_5522_; 
v_res_5522_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5517_, v_name_5518_, v___y_5519_, v___y_5520_);
lean_dec(v___y_5520_);
lean_dec_ref(v___y_5519_);
return v_res_5522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5526_; lean_object* v___x_5527_; 
v___f_5526_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5527_ = l_Lean_registerReservedNameAction(v___f_5526_);
return v___x_5527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5528_){
_start:
{
lean_object* v_res_5529_; 
v_res_5529_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5530_, lean_object* v_n_5531_){
_start:
{
if (lean_obj_tag(v_n_5531_) == 1)
{
lean_object* v_pre_5532_; lean_object* v_str_5533_; uint8_t v___x_5534_; 
v_pre_5532_ = lean_ctor_get(v_n_5531_, 0);
lean_inc(v_pre_5532_);
v_str_5533_ = lean_ctor_get(v_n_5531_, 1);
lean_inc_ref(v_str_5533_);
lean_dec_ref(v_n_5531_);
v___x_5534_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5533_);
if (v___x_5534_ == 0)
{
lean_object* v___x_5535_; 
lean_dec(v_pre_5532_);
lean_dec_ref(v_env_5530_);
v___x_5535_ = lean_box(0);
return v___x_5535_;
}
else
{
uint8_t v___x_5536_; 
lean_inc(v_pre_5532_);
v___x_5536_ = lean_is_matcher(v_env_5530_, v_pre_5532_);
if (v___x_5536_ == 0)
{
lean_object* v___x_5537_; 
lean_dec(v_pre_5532_);
v___x_5537_ = lean_box(0);
return v___x_5537_;
}
else
{
lean_object* v___x_5538_; 
v___x_5538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5538_, 0, v_pre_5532_);
return v___x_5538_;
}
}
}
else
{
lean_object* v___x_5539_; 
lean_dec(v_n_5531_);
lean_dec_ref(v_env_5530_);
v___x_5539_ = lean_box(0);
return v___x_5539_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5540_, lean_object* v_x2_5541_){
_start:
{
lean_object* v___x_5542_; 
v___x_5542_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5540_, v_x2_5541_);
if (lean_obj_tag(v___x_5542_) == 0)
{
uint8_t v___x_5543_; 
v___x_5543_ = 0;
return v___x_5543_;
}
else
{
uint8_t v___x_5544_; 
lean_dec_ref(v___x_5542_);
v___x_5544_ = 1;
return v___x_5544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5545_, lean_object* v_x2_5546_){
_start:
{
uint8_t v_res_5547_; lean_object* v_r_5548_; 
v_res_5547_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5545_, v_x2_5546_);
v_r_5548_ = lean_box(v_res_5547_);
return v_r_5548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5551_; lean_object* v___x_5552_; 
v___f_5551_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5552_ = l_Lean_registerReservedNamePredicate(v___f_5551_);
return v___x_5552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5553_){
_start:
{
lean_object* v_res_5554_; 
v_res_5554_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5555_, lean_object* v_name_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_){
_start:
{
lean_object* v___x_5560_; lean_object* v_env_5561_; lean_object* v___x_5562_; 
v___x_5560_ = lean_st_ref_get(v___y_5558_);
v_env_5561_ = lean_ctor_get(v___x_5560_, 0);
lean_inc_ref(v_env_5561_);
lean_dec(v___x_5560_);
v___x_5562_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5561_, v_name_5556_);
if (lean_obj_tag(v___x_5562_) == 1)
{
lean_object* v_val_5563_; uint8_t v___x_5564_; uint8_t v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; 
v_val_5563_ = lean_ctor_get(v___x_5562_, 0);
lean_inc(v_val_5563_);
lean_dec_ref(v___x_5562_);
v___x_5564_ = 0;
v___x_5565_ = 1;
v___x_5566_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5567_ = lean_unsigned_to_nat(32u);
v___x_5568_ = lean_mk_empty_array_with_capacity(v___x_5567_);
lean_dec_ref(v___x_5568_);
v___x_5569_ = lean_unsigned_to_nat(0u);
v___x_5570_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5571_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5572_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5573_ = lean_box(0);
lean_inc(v___x_5555_);
v___x_5574_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5574_, 0, v___x_5566_);
lean_ctor_set(v___x_5574_, 1, v___x_5555_);
lean_ctor_set(v___x_5574_, 2, v___x_5571_);
lean_ctor_set(v___x_5574_, 3, v___x_5572_);
lean_ctor_set(v___x_5574_, 4, v___x_5573_);
lean_ctor_set(v___x_5574_, 5, v___x_5569_);
lean_ctor_set(v___x_5574_, 6, v___x_5573_);
lean_ctor_set_uint8(v___x_5574_, sizeof(void*)*7, v___x_5564_);
lean_ctor_set_uint8(v___x_5574_, sizeof(void*)*7 + 1, v___x_5564_);
lean_ctor_set_uint8(v___x_5574_, sizeof(void*)*7 + 2, v___x_5564_);
lean_ctor_set_uint8(v___x_5574_, sizeof(void*)*7 + 3, v___x_5565_);
v___x_5575_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5576_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5577_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5578_, 0, v___x_5575_);
lean_ctor_set(v___x_5578_, 1, v___x_5576_);
lean_ctor_set(v___x_5578_, 2, v___x_5555_);
lean_ctor_set(v___x_5578_, 3, v___x_5570_);
lean_ctor_set(v___x_5578_, 4, v___x_5577_);
v___x_5579_ = lean_st_mk_ref(v___x_5578_);
lean_inc(v___y_5558_);
lean_inc_ref(v___y_5557_);
lean_inc(v___x_5579_);
v___x_5580_ = lean_get_congr_match_equations_for(v_val_5563_, v___x_5574_, v___x_5579_, v___y_5557_, v___y_5558_);
if (lean_obj_tag(v___x_5580_) == 0)
{
lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5589_; 
v_isSharedCheck_5589_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5589_ == 0)
{
lean_object* v_unused_5590_; 
v_unused_5590_ = lean_ctor_get(v___x_5580_, 0);
lean_dec(v_unused_5590_);
v___x_5582_ = v___x_5580_;
v_isShared_5583_ = v_isSharedCheck_5589_;
goto v_resetjp_5581_;
}
else
{
lean_dec(v___x_5580_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5589_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5587_; 
v___x_5584_ = lean_st_ref_get(v___x_5579_);
lean_dec(v___x_5579_);
lean_dec(v___x_5584_);
v___x_5585_ = lean_box(v___x_5565_);
if (v_isShared_5583_ == 0)
{
lean_ctor_set(v___x_5582_, 0, v___x_5585_);
v___x_5587_ = v___x_5582_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5585_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
return v___x_5587_;
}
}
}
else
{
lean_dec(v___x_5579_);
if (lean_obj_tag(v___x_5580_) == 0)
{
lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5598_; 
v_isSharedCheck_5598_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5598_ == 0)
{
lean_object* v_unused_5599_; 
v_unused_5599_ = lean_ctor_get(v___x_5580_, 0);
lean_dec(v_unused_5599_);
v___x_5592_ = v___x_5580_;
v_isShared_5593_ = v_isSharedCheck_5598_;
goto v_resetjp_5591_;
}
else
{
lean_dec(v___x_5580_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5598_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v___x_5594_; lean_object* v___x_5596_; 
v___x_5594_ = lean_box(v___x_5565_);
if (v_isShared_5593_ == 0)
{
lean_ctor_set_tag(v___x_5592_, 0);
lean_ctor_set(v___x_5592_, 0, v___x_5594_);
v___x_5596_ = v___x_5592_;
goto v_reusejp_5595_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v___x_5594_);
v___x_5596_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5595_;
}
v_reusejp_5595_:
{
return v___x_5596_;
}
}
}
else
{
lean_object* v_a_5600_; lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5607_; 
v_a_5600_ = lean_ctor_get(v___x_5580_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5602_ = v___x_5580_;
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
else
{
lean_inc(v_a_5600_);
lean_dec(v___x_5580_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v___x_5605_; 
if (v_isShared_5603_ == 0)
{
v___x_5605_ = v___x_5602_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_a_5600_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
}
}
}
else
{
uint8_t v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; 
lean_dec(v___x_5562_);
lean_dec(v___x_5555_);
v___x_5608_ = 0;
v___x_5609_ = lean_box(v___x_5608_);
v___x_5610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5610_, 0, v___x_5609_);
return v___x_5610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5611_, lean_object* v_name_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_){
_start:
{
lean_object* v_res_5616_; 
v_res_5616_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5611_, v_name_5612_, v___y_5613_, v___y_5614_);
lean_dec(v___y_5614_);
lean_dec_ref(v___y_5613_);
return v_res_5616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5620_; lean_object* v___x_5621_; 
v___f_5620_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5621_ = l_Lean_registerReservedNameAction(v___f_5620_);
return v___x_5621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5622_){
_start:
{
lean_object* v_res_5623_; 
v_res_5623_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5623_;
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
