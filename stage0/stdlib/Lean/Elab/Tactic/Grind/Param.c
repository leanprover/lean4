// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Param
// Imports: public import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Tactic.Grind.ForallProp import Lean.Elab.Tactic.Grind.Anchor import Lean.Elab.SyntheticMVars
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Meta_Grind_CasesTypes_contains(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Expr_eta(lean_object*);
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Grind_isMatchEqLikeDeclName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabAnchorRef(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toPArray_x27___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(lean_object*);
uint8_t l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremForDecl(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_backward_grind_inferPattern;
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_Grind_grindExt;
lean_object* l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_find___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Linter_checkDeprecated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_erase___redArg(lean_object*, lean_object*);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_assertExtra___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_runParserCategory(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "this parameter is redundant, environment already contains `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` annotated with `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<input>"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "unexpected modifier "};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "redundant modifier `!` in `grind` parameter"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "failed to generate equation theorems for `"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "invalid `grind` parameter, `"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "` is a definition, the only acceptable (and redundant) modifier is '='"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "` is a reducible definition, `grind` automatically unfolds them"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_addEMatchTheorem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` is not a theorem, definition, or inductive type"};
static const lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_addEMatchTheorem___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "invalid `grind` parameter, only global declarations are allowed when `+revert` is used"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 97, 194, 195, 68, 28, 219, 173)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "invalid `grind` parameter, failed to infer patterns"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "invalid `grind` parameter, parameter type is not a `forall` and is universe polymorphic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "invalid `grind` parameter, modifier is redundant since the parameter type is not a `forall`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid `grind` parameter, proof term expected"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "invalid `grind` parameter, only global declarations are allowed with this kind of modifier"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___closed__0 = (const lean_object*)&l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "invalid use of `usr` modifier, `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` does not have patterns specified with the command `grind_pattern`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "`cases` parameter are not supported here"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "invalid use of `intro` modifier, `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "`[grind ext]` cannot be set using parameters"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "normalization theorems should be registered using the `@[grind norm]` attribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "declarations to be unfolded during normalization should be registered using the `@[grind unfold]` attribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid use of modifier in `grind` attribute `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "redundant parameter `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "`, `grind` uses local hypotheses automatically"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindParam"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 144, 208, 205, 52, 106, 220, 83)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unexpected `grind` parameter"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindErase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(171, 172, 113, 174, 15, 5, 26, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindLemma"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 180, 24, 243, 113, 54, 79, 133)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLemmaMin"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(65, 124, 255, 191, 121, 182, 88, 219)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "anchor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(168, 155, 228, 98, 168, 72, 115, 174)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "invalid anchor, `only` modifier expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "invalid `-` occurrence, it can only used at the `grind` tactic entry point"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object**);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(lean_object* v_params_1_, lean_object* v_declName_2_, uint8_t v_eager_3_){
_start:
{
lean_object* v_config_4_; lean_object* v_extensions_5_; lean_object* v_extra_6_; lean_object* v_extraInj_7_; lean_object* v_extraFacts_8_; lean_object* v_symPrios_9_; lean_object* v_norm_10_; lean_object* v_normProcs_11_; lean_object* v_anchorRefs_x3f_12_; lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v_config_4_ = lean_ctor_get(v_params_1_, 0);
v_extensions_5_ = lean_ctor_get(v_params_1_, 1);
v_extra_6_ = lean_ctor_get(v_params_1_, 2);
v_extraInj_7_ = lean_ctor_get(v_params_1_, 3);
v_extraFacts_8_ = lean_ctor_get(v_params_1_, 4);
v_symPrios_9_ = lean_ctor_get(v_params_1_, 5);
v_norm_10_ = lean_ctor_get(v_params_1_, 6);
v_normProcs_11_ = lean_ctor_get(v_params_1_, 7);
v_anchorRefs_x3f_12_ = lean_ctor_get(v_params_1_, 8);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_array_get_size(v_extensions_5_);
v___x_15_ = lean_nat_dec_lt(v___x_13_, v___x_14_);
if (v___x_15_ == 0)
{
lean_dec(v_declName_2_);
return v_params_1_;
}
else
{
lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_39_; 
lean_inc(v_anchorRefs_x3f_12_);
lean_inc_ref(v_normProcs_11_);
lean_inc_ref(v_norm_10_);
lean_inc_ref(v_symPrios_9_);
lean_inc_ref(v_extraFacts_8_);
lean_inc_ref(v_extraInj_7_);
lean_inc_ref(v_extra_6_);
lean_inc_ref(v_extensions_5_);
lean_inc_ref(v_config_4_);
v_isSharedCheck_39_ = !lean_is_exclusive(v_params_1_);
if (v_isSharedCheck_39_ == 0)
{
lean_object* v_unused_40_; lean_object* v_unused_41_; lean_object* v_unused_42_; lean_object* v_unused_43_; lean_object* v_unused_44_; lean_object* v_unused_45_; lean_object* v_unused_46_; lean_object* v_unused_47_; lean_object* v_unused_48_; 
v_unused_40_ = lean_ctor_get(v_params_1_, 8);
lean_dec(v_unused_40_);
v_unused_41_ = lean_ctor_get(v_params_1_, 7);
lean_dec(v_unused_41_);
v_unused_42_ = lean_ctor_get(v_params_1_, 6);
lean_dec(v_unused_42_);
v_unused_43_ = lean_ctor_get(v_params_1_, 5);
lean_dec(v_unused_43_);
v_unused_44_ = lean_ctor_get(v_params_1_, 4);
lean_dec(v_unused_44_);
v_unused_45_ = lean_ctor_get(v_params_1_, 3);
lean_dec(v_unused_45_);
v_unused_46_ = lean_ctor_get(v_params_1_, 2);
lean_dec(v_unused_46_);
v_unused_47_ = lean_ctor_get(v_params_1_, 1);
lean_dec(v_unused_47_);
v_unused_48_ = lean_ctor_get(v_params_1_, 0);
lean_dec(v_unused_48_);
v___x_17_ = v_params_1_;
v_isShared_18_ = v_isSharedCheck_39_;
goto v_resetjp_16_;
}
else
{
lean_dec(v_params_1_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_39_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_v_19_; lean_object* v_casesTypes_20_; lean_object* v_extThms_21_; lean_object* v_funCC_22_; lean_object* v_ematch_23_; lean_object* v_inj_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_38_; 
v_v_19_ = lean_array_fget(v_extensions_5_, v___x_13_);
v_casesTypes_20_ = lean_ctor_get(v_v_19_, 0);
v_extThms_21_ = lean_ctor_get(v_v_19_, 1);
v_funCC_22_ = lean_ctor_get(v_v_19_, 2);
v_ematch_23_ = lean_ctor_get(v_v_19_, 3);
v_inj_24_ = lean_ctor_get(v_v_19_, 4);
v_isSharedCheck_38_ = !lean_is_exclusive(v_v_19_);
if (v_isSharedCheck_38_ == 0)
{
v___x_26_ = v_v_19_;
v_isShared_27_ = v_isSharedCheck_38_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_inj_24_);
lean_inc(v_ematch_23_);
lean_inc(v_funCC_22_);
lean_inc(v_extThms_21_);
lean_inc(v_casesTypes_20_);
lean_dec(v_v_19_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_38_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v_xs_x27_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_28_ = lean_box(0);
v_xs_x27_29_ = lean_array_fset(v_extensions_5_, v___x_13_, v___x_28_);
v___x_30_ = l_Lean_Meta_Grind_CasesTypes_insert(v_casesTypes_20_, v_declName_2_, v_eager_3_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_30_);
v___x_32_ = v___x_26_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_extThms_21_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v_funCC_22_);
lean_ctor_set(v_reuseFailAlloc_37_, 3, v_ematch_23_);
lean_ctor_set(v_reuseFailAlloc_37_, 4, v_inj_24_);
v___x_32_ = v_reuseFailAlloc_37_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = lean_array_fset(v_xs_x27_29_, v___x_13_, v___x_32_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___x_33_);
v___x_35_ = v___x_17_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_config_4_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_36_, 2, v_extra_6_);
lean_ctor_set(v_reuseFailAlloc_36_, 3, v_extraInj_7_);
lean_ctor_set(v_reuseFailAlloc_36_, 4, v_extraFacts_8_);
lean_ctor_set(v_reuseFailAlloc_36_, 5, v_symPrios_9_);
lean_ctor_set(v_reuseFailAlloc_36_, 6, v_norm_10_);
lean_ctor_set(v_reuseFailAlloc_36_, 7, v_normProcs_11_);
lean_ctor_set(v_reuseFailAlloc_36_, 8, v_anchorRefs_x3f_12_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes___boxed(lean_object* v_params_49_, lean_object* v_declName_50_, lean_object* v_eager_51_){
_start:
{
uint8_t v_eager_boxed_52_; lean_object* v_res_53_; 
v_eager_boxed_52_ = lean_unbox(v_eager_51_);
v_res_53_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_49_, v_declName_50_, v_eager_boxed_52_);
return v_res_53_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(lean_object* v_declName_54_, lean_object* v_as_55_, size_t v_i_56_, size_t v_stop_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = lean_usize_dec_eq(v_i_56_, v_stop_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v_casesTypes_60_; uint8_t v___x_61_; 
v___x_59_ = lean_array_uget_borrowed(v_as_55_, v_i_56_);
v_casesTypes_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_casesTypes_60_);
v___x_61_ = l_Lean_Meta_Grind_CasesTypes_contains(v_casesTypes_60_, v_declName_54_);
if (v___x_61_ == 0)
{
size_t v___x_62_; size_t v___x_63_; 
v___x_62_ = ((size_t)1ULL);
v___x_63_ = lean_usize_add(v_i_56_, v___x_62_);
v_i_56_ = v___x_63_;
goto _start;
}
else
{
return v___x_61_;
}
}
else
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0___boxed(lean_object* v_declName_66_, lean_object* v_as_67_, lean_object* v_i_68_, lean_object* v_stop_69_){
_start:
{
size_t v_i_boxed_70_; size_t v_stop_boxed_71_; uint8_t v_res_72_; lean_object* v_r_73_; 
v_i_boxed_70_ = lean_unbox_usize(v_i_68_);
lean_dec(v_i_68_);
v_stop_boxed_71_ = lean_unbox_usize(v_stop_69_);
lean_dec(v_stop_69_);
v_res_72_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(v_declName_66_, v_as_67_, v_i_boxed_70_, v_stop_boxed_71_);
lean_dec_ref(v_as_67_);
lean_dec(v_declName_66_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(lean_object* v_params_74_, lean_object* v_declName_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___y_83_; lean_object* v___y_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v_config_91_; lean_object* v_extensions_92_; lean_object* v_extra_93_; lean_object* v_extraInj_94_; lean_object* v_extraFacts_95_; lean_object* v_symPrios_96_; lean_object* v_norm_97_; lean_object* v_normProcs_98_; lean_object* v_anchorRefs_x3f_99_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_config_91_ = lean_ctor_get(v_params_74_, 0);
lean_inc_ref(v_config_91_);
v_extensions_92_ = lean_ctor_get(v_params_74_, 1);
lean_inc_ref(v_extensions_92_);
v_extra_93_ = lean_ctor_get(v_params_74_, 2);
lean_inc_ref(v_extra_93_);
v_extraInj_94_ = lean_ctor_get(v_params_74_, 3);
lean_inc_ref(v_extraInj_94_);
v_extraFacts_95_ = lean_ctor_get(v_params_74_, 4);
lean_inc_ref(v_extraFacts_95_);
v_symPrios_96_ = lean_ctor_get(v_params_74_, 5);
lean_inc_ref(v_symPrios_96_);
v_norm_97_ = lean_ctor_get(v_params_74_, 6);
lean_inc_ref(v_norm_97_);
v_normProcs_98_ = lean_ctor_get(v_params_74_, 7);
lean_inc_ref(v_normProcs_98_);
v_anchorRefs_x3f_99_ = lean_ctor_get(v_params_74_, 8);
lean_inc(v_anchorRefs_x3f_99_);
lean_dec_ref(v_params_74_);
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_array_get_size(v_extensions_92_);
v___x_133_ = lean_nat_dec_lt(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
goto v___jp_121_;
}
else
{
if (v___x_133_ == 0)
{
goto v___jp_121_;
}
else
{
size_t v___x_134_; size_t v___x_135_; uint8_t v___x_136_; 
v___x_134_ = ((size_t)0ULL);
v___x_135_ = lean_usize_of_nat(v___x_132_);
v___x_136_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes_spec__0(v_declName_75_, v_extensions_92_, v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
goto v___jp_121_;
}
else
{
goto v___jp_100_;
}
}
}
v___jp_79_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_89_, 0, v___y_81_);
lean_ctor_set(v___x_89_, 1, v___y_88_);
lean_ctor_set(v___x_89_, 2, v___y_84_);
lean_ctor_set(v___x_89_, 3, v___y_87_);
lean_ctor_set(v___x_89_, 4, v___y_86_);
lean_ctor_set(v___x_89_, 5, v___y_80_);
lean_ctor_set(v___x_89_, 6, v___y_85_);
lean_ctor_set(v___x_89_, 7, v___y_82_);
lean_ctor_set(v___x_89_, 8, v___y_83_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
v___jp_100_:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_array_get_size(v_extensions_92_);
v___x_103_ = lean_nat_dec_lt(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_dec(v_declName_75_);
v___y_80_ = v_symPrios_96_;
v___y_81_ = v_config_91_;
v___y_82_ = v_normProcs_98_;
v___y_83_ = v_anchorRefs_x3f_99_;
v___y_84_ = v_extra_93_;
v___y_85_ = v_norm_97_;
v___y_86_ = v_extraFacts_95_;
v___y_87_ = v_extraInj_94_;
v___y_88_ = v_extensions_92_;
goto v___jp_79_;
}
else
{
lean_object* v_v_104_; lean_object* v_casesTypes_105_; lean_object* v_extThms_106_; lean_object* v_funCC_107_; lean_object* v_ematch_108_; lean_object* v_inj_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_120_; 
v_v_104_ = lean_array_fget(v_extensions_92_, v___x_101_);
v_casesTypes_105_ = lean_ctor_get(v_v_104_, 0);
v_extThms_106_ = lean_ctor_get(v_v_104_, 1);
v_funCC_107_ = lean_ctor_get(v_v_104_, 2);
v_ematch_108_ = lean_ctor_get(v_v_104_, 3);
v_inj_109_ = lean_ctor_get(v_v_104_, 4);
v_isSharedCheck_120_ = !lean_is_exclusive(v_v_104_);
if (v_isSharedCheck_120_ == 0)
{
v___x_111_ = v_v_104_;
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_inj_109_);
lean_inc(v_ematch_108_);
lean_inc(v_funCC_107_);
lean_inc(v_extThms_106_);
lean_inc(v_casesTypes_105_);
lean_dec(v_v_104_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v_xs_x27_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_113_ = lean_box(0);
v_xs_x27_114_ = lean_array_fset(v_extensions_92_, v___x_101_, v___x_113_);
v___x_115_ = l_Lean_Meta_Grind_CasesTypes_erase(v_casesTypes_105_, v_declName_75_);
lean_dec(v_declName_75_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_115_);
v___x_117_ = v___x_111_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_extThms_106_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_funCC_107_);
lean_ctor_set(v_reuseFailAlloc_119_, 3, v_ematch_108_);
lean_ctor_set(v_reuseFailAlloc_119_, 4, v_inj_109_);
v___x_117_ = v_reuseFailAlloc_119_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; 
v___x_118_ = lean_array_fset(v_xs_x27_114_, v___x_101_, v___x_117_);
v___y_80_ = v_symPrios_96_;
v___y_81_ = v_config_91_;
v___y_82_ = v_normProcs_98_;
v___y_83_ = v_anchorRefs_x3f_99_;
v___y_84_ = v_extra_93_;
v___y_85_ = v_norm_97_;
v___y_86_ = v_extraFacts_95_;
v___y_87_ = v_extraInj_94_;
v___y_88_ = v___x_118_;
goto v___jp_79_;
}
}
}
}
v___jp_121_:
{
lean_object* v___x_122_; 
lean_inc(v_declName_75_);
v___x_122_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_dec_ref(v___x_122_);
goto v___jp_100_;
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_anchorRefs_x3f_99_);
lean_dec_ref(v_normProcs_98_);
lean_dec_ref(v_norm_97_);
lean_dec_ref(v_symPrios_96_);
lean_dec_ref(v_extraFacts_95_);
lean_dec_ref(v_extraInj_94_);
lean_dec_ref(v_extra_93_);
lean_dec_ref(v_extensions_92_);
lean_dec_ref(v_config_91_);
lean_dec(v_declName_75_);
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes___boxed(lean_object* v_params_137_, lean_object* v_declName_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_params_137_, v_declName_138_, v_a_139_, v_a_140_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(lean_object* v_params_143_, lean_object* v_declName_144_){
_start:
{
lean_object* v_config_145_; lean_object* v_extensions_146_; lean_object* v_extra_147_; lean_object* v_extraInj_148_; lean_object* v_extraFacts_149_; lean_object* v_symPrios_150_; lean_object* v_norm_151_; lean_object* v_normProcs_152_; lean_object* v_anchorRefs_x3f_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v_config_145_ = lean_ctor_get(v_params_143_, 0);
v_extensions_146_ = lean_ctor_get(v_params_143_, 1);
v_extra_147_ = lean_ctor_get(v_params_143_, 2);
v_extraInj_148_ = lean_ctor_get(v_params_143_, 3);
v_extraFacts_149_ = lean_ctor_get(v_params_143_, 4);
v_symPrios_150_ = lean_ctor_get(v_params_143_, 5);
v_norm_151_ = lean_ctor_get(v_params_143_, 6);
v_normProcs_152_ = lean_ctor_get(v_params_143_, 7);
v_anchorRefs_x3f_153_ = lean_ctor_get(v_params_143_, 8);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_array_get_size(v_extensions_146_);
v___x_156_ = lean_nat_dec_lt(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_dec(v_declName_144_);
return v_params_143_;
}
else
{
lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_180_; 
lean_inc(v_anchorRefs_x3f_153_);
lean_inc_ref(v_normProcs_152_);
lean_inc_ref(v_norm_151_);
lean_inc_ref(v_symPrios_150_);
lean_inc_ref(v_extraFacts_149_);
lean_inc_ref(v_extraInj_148_);
lean_inc_ref(v_extra_147_);
lean_inc_ref(v_extensions_146_);
lean_inc_ref(v_config_145_);
v_isSharedCheck_180_ = !lean_is_exclusive(v_params_143_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; lean_object* v_unused_182_; lean_object* v_unused_183_; lean_object* v_unused_184_; lean_object* v_unused_185_; lean_object* v_unused_186_; lean_object* v_unused_187_; lean_object* v_unused_188_; lean_object* v_unused_189_; 
v_unused_181_ = lean_ctor_get(v_params_143_, 8);
lean_dec(v_unused_181_);
v_unused_182_ = lean_ctor_get(v_params_143_, 7);
lean_dec(v_unused_182_);
v_unused_183_ = lean_ctor_get(v_params_143_, 6);
lean_dec(v_unused_183_);
v_unused_184_ = lean_ctor_get(v_params_143_, 5);
lean_dec(v_unused_184_);
v_unused_185_ = lean_ctor_get(v_params_143_, 4);
lean_dec(v_unused_185_);
v_unused_186_ = lean_ctor_get(v_params_143_, 3);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_params_143_, 2);
lean_dec(v_unused_187_);
v_unused_188_ = lean_ctor_get(v_params_143_, 1);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_params_143_, 0);
lean_dec(v_unused_189_);
v___x_158_ = v_params_143_;
v_isShared_159_ = v_isSharedCheck_180_;
goto v_resetjp_157_;
}
else
{
lean_dec(v_params_143_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_180_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_v_160_; lean_object* v_casesTypes_161_; lean_object* v_extThms_162_; lean_object* v_funCC_163_; lean_object* v_ematch_164_; lean_object* v_inj_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_179_; 
v_v_160_ = lean_array_fget(v_extensions_146_, v___x_154_);
v_casesTypes_161_ = lean_ctor_get(v_v_160_, 0);
v_extThms_162_ = lean_ctor_get(v_v_160_, 1);
v_funCC_163_ = lean_ctor_get(v_v_160_, 2);
v_ematch_164_ = lean_ctor_get(v_v_160_, 3);
v_inj_165_ = lean_ctor_get(v_v_160_, 4);
v_isSharedCheck_179_ = !lean_is_exclusive(v_v_160_);
if (v_isSharedCheck_179_ == 0)
{
v___x_167_ = v_v_160_;
v_isShared_168_ = v_isSharedCheck_179_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_inj_165_);
lean_inc(v_ematch_164_);
lean_inc(v_funCC_163_);
lean_inc(v_extThms_162_);
lean_inc(v_casesTypes_161_);
lean_dec(v_v_160_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_179_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v_xs_x27_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_169_ = lean_box(0);
v_xs_x27_170_ = lean_array_fset(v_extensions_146_, v___x_154_, v___x_169_);
v___x_171_ = l_Lean_NameSet_insert(v_funCC_163_, v_declName_144_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 2, v___x_171_);
v___x_173_ = v___x_167_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_casesTypes_161_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_extThms_162_);
lean_ctor_set(v_reuseFailAlloc_178_, 2, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_178_, 3, v_ematch_164_);
lean_ctor_set(v_reuseFailAlloc_178_, 4, v_inj_165_);
v___x_173_ = v_reuseFailAlloc_178_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_array_fset(v_xs_x27_170_, v___x_154_, v___x_173_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_174_);
v___x_176_ = v___x_158_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_config_145_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_177_, 2, v_extra_147_);
lean_ctor_set(v_reuseFailAlloc_177_, 3, v_extraInj_148_);
lean_ctor_set(v_reuseFailAlloc_177_, 4, v_extraFacts_149_);
lean_ctor_set(v_reuseFailAlloc_177_, 5, v_symPrios_150_);
lean_ctor_set(v_reuseFailAlloc_177_, 6, v_norm_151_);
lean_ctor_set(v_reuseFailAlloc_177_, 7, v_normProcs_152_);
lean_ctor_set(v_reuseFailAlloc_177_, 8, v_anchorRefs_x3f_153_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(lean_object* v_declName_190_, lean_object* v_as_191_, size_t v_i_192_, size_t v_stop_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_eq(v_i_192_, v_stop_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v_ematch_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_195_ = lean_array_uget_borrowed(v_as_191_, v_i_192_);
v_ematch_196_ = lean_ctor_get(v___x_195_, 3);
lean_inc(v_declName_190_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v_declName_190_);
lean_inc_ref(v_ematch_196_);
v___x_198_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_ematch_196_, v___x_197_);
lean_dec_ref(v___x_197_);
if (v___x_198_ == 0)
{
size_t v___x_199_; size_t v___x_200_; 
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_i_192_, v___x_199_);
v_i_192_ = v___x_200_;
goto _start;
}
else
{
lean_dec(v_declName_190_);
return v___x_198_;
}
}
else
{
uint8_t v___x_202_; 
lean_dec(v_declName_190_);
v___x_202_ = 0;
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0___boxed(lean_object* v_declName_203_, lean_object* v_as_204_, lean_object* v_i_205_, lean_object* v_stop_206_){
_start:
{
size_t v_i_boxed_207_; size_t v_stop_boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_i_boxed_207_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_stop_boxed_208_ = lean_unbox_usize(v_stop_206_);
lean_dec(v_stop_206_);
v_res_209_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(v_declName_203_, v_as_204_, v_i_boxed_207_, v_stop_boxed_208_);
lean_dec_ref(v_as_204_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(lean_object* v_params_211_, lean_object* v_declName_212_){
_start:
{
lean_object* v_extensions_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_extensions_213_ = lean_ctor_get(v_params_211_, 1);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_array_get_size(v_extensions_213_);
v___x_216_ = lean_nat_dec_lt(v___x_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec(v_declName_212_);
return v___x_216_;
}
else
{
if (v___x_216_ == 0)
{
lean_dec(v_declName_212_);
return v___x_216_;
}
else
{
size_t v___x_217_; size_t v___x_218_; uint8_t v___x_219_; 
v___x_217_ = ((size_t)0ULL);
v___x_218_ = lean_usize_of_nat(v___x_215_);
v___x_219_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch_spec__0(v_declName_212_, v_extensions_213_, v___x_217_, v___x_218_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch___boxed(lean_object* v_params_220_, lean_object* v_declName_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_220_, v_declName_221_);
lean_dec_ref(v_params_220_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(lean_object* v_declName_224_, lean_object* v_as_225_, size_t v_i_226_, size_t v_stop_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_eq(v_i_226_, v_stop_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v_inj_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_229_ = lean_array_uget_borrowed(v_as_225_, v_i_226_);
v_inj_230_ = lean_ctor_get(v___x_229_, 4);
lean_inc(v_declName_224_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v_declName_224_);
lean_inc_ref(v_inj_230_);
v___x_232_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_230_, v___x_231_);
lean_dec_ref(v___x_231_);
if (v___x_232_ == 0)
{
size_t v___x_233_; size_t v___x_234_; 
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_add(v_i_226_, v___x_233_);
v_i_226_ = v___x_234_;
goto _start;
}
else
{
lean_dec(v_declName_224_);
return v___x_232_;
}
}
else
{
uint8_t v___x_236_; 
lean_dec(v_declName_224_);
v___x_236_ = 0;
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0___boxed(lean_object* v_declName_237_, lean_object* v_as_238_, lean_object* v_i_239_, lean_object* v_stop_240_){
_start:
{
size_t v_i_boxed_241_; size_t v_stop_boxed_242_; uint8_t v_res_243_; lean_object* v_r_244_; 
v_i_boxed_241_ = lean_unbox_usize(v_i_239_);
lean_dec(v_i_239_);
v_stop_boxed_242_ = lean_unbox_usize(v_stop_240_);
lean_dec(v_stop_240_);
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(v_declName_237_, v_as_238_, v_i_boxed_241_, v_stop_boxed_242_);
lean_dec_ref(v_as_238_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(lean_object* v_params_245_, lean_object* v_declName_246_){
_start:
{
lean_object* v_extensions_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v_extensions_247_ = lean_ctor_get(v_params_245_, 1);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_array_get_size(v_extensions_247_);
v___x_250_ = lean_nat_dec_lt(v___x_248_, v___x_249_);
if (v___x_250_ == 0)
{
lean_dec(v_declName_246_);
return v___x_250_;
}
else
{
if (v___x_250_ == 0)
{
lean_dec(v_declName_246_);
return v___x_250_;
}
else
{
size_t v___x_251_; size_t v___x_252_; uint8_t v___x_253_; 
v___x_251_ = ((size_t)0ULL);
v___x_252_ = lean_usize_of_nat(v___x_249_);
v___x_253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem_spec__0(v_declName_246_, v_extensions_247_, v___x_251_, v___x_252_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem___boxed(lean_object* v_params_254_, lean_object* v_declName_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_params_254_, v_declName_255_);
lean_dec_ref(v_params_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(lean_object* v_params_258_, lean_object* v_declName_259_){
_start:
{
lean_object* v_config_260_; lean_object* v_extensions_261_; lean_object* v_extra_262_; lean_object* v_extraInj_263_; lean_object* v_extraFacts_264_; lean_object* v_symPrios_265_; lean_object* v_norm_266_; lean_object* v_normProcs_267_; lean_object* v_anchorRefs_x3f_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_config_260_ = lean_ctor_get(v_params_258_, 0);
v_extensions_261_ = lean_ctor_get(v_params_258_, 1);
v_extra_262_ = lean_ctor_get(v_params_258_, 2);
v_extraInj_263_ = lean_ctor_get(v_params_258_, 3);
v_extraFacts_264_ = lean_ctor_get(v_params_258_, 4);
v_symPrios_265_ = lean_ctor_get(v_params_258_, 5);
v_norm_266_ = lean_ctor_get(v_params_258_, 6);
v_normProcs_267_ = lean_ctor_get(v_params_258_, 7);
v_anchorRefs_x3f_268_ = lean_ctor_get(v_params_258_, 8);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_array_get_size(v_extensions_261_);
v___x_271_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v_declName_259_);
return v_params_258_;
}
else
{
lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_296_; 
lean_inc(v_anchorRefs_x3f_268_);
lean_inc_ref(v_normProcs_267_);
lean_inc_ref(v_norm_266_);
lean_inc_ref(v_symPrios_265_);
lean_inc_ref(v_extraFacts_264_);
lean_inc_ref(v_extraInj_263_);
lean_inc_ref(v_extra_262_);
lean_inc_ref(v_extensions_261_);
lean_inc_ref(v_config_260_);
v_isSharedCheck_296_ = !lean_is_exclusive(v_params_258_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; lean_object* v_unused_298_; lean_object* v_unused_299_; lean_object* v_unused_300_; lean_object* v_unused_301_; lean_object* v_unused_302_; lean_object* v_unused_303_; lean_object* v_unused_304_; lean_object* v_unused_305_; 
v_unused_297_ = lean_ctor_get(v_params_258_, 8);
lean_dec(v_unused_297_);
v_unused_298_ = lean_ctor_get(v_params_258_, 7);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_params_258_, 6);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_params_258_, 5);
lean_dec(v_unused_300_);
v_unused_301_ = lean_ctor_get(v_params_258_, 4);
lean_dec(v_unused_301_);
v_unused_302_ = lean_ctor_get(v_params_258_, 3);
lean_dec(v_unused_302_);
v_unused_303_ = lean_ctor_get(v_params_258_, 2);
lean_dec(v_unused_303_);
v_unused_304_ = lean_ctor_get(v_params_258_, 1);
lean_dec(v_unused_304_);
v_unused_305_ = lean_ctor_get(v_params_258_, 0);
lean_dec(v_unused_305_);
v___x_273_ = v_params_258_;
v_isShared_274_ = v_isSharedCheck_296_;
goto v_resetjp_272_;
}
else
{
lean_dec(v_params_258_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_296_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_v_275_; lean_object* v_casesTypes_276_; lean_object* v_extThms_277_; lean_object* v_funCC_278_; lean_object* v_ematch_279_; lean_object* v_inj_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_295_; 
v_v_275_ = lean_array_fget(v_extensions_261_, v___x_269_);
v_casesTypes_276_ = lean_ctor_get(v_v_275_, 0);
v_extThms_277_ = lean_ctor_get(v_v_275_, 1);
v_funCC_278_ = lean_ctor_get(v_v_275_, 2);
v_ematch_279_ = lean_ctor_get(v_v_275_, 3);
v_inj_280_ = lean_ctor_get(v_v_275_, 4);
v_isSharedCheck_295_ = !lean_is_exclusive(v_v_275_);
if (v_isSharedCheck_295_ == 0)
{
v___x_282_ = v_v_275_;
v_isShared_283_ = v_isSharedCheck_295_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_inj_280_);
lean_inc(v_ematch_279_);
lean_inc(v_funCC_278_);
lean_inc(v_extThms_277_);
lean_inc(v_casesTypes_276_);
lean_dec(v_v_275_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_295_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v_xs_x27_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_284_ = lean_box(0);
v_xs_x27_285_ = lean_array_fset(v_extensions_261_, v___x_269_, v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_declName_259_);
v___x_287_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_ematch_279_, v___x_286_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 3, v___x_287_);
v___x_289_ = v___x_282_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_casesTypes_276_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_extThms_277_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_funCC_278_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_294_, 4, v_inj_280_);
v___x_289_ = v_reuseFailAlloc_294_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_array_fset(v_xs_x27_285_, v___x_269_, v___x_289_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___x_290_);
v___x_292_ = v___x_273_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_config_260_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_extra_262_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_extraInj_263_);
lean_ctor_set(v_reuseFailAlloc_293_, 4, v_extraFacts_264_);
lean_ctor_set(v_reuseFailAlloc_293_, 5, v_symPrios_265_);
lean_ctor_set(v_reuseFailAlloc_293_, 6, v_norm_266_);
lean_ctor_set(v_reuseFailAlloc_293_, 7, v_normProcs_267_);
lean_ctor_set(v_reuseFailAlloc_293_, 8, v_anchorRefs_x3f_268_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object* v_params_306_, uint8_t v___x_307_, lean_object* v_as_308_, size_t v_i_309_, size_t v_stop_310_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_eq(v_i_309_, v_stop_310_);
if (v___x_311_ == 0)
{
uint8_t v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_312_ = 1;
v___x_313_ = lean_array_uget_borrowed(v_as_308_, v_i_309_);
lean_inc(v___x_313_);
v___x_314_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_306_, v___x_313_);
if (v___x_314_ == 0)
{
return v___x_312_;
}
else
{
if (v___x_307_ == 0)
{
size_t v___x_315_; size_t v___x_316_; 
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_i_309_, v___x_315_);
v_i_309_ = v___x_316_;
goto _start;
}
else
{
return v___x_312_;
}
}
}
else
{
uint8_t v___x_318_; 
v___x_318_ = 0;
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object* v_params_319_, lean_object* v___x_320_, lean_object* v_as_321_, lean_object* v_i_322_, lean_object* v_stop_323_){
_start:
{
uint8_t v___x_2071__boxed_324_; size_t v_i_boxed_325_; size_t v_stop_boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v___x_2071__boxed_324_ = lean_unbox(v___x_320_);
v_i_boxed_325_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_stop_boxed_326_ = lean_unbox_usize(v_stop_323_);
lean_dec(v_stop_323_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_319_, v___x_2071__boxed_324_, v_as_321_, v_i_boxed_325_, v_stop_boxed_326_);
lean_dec_ref(v_as_321_);
lean_dec_ref(v_params_319_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, lean_object* v_b_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; size_t v___x_336_; size_t v___x_337_; 
v___x_334_ = lean_array_uget_borrowed(v_as_329_, v_i_330_);
lean_inc(v___x_334_);
v___x_335_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_b_332_, v___x_334_);
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_330_, v___x_336_);
v_i_330_ = v___x_337_;
v_b_332_ = v___x_335_;
goto _start;
}
else
{
return v_b_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0___boxed(lean_object* v_as_339_, lean_object* v_i_340_, lean_object* v_stop_341_, lean_object* v_b_342_){
_start:
{
size_t v_i_boxed_343_; size_t v_stop_boxed_344_; lean_object* v_res_345_; 
v_i_boxed_343_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_stop_boxed_344_ = lean_unbox_usize(v_stop_341_);
lean_dec(v_stop_341_);
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_as_339_, v_i_boxed_343_, v_stop_boxed_344_, v_b_342_);
lean_dec_ref(v_as_339_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(lean_object* v_params_346_, lean_object* v_declName_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_356_; lean_object* v_env_357_; uint8_t v___x_358_; 
v___x_356_ = lean_st_ref_get(v_a_351_);
v_env_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_env_357_);
lean_dec(v___x_356_);
lean_inc(v_declName_347_);
v___x_358_ = l_Lean_wasOriginallyTheorem(v_env_357_, v_declName_347_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_inc(v_a_351_);
lean_inc_ref(v_a_350_);
lean_inc(v_declName_347_);
v___x_359_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_404_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_404_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_404_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_404_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
if (lean_obj_tag(v_a_360_) == 1)
{
lean_object* v_val_364_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_val_364_ = lean_ctor_get(v_a_360_, 0);
lean_inc(v_val_364_);
lean_dec_ref(v_a_360_);
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = lean_array_get_size(v_val_364_);
v___x_390_ = lean_nat_dec_lt(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
if (v___x_390_ == 0)
{
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
size_t v___x_391_; size_t v___x_392_; uint8_t v___x_393_; 
v___x_391_ = ((size_t)0ULL);
v___x_392_ = lean_usize_of_nat(v___x_389_);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_346_, v___x_358_, v_val_364_, v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_dec_ref(v___x_394_);
goto v___jp_365_;
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_val_364_);
lean_del_object(v___x_362_);
lean_dec_ref(v_params_346_);
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
v___jp_365_:
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_array_get_size(v_val_364_);
v___x_368_ = lean_nat_dec_lt(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_370_; 
lean_dec(v_val_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v_params_346_);
v___x_370_ = v___x_362_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_params_346_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
else
{
uint8_t v___x_372_; 
v___x_372_ = lean_nat_dec_le(v___x_367_, v___x_367_);
if (v___x_372_ == 0)
{
if (v___x_368_ == 0)
{
lean_object* v___x_374_; 
lean_dec(v_val_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v_params_346_);
v___x_374_ = v___x_362_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_params_346_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_376_ = ((size_t)0ULL);
v___x_377_ = lean_usize_of_nat(v___x_367_);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_364_, v___x_376_, v___x_377_, v_params_346_);
lean_dec(v_val_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_378_);
v___x_380_ = v___x_362_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
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
size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_382_ = ((size_t)0ULL);
v___x_383_ = lean_usize_of_nat(v___x_367_);
v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_364_, v___x_382_, v___x_383_, v_params_346_);
lean_dec(v_val_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_384_);
v___x_386_ = v___x_362_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
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
else
{
lean_object* v___x_403_; 
lean_del_object(v___x_362_);
lean_dec(v_a_360_);
lean_dec_ref(v_params_346_);
v___x_403_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
return v___x_403_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_declName_347_);
lean_dec_ref(v_params_346_);
v_a_405_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_359_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_359_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
uint8_t v___x_413_; 
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_inc(v_declName_347_);
v___x_413_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_346_, v_declName_347_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_inc(v_declName_347_);
v___x_414_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_dec_ref(v___x_414_);
goto v___jp_353_;
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec(v_declName_347_);
lean_dec_ref(v_params_346_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
goto v___jp_353_;
}
}
v___jp_353_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_params_346_, v_declName_347_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object* v_params_423_, lean_object* v_declName_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_params_423_, v_declName_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object* v_params_431_, lean_object* v_declName_432_){
_start:
{
lean_object* v_config_433_; lean_object* v_extensions_434_; lean_object* v_extra_435_; lean_object* v_extraInj_436_; lean_object* v_extraFacts_437_; lean_object* v_symPrios_438_; lean_object* v_norm_439_; lean_object* v_normProcs_440_; lean_object* v_anchorRefs_x3f_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_config_433_ = lean_ctor_get(v_params_431_, 0);
v_extensions_434_ = lean_ctor_get(v_params_431_, 1);
v_extra_435_ = lean_ctor_get(v_params_431_, 2);
v_extraInj_436_ = lean_ctor_get(v_params_431_, 3);
v_extraFacts_437_ = lean_ctor_get(v_params_431_, 4);
v_symPrios_438_ = lean_ctor_get(v_params_431_, 5);
v_norm_439_ = lean_ctor_get(v_params_431_, 6);
v_normProcs_440_ = lean_ctor_get(v_params_431_, 7);
v_anchorRefs_x3f_441_ = lean_ctor_get(v_params_431_, 8);
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_array_get_size(v_extensions_434_);
v___x_444_ = lean_nat_dec_lt(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_dec(v_declName_432_);
return v_params_431_;
}
else
{
lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_469_; 
lean_inc(v_anchorRefs_x3f_441_);
lean_inc_ref(v_normProcs_440_);
lean_inc_ref(v_norm_439_);
lean_inc_ref(v_symPrios_438_);
lean_inc_ref(v_extraFacts_437_);
lean_inc_ref(v_extraInj_436_);
lean_inc_ref(v_extra_435_);
lean_inc_ref(v_extensions_434_);
lean_inc_ref(v_config_433_);
v_isSharedCheck_469_ = !lean_is_exclusive(v_params_431_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; lean_object* v_unused_475_; lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_470_ = lean_ctor_get(v_params_431_, 8);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_params_431_, 7);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_params_431_, 6);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_params_431_, 5);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_params_431_, 4);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_params_431_, 3);
lean_dec(v_unused_475_);
v_unused_476_ = lean_ctor_get(v_params_431_, 2);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_params_431_, 1);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_params_431_, 0);
lean_dec(v_unused_478_);
v___x_446_ = v_params_431_;
v_isShared_447_ = v_isSharedCheck_469_;
goto v_resetjp_445_;
}
else
{
lean_dec(v_params_431_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_469_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_v_448_; lean_object* v_casesTypes_449_; lean_object* v_extThms_450_; lean_object* v_funCC_451_; lean_object* v_ematch_452_; lean_object* v_inj_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_468_; 
v_v_448_ = lean_array_fget(v_extensions_434_, v___x_442_);
v_casesTypes_449_ = lean_ctor_get(v_v_448_, 0);
v_extThms_450_ = lean_ctor_get(v_v_448_, 1);
v_funCC_451_ = lean_ctor_get(v_v_448_, 2);
v_ematch_452_ = lean_ctor_get(v_v_448_, 3);
v_inj_453_ = lean_ctor_get(v_v_448_, 4);
v_isSharedCheck_468_ = !lean_is_exclusive(v_v_448_);
if (v_isSharedCheck_468_ == 0)
{
v___x_455_ = v_v_448_;
v_isShared_456_ = v_isSharedCheck_468_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_inj_453_);
lean_inc(v_ematch_452_);
lean_inc(v_funCC_451_);
lean_inc(v_extThms_450_);
lean_inc(v_casesTypes_449_);
lean_dec(v_v_448_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_468_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v_xs_x27_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_457_ = lean_box(0);
v_xs_x27_458_ = lean_array_fset(v_extensions_434_, v___x_442_, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_declName_432_);
v___x_460_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_inj_453_, v___x_459_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 4, v___x_460_);
v___x_462_ = v___x_455_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_casesTypes_449_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_extThms_450_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_funCC_451_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v_ematch_452_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v___x_460_);
v___x_462_ = v_reuseFailAlloc_467_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_array_fset(v_xs_x27_458_, v___x_442_, v___x_462_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v___x_463_);
v___x_465_ = v___x_446_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_config_433_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_extra_435_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_extraInj_436_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_extraFacts_437_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v_symPrios_438_);
lean_ctor_set(v_reuseFailAlloc_466_, 6, v_norm_439_);
lean_ctor_set(v_reuseFailAlloc_466_, 7, v_normProcs_440_);
lean_ctor_set(v_reuseFailAlloc_466_, 8, v_anchorRefs_x3f_441_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(lean_object* v_origin_479_, lean_object* v_as_480_, size_t v_sz_481_, size_t v_i_482_, lean_object* v_b_483_){
_start:
{
lean_object* v_a_485_; uint8_t v___x_489_; 
v___x_489_ = lean_usize_dec_lt(v_i_482_, v_sz_481_);
if (v___x_489_ == 0)
{
return v_b_483_;
}
else
{
lean_object* v_a_490_; lean_object* v_ematch_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_a_490_ = lean_array_uget_borrowed(v_as_480_, v_i_482_);
v_ematch_491_ = lean_ctor_get(v_a_490_, 3);
lean_inc_ref(v_ematch_491_);
v___x_492_ = l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(v_ematch_491_, v_origin_479_);
v___x_493_ = l_List_isEmpty___redArg(v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
v___x_494_ = l_List_appendTR___redArg(v_b_483_, v___x_492_);
v_a_485_ = v___x_494_;
goto v___jp_484_;
}
else
{
lean_dec(v___x_492_);
v_a_485_ = v_b_483_;
goto v___jp_484_;
}
}
v___jp_484_:
{
size_t v___x_486_; size_t v___x_487_; 
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_i_482_, v___x_486_);
v_i_482_ = v___x_487_;
v_b_483_ = v_a_485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0___boxed(lean_object* v_origin_495_, lean_object* v_as_496_, lean_object* v_sz_497_, lean_object* v_i_498_, lean_object* v_b_499_){
_start:
{
size_t v_sz_boxed_500_; size_t v_i_boxed_501_; lean_object* v_res_502_; 
v_sz_boxed_500_ = lean_unbox_usize(v_sz_497_);
lean_dec(v_sz_497_);
v_i_boxed_501_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_495_, v_as_496_, v_sz_boxed_500_, v_i_boxed_501_, v_b_499_);
lean_dec_ref(v_as_496_);
lean_dec_ref(v_origin_495_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(lean_object* v_s_503_, lean_object* v_origin_504_){
_start:
{
lean_object* v_result_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v___x_508_; 
v_result_505_ = lean_box(0);
v_sz_506_ = lean_array_size(v_s_503_);
v___x_507_ = ((size_t)0ULL);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_504_, v_s_503_, v_sz_506_, v___x_507_, v_result_505_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor___boxed(lean_object* v_s_509_, lean_object* v_origin_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_509_, v_origin_510_);
lean_dec_ref(v_origin_510_);
lean_dec_ref(v_s_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(lean_object* v_upperBound_512_, lean_object* v_s_513_, lean_object* v_origin_514_, lean_object* v_a_515_, lean_object* v_b_516_){
_start:
{
lean_object* v_a_518_; uint8_t v___x_522_; 
v___x_522_ = lean_nat_dec_lt(v_a_515_, v_upperBound_512_);
if (v___x_522_ == 0)
{
lean_dec(v_a_515_);
return v_b_516_;
}
else
{
lean_object* v___x_523_; lean_object* v_ematch_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_523_ = lean_array_fget_borrowed(v_s_513_, v_a_515_);
v_ematch_524_ = lean_ctor_get(v___x_523_, 3);
lean_inc_ref(v_ematch_524_);
v___x_525_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_ematch_524_, v_origin_514_);
v___x_526_ = l_List_isEmpty___redArg(v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
v___x_527_ = l_List_appendTR___redArg(v_b_516_, v___x_525_);
v_a_518_ = v___x_527_;
goto v___jp_517_;
}
else
{
lean_dec(v___x_525_);
v_a_518_ = v_b_516_;
goto v___jp_517_;
}
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_add(v_a_515_, v___x_519_);
lean_dec(v_a_515_);
v_a_515_ = v___x_520_;
v_b_516_ = v_a_518_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg___boxed(lean_object* v_upperBound_528_, lean_object* v_s_529_, lean_object* v_origin_530_, lean_object* v_a_531_, lean_object* v_b_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_528_, v_s_529_, v_origin_530_, v_a_531_, v_b_532_);
lean_dec_ref(v_origin_530_);
lean_dec_ref(v_s_529_);
lean_dec(v_upperBound_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find(lean_object* v_s_534_, lean_object* v_origin_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_r_538_; lean_object* v___x_539_; 
v___x_536_ = lean_array_get_size(v_s_534_);
v___x_537_ = lean_unsigned_to_nat(0u);
v_r_538_ = lean_box(0);
v___x_539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v___x_536_, v_s_534_, v_origin_535_, v___x_537_, v_r_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find___boxed(lean_object* v_s_540_, lean_object* v_origin_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Meta_Grind_ExtensionStateArray_find(v_s_540_, v_origin_541_);
lean_dec_ref(v_origin_541_);
lean_dec_ref(v_s_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(lean_object* v_upperBound_543_, lean_object* v_s_544_, lean_object* v_origin_545_, lean_object* v_inst_546_, lean_object* v_R_547_, lean_object* v_a_548_, lean_object* v_b_549_, lean_object* v_c_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_543_, v_s_544_, v_origin_545_, v_a_548_, v_b_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___boxed(lean_object* v_upperBound_552_, lean_object* v_s_553_, lean_object* v_origin_554_, lean_object* v_inst_555_, lean_object* v_R_556_, lean_object* v_a_557_, lean_object* v_b_558_, lean_object* v_c_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(v_upperBound_552_, v_s_553_, v_origin_554_, v_inst_555_, v_R_556_, v_a_557_, v_b_558_, v_c_559_);
lean_dec_ref(v_origin_554_);
lean_dec_ref(v_s_553_);
lean_dec(v_upperBound_552_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(lean_object* v_msgData_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; lean_object* v_env_568_; lean_object* v___x_569_; lean_object* v_mctx_570_; lean_object* v_lctx_571_; lean_object* v_options_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_567_ = lean_st_ref_get(v___y_565_);
v_env_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref(v_env_568_);
lean_dec(v___x_567_);
v___x_569_ = lean_st_ref_get(v___y_563_);
v_mctx_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_mctx_570_);
lean_dec(v___x_569_);
v_lctx_571_ = lean_ctor_get(v___y_562_, 2);
v_options_572_ = lean_ctor_get(v___y_564_, 2);
lean_inc_ref(v_options_572_);
lean_inc_ref(v_lctx_571_);
v___x_573_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_573_, 0, v_env_568_);
lean_ctor_set(v___x_573_, 1, v_mctx_570_);
lean_ctor_set(v___x_573_, 2, v_lctx_571_);
lean_ctor_set(v___x_573_, 3, v_options_572_);
v___x_574_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v_msgData_561_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msgData_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
return v_res_582_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_583_, lean_object* v_opt_584_){
_start:
{
lean_object* v_name_585_; lean_object* v_defValue_586_; lean_object* v_map_587_; lean_object* v___x_588_; 
v_name_585_ = lean_ctor_get(v_opt_584_, 0);
v_defValue_586_ = lean_ctor_get(v_opt_584_, 1);
v_map_587_ = lean_ctor_get(v_opts_583_, 0);
v___x_588_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_587_, v_name_585_);
if (lean_obj_tag(v___x_588_) == 0)
{
uint8_t v___x_589_; 
v___x_589_ = lean_unbox(v_defValue_586_);
return v___x_589_;
}
else
{
lean_object* v_val_590_; 
v_val_590_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_val_590_);
lean_dec_ref(v___x_588_);
if (lean_obj_tag(v_val_590_) == 1)
{
uint8_t v_v_591_; 
v_v_591_ = lean_ctor_get_uint8(v_val_590_, 0);
lean_dec_ref(v_val_590_);
return v_v_591_;
}
else
{
uint8_t v___x_592_; 
lean_dec(v_val_590_);
v___x_592_ = lean_unbox(v_defValue_586_);
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_593_, lean_object* v_opt_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_opts_593_, v_opt_594_);
lean_dec_ref(v_opt_594_);
lean_dec_ref(v_opts_593_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_605_, uint8_t v_suppressElabErrors_606_, lean_object* v_x_607_){
_start:
{
if (lean_obj_tag(v_x_607_) == 1)
{
lean_object* v_pre_608_; 
v_pre_608_ = lean_ctor_get(v_x_607_, 0);
switch(lean_obj_tag(v_pre_608_))
{
case 1:
{
lean_object* v_pre_609_; 
v_pre_609_ = lean_ctor_get(v_pre_608_, 0);
switch(lean_obj_tag(v_pre_609_))
{
case 0:
{
lean_object* v_str_610_; lean_object* v_str_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_str_610_ = lean_ctor_get(v_x_607_, 1);
v_str_611_ = lean_ctor_get(v_pre_608_, 1);
v___x_612_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_613_ = lean_string_dec_eq(v_str_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_615_ = lean_string_dec_eq(v_str_611_, v___x_614_);
if (v___x_615_ == 0)
{
return v___y_605_;
}
else
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_617_ = lean_string_dec_eq(v_str_610_, v___x_616_);
if (v___x_617_ == 0)
{
return v___y_605_;
}
else
{
return v_suppressElabErrors_606_;
}
}
}
else
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_619_ = lean_string_dec_eq(v_str_610_, v___x_618_);
if (v___x_619_ == 0)
{
return v___y_605_;
}
else
{
return v_suppressElabErrors_606_;
}
}
}
case 1:
{
lean_object* v_pre_620_; 
v_pre_620_ = lean_ctor_get(v_pre_609_, 0);
if (lean_obj_tag(v_pre_620_) == 0)
{
lean_object* v_str_621_; lean_object* v_str_622_; lean_object* v_str_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_str_621_ = lean_ctor_get(v_x_607_, 1);
v_str_622_ = lean_ctor_get(v_pre_608_, 1);
v_str_623_ = lean_ctor_get(v_pre_609_, 1);
v___x_624_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_625_ = lean_string_dec_eq(v_str_623_, v___x_624_);
if (v___x_625_ == 0)
{
return v___y_605_;
}
else
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_627_ = lean_string_dec_eq(v_str_622_, v___x_626_);
if (v___x_627_ == 0)
{
return v___y_605_;
}
else
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_629_ = lean_string_dec_eq(v_str_621_, v___x_628_);
if (v___x_629_ == 0)
{
return v___y_605_;
}
else
{
return v_suppressElabErrors_606_;
}
}
}
}
else
{
return v___y_605_;
}
}
default: 
{
return v___y_605_;
}
}
}
case 0:
{
lean_object* v_str_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_str_630_ = lean_ctor_get(v_x_607_, 1);
v___x_631_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_632_ = lean_string_dec_eq(v_str_630_, v___x_631_);
if (v___x_632_ == 0)
{
return v___y_605_;
}
else
{
return v_suppressElabErrors_606_;
}
}
default: 
{
return v___y_605_;
}
}
}
else
{
return v___y_605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_633_, lean_object* v_suppressElabErrors_634_, lean_object* v_x_635_){
_start:
{
uint8_t v___y_4361__boxed_636_; uint8_t v_suppressElabErrors_boxed_637_; uint8_t v_res_638_; lean_object* v_r_639_; 
v___y_4361__boxed_636_ = lean_unbox(v___y_633_);
v_suppressElabErrors_boxed_637_ = lean_unbox(v_suppressElabErrors_634_);
v_res_638_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v___y_4361__boxed_636_, v_suppressElabErrors_boxed_637_, v_x_635_);
lean_dec(v_x_635_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_641_, lean_object* v_msgData_642_, uint8_t v_severity_643_, uint8_t v_isSilent_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v___y_651_; lean_object* v___y_652_; uint8_t v___y_653_; uint8_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_687_; lean_object* v___y_688_; uint8_t v___y_689_; uint8_t v___y_690_; uint8_t v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; uint8_t v___y_716_; uint8_t v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_723_; lean_object* v___y_724_; uint8_t v___y_725_; uint8_t v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; uint8_t v___x_734_; lean_object* v___y_736_; uint8_t v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; uint8_t v___y_741_; uint8_t v___y_742_; uint8_t v___y_744_; uint8_t v___x_759_; 
v___x_734_ = 2;
v___x_759_ = l_Lean_instBEqMessageSeverity_beq(v_severity_643_, v___x_734_);
if (v___x_759_ == 0)
{
v___y_744_ = v___x_759_;
goto v___jp_743_;
}
else
{
uint8_t v___x_760_; 
lean_inc_ref(v_msgData_642_);
v___x_760_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_642_);
v___y_744_ = v___x_760_;
goto v___jp_743_;
}
v___jp_650_:
{
lean_object* v___x_660_; lean_object* v_currNamespace_661_; lean_object* v_openDecls_662_; lean_object* v_env_663_; lean_object* v_nextMacroScope_664_; lean_object* v_ngen_665_; lean_object* v_auxDeclNGen_666_; lean_object* v_traceState_667_; lean_object* v_cache_668_; lean_object* v_messages_669_; lean_object* v_infoState_670_; lean_object* v_snapshotTasks_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_685_; 
v___x_660_ = lean_st_ref_take(v___y_659_);
v_currNamespace_661_ = lean_ctor_get(v___y_658_, 6);
lean_inc(v_currNamespace_661_);
v_openDecls_662_ = lean_ctor_get(v___y_658_, 7);
lean_inc(v_openDecls_662_);
lean_dec_ref(v___y_658_);
v_env_663_ = lean_ctor_get(v___x_660_, 0);
v_nextMacroScope_664_ = lean_ctor_get(v___x_660_, 1);
v_ngen_665_ = lean_ctor_get(v___x_660_, 2);
v_auxDeclNGen_666_ = lean_ctor_get(v___x_660_, 3);
v_traceState_667_ = lean_ctor_get(v___x_660_, 4);
v_cache_668_ = lean_ctor_get(v___x_660_, 5);
v_messages_669_ = lean_ctor_get(v___x_660_, 6);
v_infoState_670_ = lean_ctor_get(v___x_660_, 7);
v_snapshotTasks_671_ = lean_ctor_get(v___x_660_, 8);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_685_ == 0)
{
v___x_673_ = v___x_660_;
v_isShared_674_ = v_isSharedCheck_685_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snapshotTasks_671_);
lean_inc(v_infoState_670_);
lean_inc(v_messages_669_);
lean_inc(v_cache_668_);
lean_inc(v_traceState_667_);
lean_inc(v_auxDeclNGen_666_);
lean_inc(v_ngen_665_);
lean_inc(v_nextMacroScope_664_);
lean_inc(v_env_663_);
lean_dec(v___x_660_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_685_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v_currNamespace_661_);
lean_ctor_set(v___x_675_, 1, v_openDecls_662_);
v___x_676_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___y_651_);
v___x_677_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_677_, 0, v___y_655_);
lean_ctor_set(v___x_677_, 1, v___y_656_);
lean_ctor_set(v___x_677_, 2, v___y_657_);
lean_ctor_set(v___x_677_, 3, v___y_652_);
lean_ctor_set(v___x_677_, 4, v___x_676_);
lean_ctor_set_uint8(v___x_677_, sizeof(void*)*5, v___y_653_);
lean_ctor_set_uint8(v___x_677_, sizeof(void*)*5 + 1, v___y_654_);
lean_ctor_set_uint8(v___x_677_, sizeof(void*)*5 + 2, v_isSilent_644_);
v___x_678_ = l_Lean_MessageLog_add(v___x_677_, v_messages_669_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 6, v___x_678_);
v___x_680_ = v___x_673_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_env_663_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_nextMacroScope_664_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_ngen_665_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_auxDeclNGen_666_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v_traceState_667_);
lean_ctor_set(v_reuseFailAlloc_684_, 5, v_cache_668_);
lean_ctor_set(v_reuseFailAlloc_684_, 6, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_684_, 7, v_infoState_670_);
lean_ctor_set(v_reuseFailAlloc_684_, 8, v_snapshotTasks_671_);
v___x_680_ = v_reuseFailAlloc_684_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = lean_st_ref_set(v___y_659_, v___x_680_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
v___jp_686_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_710_; 
v___x_695_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_642_);
v___x_696_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_695_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_710_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_710_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_710_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_inc_ref(v___y_688_);
v___x_701_ = l_Lean_FileMap_toPosition(v___y_688_, v___y_693_);
lean_dec(v___y_693_);
v___x_702_ = l_Lean_FileMap_toPosition(v___y_688_, v___y_694_);
lean_dec(v___y_694_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_690_ == 0)
{
lean_del_object(v___x_699_);
lean_dec_ref(v___y_687_);
v___y_651_ = v_a_697_;
v___y_652_ = v___x_704_;
v___y_653_ = v___y_689_;
v___y_654_ = v___y_691_;
v___y_655_ = v___y_692_;
v___y_656_ = v___x_701_;
v___y_657_ = v___x_703_;
v___y_658_ = v___y_647_;
v___y_659_ = v___y_648_;
goto v___jp_650_;
}
else
{
uint8_t v___x_705_; 
lean_inc(v_a_697_);
v___x_705_ = l_Lean_MessageData_hasTag(v___y_687_, v_a_697_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_708_; 
lean_dec_ref(v___x_703_);
lean_dec_ref(v___x_701_);
lean_dec(v_a_697_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v___y_647_);
v___x_706_ = lean_box(0);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_706_);
v___x_708_ = v___x_699_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
lean_del_object(v___x_699_);
v___y_651_ = v_a_697_;
v___y_652_ = v___x_704_;
v___y_653_ = v___y_689_;
v___y_654_ = v___y_691_;
v___y_655_ = v___y_692_;
v___y_656_ = v___x_701_;
v___y_657_ = v___x_703_;
v___y_658_ = v___y_647_;
v___y_659_ = v___y_648_;
goto v___jp_650_;
}
}
}
}
v___jp_711_:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Syntax_getTailPos_x3f(v___y_713_, v___y_715_);
lean_dec(v___y_713_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_inc(v___y_719_);
v___y_687_ = v___y_712_;
v___y_688_ = v___y_714_;
v___y_689_ = v___y_715_;
v___y_690_ = v___y_717_;
v___y_691_ = v___y_716_;
v___y_692_ = v___y_718_;
v___y_693_ = v___y_719_;
v___y_694_ = v___y_719_;
goto v___jp_686_;
}
else
{
lean_object* v_val_721_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref(v___x_720_);
v___y_687_ = v___y_712_;
v___y_688_ = v___y_714_;
v___y_689_ = v___y_715_;
v___y_690_ = v___y_717_;
v___y_691_ = v___y_716_;
v___y_692_ = v___y_718_;
v___y_693_ = v___y_719_;
v___y_694_ = v_val_721_;
goto v___jp_686_;
}
}
v___jp_722_:
{
lean_object* v_ref_730_; lean_object* v___x_731_; 
v_ref_730_ = l_Lean_replaceRef(v_ref_641_, v___y_728_);
lean_dec(v___y_728_);
v___x_731_ = l_Lean_Syntax_getPos_x3f(v_ref_730_, v___y_725_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___y_712_ = v___y_723_;
v___y_713_ = v_ref_730_;
v___y_714_ = v___y_724_;
v___y_715_ = v___y_725_;
v___y_716_ = v___y_729_;
v___y_717_ = v___y_726_;
v___y_718_ = v___y_727_;
v___y_719_ = v___x_732_;
goto v___jp_711_;
}
else
{
lean_object* v_val_733_; 
v_val_733_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_val_733_);
lean_dec_ref(v___x_731_);
v___y_712_ = v___y_723_;
v___y_713_ = v_ref_730_;
v___y_714_ = v___y_724_;
v___y_715_ = v___y_725_;
v___y_716_ = v___y_729_;
v___y_717_ = v___y_726_;
v___y_718_ = v___y_727_;
v___y_719_ = v_val_733_;
goto v___jp_711_;
}
}
v___jp_735_:
{
if (v___y_742_ == 0)
{
v___y_723_ = v___y_740_;
v___y_724_ = v___y_736_;
v___y_725_ = v___y_741_;
v___y_726_ = v___y_737_;
v___y_727_ = v___y_739_;
v___y_728_ = v___y_738_;
v___y_729_ = v_severity_643_;
goto v___jp_722_;
}
else
{
v___y_723_ = v___y_740_;
v___y_724_ = v___y_736_;
v___y_725_ = v___y_741_;
v___y_726_ = v___y_737_;
v___y_727_ = v___y_739_;
v___y_728_ = v___y_738_;
v___y_729_ = v___x_734_;
goto v___jp_722_;
}
}
v___jp_743_:
{
if (v___y_744_ == 0)
{
lean_object* v_fileName_745_; lean_object* v_fileMap_746_; lean_object* v_options_747_; lean_object* v_ref_748_; uint8_t v_suppressElabErrors_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___f_752_; uint8_t v___x_753_; uint8_t v___x_754_; 
v_fileName_745_ = lean_ctor_get(v___y_647_, 0);
v_fileMap_746_ = lean_ctor_get(v___y_647_, 1);
v_options_747_ = lean_ctor_get(v___y_647_, 2);
v_ref_748_ = lean_ctor_get(v___y_647_, 5);
v_suppressElabErrors_749_ = lean_ctor_get_uint8(v___y_647_, sizeof(void*)*14 + 1);
v___x_750_ = lean_box(v___y_744_);
v___x_751_ = lean_box(v_suppressElabErrors_749_);
v___f_752_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_752_, 0, v___x_750_);
lean_closure_set(v___f_752_, 1, v___x_751_);
v___x_753_ = 1;
v___x_754_ = l_Lean_instBEqMessageSeverity_beq(v_severity_643_, v___x_753_);
if (v___x_754_ == 0)
{
lean_inc_ref(v_fileName_745_);
lean_inc(v_ref_748_);
lean_inc_ref(v_fileMap_746_);
v___y_736_ = v_fileMap_746_;
v___y_737_ = v_suppressElabErrors_749_;
v___y_738_ = v_ref_748_;
v___y_739_ = v_fileName_745_;
v___y_740_ = v___f_752_;
v___y_741_ = v___y_744_;
v___y_742_ = v___x_754_;
goto v___jp_735_;
}
else
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = l_Lean_warningAsError;
v___x_756_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_747_, v___x_755_);
lean_inc_ref(v_fileName_745_);
lean_inc(v_ref_748_);
lean_inc_ref(v_fileMap_746_);
v___y_736_ = v_fileMap_746_;
v___y_737_ = v_suppressElabErrors_749_;
v___y_738_ = v_ref_748_;
v___y_739_ = v_fileName_745_;
v___y_740_ = v___f_752_;
v___y_741_ = v___y_744_;
v___y_742_ = v___x_756_;
goto v___jp_735_;
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec_ref(v___y_647_);
lean_dec_ref(v_msgData_642_);
v___x_757_ = lean_box(0);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_761_, lean_object* v_msgData_762_, lean_object* v_severity_763_, lean_object* v_isSilent_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v_severity_boxed_770_; uint8_t v_isSilent_boxed_771_; lean_object* v_res_772_; 
v_severity_boxed_770_ = lean_unbox(v_severity_763_);
v_isSilent_boxed_771_ = lean_unbox(v_isSilent_764_);
v_res_772_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_761_, v_msgData_762_, v_severity_boxed_770_, v_isSilent_boxed_771_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v_ref_761_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_773_, uint8_t v_severity_774_, uint8_t v_isSilent_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_ref_781_; lean_object* v___x_782_; 
v_ref_781_ = lean_ctor_get(v___y_778_, 5);
lean_inc(v_ref_781_);
v___x_782_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_781_, v_msgData_773_, v_severity_774_, v_isSilent_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v_ref_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_783_, lean_object* v_severity_784_, lean_object* v_isSilent_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
uint8_t v_severity_boxed_791_; uint8_t v_isSilent_boxed_792_; lean_object* v_res_793_; 
v_severity_boxed_791_ = lean_unbox(v_severity_784_);
v_isSilent_boxed_792_ = lean_unbox(v_isSilent_785_);
v_res_793_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_783_, v_severity_boxed_791_, v_isSilent_boxed_792_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
uint8_t v___x_800_; uint8_t v___x_801_; lean_object* v___x_802_; 
v___x_800_ = 1;
v___x_801_ = 0;
v___x_802_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_794_, v___x_800_, v___x_801_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_809_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
if (lean_obj_tag(v_a_813_) == 0)
{
lean_object* v___x_815_; 
v___x_815_ = l_List_reverse___redArg(v_a_814_);
return v___x_815_;
}
else
{
lean_object* v_head_816_; lean_object* v_tail_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_830_; 
v_head_816_ = lean_ctor_get(v_a_813_, 0);
v_tail_817_ = lean_ctor_get(v_a_813_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_a_813_);
if (v_isSharedCheck_830_ == 0)
{
v___x_819_ = v_a_813_;
v_isShared_820_ = v_isSharedCheck_830_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_tail_817_);
lean_inc(v_head_816_);
lean_dec(v_a_813_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_830_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
uint8_t v_minIndexable_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v_minIndexable_821_ = 0;
v___x_822_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_823_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_816_, v_minIndexable_821_);
lean_dec(v_head_816_);
v___x_824_ = l_Lean_stringToMessageData(v___x_823_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_822_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 1, v_a_814_);
lean_ctor_set(v___x_819_, 0, v___x_825_);
v___x_827_ = v___x_819_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_a_814_);
v___x_827_ = v_reuseFailAlloc_829_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
v_a_813_ = v_tail_817_;
v_a_814_ = v___x_827_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
if (lean_obj_tag(v_a_831_) == 0)
{
lean_object* v___x_833_; 
v___x_833_ = l_List_reverse___redArg(v_a_832_);
return v___x_833_;
}
else
{
lean_object* v_head_834_; lean_object* v_tail_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_843_; 
v_head_834_ = lean_ctor_get(v_a_831_, 0);
v_tail_835_ = lean_ctor_get(v_a_831_, 1);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_831_);
if (v_isSharedCheck_843_ == 0)
{
v___x_837_ = v_a_831_;
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_tail_835_);
lean_inc(v_head_834_);
lean_dec(v_a_831_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v_a_832_);
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_head_834_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_a_832_);
v___x_840_ = v_reuseFailAlloc_842_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
v_a_831_ = v_tail_835_;
v_a_832_ = v___x_840_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_846_ = l_Lean_stringToMessageData(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_853_, lean_object* v_declName_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_kinds_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v_ks_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_inc(v_declName_854_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_declName_854_);
v___x_886_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_853_, v___x_885_);
lean_dec_ref(v___x_885_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec_ref(v_a_857_);
lean_dec(v_declName_854_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
else
{
lean_object* v_head_889_; lean_object* v_tail_890_; uint8_t v_minIndexable_891_; uint8_t v_gen_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; 
v_head_889_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_head_889_);
v_tail_890_ = lean_ctor_get(v___x_886_, 1);
lean_inc(v_tail_890_);
v_minIndexable_891_ = 0;
if (lean_obj_tag(v_tail_890_) == 0)
{
lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; lean_object* v_unused_914_; 
v_unused_913_ = lean_ctor_get(v___x_886_, 1);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v___x_886_, 0);
lean_dec(v_unused_914_);
v___x_904_ = v___x_886_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_dec(v___x_886_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_906_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_907_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_889_, v_minIndexable_891_);
lean_dec(v_head_889_);
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
if (v_isShared_905_ == 0)
{
lean_ctor_set_tag(v___x_904_, 7);
lean_ctor_set(v___x_904_, 1, v___x_908_);
lean_ctor_set(v___x_904_, 0, v___x_906_);
v___x_910_ = v___x_904_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
v_kinds_861_ = v___x_910_;
v___y_862_ = v_a_855_;
v___y_863_ = v_a_856_;
v___y_864_ = v_a_857_;
v___y_865_ = v_a_858_;
goto v___jp_860_;
}
}
}
else
{
lean_object* v_head_915_; 
v_head_915_ = lean_ctor_get(v_tail_890_, 0);
switch(lean_obj_tag(v_head_915_))
{
case 1:
{
lean_object* v_tail_916_; 
v_tail_916_ = lean_ctor_get(v_tail_890_, 1);
lean_inc(v_tail_916_);
lean_dec_ref(v_tail_890_);
if (lean_obj_tag(v_tail_916_) == 0)
{
if (lean_obj_tag(v_head_889_) == 0)
{
uint8_t v_gen_917_; 
lean_dec_ref(v___x_886_);
v_gen_917_ = lean_ctor_get_uint8(v_head_889_, 0);
lean_dec_ref(v_head_889_);
v_gen_893_ = v_gen_917_;
v___y_894_ = v_a_855_;
v___y_895_ = v_a_856_;
v___y_896_ = v_a_857_;
v___y_897_ = v_a_858_;
goto v___jp_892_;
}
else
{
lean_dec(v_head_889_);
v_ks_876_ = v___x_886_;
v___y_877_ = v_a_855_;
v___y_878_ = v_a_856_;
v___y_879_ = v_a_857_;
v___y_880_ = v_a_858_;
goto v___jp_875_;
}
}
else
{
lean_dec(v_tail_916_);
lean_dec(v_head_889_);
v_ks_876_ = v___x_886_;
v___y_877_ = v_a_855_;
v___y_878_ = v_a_856_;
v___y_879_ = v_a_857_;
v___y_880_ = v_a_858_;
goto v___jp_875_;
}
}
case 0:
{
lean_object* v_tail_918_; 
v_tail_918_ = lean_ctor_get(v_tail_890_, 1);
lean_inc(v_tail_918_);
lean_dec_ref(v_tail_890_);
if (lean_obj_tag(v_tail_918_) == 0)
{
if (lean_obj_tag(v_head_889_) == 1)
{
uint8_t v_gen_919_; 
lean_dec_ref(v___x_886_);
v_gen_919_ = lean_ctor_get_uint8(v_head_889_, 0);
lean_dec_ref(v_head_889_);
v_gen_893_ = v_gen_919_;
v___y_894_ = v_a_855_;
v___y_895_ = v_a_856_;
v___y_896_ = v_a_857_;
v___y_897_ = v_a_858_;
goto v___jp_892_;
}
else
{
lean_dec(v_head_889_);
v_ks_876_ = v___x_886_;
v___y_877_ = v_a_855_;
v___y_878_ = v_a_856_;
v___y_879_ = v_a_857_;
v___y_880_ = v_a_858_;
goto v___jp_875_;
}
}
else
{
lean_dec(v_tail_918_);
lean_dec(v_head_889_);
v_ks_876_ = v___x_886_;
v___y_877_ = v_a_855_;
v___y_878_ = v_a_856_;
v___y_879_ = v_a_857_;
v___y_880_ = v_a_858_;
goto v___jp_875_;
}
}
default: 
{
lean_dec_ref(v_tail_890_);
lean_dec(v_head_889_);
v_ks_876_ = v___x_886_;
v___y_877_ = v_a_855_;
v___y_878_ = v_a_856_;
v___y_879_ = v_a_857_;
v___y_880_ = v_a_858_;
goto v___jp_875_;
}
}
}
v___jp_892_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_898_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_899_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_899_, 0, v_gen_893_);
v___x_900_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_899_, v_minIndexable_891_);
lean_dec_ref(v___x_899_);
v___x_901_ = l_Lean_stringToMessageData(v___x_900_);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_898_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v_kinds_861_ = v___x_902_;
v___y_862_ = v___y_894_;
v___y_863_ = v___y_895_;
v___y_864_ = v___y_896_;
v___y_865_ = v___y_897_;
goto v___jp_860_;
}
}
v___jp_860_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_866_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_867_ = l_Lean_MessageData_ofName(v_declName_854_);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v_kinds_861_);
v___x_872_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_873_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
return v___x_874_;
}
v___jp_875_:
{
lean_object* v___x_881_; lean_object* v_ks_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_881_ = lean_box(0);
v_ks_882_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_876_, v___x_881_);
v___x_883_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_882_, v___x_881_);
v___x_884_ = l_Lean_MessageData_ofList(v___x_883_);
v_kinds_861_ = v___x_884_;
v___y_862_ = v___y_877_;
v___y_863_ = v___y_878_;
v___y_864_ = v___y_879_;
v___y_865_ = v___y_880_;
goto v___jp_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_920_, lean_object* v_declName_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_920_, v_declName_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec_ref(v_s_920_);
return v_res_927_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_928_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
lean_ctor_set(v___x_933_, 2, v___x_932_);
lean_ctor_set(v___x_933_, 3, v___x_931_);
lean_ctor_set(v___x_933_, 4, v___x_931_);
lean_ctor_set(v___x_933_, 5, v___x_931_);
lean_ctor_set(v___x_933_, 6, v___x_931_);
lean_ctor_set(v___x_933_, 7, v___x_931_);
lean_ctor_set(v___x_933_, 8, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_unsigned_to_nat(32u);
v___x_935_ = lean_mk_empty_array_with_capacity(v___x_934_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_937_ = ((size_t)5ULL);
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = lean_unsigned_to_nat(32u);
v___x_940_ = lean_mk_empty_array_with_capacity(v___x_939_);
v___x_941_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_942_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
lean_ctor_set(v___x_942_, 2, v___x_938_);
lean_ctor_set(v___x_942_, 3, v___x_938_);
lean_ctor_set_usize(v___x_942_, 4, v___x_937_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_943_ = lean_box(1);
v___x_944_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_945_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
lean_ctor_set(v___x_946_, 2, v___x_943_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v___x_951_; lean_object* v_env_952_; lean_object* v_options_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_951_ = lean_st_ref_get(v___y_949_);
v_env_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc_ref(v_env_952_);
lean_dec(v___x_951_);
v_options_953_ = lean_ctor_get(v___y_948_, 2);
v___x_954_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_955_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_953_);
v___x_956_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_956_, 0, v_env_952_);
lean_ctor_set(v___x_956_, 1, v___x_954_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
lean_ctor_set(v___x_956_, 3, v_options_953_);
v___x_957_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_msgData_947_);
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* v_msgData_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_ref_968_; lean_object* v___x_969_; lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
v_ref_968_ = lean_ctor_get(v___y_965_, 5);
v___x_969_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msg_964_, v___y_965_, v___y_966_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_978_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
lean_inc(v_ref_968_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_ref_968_);
lean_ctor_set(v___x_974_, 1, v_a_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 1);
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
return v_res_983_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* v_s_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v_env_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1001_ = lean_st_ref_get(v_a_999_);
v_env_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc_ref(v_env_1002_);
lean_dec(v___x_1001_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
v___x_1004_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(v_s_997_);
v___x_1005_ = l_Lean_Parser_runParserCategory(v_env_1002_, v___x_1003_, v_s_997_, v___x_1004_);
if (lean_obj_tag(v___x_1005_) == 1)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
lean_dec_ref(v_s_997_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref(v___x_1005_);
v___x_1007_ = l_Lean_Meta_Grind_getAttrKindCore(v_a_1006_, v_a_998_, v_a_999_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec_ref(v___x_1005_);
v___x_1008_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
v___x_1009_ = l_Lean_stringToMessageData(v_s_997_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1010_, v_a_998_, v_a_999_);
lean_dec_ref(v_a_998_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* v_s_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* v_00_u03b1_1017_, lean_object* v_msg_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_1018_, v___y_1019_, v___y_1020_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* v_00_u03b1_1023_, lean_object* v_msg_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(v_00_u03b1_1023_, v_msg_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* v_msg_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_ref_1035_; lean_object* v___x_1036_; lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1045_; 
v_ref_1035_ = lean_ctor_get(v___y_1032_, 5);
v___x_1036_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_inc(v_ref_1035_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_ref_1035_);
lean_ctor_set(v___x_1041_, 1, v_a_1037_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 1);
lean_ctor_set(v___x_1039_, 0, v___x_1041_);
v___x_1043_ = v___x_1039_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* v_msg_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1052_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
v___x_1055_ = l_Lean_stringToMessageData(v___x_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t v_minIndexable_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
if (v_minIndexable_1056_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
v___x_1065_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1064_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* v_minIndexable_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
uint8_t v_minIndexable_boxed_1072_; lean_object* v_res_1073_; 
v_minIndexable_boxed_1072_ = lean_unbox(v_minIndexable_1066_);
v_res_1073_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_boxed_1072_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* v_00_u03b1_1074_, lean_object* v_msg_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* v_00_u03b1_1082_, lean_object* v_msg_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(v_00_u03b1_1082_, v_msg_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
return v_res_1089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1111_, lean_object* v_declHint_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v_env_1116_; uint8_t v___x_1117_; 
v___x_1115_ = lean_st_ref_get(v___y_1113_);
v_env_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_env_1116_);
lean_dec(v___x_1115_);
v___x_1117_ = l_Lean_Name_isAnonymous(v_declHint_1112_);
if (v___x_1117_ == 0)
{
uint8_t v_isExporting_1118_; 
v_isExporting_1118_ = lean_ctor_get_uint8(v_env_1116_, sizeof(void*)*8);
if (v_isExporting_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec_ref(v_env_1116_);
lean_dec(v_declHint_1112_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_msg_1111_);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
lean_inc_ref(v_env_1116_);
v___x_1120_ = l_Lean_Environment_setExporting(v_env_1116_, v___x_1117_);
lean_inc(v_declHint_1112_);
lean_inc_ref(v___x_1120_);
v___x_1121_ = l_Lean_Environment_contains(v___x_1120_, v_declHint_1112_, v_isExporting_1118_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v___x_1120_);
lean_dec_ref(v_env_1116_);
lean_dec(v_declHint_1112_);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v_msg_1111_);
return v___x_1122_;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_c_1128_; lean_object* v___x_1129_; 
v___x_1123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1124_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1125_ = l_Lean_Options_empty;
v___x_1126_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1120_);
lean_ctor_set(v___x_1126_, 1, v___x_1123_);
lean_ctor_set(v___x_1126_, 2, v___x_1124_);
lean_ctor_set(v___x_1126_, 3, v___x_1125_);
lean_inc(v_declHint_1112_);
v___x_1127_ = l_Lean_MessageData_ofConstName(v_declHint_1112_, v___x_1117_);
v_c_1128_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1128_, 0, v___x_1126_);
lean_ctor_set(v_c_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1116_, v_declHint_1112_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec_ref(v_env_1116_);
lean_dec(v_declHint_1112_);
v___x_1130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v_c_1128_);
v___x_1132_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = l_Lean_MessageData_note(v___x_1133_);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_msg_1111_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
else
{
lean_object* v_val_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1172_; 
v_val_1137_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1139_ = v___x_1129_;
v_isShared_1140_ = v_isSharedCheck_1172_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_val_1137_);
lean_dec(v___x_1129_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1172_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_mod_1144_; uint8_t v___x_1145_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = l_Lean_Environment_header(v_env_1116_);
lean_dec_ref(v_env_1116_);
v___x_1143_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1142_);
v_mod_1144_ = lean_array_get(v___x_1141_, v___x_1143_, v_val_1137_);
lean_dec(v_val_1137_);
lean_dec_ref(v___x_1143_);
v___x_1145_ = l_Lean_isPrivateName(v_declHint_1112_);
lean_dec(v_declHint_1112_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_c_1128_);
v___x_1148_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_MessageData_ofName(v_mod_1144_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_MessageData_note(v___x_1153_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v_msg_1111_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1155_);
v___x_1157_ = v___x_1139_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1159_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v_c_1128_);
v___x_1161_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = l_Lean_MessageData_ofName(v_mod_1144_);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Lean_MessageData_note(v___x_1166_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_msg_1111_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1168_);
v___x_1170_ = v___x_1139_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1173_; 
lean_dec_ref(v_env_1116_);
lean_dec(v_declHint_1112_);
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_msg_1111_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1174_, lean_object* v_declHint_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1174_, v_declHint_1175_, v___y_1176_);
lean_dec(v___y_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1179_, lean_object* v_declHint_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1196_; 
v___x_1186_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1179_, v_declHint_1180_, v___y_1184_);
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1196_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1196_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1191_ = l_Lean_unknownIdentifierMessageTag;
v___x_1192_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v_a_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1192_);
v___x_1194_ = v___x_1189_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1197_, lean_object* v_declHint_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1197_, v_declHint_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1205_, lean_object* v_msg_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_fileName_1212_; lean_object* v_fileMap_1213_; lean_object* v_options_1214_; lean_object* v_currRecDepth_1215_; lean_object* v_maxRecDepth_1216_; lean_object* v_ref_1217_; lean_object* v_currNamespace_1218_; lean_object* v_openDecls_1219_; lean_object* v_initHeartbeats_1220_; lean_object* v_maxHeartbeats_1221_; lean_object* v_quotContext_1222_; lean_object* v_currMacroScope_1223_; uint8_t v_diag_1224_; lean_object* v_cancelTk_x3f_1225_; uint8_t v_suppressElabErrors_1226_; lean_object* v_inheritedTraceOptions_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1236_; 
v_fileName_1212_ = lean_ctor_get(v___y_1209_, 0);
v_fileMap_1213_ = lean_ctor_get(v___y_1209_, 1);
v_options_1214_ = lean_ctor_get(v___y_1209_, 2);
v_currRecDepth_1215_ = lean_ctor_get(v___y_1209_, 3);
v_maxRecDepth_1216_ = lean_ctor_get(v___y_1209_, 4);
v_ref_1217_ = lean_ctor_get(v___y_1209_, 5);
v_currNamespace_1218_ = lean_ctor_get(v___y_1209_, 6);
v_openDecls_1219_ = lean_ctor_get(v___y_1209_, 7);
v_initHeartbeats_1220_ = lean_ctor_get(v___y_1209_, 8);
v_maxHeartbeats_1221_ = lean_ctor_get(v___y_1209_, 9);
v_quotContext_1222_ = lean_ctor_get(v___y_1209_, 10);
v_currMacroScope_1223_ = lean_ctor_get(v___y_1209_, 11);
v_diag_1224_ = lean_ctor_get_uint8(v___y_1209_, sizeof(void*)*14);
v_cancelTk_x3f_1225_ = lean_ctor_get(v___y_1209_, 12);
v_suppressElabErrors_1226_ = lean_ctor_get_uint8(v___y_1209_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1227_ = lean_ctor_get(v___y_1209_, 13);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___y_1209_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1229_ = v___y_1209_;
v_isShared_1230_ = v_isSharedCheck_1236_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_inheritedTraceOptions_1227_);
lean_inc(v_cancelTk_x3f_1225_);
lean_inc(v_currMacroScope_1223_);
lean_inc(v_quotContext_1222_);
lean_inc(v_maxHeartbeats_1221_);
lean_inc(v_initHeartbeats_1220_);
lean_inc(v_openDecls_1219_);
lean_inc(v_currNamespace_1218_);
lean_inc(v_ref_1217_);
lean_inc(v_maxRecDepth_1216_);
lean_inc(v_currRecDepth_1215_);
lean_inc(v_options_1214_);
lean_inc(v_fileMap_1213_);
lean_inc(v_fileName_1212_);
lean_dec(v___y_1209_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1236_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v_ref_1231_; lean_object* v___x_1233_; 
v_ref_1231_ = l_Lean_replaceRef(v_ref_1205_, v_ref_1217_);
lean_dec(v_ref_1217_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 5, v_ref_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_fileName_1212_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_fileMap_1213_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_options_1214_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_currRecDepth_1215_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_maxRecDepth_1216_);
lean_ctor_set(v_reuseFailAlloc_1235_, 5, v_ref_1231_);
lean_ctor_set(v_reuseFailAlloc_1235_, 6, v_currNamespace_1218_);
lean_ctor_set(v_reuseFailAlloc_1235_, 7, v_openDecls_1219_);
lean_ctor_set(v_reuseFailAlloc_1235_, 8, v_initHeartbeats_1220_);
lean_ctor_set(v_reuseFailAlloc_1235_, 9, v_maxHeartbeats_1221_);
lean_ctor_set(v_reuseFailAlloc_1235_, 10, v_quotContext_1222_);
lean_ctor_set(v_reuseFailAlloc_1235_, 11, v_currMacroScope_1223_);
lean_ctor_set(v_reuseFailAlloc_1235_, 12, v_cancelTk_x3f_1225_);
lean_ctor_set(v_reuseFailAlloc_1235_, 13, v_inheritedTraceOptions_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1235_, sizeof(void*)*14, v_diag_1224_);
lean_ctor_set_uint8(v_reuseFailAlloc_1235_, sizeof(void*)*14 + 1, v_suppressElabErrors_1226_);
v___x_1233_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1206_, v___y_1207_, v___y_1208_, v___x_1233_, v___y_1210_);
lean_dec_ref(v___x_1233_);
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1237_, lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1237_, v_msg_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v_ref_1237_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1245_, lean_object* v_msg_1246_, lean_object* v_declHint_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; lean_object* v_a_1254_; lean_object* v___x_1255_; 
v___x_1253_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1246_, v_declHint_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1245_, v_a_1254_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1256_, lean_object* v_msg_1257_, lean_object* v_declHint_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1256_, v_msg_1257_, v_declHint_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v_ref_1256_);
return v_res_1264_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1268_, lean_object* v_constName_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1275_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1276_ = 0;
lean_inc(v_constName_1269_);
v___x_1277_ = l_Lean_MessageData_ofConstName(v_constName_1269_, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1275_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1268_, v___x_1280_, v_constName_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1282_, lean_object* v_constName_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1282_, v_constName_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v_ref_1282_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_ref_1296_; lean_object* v___x_1297_; 
v_ref_1296_ = lean_ctor_get(v___y_1293_, 5);
lean_inc(v_ref_1296_);
v___x_1297_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1296_, v_constName_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v_ref_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1305_, uint8_t v_skipRealize_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v_env_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_st_ref_get(v___y_1310_);
v_env_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_env_1313_);
lean_dec(v___x_1312_);
lean_inc(v_constName_1305_);
v___x_1314_ = l_Lean_Environment_findAsync_x3f(v_env_1313_, v_constName_1305_, v_skipRealize_1306_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1305_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1315_;
}
else
{
lean_object* v_val_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v___y_1309_);
lean_dec(v_constName_1305_);
v_val_1316_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1314_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_val_1316_);
lean_dec(v___x_1314_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 0);
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_val_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1324_, lean_object* v_skipRealize_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_skipRealize_boxed_1331_; lean_object* v_res_1332_; 
v_skipRealize_boxed_1331_ = lean_unbox(v_skipRealize_1325_);
v_res_1332_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1324_, v_skipRealize_boxed_1331_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; lean_object* v_env_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1336_ = lean_st_ref_get(v___y_1334_);
v_env_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc_ref(v_env_1337_);
lean_dec(v___x_1336_);
v___x_1338_ = lean_get_reducibility_status(v_env_1337_, v_declName_1333_);
v___x_1339_ = lean_box(v___x_1338_);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1341_, v___y_1342_);
lean_dec(v___y_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1367_; 
v___x_1351_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1345_, v___y_1349_);
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1367_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1367_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
uint8_t v___x_1356_; 
v___x_1356_ = lean_unbox(v_a_1352_);
lean_dec(v_a_1352_);
if (v___x_1356_ == 0)
{
uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1357_ = 1;
v___x_1358_ = lean_box(v___x_1357_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1358_);
v___x_1360_ = v___x_1354_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1362_ = 0;
v___x_1363_ = lean_box(v___x_1362_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1363_);
v___x_1365_ = v___x_1354_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1374_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1377_ = l_Lean_stringToMessageData(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
return v___x_1380_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1386_ = l_Lean_stringToMessageData(v___x_1385_);
return v___x_1386_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1389_ = l_Lean_stringToMessageData(v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1390_, lean_object* v_id_1391_, lean_object* v_declName_1392_, lean_object* v_kind_1393_, uint8_t v_minIndexable_1394_, uint8_t v_suggest_1395_, uint8_t v_warn_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v___y_1403_; lean_object* v_thm_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; uint8_t v___x_1458_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___x_1655_; 
v___x_1458_ = 0;
lean_inc_ref(v_a_1399_);
lean_inc(v_declName_1392_);
v___x_1655_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1392_, v___x_1458_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; uint8_t v_kind_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v___x_1655_);
v_kind_1657_ = lean_ctor_get_uint8(v_a_1656_, sizeof(void*)*3);
lean_dec(v_a_1656_);
switch(v_kind_1657_)
{
case 1:
{
v___y_1586_ = v_a_1397_;
v___y_1587_ = v_a_1398_;
v___y_1588_ = v_a_1399_;
v___y_1589_ = v_a_1400_;
goto v___jp_1585_;
}
case 2:
{
v___y_1586_ = v_a_1397_;
v___y_1587_ = v_a_1398_;
v___y_1588_ = v_a_1399_;
v___y_1589_ = v_a_1400_;
goto v___jp_1585_;
}
case 6:
{
v___y_1586_ = v_a_1397_;
v___y_1587_ = v_a_1398_;
v___y_1588_ = v_a_1399_;
v___y_1589_ = v_a_1400_;
goto v___jp_1585_;
}
case 0:
{
lean_object* v___x_1658_; 
lean_dec(v_id_1391_);
lean_inc(v_declName_1392_);
v___x_1658_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1392_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; uint8_t v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref(v___x_1658_);
v___x_1660_ = lean_unbox(v_a_1659_);
lean_dec(v_a_1659_);
if (v___x_1660_ == 0)
{
v___y_1516_ = v_a_1397_;
v___y_1517_ = v_a_1398_;
v___y_1518_ = v_a_1399_;
v___y_1519_ = v_a_1400_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_kind_1393_);
lean_dec_ref(v_params_1390_);
v___x_1661_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1662_ = l_Lean_MessageData_ofConstName(v_declName_1392_, v___x_1458_);
v___x_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1663_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1665_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_kind_1393_);
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1675_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1658_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1658_);
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
default: 
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_kind_1393_);
lean_dec(v_id_1391_);
lean_dec_ref(v_params_1390_);
v___x_1683_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1684_ = l_Lean_MessageData_ofConstName(v_declName_1392_, v___x_1458_);
v___x_1685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1687_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
return v___x_1688_;
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_kind_1393_);
lean_dec(v_declName_1392_);
lean_dec(v_id_1391_);
lean_dec_ref(v_params_1390_);
v_a_1689_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1655_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1655_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
v___jp_1402_:
{
lean_object* v_config_1404_; lean_object* v_extensions_1405_; lean_object* v_extra_1406_; lean_object* v_extraInj_1407_; lean_object* v_extraFacts_1408_; lean_object* v_symPrios_1409_; lean_object* v_norm_1410_; lean_object* v_normProcs_1411_; lean_object* v_anchorRefs_x3f_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1421_; 
v_config_1404_ = lean_ctor_get(v_params_1390_, 0);
v_extensions_1405_ = lean_ctor_get(v_params_1390_, 1);
v_extra_1406_ = lean_ctor_get(v_params_1390_, 2);
v_extraInj_1407_ = lean_ctor_get(v_params_1390_, 3);
v_extraFacts_1408_ = lean_ctor_get(v_params_1390_, 4);
v_symPrios_1409_ = lean_ctor_get(v_params_1390_, 5);
v_norm_1410_ = lean_ctor_get(v_params_1390_, 6);
v_normProcs_1411_ = lean_ctor_get(v_params_1390_, 7);
v_anchorRefs_x3f_1412_ = lean_ctor_get(v_params_1390_, 8);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_params_1390_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1414_ = v_params_1390_;
v_isShared_1415_ = v_isSharedCheck_1421_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_anchorRefs_x3f_1412_);
lean_inc(v_normProcs_1411_);
lean_inc(v_norm_1410_);
lean_inc(v_symPrios_1409_);
lean_inc(v_extraFacts_1408_);
lean_inc(v_extraInj_1407_);
lean_inc(v_extra_1406_);
lean_inc(v_extensions_1405_);
lean_inc(v_config_1404_);
lean_dec(v_params_1390_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1421_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = l_Lean_PersistentArray_push___redArg(v_extra_1406_, v___y_1403_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 2, v___x_1416_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_config_1404_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_extensions_1405_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_extraInj_1407_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_extraFacts_1408_);
lean_ctor_set(v_reuseFailAlloc_1420_, 5, v_symPrios_1409_);
lean_ctor_set(v_reuseFailAlloc_1420_, 6, v_norm_1410_);
lean_ctor_set(v_reuseFailAlloc_1420_, 7, v_normProcs_1411_);
lean_ctor_set(v_reuseFailAlloc_1420_, 8, v_anchorRefs_x3f_1412_);
v___x_1418_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
}
v___jp_1422_:
{
if (v_warn_1396_ == 0)
{
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v_declName_1392_);
v___y_1403_ = v_thm_1423_;
goto v___jp_1402_;
}
else
{
lean_object* v_extensions_1428_; lean_object* v_patterns_1429_; lean_object* v_origin_1430_; lean_object* v_cnstrs_1431_; uint8_t v___x_1432_; 
v_extensions_1428_ = lean_ctor_get(v_params_1390_, 1);
v_patterns_1429_ = lean_ctor_get(v_thm_1423_, 3);
v_origin_1430_ = lean_ctor_get(v_thm_1423_, 5);
v_cnstrs_1431_ = lean_ctor_get(v_thm_1423_, 7);
lean_inc(v_cnstrs_1431_);
lean_inc(v_patterns_1429_);
v___x_1432_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1428_, v_origin_1430_, v_patterns_1429_, v_cnstrs_1431_);
if (v___x_1432_ == 0)
{
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v_declName_1392_);
v___y_1403_ = v_thm_1423_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1428_, v_declName_1392_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_dec_ref(v___x_1433_);
v___y_1403_ = v_thm_1423_;
goto v___jp_1402_;
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec_ref(v_thm_1423_);
lean_dec_ref(v_params_1390_);
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
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
}
}
v___jp_1442_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1454_ = l_Lean_PersistentArray_push___redArg(v___y_1450_, v___y_1447_);
v___x_1455_ = l_Lean_PersistentArray_push___redArg(v___x_1454_, v___y_1453_);
v___x_1456_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1456_, 0, v___y_1443_);
lean_ctor_set(v___x_1456_, 1, v___y_1451_);
lean_ctor_set(v___x_1456_, 2, v___x_1455_);
lean_ctor_set(v___x_1456_, 3, v___y_1446_);
lean_ctor_set(v___x_1456_, 4, v___y_1444_);
lean_ctor_set(v___x_1456_, 5, v___y_1449_);
lean_ctor_set(v___x_1456_, 6, v___y_1452_);
lean_ctor_set(v___x_1456_, 7, v___y_1448_);
lean_ctor_set(v___x_1456_, 8, v___y_1445_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
v___jp_1459_:
{
lean_object* v___x_1464_; 
v___x_1464_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1394_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; 
lean_dec_ref(v___x_1464_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v_declName_1392_);
v___x_1465_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1392_, v___x_1458_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1498_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1498_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1498_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
if (lean_obj_tag(v_a_1466_) == 1)
{
lean_object* v_val_1470_; lean_object* v_config_1471_; lean_object* v_extensions_1472_; lean_object* v_extra_1473_; lean_object* v_extraInj_1474_; lean_object* v_extraFacts_1475_; lean_object* v_symPrios_1476_; lean_object* v_norm_1477_; lean_object* v_normProcs_1478_; lean_object* v_anchorRefs_x3f_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_declName_1392_);
v_val_1470_ = lean_ctor_get(v_a_1466_, 0);
lean_inc(v_val_1470_);
lean_dec_ref(v_a_1466_);
v_config_1471_ = lean_ctor_get(v_params_1390_, 0);
v_extensions_1472_ = lean_ctor_get(v_params_1390_, 1);
v_extra_1473_ = lean_ctor_get(v_params_1390_, 2);
v_extraInj_1474_ = lean_ctor_get(v_params_1390_, 3);
v_extraFacts_1475_ = lean_ctor_get(v_params_1390_, 4);
v_symPrios_1476_ = lean_ctor_get(v_params_1390_, 5);
v_norm_1477_ = lean_ctor_get(v_params_1390_, 6);
v_normProcs_1478_ = lean_ctor_get(v_params_1390_, 7);
v_anchorRefs_x3f_1479_ = lean_ctor_get(v_params_1390_, 8);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_params_1390_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1481_ = v_params_1390_;
v_isShared_1482_ = v_isSharedCheck_1491_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_anchorRefs_x3f_1479_);
lean_inc(v_normProcs_1478_);
lean_inc(v_norm_1477_);
lean_inc(v_symPrios_1476_);
lean_inc(v_extraFacts_1475_);
lean_inc(v_extraInj_1474_);
lean_inc(v_extra_1473_);
lean_inc(v_extensions_1472_);
lean_inc(v_config_1471_);
lean_dec(v_params_1390_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1491_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1483_ = l_Array_toPArray_x27___redArg(v_val_1470_);
lean_dec(v_val_1470_);
v___x_1484_ = l_Lean_PersistentArray_append___redArg(v_extra_1473_, v___x_1483_);
lean_dec_ref(v___x_1483_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 2, v___x_1484_);
v___x_1486_ = v___x_1481_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_config_1471_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_extensions_1472_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_extraInj_1474_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_extraFacts_1475_);
lean_ctor_set(v_reuseFailAlloc_1490_, 5, v_symPrios_1476_);
lean_ctor_set(v_reuseFailAlloc_1490_, 6, v_norm_1477_);
lean_ctor_set(v_reuseFailAlloc_1490_, 7, v_normProcs_1478_);
lean_ctor_set(v_reuseFailAlloc_1490_, 8, v_anchorRefs_x3f_1479_);
v___x_1486_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1488_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1486_);
v___x_1488_ = v___x_1468_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
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
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_del_object(v___x_1468_);
lean_dec(v_a_1466_);
lean_dec_ref(v_params_1390_);
v___x_1492_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1493_ = l_Lean_MessageData_ofConstName(v_declName_1392_, v___x_1458_);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1496_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1499_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1465_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1465_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1507_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1464_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1464_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
v___jp_1515_:
{
uint8_t v___x_1520_; 
v___x_1520_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1393_);
if (v___x_1520_ == 0)
{
uint8_t v___x_1521_; 
v___x_1521_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1393_);
lean_dec(v_kind_1393_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec_ref(v_params_1390_);
v___x_1522_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1523_ = l_Lean_MessageData_ofConstName(v_declName_1392_, v___x_1458_);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1526_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
v___y_1460_ = v___y_1516_;
v___y_1461_ = v___y_1517_;
v___y_1462_ = v___y_1518_;
v___y_1463_ = v___y_1519_;
goto v___jp_1459_;
}
}
else
{
lean_dec(v_kind_1393_);
v___y_1460_ = v___y_1516_;
v___y_1461_ = v___y_1517_;
v___y_1462_ = v___y_1518_;
v___y_1463_ = v___y_1519_;
goto v___jp_1459_;
}
}
v___jp_1536_:
{
lean_object* v_symPrios_1541_; lean_object* v___x_1542_; 
v_symPrios_1541_ = lean_ctor_get(v_params_1390_, 5);
lean_inc(v___y_1537_);
lean_inc_ref(v___y_1538_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc_ref(v_symPrios_1541_);
lean_inc(v_declName_1392_);
v___x_1542_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1392_, v_kind_1393_, v_symPrios_1541_, v___x_1458_, v_minIndexable_1394_, v___y_1539_, v___y_1540_, v___y_1538_, v___y_1537_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v_thm_1423_ = v_a_1543_;
v___y_1424_ = v___y_1539_;
v___y_1425_ = v___y_1540_;
v___y_1426_ = v___y_1538_;
v___y_1427_ = v___y_1537_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1544_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1542_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1542_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
v___jp_1552_:
{
if (v_suggest_1395_ == 0)
{
lean_dec(v_id_1391_);
v___y_1537_ = v___y_1556_;
v___y_1538_ = v___y_1555_;
v___y_1539_ = v___y_1553_;
v___y_1540_ = v___y_1554_;
goto v___jp_1536_;
}
else
{
lean_object* v_options_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_options_1557_ = lean_ctor_get(v___y_1555_, 2);
v___x_1558_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1559_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v_symPrios_1560_; lean_object* v___x_1561_; 
lean_dec(v_kind_1393_);
v_symPrios_1560_ = lean_ctor_get(v_params_1390_, 5);
lean_inc(v___y_1556_);
lean_inc_ref(v___y_1555_);
lean_inc(v___y_1554_);
lean_inc_ref(v___y_1553_);
lean_inc_ref(v_symPrios_1560_);
lean_inc(v_declName_1392_);
v___x_1561_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1391_, v_declName_1392_, v_symPrios_1560_, v_minIndexable_1394_, v_suggest_1395_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1561_);
v_thm_1423_ = v_a_1562_;
v___y_1424_ = v___y_1553_;
v___y_1425_ = v___y_1554_;
v___y_1426_ = v___y_1555_;
v___y_1427_ = v___y_1556_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1563_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1561_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1561_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_dec(v_id_1391_);
v___y_1537_ = v___y_1556_;
v___y_1538_ = v___y_1555_;
v___y_1539_ = v___y_1553_;
v___y_1540_ = v___y_1554_;
goto v___jp_1536_;
}
}
}
v___jp_1571_:
{
lean_object* v___x_1576_; 
v___x_1576_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1394_, v___y_1574_, v___y_1575_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_dec_ref(v___x_1576_);
v___y_1553_ = v___y_1574_;
v___y_1554_ = v___y_1575_;
v___y_1555_ = v___y_1572_;
v___y_1556_ = v___y_1573_;
goto v___jp_1552_;
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v_kind_1393_);
lean_dec(v_declName_1392_);
lean_dec(v_id_1391_);
lean_dec_ref(v_params_1390_);
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
v___jp_1585_:
{
if (lean_obj_tag(v_kind_1393_) == 2)
{
uint8_t v_gen_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_id_1391_);
v_gen_1590_ = lean_ctor_get_uint8(v_kind_1393_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_kind_1393_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1592_ = v_kind_1393_;
v_isShared_1593_ = v_isSharedCheck_1654_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v_kind_1393_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1654_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1394_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_config_1595_; lean_object* v_extensions_1596_; lean_object* v_extra_1597_; lean_object* v_extraInj_1598_; lean_object* v_extraFacts_1599_; lean_object* v_symPrios_1600_; lean_object* v_norm_1601_; lean_object* v_normProcs_1602_; lean_object* v_anchorRefs_x3f_1603_; lean_object* v___x_1605_; 
lean_dec_ref(v___x_1594_);
v_config_1595_ = lean_ctor_get(v_params_1390_, 0);
lean_inc_ref(v_config_1595_);
v_extensions_1596_ = lean_ctor_get(v_params_1390_, 1);
lean_inc_ref(v_extensions_1596_);
v_extra_1597_ = lean_ctor_get(v_params_1390_, 2);
lean_inc_ref(v_extra_1597_);
v_extraInj_1598_ = lean_ctor_get(v_params_1390_, 3);
lean_inc_ref(v_extraInj_1598_);
v_extraFacts_1599_ = lean_ctor_get(v_params_1390_, 4);
lean_inc_ref(v_extraFacts_1599_);
v_symPrios_1600_ = lean_ctor_get(v_params_1390_, 5);
lean_inc_ref(v_symPrios_1600_);
v_norm_1601_ = lean_ctor_get(v_params_1390_, 6);
lean_inc_ref(v_norm_1601_);
v_normProcs_1602_ = lean_ctor_get(v_params_1390_, 7);
lean_inc_ref(v_normProcs_1602_);
v_anchorRefs_x3f_1603_ = lean_ctor_get(v_params_1390_, 8);
lean_inc(v_anchorRefs_x3f_1603_);
lean_dec_ref(v_params_1390_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 0);
v___x_1605_ = v___x_1592_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1645_, 0, v_gen_1590_);
v___x_1605_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; 
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc(v___y_1587_);
lean_inc_ref(v___y_1586_);
lean_inc_ref(v_symPrios_1600_);
lean_inc(v_declName_1392_);
v___x_1606_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1392_, v___x_1605_, v_symPrios_1600_, v___x_1458_, v___x_1458_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref(v___x_1606_);
v___x_1608_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1608_, 0, v_gen_1590_);
lean_inc(v___y_1589_);
lean_inc_ref(v___y_1588_);
lean_inc(v___y_1587_);
lean_inc_ref(v___y_1586_);
lean_inc_ref(v_symPrios_1600_);
lean_inc(v_declName_1392_);
v___x_1609_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1392_, v___x_1608_, v_symPrios_1600_, v___x_1458_, v___x_1458_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1609_) == 0)
{
if (v_warn_1396_ == 0)
{
lean_object* v_a_1610_; 
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v_declName_1392_);
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v___y_1443_ = v_config_1595_;
v___y_1444_ = v_extraFacts_1599_;
v___y_1445_ = v_anchorRefs_x3f_1603_;
v___y_1446_ = v_extraInj_1598_;
v___y_1447_ = v_a_1607_;
v___y_1448_ = v_normProcs_1602_;
v___y_1449_ = v_symPrios_1600_;
v___y_1450_ = v_extra_1597_;
v___y_1451_ = v_extensions_1596_;
v___y_1452_ = v_norm_1601_;
v___y_1453_ = v_a_1610_;
goto v___jp_1442_;
}
else
{
lean_object* v_a_1611_; lean_object* v_patterns_1612_; lean_object* v_origin_1613_; lean_object* v_cnstrs_1614_; uint8_t v___x_1615_; 
v_a_1611_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v___x_1609_);
v_patterns_1612_ = lean_ctor_get(v_a_1607_, 3);
v_origin_1613_ = lean_ctor_get(v_a_1607_, 5);
v_cnstrs_1614_ = lean_ctor_get(v_a_1607_, 7);
lean_inc(v_cnstrs_1614_);
lean_inc(v_patterns_1612_);
v___x_1615_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1596_, v_origin_1613_, v_patterns_1612_, v_cnstrs_1614_);
if (v___x_1615_ == 0)
{
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v_declName_1392_);
v___y_1443_ = v_config_1595_;
v___y_1444_ = v_extraFacts_1599_;
v___y_1445_ = v_anchorRefs_x3f_1603_;
v___y_1446_ = v_extraInj_1598_;
v___y_1447_ = v_a_1607_;
v___y_1448_ = v_normProcs_1602_;
v___y_1449_ = v_symPrios_1600_;
v___y_1450_ = v_extra_1597_;
v___y_1451_ = v_extensions_1596_;
v___y_1452_ = v_norm_1601_;
v___y_1453_ = v_a_1611_;
goto v___jp_1442_;
}
else
{
lean_object* v_patterns_1616_; lean_object* v_origin_1617_; lean_object* v_cnstrs_1618_; uint8_t v___x_1619_; 
v_patterns_1616_ = lean_ctor_get(v_a_1611_, 3);
v_origin_1617_ = lean_ctor_get(v_a_1611_, 5);
v_cnstrs_1618_ = lean_ctor_get(v_a_1611_, 7);
lean_inc(v_cnstrs_1618_);
lean_inc(v_patterns_1616_);
v___x_1619_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1596_, v_origin_1617_, v_patterns_1616_, v_cnstrs_1618_);
if (v___x_1619_ == 0)
{
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v_declName_1392_);
v___y_1443_ = v_config_1595_;
v___y_1444_ = v_extraFacts_1599_;
v___y_1445_ = v_anchorRefs_x3f_1603_;
v___y_1446_ = v_extraInj_1598_;
v___y_1447_ = v_a_1607_;
v___y_1448_ = v_normProcs_1602_;
v___y_1449_ = v_symPrios_1600_;
v___y_1450_ = v_extra_1597_;
v___y_1451_ = v_extensions_1596_;
v___y_1452_ = v_norm_1601_;
v___y_1453_ = v_a_1611_;
goto v___jp_1442_;
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1596_, v_declName_1392_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref(v___x_1620_);
v___y_1443_ = v_config_1595_;
v___y_1444_ = v_extraFacts_1599_;
v___y_1445_ = v_anchorRefs_x3f_1603_;
v___y_1446_ = v_extraInj_1598_;
v___y_1447_ = v_a_1607_;
v___y_1448_ = v_normProcs_1602_;
v___y_1449_ = v_symPrios_1600_;
v___y_1450_ = v_extra_1597_;
v___y_1451_ = v_extensions_1596_;
v___y_1452_ = v_norm_1601_;
v___y_1453_ = v_a_1611_;
goto v___jp_1442_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v_a_1611_);
lean_dec(v_a_1607_);
lean_dec(v_anchorRefs_x3f_1603_);
lean_dec_ref(v_normProcs_1602_);
lean_dec_ref(v_norm_1601_);
lean_dec_ref(v_symPrios_1600_);
lean_dec_ref(v_extraFacts_1599_);
lean_dec_ref(v_extraInj_1598_);
lean_dec_ref(v_extra_1597_);
lean_dec_ref(v_extensions_1596_);
lean_dec_ref(v_config_1595_);
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
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
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_a_1607_);
lean_dec(v_anchorRefs_x3f_1603_);
lean_dec_ref(v_normProcs_1602_);
lean_dec_ref(v_norm_1601_);
lean_dec_ref(v_symPrios_1600_);
lean_dec_ref(v_extraFacts_1599_);
lean_dec_ref(v_extraInj_1598_);
lean_dec_ref(v_extra_1597_);
lean_dec_ref(v_extensions_1596_);
lean_dec_ref(v_config_1595_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v_declName_1392_);
v_a_1629_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1609_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1609_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_dec(v_anchorRefs_x3f_1603_);
lean_dec_ref(v_normProcs_1602_);
lean_dec_ref(v_norm_1601_);
lean_dec_ref(v_symPrios_1600_);
lean_dec_ref(v_extraFacts_1599_);
lean_dec_ref(v_extraInj_1598_);
lean_dec_ref(v_extra_1597_);
lean_dec_ref(v_extensions_1596_);
lean_dec_ref(v_config_1595_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v_declName_1392_);
v_a_1637_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1606_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1606_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_del_object(v___x_1592_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v_declName_1392_);
lean_dec_ref(v_params_1390_);
v_a_1646_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1594_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1594_);
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
}
else
{
switch(lean_obj_tag(v_kind_1393_))
{
case 0:
{
v___y_1572_ = v___y_1588_;
v___y_1573_ = v___y_1589_;
v___y_1574_ = v___y_1586_;
v___y_1575_ = v___y_1587_;
goto v___jp_1571_;
}
case 1:
{
v___y_1572_ = v___y_1588_;
v___y_1573_ = v___y_1589_;
v___y_1574_ = v___y_1586_;
v___y_1575_ = v___y_1587_;
goto v___jp_1571_;
}
default: 
{
v___y_1553_ = v___y_1586_;
v___y_1554_ = v___y_1587_;
v___y_1555_ = v___y_1588_;
v___y_1556_ = v___y_1589_;
goto v___jp_1552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1697_, lean_object* v_id_1698_, lean_object* v_declName_1699_, lean_object* v_kind_1700_, lean_object* v_minIndexable_1701_, lean_object* v_suggest_1702_, lean_object* v_warn_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
uint8_t v_minIndexable_boxed_1709_; uint8_t v_suggest_boxed_1710_; uint8_t v_warn_boxed_1711_; lean_object* v_res_1712_; 
v_minIndexable_boxed_1709_ = lean_unbox(v_minIndexable_1701_);
v_suggest_boxed_1710_ = lean_unbox(v_suggest_1702_);
v_warn_boxed_1711_ = lean_unbox(v_warn_1703_);
v_res_1712_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1697_, v_id_1698_, v_declName_1699_, v_kind_1700_, v_minIndexable_boxed_1709_, v_suggest_boxed_1710_, v_warn_boxed_1711_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1713_, v___y_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1727_, lean_object* v_constName_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1735_, lean_object* v_constName_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1735_, v_constName_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1743_, lean_object* v_ref_1744_, lean_object* v_constName_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1744_, v_constName_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1752_, lean_object* v_ref_1753_, lean_object* v_constName_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1752_, v_ref_1753_, v_constName_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v_ref_1753_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1761_, lean_object* v_ref_1762_, lean_object* v_msg_1763_, lean_object* v_declHint_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1762_, v_msg_1763_, v_declHint_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1771_, lean_object* v_ref_1772_, lean_object* v_msg_1773_, lean_object* v_declHint_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1771_, v_ref_1772_, v_msg_1773_, v_declHint_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v_ref_1772_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1781_, lean_object* v_declHint_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1781_, v_declHint_1782_, v___y_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1789_, lean_object* v_declHint_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1789_, v_declHint_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1797_, lean_object* v_ref_1798_, lean_object* v_msg_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1798_, v_msg_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1806_, lean_object* v_ref_1807_, lean_object* v_msg_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1806_, v_ref_1807_, v_msg_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v_ref_1807_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1817_, lean_object* v_val_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_config_1822_; lean_object* v_extensions_1823_; lean_object* v_extra_1824_; lean_object* v_extraInj_1825_; lean_object* v_extraFacts_1826_; lean_object* v_symPrios_1827_; lean_object* v_norm_1828_; lean_object* v_normProcs_1829_; lean_object* v_anchorRefs_x3f_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1860_; 
v_config_1822_ = lean_ctor_get(v_params_1817_, 0);
v_extensions_1823_ = lean_ctor_get(v_params_1817_, 1);
v_extra_1824_ = lean_ctor_get(v_params_1817_, 2);
v_extraInj_1825_ = lean_ctor_get(v_params_1817_, 3);
v_extraFacts_1826_ = lean_ctor_get(v_params_1817_, 4);
v_symPrios_1827_ = lean_ctor_get(v_params_1817_, 5);
v_norm_1828_ = lean_ctor_get(v_params_1817_, 6);
v_normProcs_1829_ = lean_ctor_get(v_params_1817_, 7);
v_anchorRefs_x3f_1830_ = lean_ctor_get(v_params_1817_, 8);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_params_1817_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1832_ = v_params_1817_;
v_isShared_1833_ = v_isSharedCheck_1860_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_anchorRefs_x3f_1830_);
lean_inc(v_normProcs_1829_);
lean_inc(v_norm_1828_);
lean_inc(v_symPrios_1827_);
lean_inc(v_extraFacts_1826_);
lean_inc(v_extraInj_1825_);
lean_inc(v_extra_1824_);
lean_inc(v_extensions_1823_);
lean_inc(v_config_1822_);
lean_dec(v_params_1817_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1860_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___y_1835_; 
if (lean_obj_tag(v_anchorRefs_x3f_1830_) == 0)
{
lean_object* v___x_1858_; 
v___x_1858_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1835_ = v___x_1858_;
goto v___jp_1834_;
}
else
{
lean_object* v_val_1859_; 
v_val_1859_ = lean_ctor_get(v_anchorRefs_x3f_1830_, 0);
lean_inc(v_val_1859_);
lean_dec_ref(v_anchorRefs_x3f_1830_);
v___y_1835_ = v_val_1859_;
goto v___jp_1834_;
}
v___jp_1834_:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1849_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1849_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1849_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1841_ = lean_array_push(v___y_1835_, v_a_1837_);
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 8, v___x_1842_);
v___x_1844_ = v___x_1832_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_config_1822_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_extensions_1823_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_extra_1824_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_extraInj_1825_);
lean_ctor_set(v_reuseFailAlloc_1848_, 4, v_extraFacts_1826_);
lean_ctor_set(v_reuseFailAlloc_1848_, 5, v_symPrios_1827_);
lean_ctor_set(v_reuseFailAlloc_1848_, 6, v_norm_1828_);
lean_ctor_set(v_reuseFailAlloc_1848_, 7, v_normProcs_1829_);
lean_ctor_set(v_reuseFailAlloc_1848_, 8, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1844_);
v___x_1846_ = v___x_1839_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v___y_1835_);
lean_del_object(v___x_1832_);
lean_dec_ref(v_normProcs_1829_);
lean_dec_ref(v_norm_1828_);
lean_dec_ref(v_symPrios_1827_);
lean_dec_ref(v_extraFacts_1826_);
lean_dec_ref(v_extraInj_1825_);
lean_dec_ref(v_extra_1824_);
lean_dec_ref(v_extensions_1823_);
lean_dec_ref(v_config_1822_);
v_a_1850_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1836_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1836_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1861_, lean_object* v_val_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1861_, v_val_1862_, v_a_1863_, v_a_1864_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_val_1862_);
return v_res_1866_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1869_ = l_Lean_stringToMessageData(v___x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_config_1874_; uint8_t v_revert_1875_; 
v_config_1874_ = lean_ctor_get(v_params_1870_, 0);
v_revert_1875_ = lean_ctor_get_uint8(v_config_1874_, sizeof(void*)*11 + 29);
if (v_revert_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_box(0);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_1879_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1878_, v_a_1871_, v_a_1872_);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_1880_, v_a_1881_, v_a_1882_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec_ref(v_params_1880_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_1885_, lean_object* v___y_1886_){
_start:
{
uint8_t v___x_1888_; 
v___x_1888_ = l_Lean_Expr_hasMVar(v_e_1885_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v_e_1885_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; lean_object* v_mctx_1891_; lean_object* v___x_1892_; lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v___x_1895_; lean_object* v_cache_1896_; lean_object* v_zetaDeltaFVarIds_1897_; lean_object* v_postponed_1898_; lean_object* v_diag_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1908_; 
v___x_1890_ = lean_st_ref_get(v___y_1886_);
v_mctx_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc_ref(v_mctx_1891_);
lean_dec(v___x_1890_);
v___x_1892_ = l_Lean_instantiateMVarsCore(v_mctx_1891_, v_e_1885_);
v_fst_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_fst_1893_);
v_snd_1894_ = lean_ctor_get(v___x_1892_, 1);
lean_inc(v_snd_1894_);
lean_dec_ref(v___x_1892_);
v___x_1895_ = lean_st_ref_take(v___y_1886_);
v_cache_1896_ = lean_ctor_get(v___x_1895_, 1);
v_zetaDeltaFVarIds_1897_ = lean_ctor_get(v___x_1895_, 2);
v_postponed_1898_ = lean_ctor_get(v___x_1895_, 3);
v_diag_1899_ = lean_ctor_get(v___x_1895_, 4);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; 
v_unused_1909_ = lean_ctor_get(v___x_1895_, 0);
lean_dec(v_unused_1909_);
v___x_1901_ = v___x_1895_;
v_isShared_1902_ = v_isSharedCheck_1908_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_diag_1899_);
lean_inc(v_postponed_1898_);
lean_inc(v_zetaDeltaFVarIds_1897_);
lean_inc(v_cache_1896_);
lean_dec(v___x_1895_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1908_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v_snd_1894_);
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_snd_1894_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_cache_1896_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_zetaDeltaFVarIds_1897_);
lean_ctor_set(v_reuseFailAlloc_1907_, 3, v_postponed_1898_);
lean_ctor_set(v_reuseFailAlloc_1907_, 4, v_diag_1899_);
v___x_1904_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_st_ref_set(v___y_1886_, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_fst_1893_);
return v___x_1906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1910_, v___y_1911_);
lean_dec(v___y_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1914_, v___y_1918_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(lean_object* v_p_1934_, lean_object* v_term_1935_, lean_object* v___x_1936_, uint8_t v___x_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_fileName_1945_; lean_object* v_fileMap_1946_; lean_object* v_options_1947_; lean_object* v_currRecDepth_1948_; lean_object* v_maxRecDepth_1949_; lean_object* v_ref_1950_; lean_object* v_currNamespace_1951_; lean_object* v_openDecls_1952_; lean_object* v_initHeartbeats_1953_; lean_object* v_maxHeartbeats_1954_; lean_object* v_quotContext_1955_; lean_object* v_currMacroScope_1956_; uint8_t v_diag_1957_; lean_object* v_cancelTk_x3f_1958_; uint8_t v_suppressElabErrors_1959_; lean_object* v_inheritedTraceOptions_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2028_; 
v_fileName_1945_ = lean_ctor_get(v___y_1942_, 0);
v_fileMap_1946_ = lean_ctor_get(v___y_1942_, 1);
v_options_1947_ = lean_ctor_get(v___y_1942_, 2);
v_currRecDepth_1948_ = lean_ctor_get(v___y_1942_, 3);
v_maxRecDepth_1949_ = lean_ctor_get(v___y_1942_, 4);
v_ref_1950_ = lean_ctor_get(v___y_1942_, 5);
v_currNamespace_1951_ = lean_ctor_get(v___y_1942_, 6);
v_openDecls_1952_ = lean_ctor_get(v___y_1942_, 7);
v_initHeartbeats_1953_ = lean_ctor_get(v___y_1942_, 8);
v_maxHeartbeats_1954_ = lean_ctor_get(v___y_1942_, 9);
v_quotContext_1955_ = lean_ctor_get(v___y_1942_, 10);
v_currMacroScope_1956_ = lean_ctor_get(v___y_1942_, 11);
v_diag_1957_ = lean_ctor_get_uint8(v___y_1942_, sizeof(void*)*14);
v_cancelTk_x3f_1958_ = lean_ctor_get(v___y_1942_, 12);
v_suppressElabErrors_1959_ = lean_ctor_get_uint8(v___y_1942_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1960_ = lean_ctor_get(v___y_1942_, 13);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___y_1942_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1962_ = v___y_1942_;
v_isShared_1963_ = v_isSharedCheck_2028_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_inheritedTraceOptions_1960_);
lean_inc(v_cancelTk_x3f_1958_);
lean_inc(v_currMacroScope_1956_);
lean_inc(v_quotContext_1955_);
lean_inc(v_maxHeartbeats_1954_);
lean_inc(v_initHeartbeats_1953_);
lean_inc(v_openDecls_1952_);
lean_inc(v_currNamespace_1951_);
lean_inc(v_ref_1950_);
lean_inc(v_maxRecDepth_1949_);
lean_inc(v_currRecDepth_1948_);
lean_inc(v_options_1947_);
lean_inc(v_fileMap_1946_);
lean_inc(v_fileName_1945_);
lean_dec(v___y_1942_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2028_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_ref_1964_; lean_object* v___x_1966_; 
v_ref_1964_ = l_Lean_replaceRef(v_p_1934_, v_ref_1950_);
lean_dec(v_ref_1950_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 5, v_ref_1964_);
v___x_1966_ = v___x_1962_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_fileName_1945_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_fileMap_1946_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v_options_1947_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v_currRecDepth_1948_);
lean_ctor_set(v_reuseFailAlloc_2027_, 4, v_maxRecDepth_1949_);
lean_ctor_set(v_reuseFailAlloc_2027_, 5, v_ref_1964_);
lean_ctor_set(v_reuseFailAlloc_2027_, 6, v_currNamespace_1951_);
lean_ctor_set(v_reuseFailAlloc_2027_, 7, v_openDecls_1952_);
lean_ctor_set(v_reuseFailAlloc_2027_, 8, v_initHeartbeats_1953_);
lean_ctor_set(v_reuseFailAlloc_2027_, 9, v_maxHeartbeats_1954_);
lean_ctor_set(v_reuseFailAlloc_2027_, 10, v_quotContext_1955_);
lean_ctor_set(v_reuseFailAlloc_2027_, 11, v_currMacroScope_1956_);
lean_ctor_set(v_reuseFailAlloc_2027_, 12, v_cancelTk_x3f_1958_);
lean_ctor_set(v_reuseFailAlloc_2027_, 13, v_inheritedTraceOptions_1960_);
lean_ctor_set_uint8(v_reuseFailAlloc_2027_, sizeof(void*)*14, v_diag_1957_);
lean_ctor_set_uint8(v_reuseFailAlloc_2027_, sizeof(void*)*14 + 1, v_suppressElabErrors_1959_);
v___x_1966_ = v_reuseFailAlloc_2027_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; 
lean_inc(v___y_1943_);
lean_inc_ref(v___x_1966_);
lean_inc(v___y_1941_);
lean_inc_ref(v___y_1940_);
lean_inc(v___y_1939_);
lean_inc_ref(v___y_1938_);
v___x_1967_ = l_Lean_Elab_Term_elabTerm(v_term_1935_, v___x_1936_, v___x_1937_, v___x_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___x_1966_, v___y_1943_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1967_);
v___x_1969_ = 1;
lean_inc(v___y_1943_);
lean_inc_ref(v___x_1966_);
lean_inc(v___y_1941_);
lean_inc_ref(v___y_1940_);
v___x_1970_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1969_, v___x_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___x_1966_, v___y_1943_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v___x_1970_);
v___x_1971_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_1968_, v___y_1941_);
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_2010_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2010_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
uint8_t v___x_1976_; 
v___x_1976_ = l_Lean_Expr_hasSyntheticSorry(v_a_1972_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = l_Lean_Expr_eta(v_a_1972_);
v___x_1978_ = l_Lean_Expr_hasMVar(v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
lean_dec_ref(v___x_1966_);
lean_dec(v___y_1943_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
v___x_1979_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0));
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
lean_ctor_set(v___x_1980_, 1, v___x_1977_);
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1981_);
v___x_1983_ = v___x_1974_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
else
{
lean_object* v___x_1985_; 
lean_del_object(v___x_1974_);
v___x_1985_ = l_Lean_Meta_abstractMVars(v___x_1977_, v___x_1937_, v___y_1940_, v___y_1941_, v___x_1966_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___x_1966_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1997_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1997_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1997_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v_paramNames_1990_; lean_object* v_expr_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v_paramNames_1990_ = lean_ctor_get(v_a_1986_, 0);
lean_inc_ref(v_paramNames_1990_);
v_expr_1991_ = lean_ctor_get(v_a_1986_, 2);
lean_inc_ref(v_expr_1991_);
lean_dec(v_a_1986_);
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v_paramNames_1990_);
lean_ctor_set(v___x_1992_, 1, v_expr_1991_);
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1993_);
v___x_1995_ = v___x_1988_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
v_a_1998_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1985_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1985_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
lean_dec(v_a_1972_);
lean_dec_ref(v___x_1966_);
lean_dec(v___y_1943_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
v___x_2006_ = lean_box(0);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_2006_);
v___x_2008_ = v___x_1974_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_a_1968_);
lean_dec_ref(v___x_1966_);
lean_dec(v___y_1943_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
v_a_2011_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1970_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1970_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec_ref(v___x_1966_);
lean_dec(v___y_1943_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
v_a_2019_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1967_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1967_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v_p_2029_, lean_object* v_term_2030_, lean_object* v___x_2031_, lean_object* v___x_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
uint8_t v___x_14116__boxed_2040_; lean_object* v_res_2041_; 
v___x_14116__boxed_2040_ = lean_unbox(v___x_2032_);
v_res_2041_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v_p_2029_, v_term_2030_, v___x_2031_, v___x_14116__boxed_2040_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v_p_2029_);
return v_res_2041_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_params_2048_, lean_object* v_p_2049_, lean_object* v_fst_2050_, lean_object* v_snd_2051_, uint8_t v___x_2052_, uint8_t v_minIndexable_2053_, lean_object* v_kind_2054_, lean_object* v_idx_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_symPrios_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; 
v_symPrios_2061_ = lean_ctor_get(v_params_2048_, 5);
lean_inc_ref(v_symPrios_2061_);
lean_dec_ref(v_params_2048_);
v___x_2062_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1));
v___x_2063_ = lean_name_append_index_after(v___x_2062_, v_idx_2055_);
v___x_2064_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v_p_2049_);
v___x_2065_ = 0;
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
lean_inc(v___y_2057_);
lean_inc_ref(v___y_2056_);
v___x_2066_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2064_, v_fst_2050_, v_snd_2051_, v_kind_2054_, v_symPrios_2061_, v___x_2052_, v___x_2065_, v_minIndexable_2053_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2077_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2077_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
if (lean_obj_tag(v_a_2067_) == 1)
{
lean_object* v_val_2071_; lean_object* v___x_2073_; 
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
v_val_2071_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_val_2071_);
lean_dec_ref(v_a_2067_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v_val_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_val_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_del_object(v___x_2069_);
lean_dec(v_a_2067_);
v___x_2075_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3);
v___x_2076_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2075_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v___x_2076_;
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
v_a_2078_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2066_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2066_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_params_2086_, lean_object* v_p_2087_, lean_object* v_fst_2088_, lean_object* v_snd_2089_, lean_object* v___x_2090_, lean_object* v_minIndexable_2091_, lean_object* v_kind_2092_, lean_object* v_idx_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v___x_14290__boxed_2099_; uint8_t v_minIndexable_boxed_2100_; lean_object* v_res_2101_; 
v___x_14290__boxed_2099_ = lean_unbox(v___x_2090_);
v_minIndexable_boxed_2100_ = lean_unbox(v_minIndexable_2091_);
v_res_2101_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_params_2086_, v_p_2087_, v_fst_2088_, v_snd_2089_, v___x_14290__boxed_2099_, v_minIndexable_boxed_2100_, v_kind_2092_, v_idx_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
return v_res_2101_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_box(1);
v___x_2103_ = l_Lean_MessageData_ofFormat(v___x_2102_);
return v___x_2103_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2));
v___x_2108_ = l_Lean_MessageData_ofFormat(v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object* v_x_2109_, lean_object* v_x_2110_){
_start:
{
if (lean_obj_tag(v_x_2110_) == 0)
{
return v_x_2109_;
}
else
{
lean_object* v_head_2111_; lean_object* v_tail_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2134_; 
v_head_2111_ = lean_ctor_get(v_x_2110_, 0);
v_tail_2112_ = lean_ctor_get(v_x_2110_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_2110_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2114_ = v_x_2110_;
v_isShared_2115_ = v_isSharedCheck_2134_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_tail_2112_);
lean_inc(v_head_2111_);
lean_dec(v_x_2110_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2134_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_before_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2132_; 
v_before_2116_ = lean_ctor_get(v_head_2111_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_head_2111_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v_head_2111_, 1);
lean_dec(v_unused_2133_);
v___x_2118_ = v_head_2111_;
v_isShared_2119_ = v_isSharedCheck_2132_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_before_2116_);
lean_dec(v_head_2111_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2132_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2119_ == 0)
{
lean_ctor_set_tag(v___x_2118_, 7);
lean_ctor_set(v___x_2118_, 1, v___x_2120_);
lean_ctor_set(v___x_2118_, 0, v_x_2109_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_x_2109_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3);
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 7);
lean_ctor_set(v___x_2114_, 1, v___x_2123_);
lean_ctor_set(v___x_2114_, 0, v___x_2122_);
v___x_2125_ = v___x_2114_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = l_Lean_MessageData_ofSyntax(v_before_2116_);
v___x_2127_ = l_Lean_indentD(v___x_2126_);
v___x_2128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2125_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v_x_2109_ = v___x_2128_;
v_x_2110_ = v_tail_2112_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1));
v___x_2139_ = l_Lean_MessageData_ofFormat(v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object* v_msgData_2140_, lean_object* v_macroStack_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_options_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_options_2144_ = lean_ctor_get(v___y_2142_, 2);
v___x_2145_ = l_Lean_Elab_pp_macroStack;
v___x_2146_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_dec(v_macroStack_2141_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v_msgData_2140_);
return v___x_2147_;
}
else
{
if (lean_obj_tag(v_macroStack_2141_) == 0)
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_msgData_2140_);
return v___x_2148_;
}
else
{
lean_object* v_head_2149_; lean_object* v_after_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2165_; 
v_head_2149_ = lean_ctor_get(v_macroStack_2141_, 0);
lean_inc(v_head_2149_);
v_after_2150_ = lean_ctor_get(v_head_2149_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_head_2149_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v_head_2149_, 0);
lean_dec(v_unused_2166_);
v___x_2152_ = v_head_2149_;
v_isShared_2153_ = v_isSharedCheck_2165_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_after_2150_);
lean_dec(v_head_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2165_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2153_ == 0)
{
lean_ctor_set_tag(v___x_2152_, 7);
lean_ctor_set(v___x_2152_, 1, v___x_2154_);
lean_ctor_set(v___x_2152_, 0, v_msgData_2140_);
v___x_2156_ = v___x_2152_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_msgData_2140_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v_msgData_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2157_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_MessageData_ofSyntax(v_after_2150_);
v___x_2160_ = l_Lean_indentD(v___x_2159_);
v_msgData_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2161_, 0, v___x_2158_);
lean_ctor_set(v_msgData_2161_, 1, v___x_2160_);
v___x_2162_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(v_msgData_2161_, v_macroStack_2141_);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2167_, lean_object* v_macroStack_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2167_, v_macroStack_2168_, v___y_2169_);
lean_dec_ref(v___y_2169_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object* v_msg_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_ref_2180_; lean_object* v___x_2181_; lean_object* v_a_2182_; lean_object* v_macroStack_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2194_; 
v_ref_2180_ = lean_ctor_get(v___y_2177_, 5);
v___x_2181_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2172_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2181_);
v_macroStack_2183_ = lean_ctor_get(v___y_2173_, 1);
lean_inc(v_macroStack_2183_);
lean_dec_ref(v___y_2173_);
lean_inc(v_macroStack_2183_);
v___x_2184_ = l_Lean_Elab_getBetterRef(v_ref_2180_, v_macroStack_2183_);
v___x_2185_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_a_2182_, v_macroStack_2183_, v___y_2177_);
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2194_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2194_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2184_);
lean_ctor_set(v___x_2190_, 1, v_a_2186_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set_tag(v___x_2188_, 1);
lean_ctor_set(v___x_2188_, 0, v___x_2190_);
v___x_2192_ = v___x_2188_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v_msg_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
return v_res_2203_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2206_ = l_Lean_stringToMessageData(v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2209_ = l_Lean_stringToMessageData(v___x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2212_ = l_Lean_stringToMessageData(v___x_2211_);
return v___x_2212_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7));
v___x_2217_ = l_Lean_stringToMessageData(v___x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2218_, lean_object* v_p_2219_, lean_object* v_mod_x3f_2220_, lean_object* v_term_2221_, uint8_t v_minIndexable_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2293_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v_kind_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v_fileName_2528_; lean_object* v_fileMap_2529_; lean_object* v_options_2530_; lean_object* v_currRecDepth_2531_; lean_object* v_maxRecDepth_2532_; lean_object* v_ref_2533_; lean_object* v_currNamespace_2534_; lean_object* v_openDecls_2535_; lean_object* v_initHeartbeats_2536_; lean_object* v_maxHeartbeats_2537_; lean_object* v_quotContext_2538_; lean_object* v_currMacroScope_2539_; uint8_t v_diag_2540_; lean_object* v_cancelTk_x3f_2541_; uint8_t v_suppressElabErrors_2542_; lean_object* v_inheritedTraceOptions_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2619_; 
v_fileName_2528_ = lean_ctor_get(v_a_2227_, 0);
v_fileMap_2529_ = lean_ctor_get(v_a_2227_, 1);
v_options_2530_ = lean_ctor_get(v_a_2227_, 2);
v_currRecDepth_2531_ = lean_ctor_get(v_a_2227_, 3);
v_maxRecDepth_2532_ = lean_ctor_get(v_a_2227_, 4);
v_ref_2533_ = lean_ctor_get(v_a_2227_, 5);
v_currNamespace_2534_ = lean_ctor_get(v_a_2227_, 6);
v_openDecls_2535_ = lean_ctor_get(v_a_2227_, 7);
v_initHeartbeats_2536_ = lean_ctor_get(v_a_2227_, 8);
v_maxHeartbeats_2537_ = lean_ctor_get(v_a_2227_, 9);
v_quotContext_2538_ = lean_ctor_get(v_a_2227_, 10);
v_currMacroScope_2539_ = lean_ctor_get(v_a_2227_, 11);
v_diag_2540_ = lean_ctor_get_uint8(v_a_2227_, sizeof(void*)*14);
v_cancelTk_x3f_2541_ = lean_ctor_get(v_a_2227_, 12);
v_suppressElabErrors_2542_ = lean_ctor_get_uint8(v_a_2227_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2543_ = lean_ctor_get(v_a_2227_, 13);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_a_2227_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2545_ = v_a_2227_;
v_isShared_2546_ = v_isSharedCheck_2619_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_inheritedTraceOptions_2543_);
lean_inc(v_cancelTk_x3f_2541_);
lean_inc(v_currMacroScope_2539_);
lean_inc(v_quotContext_2538_);
lean_inc(v_maxHeartbeats_2537_);
lean_inc(v_initHeartbeats_2536_);
lean_inc(v_openDecls_2535_);
lean_inc(v_currNamespace_2534_);
lean_inc(v_ref_2533_);
lean_inc(v_maxRecDepth_2532_);
lean_inc(v_currRecDepth_2531_);
lean_inc(v_options_2530_);
lean_inc(v_fileMap_2529_);
lean_inc(v_fileName_2528_);
lean_dec(v_a_2227_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2619_;
goto v_resetjp_2544_;
}
v___jp_2230_:
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_apply_7(v___y_2240_, v___y_2232_, v___y_2236_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, lean_box(0));
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2257_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2257_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2257_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2252_ = l_Lean_PersistentArray_push___redArg(v___y_2235_, v_a_2248_);
v___x_2253_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2253_, 0, v___y_2231_);
lean_ctor_set(v___x_2253_, 1, v___y_2242_);
lean_ctor_set(v___x_2253_, 2, v___x_2252_);
lean_ctor_set(v___x_2253_, 3, v___y_2233_);
lean_ctor_set(v___x_2253_, 4, v___y_2234_);
lean_ctor_set(v___x_2253_, 5, v___y_2239_);
lean_ctor_set(v___x_2253_, 6, v___y_2238_);
lean_ctor_set(v___x_2253_, 7, v___y_2237_);
lean_ctor_set(v___x_2253_, 8, v___y_2241_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2253_);
v___x_2255_ = v___x_2250_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v___y_2231_);
v_a_2258_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2247_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2247_);
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
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_2266_:
{
lean_object* v___x_2283_; 
v___x_2283_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2222_, v___y_2271_, v___y_2276_, v___y_2267_, v___y_2270_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_dec_ref(v___x_2283_);
v___y_2231_ = v___y_2268_;
v___y_2232_ = v___y_2269_;
v___y_2233_ = v___y_2277_;
v___y_2234_ = v___y_2272_;
v___y_2235_ = v___y_2278_;
v___y_2236_ = v___y_2273_;
v___y_2237_ = v___y_2279_;
v___y_2238_ = v___y_2274_;
v___y_2239_ = v___y_2280_;
v___y_2240_ = v___y_2275_;
v___y_2241_ = v___y_2281_;
v___y_2242_ = v___y_2282_;
v___y_2243_ = v___y_2271_;
v___y_2244_ = v___y_2276_;
v___y_2245_ = v___y_2267_;
v___y_2246_ = v___y_2270_;
goto v___jp_2230_;
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec_ref(v___y_2267_);
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
v___jp_2292_:
{
lean_object* v_config_2294_; lean_object* v_extensions_2295_; lean_object* v_extra_2296_; lean_object* v_extraInj_2297_; lean_object* v_extraFacts_2298_; lean_object* v_symPrios_2299_; lean_object* v_norm_2300_; lean_object* v_normProcs_2301_; lean_object* v_anchorRefs_x3f_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2311_; 
v_config_2294_ = lean_ctor_get(v_params_2218_, 0);
v_extensions_2295_ = lean_ctor_get(v_params_2218_, 1);
v_extra_2296_ = lean_ctor_get(v_params_2218_, 2);
v_extraInj_2297_ = lean_ctor_get(v_params_2218_, 3);
v_extraFacts_2298_ = lean_ctor_get(v_params_2218_, 4);
v_symPrios_2299_ = lean_ctor_get(v_params_2218_, 5);
v_norm_2300_ = lean_ctor_get(v_params_2218_, 6);
v_normProcs_2301_ = lean_ctor_get(v_params_2218_, 7);
v_anchorRefs_x3f_2302_ = lean_ctor_get(v_params_2218_, 8);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_params_2218_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2304_ = v_params_2218_;
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_anchorRefs_x3f_2302_);
lean_inc(v_normProcs_2301_);
lean_inc(v_norm_2300_);
lean_inc(v_symPrios_2299_);
lean_inc(v_extraFacts_2298_);
lean_inc(v_extraInj_2297_);
lean_inc(v_extra_2296_);
lean_inc(v_extensions_2295_);
lean_inc(v_config_2294_);
lean_dec(v_params_2218_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2306_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2298_, v___y_2293_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 4, v___x_2306_);
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_config_2294_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_extensions_2295_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_extra_2296_);
lean_ctor_set(v_reuseFailAlloc_2310_, 3, v_extraInj_2297_);
lean_ctor_set(v_reuseFailAlloc_2310_, 4, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2310_, 5, v_symPrios_2299_);
lean_ctor_set(v_reuseFailAlloc_2310_, 6, v_norm_2300_);
lean_ctor_set(v_reuseFailAlloc_2310_, 7, v_normProcs_2301_);
lean_ctor_set(v_reuseFailAlloc_2310_, 8, v_anchorRefs_x3f_2302_);
v___x_2308_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
}
}
v___jp_2312_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2322_ = lean_array_get_size(v___y_2314_);
lean_dec_ref(v___y_2314_);
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = lean_nat_dec_eq(v___x_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec_ref(v___y_2315_);
lean_dec_ref(v_params_2218_);
v___x_2325_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2326_ = l_Lean_indentExpr(v___y_2313_);
v___x_2327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2327_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
else
{
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___y_2313_);
v___y_2293_ = v___y_2315_;
goto v___jp_2292_;
}
}
v___jp_2337_:
{
uint8_t v___x_2349_; 
v___x_2349_ = l_Lean_Expr_isForall(v___y_2339_);
if (v___x_2349_ == 0)
{
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2338_);
if (lean_obj_tag(v_mod_x3f_2220_) == 0)
{
v___y_2313_ = v___y_2339_;
v___y_2314_ = v___y_2340_;
v___y_2315_ = v___y_2342_;
v___y_2316_ = v___y_2343_;
v___y_2317_ = v___y_2344_;
v___y_2318_ = v___y_2345_;
v___y_2319_ = v___y_2346_;
v___y_2320_ = v___y_2347_;
v___y_2321_ = v___y_2348_;
goto v___jp_2312_;
}
else
{
lean_dec_ref(v_mod_x3f_2220_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___y_2340_);
lean_dec_ref(v_params_2218_);
v___x_2350_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2351_ = l_Lean_indentExpr(v___y_2339_);
v___x_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2352_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
v___y_2313_ = v___y_2339_;
v___y_2314_ = v___y_2340_;
v___y_2315_ = v___y_2342_;
v___y_2316_ = v___y_2343_;
v___y_2317_ = v___y_2344_;
v___y_2318_ = v___y_2345_;
v___y_2319_ = v___y_2346_;
v___y_2320_ = v___y_2347_;
v___y_2321_ = v___y_2348_;
goto v___jp_2312_;
}
}
}
else
{
lean_object* v_extra_2362_; 
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v_mod_x3f_2220_);
v_extra_2362_ = lean_ctor_get(v_params_2218_, 2);
lean_inc_ref(v_extra_2362_);
if (lean_obj_tag(v___y_2338_) == 2)
{
lean_object* v_config_2363_; lean_object* v_extensions_2364_; lean_object* v_extraInj_2365_; lean_object* v_extraFacts_2366_; lean_object* v_symPrios_2367_; lean_object* v_norm_2368_; lean_object* v_normProcs_2369_; lean_object* v_anchorRefs_x3f_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2425_; 
v_config_2363_ = lean_ctor_get(v_params_2218_, 0);
v_extensions_2364_ = lean_ctor_get(v_params_2218_, 1);
v_extraInj_2365_ = lean_ctor_get(v_params_2218_, 3);
v_extraFacts_2366_ = lean_ctor_get(v_params_2218_, 4);
v_symPrios_2367_ = lean_ctor_get(v_params_2218_, 5);
v_norm_2368_ = lean_ctor_get(v_params_2218_, 6);
v_normProcs_2369_ = lean_ctor_get(v_params_2218_, 7);
v_anchorRefs_x3f_2370_ = lean_ctor_get(v_params_2218_, 8);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_params_2218_);
if (v_isSharedCheck_2425_ == 0)
{
lean_object* v_unused_2426_; 
v_unused_2426_ = lean_ctor_get(v_params_2218_, 2);
lean_dec(v_unused_2426_);
v___x_2372_ = v_params_2218_;
v_isShared_2373_ = v_isSharedCheck_2425_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_anchorRefs_x3f_2370_);
lean_inc(v_normProcs_2369_);
lean_inc(v_norm_2368_);
lean_inc(v_symPrios_2367_);
lean_inc(v_extraFacts_2366_);
lean_inc(v_extraInj_2365_);
lean_inc(v_extensions_2364_);
lean_inc(v_config_2363_);
lean_dec(v_params_2218_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2425_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v_size_2374_; uint8_t v_gen_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2424_; 
v_size_2374_ = lean_ctor_get(v_extra_2362_, 2);
v_gen_2375_ = lean_ctor_get_uint8(v___y_2338_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___y_2338_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2377_ = v___y_2338_;
v_isShared_2378_ = v_isSharedCheck_2424_;
goto v_resetjp_2376_;
}
else
{
lean_dec(v___y_2338_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2424_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; 
v___x_2379_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2222_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v___x_2381_; 
lean_dec_ref(v___x_2379_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set_tag(v___x_2377_, 0);
v___x_2381_ = v___x_2377_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2415_, 0, v_gen_2375_);
v___x_2381_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2382_; 
lean_inc_ref(v___y_2341_);
lean_inc(v___y_2348_);
lean_inc_ref(v___y_2347_);
lean_inc(v___y_2346_);
lean_inc_ref(v___y_2345_);
lean_inc(v_size_2374_);
v___x_2382_ = lean_apply_7(v___y_2341_, v___x_2381_, v_size_2374_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, lean_box(0));
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref(v___x_2382_);
v___x_2384_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2384_, 0, v_gen_2375_);
lean_inc(v_size_2374_);
v___x_2385_ = lean_apply_7(v___y_2341_, v___x_2384_, v_size_2374_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, lean_box(0));
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2398_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2398_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2398_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2390_ = l_Lean_PersistentArray_push___redArg(v_extra_2362_, v_a_2383_);
v___x_2391_ = l_Lean_PersistentArray_push___redArg(v___x_2390_, v_a_2386_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 2, v___x_2391_);
v___x_2393_ = v___x_2372_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_config_2363_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_extensions_2364_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_extraInj_2365_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_extraFacts_2366_);
lean_ctor_set(v_reuseFailAlloc_2397_, 5, v_symPrios_2367_);
lean_ctor_set(v_reuseFailAlloc_2397_, 6, v_norm_2368_);
lean_ctor_set(v_reuseFailAlloc_2397_, 7, v_normProcs_2369_);
lean_ctor_set(v_reuseFailAlloc_2397_, 8, v_anchorRefs_x3f_2370_);
v___x_2393_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2395_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2393_);
v___x_2395_ = v___x_2388_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v_a_2383_);
lean_del_object(v___x_2372_);
lean_dec(v_anchorRefs_x3f_2370_);
lean_dec_ref(v_normProcs_2369_);
lean_dec_ref(v_norm_2368_);
lean_dec_ref(v_symPrios_2367_);
lean_dec_ref(v_extraFacts_2366_);
lean_dec_ref(v_extraInj_2365_);
lean_dec_ref(v_extensions_2364_);
lean_dec_ref(v_config_2363_);
lean_dec_ref(v_extra_2362_);
v_a_2399_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2385_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2385_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_del_object(v___x_2372_);
lean_dec(v_anchorRefs_x3f_2370_);
lean_dec_ref(v_normProcs_2369_);
lean_dec_ref(v_norm_2368_);
lean_dec_ref(v_symPrios_2367_);
lean_dec_ref(v_extraFacts_2366_);
lean_dec_ref(v_extraInj_2365_);
lean_dec_ref(v_extensions_2364_);
lean_dec_ref(v_config_2363_);
lean_dec_ref(v_extra_2362_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec_ref(v___y_2341_);
v_a_2407_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2382_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2382_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_del_object(v___x_2377_);
lean_del_object(v___x_2372_);
lean_dec(v_anchorRefs_x3f_2370_);
lean_dec_ref(v_normProcs_2369_);
lean_dec_ref(v_norm_2368_);
lean_dec_ref(v_symPrios_2367_);
lean_dec_ref(v_extraFacts_2366_);
lean_dec_ref(v_extraInj_2365_);
lean_dec_ref(v_extensions_2364_);
lean_dec_ref(v_config_2363_);
lean_dec_ref(v_extra_2362_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec_ref(v___y_2341_);
v_a_2416_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2379_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2379_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
}
else
{
switch(lean_obj_tag(v___y_2338_))
{
case 0:
{
lean_object* v_config_2427_; lean_object* v_extensions_2428_; lean_object* v_extraInj_2429_; lean_object* v_extraFacts_2430_; lean_object* v_symPrios_2431_; lean_object* v_norm_2432_; lean_object* v_normProcs_2433_; lean_object* v_anchorRefs_x3f_2434_; lean_object* v_size_2435_; 
v_config_2427_ = lean_ctor_get(v_params_2218_, 0);
lean_inc_ref(v_config_2427_);
v_extensions_2428_ = lean_ctor_get(v_params_2218_, 1);
lean_inc_ref(v_extensions_2428_);
v_extraInj_2429_ = lean_ctor_get(v_params_2218_, 3);
lean_inc_ref(v_extraInj_2429_);
v_extraFacts_2430_ = lean_ctor_get(v_params_2218_, 4);
lean_inc_ref(v_extraFacts_2430_);
v_symPrios_2431_ = lean_ctor_get(v_params_2218_, 5);
lean_inc_ref(v_symPrios_2431_);
v_norm_2432_ = lean_ctor_get(v_params_2218_, 6);
lean_inc_ref(v_norm_2432_);
v_normProcs_2433_ = lean_ctor_get(v_params_2218_, 7);
lean_inc_ref(v_normProcs_2433_);
v_anchorRefs_x3f_2434_ = lean_ctor_get(v_params_2218_, 8);
lean_inc(v_anchorRefs_x3f_2434_);
lean_dec_ref(v_params_2218_);
v_size_2435_ = lean_ctor_get(v_extra_2362_, 2);
lean_inc(v_size_2435_);
v___y_2267_ = v___y_2347_;
v___y_2268_ = v_config_2427_;
v___y_2269_ = v___y_2338_;
v___y_2270_ = v___y_2348_;
v___y_2271_ = v___y_2345_;
v___y_2272_ = v_extraFacts_2430_;
v___y_2273_ = v_size_2435_;
v___y_2274_ = v_norm_2432_;
v___y_2275_ = v___y_2341_;
v___y_2276_ = v___y_2346_;
v___y_2277_ = v_extraInj_2429_;
v___y_2278_ = v_extra_2362_;
v___y_2279_ = v_normProcs_2433_;
v___y_2280_ = v_symPrios_2431_;
v___y_2281_ = v_anchorRefs_x3f_2434_;
v___y_2282_ = v_extensions_2428_;
goto v___jp_2266_;
}
case 1:
{
lean_object* v_config_2436_; lean_object* v_extensions_2437_; lean_object* v_extraInj_2438_; lean_object* v_extraFacts_2439_; lean_object* v_symPrios_2440_; lean_object* v_norm_2441_; lean_object* v_normProcs_2442_; lean_object* v_anchorRefs_x3f_2443_; lean_object* v_size_2444_; 
v_config_2436_ = lean_ctor_get(v_params_2218_, 0);
lean_inc_ref(v_config_2436_);
v_extensions_2437_ = lean_ctor_get(v_params_2218_, 1);
lean_inc_ref(v_extensions_2437_);
v_extraInj_2438_ = lean_ctor_get(v_params_2218_, 3);
lean_inc_ref(v_extraInj_2438_);
v_extraFacts_2439_ = lean_ctor_get(v_params_2218_, 4);
lean_inc_ref(v_extraFacts_2439_);
v_symPrios_2440_ = lean_ctor_get(v_params_2218_, 5);
lean_inc_ref(v_symPrios_2440_);
v_norm_2441_ = lean_ctor_get(v_params_2218_, 6);
lean_inc_ref(v_norm_2441_);
v_normProcs_2442_ = lean_ctor_get(v_params_2218_, 7);
lean_inc_ref(v_normProcs_2442_);
v_anchorRefs_x3f_2443_ = lean_ctor_get(v_params_2218_, 8);
lean_inc(v_anchorRefs_x3f_2443_);
lean_dec_ref(v_params_2218_);
v_size_2444_ = lean_ctor_get(v_extra_2362_, 2);
lean_inc(v_size_2444_);
v___y_2267_ = v___y_2347_;
v___y_2268_ = v_config_2436_;
v___y_2269_ = v___y_2338_;
v___y_2270_ = v___y_2348_;
v___y_2271_ = v___y_2345_;
v___y_2272_ = v_extraFacts_2439_;
v___y_2273_ = v_size_2444_;
v___y_2274_ = v_norm_2441_;
v___y_2275_ = v___y_2341_;
v___y_2276_ = v___y_2346_;
v___y_2277_ = v_extraInj_2438_;
v___y_2278_ = v_extra_2362_;
v___y_2279_ = v_normProcs_2442_;
v___y_2280_ = v_symPrios_2440_;
v___y_2281_ = v_anchorRefs_x3f_2443_;
v___y_2282_ = v_extensions_2437_;
goto v___jp_2266_;
}
default: 
{
lean_object* v_config_2445_; lean_object* v_extensions_2446_; lean_object* v_extraInj_2447_; lean_object* v_extraFacts_2448_; lean_object* v_symPrios_2449_; lean_object* v_norm_2450_; lean_object* v_normProcs_2451_; lean_object* v_anchorRefs_x3f_2452_; lean_object* v_size_2453_; 
v_config_2445_ = lean_ctor_get(v_params_2218_, 0);
lean_inc_ref(v_config_2445_);
v_extensions_2446_ = lean_ctor_get(v_params_2218_, 1);
lean_inc_ref(v_extensions_2446_);
v_extraInj_2447_ = lean_ctor_get(v_params_2218_, 3);
lean_inc_ref(v_extraInj_2447_);
v_extraFacts_2448_ = lean_ctor_get(v_params_2218_, 4);
lean_inc_ref(v_extraFacts_2448_);
v_symPrios_2449_ = lean_ctor_get(v_params_2218_, 5);
lean_inc_ref(v_symPrios_2449_);
v_norm_2450_ = lean_ctor_get(v_params_2218_, 6);
lean_inc_ref(v_norm_2450_);
v_normProcs_2451_ = lean_ctor_get(v_params_2218_, 7);
lean_inc_ref(v_normProcs_2451_);
v_anchorRefs_x3f_2452_ = lean_ctor_get(v_params_2218_, 8);
lean_inc(v_anchorRefs_x3f_2452_);
lean_dec_ref(v_params_2218_);
v_size_2453_ = lean_ctor_get(v_extra_2362_, 2);
lean_inc(v_size_2453_);
v___y_2231_ = v_config_2445_;
v___y_2232_ = v___y_2338_;
v___y_2233_ = v_extraInj_2447_;
v___y_2234_ = v_extraFacts_2448_;
v___y_2235_ = v_extra_2362_;
v___y_2236_ = v_size_2453_;
v___y_2237_ = v_normProcs_2451_;
v___y_2238_ = v_norm_2450_;
v___y_2239_ = v_symPrios_2449_;
v___y_2240_ = v___y_2341_;
v___y_2241_ = v_anchorRefs_x3f_2452_;
v___y_2242_ = v_extensions_2446_;
v___y_2243_ = v___y_2345_;
v___y_2244_ = v___y_2346_;
v___y_2245_ = v___y_2347_;
v___y_2246_ = v___y_2348_;
goto v___jp_2230_;
}
}
}
}
}
v___jp_2454_:
{
lean_object* v___x_2462_; uint8_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___f_2465_; lean_object* v___x_2466_; 
v___x_2462_ = lean_box(0);
v___x_2463_ = 1;
v___x_2464_ = lean_box(v___x_2463_);
lean_inc(v_p_2219_);
v___f_2465_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2465_, 0, v_p_2219_);
lean_closure_set(v___f_2465_, 1, v_term_2221_);
lean_closure_set(v___f_2465_, 2, v___x_2462_);
lean_closure_set(v___f_2465_, 3, v___x_2464_);
lean_inc(v___y_2461_);
lean_inc_ref(v___y_2460_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc(v___y_2457_);
lean_inc_ref(v___y_2456_);
v___x_2466_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2465_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2511_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2511_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2511_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
if (lean_obj_tag(v_a_2467_) == 1)
{
lean_object* v_val_2471_; lean_object* v_fst_2472_; lean_object* v_snd_2473_; lean_object* v___x_2474_; 
lean_del_object(v___x_2469_);
v_val_2471_ = lean_ctor_get(v_a_2467_, 0);
lean_inc(v_val_2471_);
lean_dec_ref(v_a_2467_);
v_fst_2472_ = lean_ctor_get(v_val_2471_, 0);
lean_inc(v_fst_2472_);
v_snd_2473_ = lean_ctor_get(v_val_2471_, 1);
lean_inc(v_snd_2473_);
lean_dec(v_val_2471_);
lean_inc(v___y_2461_);
lean_inc_ref(v___y_2460_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc(v_snd_2473_);
v___x_2474_ = lean_infer_type(v_snd_2473_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref(v___x_2474_);
lean_inc(v___y_2461_);
lean_inc_ref(v___y_2460_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc(v_a_2475_);
v___x_2476_ = l_Lean_Meta_isProp(v_a_2475_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___f_2480_; uint8_t v___x_2481_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref(v___x_2476_);
v___x_2478_ = lean_box(v___x_2463_);
v___x_2479_ = lean_box(v_minIndexable_2222_);
lean_inc(v_snd_2473_);
lean_inc(v_fst_2472_);
lean_inc_ref(v_params_2218_);
v___f_2480_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2480_, 0, v_params_2218_);
lean_closure_set(v___f_2480_, 1, v_p_2219_);
lean_closure_set(v___f_2480_, 2, v_fst_2472_);
lean_closure_set(v___f_2480_, 3, v_snd_2473_);
lean_closure_set(v___f_2480_, 4, v___x_2478_);
lean_closure_set(v___f_2480_, 5, v___x_2479_);
v___x_2481_ = lean_unbox(v_a_2477_);
lean_dec(v_a_2477_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec_ref(v___f_2480_);
lean_dec(v_a_2475_);
lean_dec(v_snd_2473_);
lean_dec(v_fst_2472_);
lean_dec(v_kind_2455_);
lean_dec(v_mod_x3f_2220_);
lean_dec_ref(v_params_2218_);
v___x_2482_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2483_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2482_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
else
{
v___y_2338_ = v_kind_2455_;
v___y_2339_ = v_a_2475_;
v___y_2340_ = v_fst_2472_;
v___y_2341_ = v___f_2480_;
v___y_2342_ = v_snd_2473_;
v___y_2343_ = v___y_2456_;
v___y_2344_ = v___y_2457_;
v___y_2345_ = v___y_2458_;
v___y_2346_ = v___y_2459_;
v___y_2347_ = v___y_2460_;
v___y_2348_ = v___y_2461_;
goto v___jp_2337_;
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_a_2475_);
lean_dec(v_snd_2473_);
lean_dec(v_fst_2472_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v_kind_2455_);
lean_dec(v_mod_x3f_2220_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v_a_2492_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2476_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2476_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_snd_2473_);
lean_dec(v_fst_2472_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v_kind_2455_);
lean_dec(v_mod_x3f_2220_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v_a_2500_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2474_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2474_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v___x_2509_; 
lean_dec(v_a_2467_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v_kind_2455_);
lean_dec(v_mod_x3f_2220_);
lean_dec(v_p_2219_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v_params_2218_);
v___x_2509_ = v___x_2469_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_params_2218_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v_kind_2455_);
lean_dec(v_mod_x3f_2220_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v_a_2512_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2466_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2466_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
v___jp_2520_:
{
lean_object* v___x_2527_; 
v___x_2527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_kind_2455_ = v___x_2527_;
v___y_2456_ = v___y_2521_;
v___y_2457_ = v___y_2522_;
v___y_2458_ = v___y_2523_;
v___y_2459_ = v___y_2524_;
v___y_2460_ = v___y_2525_;
v___y_2461_ = v___y_2526_;
goto v___jp_2454_;
}
v_resetjp_2544_:
{
lean_object* v_ref_2547_; lean_object* v___x_2549_; 
v_ref_2547_ = l_Lean_replaceRef(v_p_2219_, v_ref_2533_);
lean_dec(v_ref_2533_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 5, v_ref_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_fileName_2528_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_fileMap_2529_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v_options_2530_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v_currRecDepth_2531_);
lean_ctor_set(v_reuseFailAlloc_2618_, 4, v_maxRecDepth_2532_);
lean_ctor_set(v_reuseFailAlloc_2618_, 5, v_ref_2547_);
lean_ctor_set(v_reuseFailAlloc_2618_, 6, v_currNamespace_2534_);
lean_ctor_set(v_reuseFailAlloc_2618_, 7, v_openDecls_2535_);
lean_ctor_set(v_reuseFailAlloc_2618_, 8, v_initHeartbeats_2536_);
lean_ctor_set(v_reuseFailAlloc_2618_, 9, v_maxHeartbeats_2537_);
lean_ctor_set(v_reuseFailAlloc_2618_, 10, v_quotContext_2538_);
lean_ctor_set(v_reuseFailAlloc_2618_, 11, v_currMacroScope_2539_);
lean_ctor_set(v_reuseFailAlloc_2618_, 12, v_cancelTk_x3f_2541_);
lean_ctor_set(v_reuseFailAlloc_2618_, 13, v_inheritedTraceOptions_2543_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*14, v_diag_2540_);
lean_ctor_set_uint8(v_reuseFailAlloc_2618_, sizeof(void*)*14 + 1, v_suppressElabErrors_2542_);
v___x_2549_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; 
v___x_2550_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2218_, v___x_2549_, v_a_2228_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_dec_ref(v___x_2550_);
if (lean_obj_tag(v_mod_x3f_2220_) == 1)
{
lean_object* v_val_2551_; lean_object* v___x_2552_; 
v_val_2551_ = lean_ctor_get(v_mod_x3f_2220_, 0);
lean_inc_ref(v___x_2549_);
lean_inc(v_val_2551_);
v___x_2552_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2551_, v___x_2549_, v_a_2228_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2552_);
switch(lean_obj_tag(v_a_2553_))
{
case 0:
{
lean_object* v_k_2571_; 
v_k_2571_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_k_2571_);
lean_dec_ref(v_a_2553_);
if (lean_obj_tag(v_k_2571_) == 9)
{
lean_dec_ref(v_mod_x3f_2220_);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v___y_2555_ = v_a_2223_;
v___y_2556_ = v_a_2224_;
v___y_2557_ = v_a_2225_;
v___y_2558_ = v_a_2226_;
v___y_2559_ = v___x_2549_;
v___y_2560_ = v_a_2228_;
goto v___jp_2554_;
}
else
{
v_kind_2455_ = v_k_2571_;
v___y_2456_ = v_a_2223_;
v___y_2457_ = v_a_2224_;
v___y_2458_ = v_a_2225_;
v___y_2459_ = v_a_2226_;
v___y_2460_ = v___x_2549_;
v___y_2461_ = v_a_2228_;
goto v___jp_2454_;
}
}
case 1:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v_a_2553_);
lean_dec_ref(v_mod_x3f_2220_);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v___x_2572_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2573_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2572_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v___x_2549_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec_ref(v___x_2549_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
case 3:
{
v___y_2521_ = v_a_2223_;
v___y_2522_ = v_a_2224_;
v___y_2523_ = v_a_2225_;
v___y_2524_ = v_a_2226_;
v___y_2525_ = v___x_2549_;
v___y_2526_ = v_a_2228_;
goto v___jp_2520_;
}
case 5:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec_ref(v_a_2553_);
lean_dec_ref(v_mod_x3f_2220_);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v___x_2582_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2583_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2582_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v___x_2549_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec_ref(v___x_2549_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
case 8:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec_ref(v_a_2553_);
lean_dec_ref(v_mod_x3f_2220_);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v___x_2592_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2593_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2592_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v___x_2549_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec_ref(v___x_2549_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
default: 
{
lean_dec(v_a_2553_);
lean_dec_ref(v_mod_x3f_2220_);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v___y_2555_ = v_a_2223_;
v___y_2556_ = v_a_2224_;
v___y_2557_ = v_a_2225_;
v___y_2558_ = v_a_2226_;
v___y_2559_ = v___x_2549_;
v___y_2560_ = v_a_2228_;
goto v___jp_2554_;
}
}
v___jp_2554_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v___x_2561_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2562_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2561_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
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
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec_ref(v_mod_x3f_2220_);
lean_dec_ref(v___x_2549_);
lean_dec(v_a_2228_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v_a_2602_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2552_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2552_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
v___y_2521_ = v_a_2223_;
v___y_2522_ = v_a_2224_;
v___y_2523_ = v_a_2225_;
v___y_2524_ = v_a_2226_;
v___y_2525_ = v___x_2549_;
v___y_2526_ = v_a_2228_;
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec_ref(v___x_2549_);
lean_dec(v_a_2228_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_term_2221_);
lean_dec(v_mod_x3f_2220_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v_a_2610_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2550_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2550_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2620_, lean_object* v_p_2621_, lean_object* v_mod_x3f_2622_, lean_object* v_term_2623_, lean_object* v_minIndexable_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
uint8_t v_minIndexable_boxed_2632_; lean_object* v_res_2633_; 
v_minIndexable_boxed_2632_ = lean_unbox(v_minIndexable_2624_);
v_res_2633_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2620_, v_p_2621_, v_mod_x3f_2622_, v_term_2623_, v_minIndexable_boxed_2632_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object* v_00_u03b1_2634_, lean_object* v_msg_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v_00_u03b1_2644_, lean_object* v_msg_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v_00_u03b1_2644_, v_msg_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object* v_msgData_2654_, lean_object* v_macroStack_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2654_, v_macroStack_2655_, v___y_2660_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object* v_msgData_2664_, lean_object* v_macroStack_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(v_msgData_2664_, v_macroStack_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2674_, lean_object* v_val_2675_, lean_object* v_____r_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v___x_2684_; lean_object* v_ext_2685_; lean_object* v_toEnvExtension_2686_; lean_object* v_env_2687_; lean_object* v_config_2688_; lean_object* v_extensions_2689_; lean_object* v_extra_2690_; lean_object* v_extraInj_2691_; lean_object* v_extraFacts_2692_; lean_object* v_symPrios_2693_; lean_object* v_norm_2694_; lean_object* v_normProcs_2695_; lean_object* v_anchorRefs_x3f_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2709_; 
v___x_2684_ = lean_st_ref_get(v___y_2682_);
v_ext_2685_ = lean_ctor_get(v_val_2675_, 1);
v_toEnvExtension_2686_ = lean_ctor_get(v_ext_2685_, 0);
v_env_2687_ = lean_ctor_get(v___x_2684_, 0);
lean_inc_ref(v_env_2687_);
lean_dec(v___x_2684_);
v_config_2688_ = lean_ctor_get(v_params_2674_, 0);
v_extensions_2689_ = lean_ctor_get(v_params_2674_, 1);
v_extra_2690_ = lean_ctor_get(v_params_2674_, 2);
v_extraInj_2691_ = lean_ctor_get(v_params_2674_, 3);
v_extraFacts_2692_ = lean_ctor_get(v_params_2674_, 4);
v_symPrios_2693_ = lean_ctor_get(v_params_2674_, 5);
v_norm_2694_ = lean_ctor_get(v_params_2674_, 6);
v_normProcs_2695_ = lean_ctor_get(v_params_2674_, 7);
v_anchorRefs_x3f_2696_ = lean_ctor_get(v_params_2674_, 8);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_params_2674_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2698_ = v_params_2674_;
v_isShared_2699_ = v_isSharedCheck_2709_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_anchorRefs_x3f_2696_);
lean_inc(v_normProcs_2695_);
lean_inc(v_norm_2694_);
lean_inc(v_symPrios_2693_);
lean_inc(v_extraFacts_2692_);
lean_inc(v_extraInj_2691_);
lean_inc(v_extra_2690_);
lean_inc(v_extensions_2689_);
lean_inc(v_config_2688_);
lean_dec(v_params_2674_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2709_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v_asyncMode_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v_asyncMode_2700_ = lean_ctor_get(v_toEnvExtension_2686_, 2);
v___x_2701_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2702_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2701_, v_val_2675_, v_env_2687_, v_asyncMode_2700_);
v___x_2703_ = lean_array_push(v_extensions_2689_, v___x_2702_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 1, v___x_2703_);
v___x_2705_ = v___x_2698_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_config_2688_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_extra_2690_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_extraInj_2691_);
lean_ctor_set(v_reuseFailAlloc_2708_, 4, v_extraFacts_2692_);
lean_ctor_set(v_reuseFailAlloc_2708_, 5, v_symPrios_2693_);
lean_ctor_set(v_reuseFailAlloc_2708_, 6, v_norm_2694_);
lean_ctor_set(v_reuseFailAlloc_2708_, 7, v_normProcs_2695_);
lean_ctor_set(v_reuseFailAlloc_2708_, 8, v_anchorRefs_x3f_2696_);
v___x_2705_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
return v___x_2707_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2710_, lean_object* v_val_2711_, lean_object* v_____r_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2710_, v_val_2711_, v_____r_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec_ref(v_val_2711_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2721_, lean_object* v_id_2722_, uint8_t v_minIndexable_2723_, lean_object* v_as_x27_2724_, lean_object* v_b_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
if (lean_obj_tag(v_as_x27_2724_) == 0)
{
lean_object* v___x_2731_; 
lean_dec(v___y_2729_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_id_2722_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_b_2725_);
return v___x_2731_;
}
else
{
lean_object* v_head_2732_; lean_object* v_tail_2733_; lean_object* v_fileName_2734_; lean_object* v_fileMap_2735_; lean_object* v_options_2736_; lean_object* v_currRecDepth_2737_; lean_object* v_maxRecDepth_2738_; lean_object* v_ref_2739_; lean_object* v_currNamespace_2740_; lean_object* v_openDecls_2741_; lean_object* v_initHeartbeats_2742_; lean_object* v_maxHeartbeats_2743_; lean_object* v_quotContext_2744_; lean_object* v_currMacroScope_2745_; uint8_t v_diag_2746_; lean_object* v_cancelTk_x3f_2747_; uint8_t v_suppressElabErrors_2748_; lean_object* v_inheritedTraceOptions_2749_; uint8_t v___x_2750_; lean_object* v___x_2751_; lean_object* v_ref_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v_head_2732_ = lean_ctor_get(v_as_x27_2724_, 0);
lean_inc(v_head_2732_);
v_tail_2733_ = lean_ctor_get(v_as_x27_2724_, 1);
lean_inc(v_tail_2733_);
lean_dec_ref(v_as_x27_2724_);
v_fileName_2734_ = lean_ctor_get(v___y_2728_, 0);
v_fileMap_2735_ = lean_ctor_get(v___y_2728_, 1);
v_options_2736_ = lean_ctor_get(v___y_2728_, 2);
v_currRecDepth_2737_ = lean_ctor_get(v___y_2728_, 3);
v_maxRecDepth_2738_ = lean_ctor_get(v___y_2728_, 4);
v_ref_2739_ = lean_ctor_get(v___y_2728_, 5);
v_currNamespace_2740_ = lean_ctor_get(v___y_2728_, 6);
v_openDecls_2741_ = lean_ctor_get(v___y_2728_, 7);
v_initHeartbeats_2742_ = lean_ctor_get(v___y_2728_, 8);
v_maxHeartbeats_2743_ = lean_ctor_get(v___y_2728_, 9);
v_quotContext_2744_ = lean_ctor_get(v___y_2728_, 10);
v_currMacroScope_2745_ = lean_ctor_get(v___y_2728_, 11);
v_diag_2746_ = lean_ctor_get_uint8(v___y_2728_, sizeof(void*)*14);
v_cancelTk_x3f_2747_ = lean_ctor_get(v___y_2728_, 12);
v_suppressElabErrors_2748_ = lean_ctor_get_uint8(v___y_2728_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2749_ = lean_ctor_get(v___y_2728_, 13);
v___x_2750_ = 0;
v___x_2751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_2752_ = l_Lean_replaceRef(v_p_2721_, v_ref_2739_);
lean_inc_ref(v_inheritedTraceOptions_2749_);
lean_inc(v_cancelTk_x3f_2747_);
lean_inc(v_currMacroScope_2745_);
lean_inc(v_quotContext_2744_);
lean_inc(v_maxHeartbeats_2743_);
lean_inc(v_initHeartbeats_2742_);
lean_inc(v_openDecls_2741_);
lean_inc(v_currNamespace_2740_);
lean_inc(v_maxRecDepth_2738_);
lean_inc(v_currRecDepth_2737_);
lean_inc_ref(v_options_2736_);
lean_inc_ref(v_fileMap_2735_);
lean_inc_ref(v_fileName_2734_);
v___x_2753_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2753_, 0, v_fileName_2734_);
lean_ctor_set(v___x_2753_, 1, v_fileMap_2735_);
lean_ctor_set(v___x_2753_, 2, v_options_2736_);
lean_ctor_set(v___x_2753_, 3, v_currRecDepth_2737_);
lean_ctor_set(v___x_2753_, 4, v_maxRecDepth_2738_);
lean_ctor_set(v___x_2753_, 5, v_ref_2752_);
lean_ctor_set(v___x_2753_, 6, v_currNamespace_2740_);
lean_ctor_set(v___x_2753_, 7, v_openDecls_2741_);
lean_ctor_set(v___x_2753_, 8, v_initHeartbeats_2742_);
lean_ctor_set(v___x_2753_, 9, v_maxHeartbeats_2743_);
lean_ctor_set(v___x_2753_, 10, v_quotContext_2744_);
lean_ctor_set(v___x_2753_, 11, v_currMacroScope_2745_);
lean_ctor_set(v___x_2753_, 12, v_cancelTk_x3f_2747_);
lean_ctor_set(v___x_2753_, 13, v_inheritedTraceOptions_2749_);
lean_ctor_set_uint8(v___x_2753_, sizeof(void*)*14, v_diag_2746_);
lean_ctor_set_uint8(v___x_2753_, sizeof(void*)*14 + 1, v_suppressElabErrors_2748_);
lean_inc(v___y_2729_);
lean_inc(v___y_2727_);
lean_inc_ref(v___y_2726_);
lean_inc(v_id_2722_);
v___x_2754_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2725_, v_id_2722_, v_head_2732_, v___x_2751_, v_minIndexable_2723_, v___x_2750_, v___x_2750_, v___y_2726_, v___y_2727_, v___x_2753_, v___y_2729_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref(v___x_2754_);
v_as_x27_2724_ = v_tail_2733_;
v_b_2725_ = v_a_2755_;
goto _start;
}
else
{
lean_dec(v_tail_2733_);
lean_dec(v___y_2729_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_id_2722_);
return v___x_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2757_, lean_object* v_id_2758_, lean_object* v_minIndexable_2759_, lean_object* v_as_x27_2760_, lean_object* v_b_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
uint8_t v_minIndexable_boxed_2767_; lean_object* v_res_2768_; 
v_minIndexable_boxed_2767_ = lean_unbox(v_minIndexable_2759_);
v_res_2768_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2757_, v_id_2758_, v_minIndexable_boxed_2767_, v_as_x27_2760_, v_b_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v_p_2757_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
if (lean_obj_tag(v_a_2770_) == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = l_List_reverse___redArg(v_a_2771_);
return v___x_2772_;
}
else
{
lean_object* v_head_2773_; lean_object* v_tail_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2785_; 
v_head_2773_ = lean_ctor_get(v_a_2770_, 0);
v_tail_2774_ = lean_ctor_get(v_a_2770_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_a_2770_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2776_ = v_a_2770_;
v_isShared_2777_ = v_isSharedCheck_2785_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_tail_2774_);
lean_inc(v_head_2773_);
lean_dec(v_a_2770_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2785_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v_kind_2778_; uint8_t v___x_2779_; 
v_kind_2778_ = lean_ctor_get(v_head_2773_, 6);
v___x_2779_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2778_, v_k_2769_);
if (v___x_2779_ == 0)
{
lean_del_object(v___x_2776_);
lean_dec(v_head_2773_);
v_a_2770_ = v_tail_2774_;
goto _start;
}
else
{
lean_object* v___x_2782_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v_a_2771_);
v___x_2782_ = v___x_2776_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_head_2773_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_a_2771_);
v___x_2782_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
v_a_2770_ = v_tail_2774_;
v_a_2771_ = v___x_2782_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2786_, v_a_2787_, v_a_2788_);
lean_dec(v_k_2786_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_2790_, lean_object* v_msg_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_fileName_2799_; lean_object* v_fileMap_2800_; lean_object* v_options_2801_; lean_object* v_currRecDepth_2802_; lean_object* v_maxRecDepth_2803_; lean_object* v_ref_2804_; lean_object* v_currNamespace_2805_; lean_object* v_openDecls_2806_; lean_object* v_initHeartbeats_2807_; lean_object* v_maxHeartbeats_2808_; lean_object* v_quotContext_2809_; lean_object* v_currMacroScope_2810_; uint8_t v_diag_2811_; lean_object* v_cancelTk_x3f_2812_; uint8_t v_suppressElabErrors_2813_; lean_object* v_inheritedTraceOptions_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2823_; 
v_fileName_2799_ = lean_ctor_get(v___y_2796_, 0);
v_fileMap_2800_ = lean_ctor_get(v___y_2796_, 1);
v_options_2801_ = lean_ctor_get(v___y_2796_, 2);
v_currRecDepth_2802_ = lean_ctor_get(v___y_2796_, 3);
v_maxRecDepth_2803_ = lean_ctor_get(v___y_2796_, 4);
v_ref_2804_ = lean_ctor_get(v___y_2796_, 5);
v_currNamespace_2805_ = lean_ctor_get(v___y_2796_, 6);
v_openDecls_2806_ = lean_ctor_get(v___y_2796_, 7);
v_initHeartbeats_2807_ = lean_ctor_get(v___y_2796_, 8);
v_maxHeartbeats_2808_ = lean_ctor_get(v___y_2796_, 9);
v_quotContext_2809_ = lean_ctor_get(v___y_2796_, 10);
v_currMacroScope_2810_ = lean_ctor_get(v___y_2796_, 11);
v_diag_2811_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*14);
v_cancelTk_x3f_2812_ = lean_ctor_get(v___y_2796_, 12);
v_suppressElabErrors_2813_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2814_ = lean_ctor_get(v___y_2796_, 13);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___y_2796_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2816_ = v___y_2796_;
v_isShared_2817_ = v_isSharedCheck_2823_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_inheritedTraceOptions_2814_);
lean_inc(v_cancelTk_x3f_2812_);
lean_inc(v_currMacroScope_2810_);
lean_inc(v_quotContext_2809_);
lean_inc(v_maxHeartbeats_2808_);
lean_inc(v_initHeartbeats_2807_);
lean_inc(v_openDecls_2806_);
lean_inc(v_currNamespace_2805_);
lean_inc(v_ref_2804_);
lean_inc(v_maxRecDepth_2803_);
lean_inc(v_currRecDepth_2802_);
lean_inc(v_options_2801_);
lean_inc(v_fileMap_2800_);
lean_inc(v_fileName_2799_);
lean_dec(v___y_2796_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2823_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v_ref_2818_; lean_object* v___x_2820_; 
v_ref_2818_ = l_Lean_replaceRef(v_ref_2790_, v_ref_2804_);
lean_dec(v_ref_2804_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 5, v_ref_2818_);
v___x_2820_ = v___x_2816_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_fileName_2799_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_fileMap_2800_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_options_2801_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_currRecDepth_2802_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_maxRecDepth_2803_);
lean_ctor_set(v_reuseFailAlloc_2822_, 5, v_ref_2818_);
lean_ctor_set(v_reuseFailAlloc_2822_, 6, v_currNamespace_2805_);
lean_ctor_set(v_reuseFailAlloc_2822_, 7, v_openDecls_2806_);
lean_ctor_set(v_reuseFailAlloc_2822_, 8, v_initHeartbeats_2807_);
lean_ctor_set(v_reuseFailAlloc_2822_, 9, v_maxHeartbeats_2808_);
lean_ctor_set(v_reuseFailAlloc_2822_, 10, v_quotContext_2809_);
lean_ctor_set(v_reuseFailAlloc_2822_, 11, v_currMacroScope_2810_);
lean_ctor_set(v_reuseFailAlloc_2822_, 12, v_cancelTk_x3f_2812_);
lean_ctor_set(v_reuseFailAlloc_2822_, 13, v_inheritedTraceOptions_2814_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, sizeof(void*)*14, v_diag_2811_);
lean_ctor_set_uint8(v_reuseFailAlloc_2822_, sizeof(void*)*14 + 1, v_suppressElabErrors_2813_);
v___x_2820_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___x_2820_, v___y_2797_);
lean_dec_ref(v___x_2820_);
return v___x_2821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_2824_, lean_object* v_msg_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_2824_, v_msg_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec(v_ref_2824_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_2834_, lean_object* v_id_2835_, uint8_t v_minIndexable_2836_, lean_object* v_as_x27_2837_, lean_object* v_b_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
if (lean_obj_tag(v_as_x27_2837_) == 0)
{
lean_object* v___x_2844_; 
lean_dec(v___y_2842_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v_id_2835_);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v_b_2838_);
return v___x_2844_;
}
else
{
lean_object* v_head_2845_; lean_object* v_tail_2846_; lean_object* v_fileName_2847_; lean_object* v_fileMap_2848_; lean_object* v_options_2849_; lean_object* v_currRecDepth_2850_; lean_object* v_maxRecDepth_2851_; lean_object* v_ref_2852_; lean_object* v_currNamespace_2853_; lean_object* v_openDecls_2854_; lean_object* v_initHeartbeats_2855_; lean_object* v_maxHeartbeats_2856_; lean_object* v_quotContext_2857_; lean_object* v_currMacroScope_2858_; uint8_t v_diag_2859_; lean_object* v_cancelTk_x3f_2860_; uint8_t v_suppressElabErrors_2861_; lean_object* v_inheritedTraceOptions_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; lean_object* v_ref_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_head_2845_ = lean_ctor_get(v_as_x27_2837_, 0);
lean_inc(v_head_2845_);
v_tail_2846_ = lean_ctor_get(v_as_x27_2837_, 1);
lean_inc(v_tail_2846_);
lean_dec_ref(v_as_x27_2837_);
v_fileName_2847_ = lean_ctor_get(v___y_2841_, 0);
v_fileMap_2848_ = lean_ctor_get(v___y_2841_, 1);
v_options_2849_ = lean_ctor_get(v___y_2841_, 2);
v_currRecDepth_2850_ = lean_ctor_get(v___y_2841_, 3);
v_maxRecDepth_2851_ = lean_ctor_get(v___y_2841_, 4);
v_ref_2852_ = lean_ctor_get(v___y_2841_, 5);
v_currNamespace_2853_ = lean_ctor_get(v___y_2841_, 6);
v_openDecls_2854_ = lean_ctor_get(v___y_2841_, 7);
v_initHeartbeats_2855_ = lean_ctor_get(v___y_2841_, 8);
v_maxHeartbeats_2856_ = lean_ctor_get(v___y_2841_, 9);
v_quotContext_2857_ = lean_ctor_get(v___y_2841_, 10);
v_currMacroScope_2858_ = lean_ctor_get(v___y_2841_, 11);
v_diag_2859_ = lean_ctor_get_uint8(v___y_2841_, sizeof(void*)*14);
v_cancelTk_x3f_2860_ = lean_ctor_get(v___y_2841_, 12);
v_suppressElabErrors_2861_ = lean_ctor_get_uint8(v___y_2841_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2862_ = lean_ctor_get(v___y_2841_, 13);
v___x_2863_ = 0;
v___x_2864_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2865_ = 1;
v_ref_2866_ = l_Lean_replaceRef(v_p_2834_, v_ref_2852_);
lean_inc_ref(v_inheritedTraceOptions_2862_);
lean_inc(v_cancelTk_x3f_2860_);
lean_inc(v_currMacroScope_2858_);
lean_inc(v_quotContext_2857_);
lean_inc(v_maxHeartbeats_2856_);
lean_inc(v_initHeartbeats_2855_);
lean_inc(v_openDecls_2854_);
lean_inc(v_currNamespace_2853_);
lean_inc(v_maxRecDepth_2851_);
lean_inc(v_currRecDepth_2850_);
lean_inc_ref(v_options_2849_);
lean_inc_ref(v_fileMap_2848_);
lean_inc_ref(v_fileName_2847_);
v___x_2867_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2867_, 0, v_fileName_2847_);
lean_ctor_set(v___x_2867_, 1, v_fileMap_2848_);
lean_ctor_set(v___x_2867_, 2, v_options_2849_);
lean_ctor_set(v___x_2867_, 3, v_currRecDepth_2850_);
lean_ctor_set(v___x_2867_, 4, v_maxRecDepth_2851_);
lean_ctor_set(v___x_2867_, 5, v_ref_2866_);
lean_ctor_set(v___x_2867_, 6, v_currNamespace_2853_);
lean_ctor_set(v___x_2867_, 7, v_openDecls_2854_);
lean_ctor_set(v___x_2867_, 8, v_initHeartbeats_2855_);
lean_ctor_set(v___x_2867_, 9, v_maxHeartbeats_2856_);
lean_ctor_set(v___x_2867_, 10, v_quotContext_2857_);
lean_ctor_set(v___x_2867_, 11, v_currMacroScope_2858_);
lean_ctor_set(v___x_2867_, 12, v_cancelTk_x3f_2860_);
lean_ctor_set(v___x_2867_, 13, v_inheritedTraceOptions_2862_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*14, v_diag_2859_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*14 + 1, v_suppressElabErrors_2861_);
lean_inc(v___y_2842_);
lean_inc(v___y_2840_);
lean_inc_ref(v___y_2839_);
lean_inc(v_id_2835_);
v___x_2868_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2838_, v_id_2835_, v_head_2845_, v___x_2864_, v_minIndexable_2836_, v___x_2863_, v___x_2865_, v___y_2839_, v___y_2840_, v___x_2867_, v___y_2842_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref(v___x_2868_);
v_as_x27_2837_ = v_tail_2846_;
v_b_2838_ = v_a_2869_;
goto _start;
}
else
{
lean_dec(v_tail_2846_);
lean_dec(v___y_2842_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v_id_2835_);
return v___x_2868_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_2871_, lean_object* v_id_2872_, lean_object* v_minIndexable_2873_, lean_object* v_as_x27_2874_, lean_object* v_b_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
uint8_t v_minIndexable_boxed_2881_; lean_object* v_res_2882_; 
v_minIndexable_boxed_2881_ = lean_unbox(v_minIndexable_2873_);
v_res_2882_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_2871_, v_id_2872_, v_minIndexable_boxed_2881_, v_as_x27_2874_, v_b_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v_p_2871_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg(lean_object* v_ref_2883_, lean_object* v_msgData_2884_, uint8_t v_severity_2885_, uint8_t v_isSilent_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___y_2893_; lean_object* v___y_2894_; uint8_t v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; uint8_t v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; uint8_t v___y_2932_; uint8_t v___y_2933_; lean_object* v___y_2934_; uint8_t v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2954_; lean_object* v___y_2955_; uint8_t v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; uint8_t v___y_2959_; uint8_t v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; uint8_t v___y_2968_; lean_object* v___y_2969_; uint8_t v___y_2970_; uint8_t v___y_2971_; uint8_t v___x_2976_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; uint8_t v___y_2982_; uint8_t v___y_2983_; uint8_t v___y_2984_; uint8_t v___y_2986_; uint8_t v___x_3001_; 
v___x_2976_ = 2;
v___x_3001_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2885_, v___x_2976_);
if (v___x_3001_ == 0)
{
v___y_2986_ = v___x_3001_;
goto v___jp_2985_;
}
else
{
uint8_t v___x_3002_; 
lean_inc_ref(v_msgData_2884_);
v___x_3002_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2884_);
v___y_2986_ = v___x_3002_;
goto v___jp_2985_;
}
v___jp_2892_:
{
lean_object* v___x_2902_; lean_object* v_currNamespace_2903_; lean_object* v_openDecls_2904_; lean_object* v_env_2905_; lean_object* v_nextMacroScope_2906_; lean_object* v_ngen_2907_; lean_object* v_auxDeclNGen_2908_; lean_object* v_traceState_2909_; lean_object* v_cache_2910_; lean_object* v_messages_2911_; lean_object* v_infoState_2912_; lean_object* v_snapshotTasks_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2927_; 
v___x_2902_ = lean_st_ref_take(v___y_2901_);
v_currNamespace_2903_ = lean_ctor_get(v___y_2900_, 6);
lean_inc(v_currNamespace_2903_);
v_openDecls_2904_ = lean_ctor_get(v___y_2900_, 7);
lean_inc(v_openDecls_2904_);
lean_dec_ref(v___y_2900_);
v_env_2905_ = lean_ctor_get(v___x_2902_, 0);
v_nextMacroScope_2906_ = lean_ctor_get(v___x_2902_, 1);
v_ngen_2907_ = lean_ctor_get(v___x_2902_, 2);
v_auxDeclNGen_2908_ = lean_ctor_get(v___x_2902_, 3);
v_traceState_2909_ = lean_ctor_get(v___x_2902_, 4);
v_cache_2910_ = lean_ctor_get(v___x_2902_, 5);
v_messages_2911_ = lean_ctor_get(v___x_2902_, 6);
v_infoState_2912_ = lean_ctor_get(v___x_2902_, 7);
v_snapshotTasks_2913_ = lean_ctor_get(v___x_2902_, 8);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2915_ = v___x_2902_;
v_isShared_2916_ = v_isSharedCheck_2927_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_snapshotTasks_2913_);
lean_inc(v_infoState_2912_);
lean_inc(v_messages_2911_);
lean_inc(v_cache_2910_);
lean_inc(v_traceState_2909_);
lean_inc(v_auxDeclNGen_2908_);
lean_inc(v_ngen_2907_);
lean_inc(v_nextMacroScope_2906_);
lean_inc(v_env_2905_);
lean_dec(v___x_2902_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2927_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v_currNamespace_2903_);
lean_ctor_set(v___x_2917_, 1, v_openDecls_2904_);
v___x_2918_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v___y_2894_);
v___x_2919_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2919_, 0, v___y_2896_);
lean_ctor_set(v___x_2919_, 1, v___y_2898_);
lean_ctor_set(v___x_2919_, 2, v___y_2897_);
lean_ctor_set(v___x_2919_, 3, v___y_2893_);
lean_ctor_set(v___x_2919_, 4, v___x_2918_);
lean_ctor_set_uint8(v___x_2919_, sizeof(void*)*5, v___y_2899_);
lean_ctor_set_uint8(v___x_2919_, sizeof(void*)*5 + 1, v___y_2895_);
lean_ctor_set_uint8(v___x_2919_, sizeof(void*)*5 + 2, v_isSilent_2886_);
v___x_2920_ = l_Lean_MessageLog_add(v___x_2919_, v_messages_2911_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 6, v___x_2920_);
v___x_2922_ = v___x_2915_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_env_2905_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_nextMacroScope_2906_);
lean_ctor_set(v_reuseFailAlloc_2926_, 2, v_ngen_2907_);
lean_ctor_set(v_reuseFailAlloc_2926_, 3, v_auxDeclNGen_2908_);
lean_ctor_set(v_reuseFailAlloc_2926_, 4, v_traceState_2909_);
lean_ctor_set(v_reuseFailAlloc_2926_, 5, v_cache_2910_);
lean_ctor_set(v_reuseFailAlloc_2926_, 6, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_2926_, 7, v_infoState_2912_);
lean_ctor_set(v_reuseFailAlloc_2926_, 8, v_snapshotTasks_2913_);
v___x_2922_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = lean_st_ref_set(v___y_2901_, v___x_2922_);
v___x_2924_ = lean_box(0);
v___x_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
return v___x_2925_;
}
}
}
v___jp_2928_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2952_; 
v___x_2937_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2884_);
v___x_2938_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_2937_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2941_ = v___x_2938_;
v_isShared_2942_ = v_isSharedCheck_2952_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2938_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2952_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
lean_inc_ref(v___y_2934_);
v___x_2943_ = l_Lean_FileMap_toPosition(v___y_2934_, v___y_2930_);
lean_dec(v___y_2930_);
v___x_2944_ = l_Lean_FileMap_toPosition(v___y_2934_, v___y_2936_);
lean_dec(v___y_2936_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
v___x_2946_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_2933_ == 0)
{
lean_del_object(v___x_2941_);
lean_dec_ref(v___y_2929_);
v___y_2893_ = v___x_2946_;
v___y_2894_ = v_a_2939_;
v___y_2895_ = v___y_2932_;
v___y_2896_ = v___y_2931_;
v___y_2897_ = v___x_2945_;
v___y_2898_ = v___x_2943_;
v___y_2899_ = v___y_2935_;
v___y_2900_ = v___y_2889_;
v___y_2901_ = v___y_2890_;
goto v___jp_2892_;
}
else
{
uint8_t v___x_2947_; 
lean_inc(v_a_2939_);
v___x_2947_ = l_Lean_MessageData_hasTag(v___y_2929_, v_a_2939_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
lean_dec_ref(v___x_2945_);
lean_dec_ref(v___x_2943_);
lean_dec(v_a_2939_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2889_);
v___x_2948_ = lean_box(0);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v___x_2948_);
v___x_2950_ = v___x_2941_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
else
{
lean_del_object(v___x_2941_);
v___y_2893_ = v___x_2946_;
v___y_2894_ = v_a_2939_;
v___y_2895_ = v___y_2932_;
v___y_2896_ = v___y_2931_;
v___y_2897_ = v___x_2945_;
v___y_2898_ = v___x_2943_;
v___y_2899_ = v___y_2935_;
v___y_2900_ = v___y_2889_;
v___y_2901_ = v___y_2890_;
goto v___jp_2892_;
}
}
}
}
v___jp_2953_:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_Syntax_getTailPos_x3f(v___y_2955_, v___y_2960_);
lean_dec(v___y_2955_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_inc(v___y_2961_);
v___y_2929_ = v___y_2954_;
v___y_2930_ = v___y_2961_;
v___y_2931_ = v___y_2957_;
v___y_2932_ = v___y_2956_;
v___y_2933_ = v___y_2959_;
v___y_2934_ = v___y_2958_;
v___y_2935_ = v___y_2960_;
v___y_2936_ = v___y_2961_;
goto v___jp_2928_;
}
else
{
lean_object* v_val_2963_; 
v_val_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_val_2963_);
lean_dec_ref(v___x_2962_);
v___y_2929_ = v___y_2954_;
v___y_2930_ = v___y_2961_;
v___y_2931_ = v___y_2957_;
v___y_2932_ = v___y_2956_;
v___y_2933_ = v___y_2959_;
v___y_2934_ = v___y_2958_;
v___y_2935_ = v___y_2960_;
v___y_2936_ = v_val_2963_;
goto v___jp_2928_;
}
}
v___jp_2964_:
{
lean_object* v_ref_2972_; lean_object* v___x_2973_; 
v_ref_2972_ = l_Lean_replaceRef(v_ref_2883_, v___y_2966_);
lean_dec(v___y_2966_);
v___x_2973_ = l_Lean_Syntax_getPos_x3f(v_ref_2972_, v___y_2970_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_unsigned_to_nat(0u);
v___y_2954_ = v___y_2965_;
v___y_2955_ = v_ref_2972_;
v___y_2956_ = v___y_2971_;
v___y_2957_ = v___y_2967_;
v___y_2958_ = v___y_2969_;
v___y_2959_ = v___y_2968_;
v___y_2960_ = v___y_2970_;
v___y_2961_ = v___x_2974_;
goto v___jp_2953_;
}
else
{
lean_object* v_val_2975_; 
v_val_2975_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_val_2975_);
lean_dec_ref(v___x_2973_);
v___y_2954_ = v___y_2965_;
v___y_2955_ = v_ref_2972_;
v___y_2956_ = v___y_2971_;
v___y_2957_ = v___y_2967_;
v___y_2958_ = v___y_2969_;
v___y_2959_ = v___y_2968_;
v___y_2960_ = v___y_2970_;
v___y_2961_ = v_val_2975_;
goto v___jp_2953_;
}
}
v___jp_2977_:
{
if (v___y_2984_ == 0)
{
v___y_2965_ = v___y_2978_;
v___y_2966_ = v___y_2979_;
v___y_2967_ = v___y_2980_;
v___y_2968_ = v___y_2982_;
v___y_2969_ = v___y_2981_;
v___y_2970_ = v___y_2983_;
v___y_2971_ = v_severity_2885_;
goto v___jp_2964_;
}
else
{
v___y_2965_ = v___y_2978_;
v___y_2966_ = v___y_2979_;
v___y_2967_ = v___y_2980_;
v___y_2968_ = v___y_2982_;
v___y_2969_ = v___y_2981_;
v___y_2970_ = v___y_2983_;
v___y_2971_ = v___x_2976_;
goto v___jp_2964_;
}
}
v___jp_2985_:
{
if (v___y_2986_ == 0)
{
lean_object* v_fileName_2987_; lean_object* v_fileMap_2988_; lean_object* v_options_2989_; lean_object* v_ref_2990_; uint8_t v_suppressElabErrors_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___f_2994_; uint8_t v___x_2995_; uint8_t v___x_2996_; 
v_fileName_2987_ = lean_ctor_get(v___y_2889_, 0);
v_fileMap_2988_ = lean_ctor_get(v___y_2889_, 1);
v_options_2989_ = lean_ctor_get(v___y_2889_, 2);
v_ref_2990_ = lean_ctor_get(v___y_2889_, 5);
v_suppressElabErrors_2991_ = lean_ctor_get_uint8(v___y_2889_, sizeof(void*)*14 + 1);
v___x_2992_ = lean_box(v___y_2986_);
v___x_2993_ = lean_box(v_suppressElabErrors_2991_);
v___f_2994_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2994_, 0, v___x_2992_);
lean_closure_set(v___f_2994_, 1, v___x_2993_);
v___x_2995_ = 1;
v___x_2996_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2885_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_inc_ref(v_fileMap_2988_);
lean_inc_ref(v_fileName_2987_);
lean_inc(v_ref_2990_);
v___y_2978_ = v___f_2994_;
v___y_2979_ = v_ref_2990_;
v___y_2980_ = v_fileName_2987_;
v___y_2981_ = v_fileMap_2988_;
v___y_2982_ = v_suppressElabErrors_2991_;
v___y_2983_ = v___y_2986_;
v___y_2984_ = v___x_2996_;
goto v___jp_2977_;
}
else
{
lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2997_ = l_Lean_warningAsError;
v___x_2998_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2989_, v___x_2997_);
lean_inc_ref(v_fileMap_2988_);
lean_inc_ref(v_fileName_2987_);
lean_inc(v_ref_2990_);
v___y_2978_ = v___f_2994_;
v___y_2979_ = v_ref_2990_;
v___y_2980_ = v_fileName_2987_;
v___y_2981_ = v_fileMap_2988_;
v___y_2982_ = v_suppressElabErrors_2991_;
v___y_2983_ = v___y_2986_;
v___y_2984_ = v___x_2998_;
goto v___jp_2977_;
}
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec_ref(v___y_2889_);
lean_dec_ref(v_msgData_2884_);
v___x_2999_ = lean_box(0);
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg___boxed(lean_object* v_ref_3003_, lean_object* v_msgData_3004_, lean_object* v_severity_3005_, lean_object* v_isSilent_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
uint8_t v_severity_boxed_3012_; uint8_t v_isSilent_boxed_3013_; lean_object* v_res_3014_; 
v_severity_boxed_3012_ = lean_unbox(v_severity_3005_);
v_isSilent_boxed_3013_ = lean_unbox(v_isSilent_3006_);
v_res_3014_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg(v_ref_3003_, v_msgData_3004_, v_severity_boxed_3012_, v_isSilent_boxed_3013_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v_ref_3003_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20(lean_object* v_msgData_3015_, uint8_t v_severity_3016_, uint8_t v_isSilent_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_ref_3025_; lean_object* v___x_3026_; 
v_ref_3025_ = lean_ctor_get(v___y_3022_, 5);
lean_inc(v_ref_3025_);
v___x_3026_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg(v_ref_3025_, v_msgData_3015_, v_severity_3016_, v_isSilent_3017_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v_ref_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20___boxed(lean_object* v_msgData_3027_, lean_object* v_severity_3028_, lean_object* v_isSilent_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
uint8_t v_severity_boxed_3037_; uint8_t v_isSilent_boxed_3038_; lean_object* v_res_3039_; 
v_severity_boxed_3037_ = lean_unbox(v_severity_3028_);
v_isSilent_boxed_3038_ = lean_unbox(v_isSilent_3029_);
v_res_3039_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20(v_msgData_3027_, v_severity_boxed_3037_, v_isSilent_boxed_3038_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18(lean_object* v_msgData_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
uint8_t v___x_3048_; uint8_t v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = 1;
v___x_3049_ = 0;
v___x_3050_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20(v_msgData_3040_, v___x_3048_, v___x_3049_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18___boxed(lean_object* v_msgData_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18(v_msgData_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg(lean_object* v_opt_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_options_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_options_3063_ = lean_ctor_get(v___y_3061_, 2);
v___x_3064_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_3063_, v_opt_3060_);
v___x_3065_ = lean_box(v___x_3064_);
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg___boxed(lean_object* v_opt_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg(v_opt_3067_, v___y_3068_);
lean_dec_ref(v___y_3068_);
lean_dec_ref(v_opt_3067_);
return v_res_3070_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__0));
v___x_3073_ = l_Lean_stringToMessageData(v___x_3072_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__2));
v___x_3076_ = l_Lean_stringToMessageData(v___x_3075_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_id_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
lean_object* v___x_3085_; lean_object* v_env_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3108_; 
v___x_3085_ = lean_st_ref_get(v___y_3083_);
v_env_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc_ref(v_env_3086_);
lean_dec(v___x_3085_);
v___x_3087_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3088_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg(v___x_3087_, v___y_3082_);
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3108_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3108_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
uint8_t v_isExporting_3098_; 
v_isExporting_3098_ = lean_ctor_get_uint8(v_env_3086_, sizeof(void*)*8);
lean_dec_ref(v_env_3086_);
if (v_isExporting_3098_ == 0)
{
lean_dec(v_a_3089_);
lean_dec_ref(v___y_3082_);
lean_dec(v_id_3077_);
goto v___jp_3093_;
}
else
{
uint8_t v___x_3099_; 
v___x_3099_ = l_Lean_isPrivateName(v_id_3077_);
if (v___x_3099_ == 0)
{
lean_dec(v_a_3089_);
lean_dec_ref(v___y_3082_);
lean_dec(v_id_3077_);
goto v___jp_3093_;
}
else
{
uint8_t v___x_3100_; 
v___x_3100_ = lean_unbox(v_a_3089_);
lean_dec(v_a_3089_);
if (v___x_3100_ == 0)
{
lean_dec_ref(v___y_3082_);
lean_dec(v_id_3077_);
goto v___jp_3093_;
}
else
{
lean_object* v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_del_object(v___x_3091_);
v___x_3101_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__1);
v___x_3102_ = 0;
v___x_3103_ = l_Lean_MessageData_ofConstName(v_id_3077_, v___x_3102_);
v___x_3104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3101_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___closed__3);
v___x_3106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3104_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18(v___x_3106_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
return v___x_3107_;
}
}
}
v___jp_3093_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = lean_box(0);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3094_);
v___x_3096_ = v___x_3091_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_id_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_id_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
return v_res_3117_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0(lean_object* v_x_3118_){
_start:
{
lean_object* v_fst_3119_; uint8_t v___x_3120_; 
v_fst_3119_ = lean_ctor_get(v_x_3118_, 0);
v___x_3120_ = l_Lean_isPrivateName(v_fst_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0___boxed(lean_object* v_x_3121_){
_start:
{
uint8_t v_res_3122_; lean_object* v_r_3123_; 
v_res_3122_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___lam__0(v_x_3121_);
lean_dec_ref(v_x_3121_);
v_r_3123_ = lean_box(v_res_3122_);
return v_r_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3125_, uint8_t v_enableLog_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v___x_3134_; lean_object* v_env_3135_; lean_object* v_options_3136_; lean_object* v_currNamespace_3137_; lean_object* v_openDecls_3138_; lean_object* v___x_3139_; lean_object* v_env_3140_; lean_object* v_res_3141_; 
v___x_3134_ = lean_st_ref_get(v___y_3132_);
v_env_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc_ref(v_env_3135_);
lean_dec(v___x_3134_);
v_options_3136_ = lean_ctor_get(v___y_3131_, 2);
v_currNamespace_3137_ = lean_ctor_get(v___y_3131_, 6);
v_openDecls_3138_ = lean_ctor_get(v___y_3131_, 7);
v___x_3139_ = lean_st_ref_get(v___y_3132_);
v_env_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc_ref(v_env_3140_);
lean_dec(v___x_3139_);
lean_inc(v_openDecls_3138_);
lean_inc(v_currNamespace_3137_);
v_res_3141_ = l_Lean_ResolveName_resolveGlobalName(v_env_3135_, v_options_3136_, v_currNamespace_3137_, v_openDecls_3138_, v_id_3125_);
if (v_enableLog_3126_ == 0)
{
lean_object* v___x_3142_; 
lean_dec_ref(v_env_3140_);
lean_dec_ref(v___y_3131_);
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v_res_3141_);
return v___x_3142_;
}
else
{
uint8_t v_isExporting_3143_; 
v_isExporting_3143_ = lean_ctor_get_uint8(v_env_3140_, sizeof(void*)*8);
lean_dec_ref(v_env_3140_);
if (v_isExporting_3143_ == 0)
{
lean_object* v___x_3144_; 
lean_dec_ref(v___y_3131_);
v___x_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3144_, 0, v_res_3141_);
return v___x_3144_;
}
else
{
lean_object* v___f_3145_; lean_object* v___x_3146_; 
v___f_3145_ = ((lean_object*)(l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___closed__0));
lean_inc(v_res_3141_);
v___x_3146_ = l_List_find_x3f___redArg(v___f_3145_, v_res_3141_);
if (lean_obj_tag(v___x_3146_) == 1)
{
lean_object* v_val_3147_; lean_object* v_fst_3148_; lean_object* v___x_3149_; 
v_val_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_val_3147_);
lean_dec_ref(v___x_3146_);
v_fst_3148_ = lean_ctor_get(v_val_3147_, 0);
lean_inc(v_fst_3148_);
lean_dec(v_val_3147_);
v___x_3149_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_fst_3148_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; 
v_unused_3157_ = lean_ctor_get(v___x_3149_, 0);
lean_dec(v_unused_3157_);
v___x_3151_ = v___x_3149_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_dec(v___x_3149_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v_res_3141_);
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_res_3141_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v_res_3141_);
v_a_3158_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3149_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3149_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_object* v___x_3166_; 
lean_dec(v___x_3146_);
lean_dec_ref(v___y_3131_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_res_3141_);
return v___x_3166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3167_, lean_object* v_enableLog_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v_enableLog_boxed_3176_; lean_object* v_res_3177_; 
v_enableLog_boxed_3176_ = lean_unbox(v_enableLog_3168_);
v_res_3177_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3167_, v_enableLog_boxed_3176_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3178_, lean_object* v_a_3179_){
_start:
{
if (lean_obj_tag(v_a_3178_) == 0)
{
lean_object* v___x_3180_; 
v___x_3180_ = l_List_reverse___redArg(v_a_3179_);
return v___x_3180_;
}
else
{
lean_object* v_head_3181_; lean_object* v_tail_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3193_; 
v_head_3181_ = lean_ctor_get(v_a_3178_, 0);
v_tail_3182_ = lean_ctor_get(v_a_3178_, 1);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_a_3178_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3184_ = v_a_3178_;
v_isShared_3185_ = v_isSharedCheck_3193_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_tail_3182_);
lean_inc(v_head_3181_);
lean_dec(v_a_3178_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3193_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_snd_3186_; uint8_t v___x_3187_; 
v_snd_3186_ = lean_ctor_get(v_head_3181_, 1);
v___x_3187_ = l_List_isEmpty___redArg(v_snd_3186_);
if (v___x_3187_ == 0)
{
lean_del_object(v___x_3184_);
lean_dec(v_head_3181_);
v_a_3178_ = v_tail_3182_;
goto _start;
}
else
{
lean_object* v___x_3190_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 1, v_a_3179_);
v___x_3190_ = v___x_3184_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_head_3181_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_a_3179_);
v___x_3190_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
v_a_3178_ = v_tail_3182_;
v_a_3179_ = v___x_3190_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3194_, lean_object* v_findLocalDecl_x3f_3195_, lean_object* v_n_3196_, lean_object* v_projs_3197_, uint8_t v_globalDeclFound_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___y_3207_; lean_object* v___y_3208_; uint8_t v_globalDeclFoundNext_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v_imported_3218_; lean_object* v_ctx_3219_; lean_object* v_scopes_3220_; lean_object* v_givenNameView_3221_; uint8_t v___y_3223_; 
v_imported_3218_ = lean_ctor_get(v_view_3194_, 1);
v_ctx_3219_ = lean_ctor_get(v_view_3194_, 2);
v_scopes_3220_ = lean_ctor_get(v_view_3194_, 3);
lean_inc(v_scopes_3220_);
lean_inc(v_ctx_3219_);
lean_inc(v_imported_3218_);
lean_inc(v_n_3196_);
v_givenNameView_3221_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3221_, 0, v_n_3196_);
lean_ctor_set(v_givenNameView_3221_, 1, v_imported_3218_);
lean_ctor_set(v_givenNameView_3221_, 2, v_ctx_3219_);
lean_ctor_set(v_givenNameView_3221_, 3, v_scopes_3220_);
if (v_globalDeclFound_3198_ == 0)
{
v___y_3223_ = v_globalDeclFound_3198_;
goto v___jp_3222_;
}
else
{
uint8_t v___x_3258_; 
v___x_3258_ = l_List_isEmpty___redArg(v_projs_3197_);
if (v___x_3258_ == 0)
{
v___y_3223_ = v_globalDeclFound_3198_;
goto v___jp_3222_;
}
else
{
uint8_t v___x_3259_; 
v___x_3259_ = 0;
v___y_3223_ = v___x_3259_;
goto v___jp_3222_;
}
}
v___jp_3206_:
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___y_3207_);
lean_ctor_set(v___x_3216_, 1, v_projs_3197_);
v_n_3196_ = v___y_3208_;
v_projs_3197_ = v___x_3216_;
v_globalDeclFound_3198_ = v_globalDeclFoundNext_3209_;
v___y_3199_ = v___y_3210_;
v___y_3200_ = v___y_3211_;
v___y_3201_ = v___y_3212_;
v___y_3202_ = v___y_3213_;
v___y_3203_ = v___y_3214_;
v___y_3204_ = v___y_3215_;
goto _start;
}
v___jp_3222_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = lean_box(v___y_3223_);
lean_inc_ref(v_findLocalDecl_x3f_3195_);
lean_inc_ref(v_givenNameView_3221_);
v___x_3225_ = lean_apply_2(v_findLocalDecl_x3f_3195_, v_givenNameView_3221_, v___x_3224_);
if (lean_obj_tag(v___x_3225_) == 0)
{
if (lean_obj_tag(v_n_3196_) == 1)
{
if (v_globalDeclFound_3198_ == 0)
{
lean_object* v_pre_3226_; lean_object* v_str_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v_pre_3226_ = lean_ctor_get(v_n_3196_, 0);
lean_inc(v_pre_3226_);
v_str_3227_ = lean_ctor_get(v_n_3196_, 1);
lean_inc_ref(v_str_3227_);
lean_dec_ref(v_n_3196_);
v___x_3228_ = l_Lean_MacroScopesView_review(v_givenNameView_3221_);
lean_inc_ref(v___y_3203_);
v___x_3229_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3228_, v_globalDeclFound_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3231_; lean_object* v_r_3232_; uint8_t v___x_3233_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref(v___x_3229_);
v___x_3231_ = lean_box(0);
v_r_3232_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3230_, v___x_3231_);
v___x_3233_ = l_List_isEmpty___redArg(v_r_3232_);
lean_dec(v_r_3232_);
if (v___x_3233_ == 0)
{
uint8_t v_globalDeclFoundNext_3234_; 
v_globalDeclFoundNext_3234_ = 1;
v___y_3207_ = v_str_3227_;
v___y_3208_ = v_pre_3226_;
v_globalDeclFoundNext_3209_ = v_globalDeclFoundNext_3234_;
v___y_3210_ = v___y_3199_;
v___y_3211_ = v___y_3200_;
v___y_3212_ = v___y_3201_;
v___y_3213_ = v___y_3202_;
v___y_3214_ = v___y_3203_;
v___y_3215_ = v___y_3204_;
goto v___jp_3206_;
}
else
{
v___y_3207_ = v_str_3227_;
v___y_3208_ = v_pre_3226_;
v_globalDeclFoundNext_3209_ = v_globalDeclFound_3198_;
v___y_3210_ = v___y_3199_;
v___y_3211_ = v___y_3200_;
v___y_3212_ = v___y_3201_;
v___y_3213_ = v___y_3202_;
v___y_3214_ = v___y_3203_;
v___y_3215_ = v___y_3204_;
goto v___jp_3206_;
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec_ref(v_str_3227_);
lean_dec(v_pre_3226_);
lean_dec_ref(v___y_3203_);
lean_dec(v_projs_3197_);
lean_dec_ref(v_findLocalDecl_x3f_3195_);
v_a_3235_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3229_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3229_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_object* v_pre_3243_; lean_object* v_str_3244_; 
lean_dec_ref(v_givenNameView_3221_);
v_pre_3243_ = lean_ctor_get(v_n_3196_, 0);
lean_inc(v_pre_3243_);
v_str_3244_ = lean_ctor_get(v_n_3196_, 1);
lean_inc_ref(v_str_3244_);
lean_dec_ref(v_n_3196_);
v___y_3207_ = v_str_3244_;
v___y_3208_ = v_pre_3243_;
v_globalDeclFoundNext_3209_ = v_globalDeclFound_3198_;
v___y_3210_ = v___y_3199_;
v___y_3211_ = v___y_3200_;
v___y_3212_ = v___y_3201_;
v___y_3213_ = v___y_3202_;
v___y_3214_ = v___y_3203_;
v___y_3215_ = v___y_3204_;
goto v___jp_3206_;
}
}
else
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
lean_dec_ref(v_givenNameView_3221_);
lean_dec_ref(v___y_3203_);
lean_dec(v_projs_3197_);
lean_dec(v_n_3196_);
lean_dec_ref(v_findLocalDecl_x3f_3195_);
v___x_3245_ = lean_box(0);
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
return v___x_3246_;
}
}
else
{
lean_object* v_val_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3257_; 
lean_dec_ref(v_givenNameView_3221_);
lean_dec_ref(v___y_3203_);
lean_dec(v_n_3196_);
lean_dec_ref(v_findLocalDecl_x3f_3195_);
v_val_3247_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3249_ = v___x_3225_;
v_isShared_3250_ = v_isSharedCheck_3257_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_val_3247_);
lean_dec(v___x_3225_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3257_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3251_ = l_Lean_LocalDecl_toExpr(v_val_3247_);
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
lean_ctor_set(v___x_3252_, 1, v_projs_3197_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3252_);
v___x_3254_ = v___x_3249_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; 
v___x_3255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
return v___x_3255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3260_, lean_object* v_findLocalDecl_x3f_3261_, lean_object* v_n_3262_, lean_object* v_projs_3263_, lean_object* v_globalDeclFound_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
uint8_t v_globalDeclFound_boxed_3272_; lean_object* v_res_3273_; 
v_globalDeclFound_boxed_3272_ = lean_unbox(v_globalDeclFound_3264_);
v_res_3273_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3260_, v_findLocalDecl_x3f_3261_, v_n_3262_, v_projs_3263_, v_globalDeclFound_boxed_3272_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v_view_3260_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3274_, lean_object* v_givenName_3275_, lean_object* v_as_3276_, lean_object* v_i_3277_){
_start:
{
lean_object* v_zero_3278_; uint8_t v_isZero_3279_; 
v_zero_3278_ = lean_unsigned_to_nat(0u);
v_isZero_3279_ = lean_nat_dec_eq(v_i_3277_, v_zero_3278_);
if (v_isZero_3279_ == 1)
{
lean_object* v___x_3280_; 
lean_dec(v_i_3277_);
lean_dec(v_localDecl_x3f_3274_);
v___x_3280_ = lean_box(0);
return v___x_3280_;
}
else
{
lean_object* v_one_3281_; lean_object* v_n_3282_; lean_object* v___y_3284_; lean_object* v___x_3286_; 
v_one_3281_ = lean_unsigned_to_nat(1u);
v_n_3282_ = lean_nat_sub(v_i_3277_, v_one_3281_);
lean_dec(v_i_3277_);
v___x_3286_ = lean_array_fget_borrowed(v_as_3276_, v_n_3282_);
if (lean_obj_tag(v___x_3286_) == 0)
{
v___y_3284_ = v___x_3286_;
goto v___jp_3283_;
}
else
{
lean_object* v_val_3287_; uint8_t v___x_3288_; 
v_val_3287_ = lean_ctor_get(v___x_3286_, 0);
v___x_3288_ = l_Lean_LocalDecl_isAuxDecl(v_val_3287_);
if (v___x_3288_ == 0)
{
lean_inc(v_localDecl_x3f_3274_);
v___y_3284_ = v_localDecl_x3f_3274_;
goto v___jp_3283_;
}
else
{
lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3289_ = l_Lean_LocalDecl_userName(v_val_3287_);
v___x_3290_ = lean_name_eq(v___x_3289_, v_givenName_3275_);
lean_dec(v___x_3289_);
if (v___x_3290_ == 0)
{
v_i_3277_ = v_n_3282_;
goto _start;
}
else
{
lean_inc_ref(v___x_3286_);
v___y_3284_ = v___x_3286_;
goto v___jp_3283_;
}
}
}
v___jp_3283_:
{
if (lean_obj_tag(v___y_3284_) == 0)
{
v_i_3277_ = v_n_3282_;
goto _start;
}
else
{
lean_dec(v_n_3282_);
lean_dec(v_localDecl_x3f_3274_);
return v___y_3284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3292_, lean_object* v_givenName_3293_, lean_object* v_as_3294_, lean_object* v_i_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3292_, v_givenName_3293_, v_as_3294_, v_i_3295_);
lean_dec_ref(v_as_3294_);
lean_dec(v_givenName_3293_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3297_, lean_object* v_givenName_3298_, lean_object* v_as_3299_, lean_object* v_i_3300_){
_start:
{
lean_object* v_zero_3301_; uint8_t v_isZero_3302_; 
v_zero_3301_ = lean_unsigned_to_nat(0u);
v_isZero_3302_ = lean_nat_dec_eq(v_i_3300_, v_zero_3301_);
if (v_isZero_3302_ == 1)
{
lean_object* v___x_3303_; 
lean_dec(v_i_3300_);
lean_dec(v_localDecl_x3f_3297_);
v___x_3303_ = lean_box(0);
return v___x_3303_;
}
else
{
lean_object* v_one_3304_; lean_object* v_n_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_one_3304_ = lean_unsigned_to_nat(1u);
v_n_3305_ = lean_nat_sub(v_i_3300_, v_one_3304_);
lean_dec(v_i_3300_);
v___x_3306_ = lean_array_fget_borrowed(v_as_3299_, v_n_3305_);
lean_inc(v_localDecl_x3f_3297_);
v___x_3307_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3297_, v_givenName_3298_, v___x_3306_);
if (lean_obj_tag(v___x_3307_) == 0)
{
v_i_3300_ = v_n_3305_;
goto _start;
}
else
{
lean_dec(v_n_3305_);
lean_dec(v_localDecl_x3f_3297_);
return v___x_3307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3309_, lean_object* v_givenName_3310_, lean_object* v_x_3311_){
_start:
{
if (lean_obj_tag(v_x_3311_) == 0)
{
lean_object* v_cs_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_cs_3312_ = lean_ctor_get(v_x_3311_, 0);
v___x_3313_ = lean_array_get_size(v_cs_3312_);
v___x_3314_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3309_, v_givenName_3310_, v_cs_3312_, v___x_3313_);
return v___x_3314_;
}
else
{
lean_object* v_vs_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_vs_3315_ = lean_ctor_get(v_x_3311_, 0);
v___x_3316_ = lean_array_get_size(v_vs_3315_);
v___x_3317_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3309_, v_givenName_3310_, v_vs_3315_, v___x_3316_);
return v___x_3317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3318_, lean_object* v_givenName_3319_, lean_object* v_x_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3318_, v_givenName_3319_, v_x_3320_);
lean_dec_ref(v_x_3320_);
lean_dec(v_givenName_3319_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3322_, lean_object* v_givenName_3323_, lean_object* v_as_3324_, lean_object* v_i_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3322_, v_givenName_3323_, v_as_3324_, v_i_3325_);
lean_dec_ref(v_as_3324_);
lean_dec(v_givenName_3323_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3327_, lean_object* v_givenName_3328_, lean_object* v_t_3329_){
_start:
{
lean_object* v_root_3330_; lean_object* v_tail_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v_root_3330_ = lean_ctor_get(v_t_3329_, 0);
v_tail_3331_ = lean_ctor_get(v_t_3329_, 1);
v___x_3332_ = lean_array_get_size(v_tail_3331_);
lean_inc(v_localDecl_x3f_3327_);
v___x_3333_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3327_, v_givenName_3328_, v_tail_3331_, v___x_3332_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; 
v___x_3334_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3327_, v_givenName_3328_, v_root_3330_);
return v___x_3334_;
}
else
{
lean_dec(v_localDecl_x3f_3327_);
return v___x_3333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3335_, lean_object* v_givenName_3336_, lean_object* v_t_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3335_, v_givenName_3336_, v_t_3337_);
lean_dec_ref(v_t_3337_);
lean_dec(v_givenName_3336_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3339_, lean_object* v_k_3340_){
_start:
{
if (lean_obj_tag(v_t_3339_) == 0)
{
lean_object* v_k_3341_; lean_object* v_v_3342_; lean_object* v_l_3343_; lean_object* v_r_3344_; uint8_t v___x_3345_; 
v_k_3341_ = lean_ctor_get(v_t_3339_, 1);
v_v_3342_ = lean_ctor_get(v_t_3339_, 2);
v_l_3343_ = lean_ctor_get(v_t_3339_, 3);
v_r_3344_ = lean_ctor_get(v_t_3339_, 4);
v___x_3345_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3340_, v_k_3341_);
switch(v___x_3345_)
{
case 0:
{
v_t_3339_ = v_l_3343_;
goto _start;
}
case 1:
{
lean_object* v___x_3347_; 
lean_inc(v_v_3342_);
v___x_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_v_3342_);
return v___x_3347_;
}
default: 
{
v_t_3339_ = v_r_3344_;
goto _start;
}
}
}
else
{
lean_object* v___x_3349_; 
v___x_3349_ = lean_box(0);
return v___x_3349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3350_, lean_object* v_k_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3350_, v_k_3351_);
lean_dec(v_k_3351_);
lean_dec(v_t_3350_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3353_, lean_object* v_givenName_3354_){
_start:
{
lean_object* v___x_3355_; uint8_t v___x_3356_; 
v___x_3355_ = l_Lean_LocalDecl_userName(v_localDecl_3353_);
v___x_3356_ = lean_name_eq(v___x_3355_, v_givenName_3354_);
lean_dec(v___x_3355_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; 
lean_dec_ref(v_localDecl_3353_);
v___x_3357_ = lean_box(0);
return v___x_3357_;
}
else
{
lean_object* v___x_3358_; 
v___x_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3358_, 0, v_localDecl_3353_);
return v___x_3358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3359_, lean_object* v_givenName_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3359_, v_givenName_3360_);
lean_dec(v_givenName_3360_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3362_, uint8_t v_skipAuxDecl_3363_, lean_object* v_auxDeclToFullName_3364_, lean_object* v___x_3365_, lean_object* v_givenNameView_3366_, lean_object* v_as_3367_, lean_object* v_i_3368_){
_start:
{
lean_object* v_zero_3369_; uint8_t v_isZero_3370_; 
v_zero_3369_ = lean_unsigned_to_nat(0u);
v_isZero_3370_ = lean_nat_dec_eq(v_i_3368_, v_zero_3369_);
if (v_isZero_3370_ == 1)
{
lean_object* v___x_3371_; 
lean_dec(v_i_3368_);
lean_dec_ref(v_givenNameView_3366_);
lean_dec(v___x_3365_);
v___x_3371_ = lean_box(0);
return v___x_3371_;
}
else
{
lean_object* v_one_3372_; lean_object* v_n_3373_; lean_object* v___y_3375_; lean_object* v___x_3377_; 
v_one_3372_ = lean_unsigned_to_nat(1u);
v_n_3373_ = lean_nat_sub(v_i_3368_, v_one_3372_);
lean_dec(v_i_3368_);
v___x_3377_ = lean_array_fget_borrowed(v_as_3367_, v_n_3373_);
if (lean_obj_tag(v___x_3377_) == 0)
{
v___y_3375_ = v___x_3377_;
goto v___jp_3374_;
}
else
{
lean_object* v_val_3378_; uint8_t v___x_3379_; 
v_val_3378_ = lean_ctor_get(v___x_3377_, 0);
v___x_3379_ = l_Lean_LocalDecl_isAuxDecl(v_val_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; 
lean_inc(v_val_3378_);
v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3378_, v_givenName_3362_);
v___y_3375_ = v___x_3380_;
goto v___jp_3374_;
}
else
{
if (v_skipAuxDecl_3363_ == 0)
{
if (v___x_3379_ == 0)
{
v_i_3368_ = v_n_3373_;
goto _start;
}
else
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = l_Lean_LocalDecl_fvarId(v_val_3378_);
v___x_3383_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3364_, v___x_3382_);
lean_dec(v___x_3382_);
if (lean_obj_tag(v___x_3383_) == 1)
{
lean_object* v_val_3384_; lean_object* v_fullDeclView_3385_; lean_object* v___y_3387_; lean_object* v_name_3408_; lean_object* v___x_3409_; 
v_val_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_val_3384_);
lean_dec_ref(v___x_3383_);
v_fullDeclView_3385_ = l_Lean_extractMacroScopes(v_val_3384_);
v_name_3408_ = lean_ctor_get(v_fullDeclView_3385_, 0);
lean_inc(v_name_3408_);
lean_inc(v_name_3408_);
v___x_3409_ = lean_private_to_user_name(v_name_3408_);
if (lean_obj_tag(v___x_3409_) == 0)
{
v___y_3387_ = v_name_3408_;
goto v___jp_3386_;
}
else
{
lean_object* v_val_3410_; 
lean_dec(v_name_3408_);
v_val_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_val_3410_);
lean_dec_ref(v___x_3409_);
v___y_3387_ = v_val_3410_;
goto v___jp_3386_;
}
v___jp_3386_:
{
lean_object* v_imported_3388_; lean_object* v_ctx_3389_; lean_object* v_scopes_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3406_; 
v_imported_3388_ = lean_ctor_get(v_fullDeclView_3385_, 1);
v_ctx_3389_ = lean_ctor_get(v_fullDeclView_3385_, 2);
v_scopes_3390_ = lean_ctor_get(v_fullDeclView_3385_, 3);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_fullDeclView_3385_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v_fullDeclView_3385_, 0);
lean_dec(v_unused_3407_);
v___x_3392_ = v_fullDeclView_3385_;
v_isShared_3393_ = v_isSharedCheck_3406_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_scopes_3390_);
lean_inc(v_ctx_3389_);
lean_inc(v_imported_3388_);
lean_dec(v_fullDeclView_3385_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3406_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v_fullDeclView_3395_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v___y_3387_);
v_fullDeclView_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___y_3387_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_imported_3388_);
lean_ctor_set(v_reuseFailAlloc_3405_, 2, v_ctx_3389_);
lean_ctor_set(v_reuseFailAlloc_3405_, 3, v_scopes_3390_);
v_fullDeclView_3395_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
lean_object* v_fullDeclName_3396_; uint8_t v___x_3397_; 
lean_inc_ref(v_fullDeclView_3395_);
v_fullDeclName_3396_ = l_Lean_MacroScopesView_review(v_fullDeclView_3395_);
v___x_3397_ = l_Lean_Name_isPrefixOf(v___x_3365_, v_fullDeclName_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; 
lean_dec_ref(v_fullDeclView_3395_);
lean_inc(v___x_3365_);
lean_inc_ref(v_givenNameView_3366_);
lean_inc(v_val_3378_);
v___x_3398_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3378_, v_givenNameView_3366_, v_fullDeclName_3396_, v___x_3365_);
lean_dec(v_fullDeclName_3396_);
v___y_3375_ = v___x_3398_;
goto v___jp_3374_;
}
else
{
lean_object* v___x_3399_; lean_object* v_localDeclNameView_3400_; uint8_t v___x_3401_; 
lean_dec(v_fullDeclName_3396_);
v___x_3399_ = l_Lean_LocalDecl_userName(v_val_3378_);
v_localDeclNameView_3400_ = l_Lean_extractMacroScopes(v___x_3399_);
v___x_3401_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3400_, v_givenNameView_3366_);
lean_dec_ref(v_localDeclNameView_3400_);
if (v___x_3401_ == 0)
{
lean_dec_ref(v_fullDeclView_3395_);
v_i_3368_ = v_n_3373_;
goto _start;
}
else
{
uint8_t v___x_3403_; 
v___x_3403_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3366_, v_fullDeclView_3395_);
lean_dec_ref(v_fullDeclView_3395_);
if (v___x_3403_ == 0)
{
v_i_3368_ = v_n_3373_;
goto _start;
}
else
{
lean_inc_ref(v___x_3377_);
v___y_3375_ = v___x_3377_;
goto v___jp_3374_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3411_; 
lean_dec(v___x_3383_);
lean_inc(v_val_3378_);
v___x_3411_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3378_, v_givenName_3362_);
v___y_3375_ = v___x_3411_;
goto v___jp_3374_;
}
}
}
else
{
v_i_3368_ = v_n_3373_;
goto _start;
}
}
}
v___jp_3374_:
{
if (lean_obj_tag(v___y_3375_) == 0)
{
v_i_3368_ = v_n_3373_;
goto _start;
}
else
{
lean_dec(v_n_3373_);
lean_dec_ref(v_givenNameView_3366_);
lean_dec(v___x_3365_);
return v___y_3375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3413_, lean_object* v_skipAuxDecl_3414_, lean_object* v_auxDeclToFullName_3415_, lean_object* v___x_3416_, lean_object* v_givenNameView_3417_, lean_object* v_as_3418_, lean_object* v_i_3419_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3420_; lean_object* v_res_3421_; 
v_skipAuxDecl_boxed_3420_ = lean_unbox(v_skipAuxDecl_3414_);
v_res_3421_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3413_, v_skipAuxDecl_boxed_3420_, v_auxDeclToFullName_3415_, v___x_3416_, v_givenNameView_3417_, v_as_3418_, v_i_3419_);
lean_dec_ref(v_as_3418_);
lean_dec(v_auxDeclToFullName_3415_);
lean_dec(v_givenName_3413_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3422_, uint8_t v_skipAuxDecl_3423_, lean_object* v_auxDeclToFullName_3424_, lean_object* v___x_3425_, lean_object* v_givenNameView_3426_, lean_object* v_as_3427_, lean_object* v_i_3428_){
_start:
{
lean_object* v_zero_3429_; uint8_t v_isZero_3430_; 
v_zero_3429_ = lean_unsigned_to_nat(0u);
v_isZero_3430_ = lean_nat_dec_eq(v_i_3428_, v_zero_3429_);
if (v_isZero_3430_ == 1)
{
lean_object* v___x_3431_; 
lean_dec(v_i_3428_);
lean_dec_ref(v_givenNameView_3426_);
lean_dec(v___x_3425_);
v___x_3431_ = lean_box(0);
return v___x_3431_;
}
else
{
lean_object* v_one_3432_; lean_object* v_n_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_one_3432_ = lean_unsigned_to_nat(1u);
v_n_3433_ = lean_nat_sub(v_i_3428_, v_one_3432_);
lean_dec(v_i_3428_);
v___x_3434_ = lean_array_fget_borrowed(v_as_3427_, v_n_3433_);
lean_inc_ref(v_givenNameView_3426_);
lean_inc(v___x_3425_);
v___x_3435_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3422_, v_skipAuxDecl_3423_, v_auxDeclToFullName_3424_, v___x_3425_, v_givenNameView_3426_, v___x_3434_);
if (lean_obj_tag(v___x_3435_) == 0)
{
v_i_3428_ = v_n_3433_;
goto _start;
}
else
{
lean_dec(v_n_3433_);
lean_dec_ref(v_givenNameView_3426_);
lean_dec(v___x_3425_);
return v___x_3435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3437_, uint8_t v_skipAuxDecl_3438_, lean_object* v_auxDeclToFullName_3439_, lean_object* v___x_3440_, lean_object* v_givenNameView_3441_, lean_object* v_x_3442_){
_start:
{
if (lean_obj_tag(v_x_3442_) == 0)
{
lean_object* v_cs_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_cs_3443_ = lean_ctor_get(v_x_3442_, 0);
v___x_3444_ = lean_array_get_size(v_cs_3443_);
v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3437_, v_skipAuxDecl_3438_, v_auxDeclToFullName_3439_, v___x_3440_, v_givenNameView_3441_, v_cs_3443_, v___x_3444_);
return v___x_3445_;
}
else
{
lean_object* v_vs_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v_vs_3446_ = lean_ctor_get(v_x_3442_, 0);
v___x_3447_ = lean_array_get_size(v_vs_3446_);
v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3437_, v_skipAuxDecl_3438_, v_auxDeclToFullName_3439_, v___x_3440_, v_givenNameView_3441_, v_vs_3446_, v___x_3447_);
return v___x_3448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3449_, lean_object* v_skipAuxDecl_3450_, lean_object* v_auxDeclToFullName_3451_, lean_object* v___x_3452_, lean_object* v_givenNameView_3453_, lean_object* v_x_3454_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3455_; lean_object* v_res_3456_; 
v_skipAuxDecl_boxed_3455_ = lean_unbox(v_skipAuxDecl_3450_);
v_res_3456_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3449_, v_skipAuxDecl_boxed_3455_, v_auxDeclToFullName_3451_, v___x_3452_, v_givenNameView_3453_, v_x_3454_);
lean_dec_ref(v_x_3454_);
lean_dec(v_auxDeclToFullName_3451_);
lean_dec(v_givenName_3449_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3457_, lean_object* v_skipAuxDecl_3458_, lean_object* v_auxDeclToFullName_3459_, lean_object* v___x_3460_, lean_object* v_givenNameView_3461_, lean_object* v_as_3462_, lean_object* v_i_3463_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3464_; lean_object* v_res_3465_; 
v_skipAuxDecl_boxed_3464_ = lean_unbox(v_skipAuxDecl_3458_);
v_res_3465_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3457_, v_skipAuxDecl_boxed_3464_, v_auxDeclToFullName_3459_, v___x_3460_, v_givenNameView_3461_, v_as_3462_, v_i_3463_);
lean_dec_ref(v_as_3462_);
lean_dec(v_auxDeclToFullName_3459_);
lean_dec(v_givenName_3457_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3466_, uint8_t v_skipAuxDecl_3467_, lean_object* v_auxDeclToFullName_3468_, lean_object* v___x_3469_, lean_object* v_givenNameView_3470_, lean_object* v_t_3471_){
_start:
{
lean_object* v_root_3472_; lean_object* v_tail_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v_root_3472_ = lean_ctor_get(v_t_3471_, 0);
v_tail_3473_ = lean_ctor_get(v_t_3471_, 1);
v___x_3474_ = lean_array_get_size(v_tail_3473_);
lean_inc_ref(v_givenNameView_3470_);
lean_inc(v___x_3469_);
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3466_, v_skipAuxDecl_3467_, v_auxDeclToFullName_3468_, v___x_3469_, v_givenNameView_3470_, v_tail_3473_, v___x_3474_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3466_, v_skipAuxDecl_3467_, v_auxDeclToFullName_3468_, v___x_3469_, v_givenNameView_3470_, v_root_3472_);
return v___x_3476_;
}
else
{
lean_dec_ref(v_givenNameView_3470_);
lean_dec(v___x_3469_);
return v___x_3475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3477_, lean_object* v_skipAuxDecl_3478_, lean_object* v_auxDeclToFullName_3479_, lean_object* v___x_3480_, lean_object* v_givenNameView_3481_, lean_object* v_t_3482_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3483_; lean_object* v_res_3484_; 
v_skipAuxDecl_boxed_3483_ = lean_unbox(v_skipAuxDecl_3478_);
v_res_3484_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3477_, v_skipAuxDecl_boxed_3483_, v_auxDeclToFullName_3479_, v___x_3480_, v_givenNameView_3481_, v_t_3482_);
lean_dec_ref(v_t_3482_);
lean_dec(v_auxDeclToFullName_3479_);
lean_dec(v_givenName_3477_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3485_, lean_object* v_currNamespace_3486_, lean_object* v_decls_3487_, lean_object* v_givenNameView_3488_, uint8_t v_skipAuxDecl_3489_){
_start:
{
lean_object* v_givenName_3490_; lean_object* v_localDecl_x3f_3491_; 
lean_inc_ref(v_givenNameView_3488_);
v_givenName_3490_ = l_Lean_MacroScopesView_review(v_givenNameView_3488_);
v_localDecl_x3f_3491_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3490_, v_skipAuxDecl_3489_, v_auxDeclToFullName_3485_, v_currNamespace_3486_, v_givenNameView_3488_, v_decls_3487_);
if (lean_obj_tag(v_localDecl_x3f_3491_) == 0)
{
if (v_skipAuxDecl_3489_ == 0)
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3491_, v_givenName_3490_, v_decls_3487_);
lean_dec(v_givenName_3490_);
return v___x_3492_;
}
else
{
lean_dec(v_givenName_3490_);
return v_localDecl_x3f_3491_;
}
}
else
{
lean_dec(v_givenName_3490_);
return v_localDecl_x3f_3491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3493_, lean_object* v_currNamespace_3494_, lean_object* v_decls_3495_, lean_object* v_givenNameView_3496_, lean_object* v_skipAuxDecl_3497_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3498_; lean_object* v_res_3499_; 
v_skipAuxDecl_boxed_3498_ = lean_unbox(v_skipAuxDecl_3497_);
v_res_3499_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3493_, v_currNamespace_3494_, v_decls_3495_, v_givenNameView_3496_, v_skipAuxDecl_boxed_3498_);
lean_dec_ref(v_decls_3495_);
lean_dec(v_auxDeclToFullName_3493_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_lctx_3508_; lean_object* v_decls_3509_; lean_object* v_auxDeclToFullName_3510_; lean_object* v_currNamespace_3511_; lean_object* v_view_3512_; lean_object* v_name_3513_; lean_object* v_findLocalDecl_x3f_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; lean_object* v___x_3517_; 
v_lctx_3508_ = lean_ctor_get(v___y_3503_, 2);
v_decls_3509_ = lean_ctor_get(v_lctx_3508_, 1);
v_auxDeclToFullName_3510_ = lean_ctor_get(v_lctx_3508_, 2);
v_currNamespace_3511_ = lean_ctor_get(v___y_3505_, 6);
v_view_3512_ = l_Lean_extractMacroScopes(v_n_3500_);
v_name_3513_ = lean_ctor_get(v_view_3512_, 0);
lean_inc(v_name_3513_);
lean_inc_ref(v_decls_3509_);
lean_inc(v_currNamespace_3511_);
lean_inc(v_auxDeclToFullName_3510_);
v_findLocalDecl_x3f_3514_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3514_, 0, v_auxDeclToFullName_3510_);
lean_closure_set(v_findLocalDecl_x3f_3514_, 1, v_currNamespace_3511_);
lean_closure_set(v_findLocalDecl_x3f_3514_, 2, v_decls_3509_);
v___x_3515_ = lean_box(0);
v___x_3516_ = 0;
v___x_3517_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3512_, v_findLocalDecl_x3f_3514_, v_name_3513_, v___x_3515_, v___x_3516_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec_ref(v___y_3503_);
lean_dec_ref(v_view_3512_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
lean_dec(v___y_3524_);
lean_dec(v___y_3522_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3527_, lean_object* v_b_3528_){
_start:
{
if (lean_obj_tag(v_as_x27_3527_) == 0)
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3530_, 0, v_b_3528_);
return v___x_3530_;
}
else
{
lean_object* v_head_3531_; lean_object* v_tail_3532_; lean_object* v_config_3533_; lean_object* v_extensions_3534_; lean_object* v_extra_3535_; lean_object* v_extraInj_3536_; lean_object* v_extraFacts_3537_; lean_object* v_symPrios_3538_; lean_object* v_norm_3539_; lean_object* v_normProcs_3540_; lean_object* v_anchorRefs_x3f_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3550_; 
v_head_3531_ = lean_ctor_get(v_as_x27_3527_, 0);
lean_inc(v_head_3531_);
v_tail_3532_ = lean_ctor_get(v_as_x27_3527_, 1);
lean_inc(v_tail_3532_);
lean_dec_ref(v_as_x27_3527_);
v_config_3533_ = lean_ctor_get(v_b_3528_, 0);
v_extensions_3534_ = lean_ctor_get(v_b_3528_, 1);
v_extra_3535_ = lean_ctor_get(v_b_3528_, 2);
v_extraInj_3536_ = lean_ctor_get(v_b_3528_, 3);
v_extraFacts_3537_ = lean_ctor_get(v_b_3528_, 4);
v_symPrios_3538_ = lean_ctor_get(v_b_3528_, 5);
v_norm_3539_ = lean_ctor_get(v_b_3528_, 6);
v_normProcs_3540_ = lean_ctor_get(v_b_3528_, 7);
v_anchorRefs_x3f_3541_ = lean_ctor_get(v_b_3528_, 8);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_b_3528_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3543_ = v_b_3528_;
v_isShared_3544_ = v_isSharedCheck_3550_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_anchorRefs_x3f_3541_);
lean_inc(v_normProcs_3540_);
lean_inc(v_norm_3539_);
lean_inc(v_symPrios_3538_);
lean_inc(v_extraFacts_3537_);
lean_inc(v_extraInj_3536_);
lean_inc(v_extra_3535_);
lean_inc(v_extensions_3534_);
lean_inc(v_config_3533_);
lean_dec(v_b_3528_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3550_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3545_ = l_Lean_PersistentArray_push___redArg(v_extra_3535_, v_head_3531_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 2, v___x_3545_);
v___x_3547_ = v___x_3543_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_config_3533_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_extensions_3534_);
lean_ctor_set(v_reuseFailAlloc_3549_, 2, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3549_, 3, v_extraInj_3536_);
lean_ctor_set(v_reuseFailAlloc_3549_, 4, v_extraFacts_3537_);
lean_ctor_set(v_reuseFailAlloc_3549_, 5, v_symPrios_3538_);
lean_ctor_set(v_reuseFailAlloc_3549_, 6, v_norm_3539_);
lean_ctor_set(v_reuseFailAlloc_3549_, 7, v_normProcs_3540_);
lean_ctor_set(v_reuseFailAlloc_3549_, 8, v_anchorRefs_x3f_3541_);
v___x_3547_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
v_as_x27_3527_ = v_tail_3532_;
v_b_3528_ = v___x_3547_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3551_, lean_object* v_b_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3551_, v_b_3552_);
return v_res_3554_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3557_ = l_Lean_stringToMessageData(v___x_3556_);
return v___x_3557_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3560_ = l_Lean_stringToMessageData(v___x_3559_);
return v___x_3560_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3563_ = l_Lean_stringToMessageData(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3566_ = l_Lean_stringToMessageData(v___x_3565_);
return v___x_3566_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3569_ = l_Lean_stringToMessageData(v___x_3568_);
return v___x_3569_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3572_ = l_Lean_stringToMessageData(v___x_3571_);
return v___x_3572_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3575_ = l_Lean_stringToMessageData(v___x_3574_);
return v___x_3575_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3578_ = l_Lean_stringToMessageData(v___x_3577_);
return v___x_3578_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3581_ = l_Lean_stringToMessageData(v___x_3580_);
return v___x_3581_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3584_ = l_Lean_stringToMessageData(v___x_3583_);
return v___x_3584_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3587_ = l_Lean_stringToMessageData(v___x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3588_, lean_object* v_p_3589_, lean_object* v_mod_x3f_3590_, lean_object* v_id_3591_, uint8_t v_minIndexable_3592_, uint8_t v_only_3593_, uint8_t v_incremental_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; uint8_t v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v_a_3789_; lean_object* v___y_4020_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = lean_box(0);
lean_inc(v_a_3600_);
lean_inc_ref(v_a_3599_);
lean_inc(v_id_3591_);
v___x_4032_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3591_, v___x_4031_, v_a_3599_, v_a_3600_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref(v___x_4032_);
v_a_3789_ = v_a_4033_;
goto v___jp_3788_;
}
else
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4108_; 
v_a_4034_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4036_ = v___x_4032_;
v_isShared_4037_ = v_isSharedCheck_4108_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4032_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4108_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
uint8_t v___y_4039_; uint8_t v___x_4106_; 
v___x_4106_ = l_Lean_Exception_isInterrupt(v_a_4034_);
if (v___x_4106_ == 0)
{
uint8_t v___x_4107_; 
lean_inc(v_a_4034_);
v___x_4107_ = l_Lean_Exception_isRuntime(v_a_4034_);
v___y_4039_ = v___x_4107_;
goto v___jp_4038_;
}
else
{
v___y_4039_ = v___x_4106_;
goto v___jp_4038_;
}
v___jp_4038_:
{
if (v___y_4039_ == 0)
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
lean_del_object(v___x_4036_);
v___x_4040_ = l_Lean_TSyntax_getId(v_id_3591_);
lean_inc_ref(v_a_3599_);
lean_inc_ref(v_a_3597_);
lean_inc(v___x_4040_);
v___x_4041_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4040_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref(v___x_4041_);
if (lean_obj_tag(v_a_4042_) == 0)
{
lean_object* v___x_4043_; 
v___x_4043_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4040_, v_a_3599_, v_a_3600_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4072_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4046_ = v___x_4043_;
v_isShared_4047_ = v_isSharedCheck_4072_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4043_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4072_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
if (lean_obj_tag(v_a_4044_) == 1)
{
lean_del_object(v___x_4046_);
lean_dec(v_a_4034_);
if (lean_obj_tag(v_mod_x3f_3590_) == 1)
{
lean_object* v_val_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec_ref(v_a_4044_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_val_4048_ = lean_ctor_get(v_mod_x3f_3590_, 0);
lean_inc(v_val_4048_);
lean_dec_ref(v_mod_x3f_3590_);
v___x_4049_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4050_ = l_Lean_MessageData_ofName(v___x_4040_);
v___x_4051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4049_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4051_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4048_, v___x_4053_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec(v_val_4048_);
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4054_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4054_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
else
{
lean_object* v_val_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_dec(v___x_4040_);
v_val_4063_ = lean_ctor_get(v_a_4044_, 0);
lean_inc(v_val_4063_);
lean_dec_ref(v_a_4044_);
v___x_4064_ = lean_box(0);
lean_inc_ref(v_params_3588_);
v___x_4065_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3588_, v_val_4063_, v___x_4064_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_val_4063_);
v___y_4020_ = v___x_4065_;
goto v___jp_4019_;
}
}
else
{
lean_object* v___x_4066_; uint8_t v___x_4067_; 
lean_dec(v_a_4044_);
v___x_4066_ = l_Lean_Name_getPrefix(v___x_4040_);
lean_dec(v___x_4040_);
v___x_4067_ = l_Lean_Name_isAnonymous(v___x_4066_);
lean_dec(v___x_4066_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4068_; 
lean_del_object(v___x_4046_);
lean_dec(v_a_4034_);
v___x_4068_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3588_, v_p_3589_, v_mod_x3f_3590_, v_id_3591_, v_minIndexable_3592_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
return v___x_4068_;
}
else
{
lean_object* v___x_4070_; 
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_mod_x3f_3590_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set_tag(v___x_4046_, 1);
lean_ctor_set(v___x_4046_, 0, v_a_4034_);
v___x_4070_ = v___x_4046_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4034_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v___x_4040_);
lean_dec(v_a_4034_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_mod_x3f_3590_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_4073_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4043_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4043_);
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
else
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_dec_ref(v_a_4042_);
lean_dec(v___x_4040_);
lean_dec(v_a_4034_);
lean_dec(v_mod_x3f_3590_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v___x_4081_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
lean_inc(v_id_3591_);
v___x_4082_ = l_Lean_MessageData_ofSyntax(v_id_3591_);
v___x_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4083_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
v___x_4086_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3591_, v___x_4085_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec(v_id_3591_);
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
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_dec(v___x_4040_);
lean_dec(v_a_4034_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_mod_x3f_3590_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_4095_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4041_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4041_);
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
else
{
lean_object* v___x_4104_; 
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_mod_x3f_3590_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
if (v_isShared_4037_ == 0)
{
v___x_4104_ = v___x_4036_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4034_);
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
v___jp_3602_:
{
uint8_t v___x_3610_; lean_object* v___x_3611_; 
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
v___x_3610_ = 0;
lean_inc(v___y_3603_);
v___x_3611_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3603_, v___x_3610_, v___y_3608_, v___y_3609_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref(v___x_3611_);
if (lean_obj_tag(v_a_3612_) == 1)
{
lean_object* v_val_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_dec(v___y_3603_);
v_val_3613_ = lean_ctor_get(v_a_3612_, 0);
lean_inc(v_val_3613_);
lean_dec_ref(v_a_3612_);
lean_inc(v_val_3613_);
v___x_3614_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3588_, v_val_3613_, v___x_3610_);
lean_inc(v___y_3609_);
lean_inc_ref(v___y_3608_);
lean_inc(v___y_3607_);
lean_inc_ref(v___y_3606_);
v___x_3615_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3613_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3626_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3618_ = v___x_3615_;
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
if (lean_obj_tag(v_a_3616_) == 1)
{
lean_object* v_val_3620_; lean_object* v_ctors_3621_; lean_object* v___x_3622_; 
lean_del_object(v___x_3618_);
v_val_3620_ = lean_ctor_get(v_a_3616_, 0);
lean_inc(v_val_3620_);
lean_dec_ref(v_a_3616_);
v_ctors_3621_ = lean_ctor_get(v_val_3620_, 4);
lean_inc(v_ctors_3621_);
lean_dec(v_val_3620_);
v___x_3622_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3589_, v_id_3591_, v_minIndexable_3592_, v_ctors_3621_, v___x_3614_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v_p_3589_);
return v___x_3622_;
}
else
{
lean_object* v___x_3624_; 
lean_dec(v_a_3616_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 0, v___x_3614_);
v___x_3624_ = v___x_3618_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3614_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v___x_3614_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
v_a_3627_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3615_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3615_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
else
{
lean_object* v_fileName_3635_; lean_object* v_fileMap_3636_; lean_object* v_options_3637_; lean_object* v_currRecDepth_3638_; lean_object* v_maxRecDepth_3639_; lean_object* v_ref_3640_; lean_object* v_currNamespace_3641_; lean_object* v_openDecls_3642_; lean_object* v_initHeartbeats_3643_; lean_object* v_maxHeartbeats_3644_; lean_object* v_quotContext_3645_; lean_object* v_currMacroScope_3646_; uint8_t v_diag_3647_; lean_object* v_cancelTk_x3f_3648_; uint8_t v_suppressElabErrors_3649_; lean_object* v_inheritedTraceOptions_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3661_; 
lean_dec(v_a_3612_);
v_fileName_3635_ = lean_ctor_get(v___y_3608_, 0);
v_fileMap_3636_ = lean_ctor_get(v___y_3608_, 1);
v_options_3637_ = lean_ctor_get(v___y_3608_, 2);
v_currRecDepth_3638_ = lean_ctor_get(v___y_3608_, 3);
v_maxRecDepth_3639_ = lean_ctor_get(v___y_3608_, 4);
v_ref_3640_ = lean_ctor_get(v___y_3608_, 5);
v_currNamespace_3641_ = lean_ctor_get(v___y_3608_, 6);
v_openDecls_3642_ = lean_ctor_get(v___y_3608_, 7);
v_initHeartbeats_3643_ = lean_ctor_get(v___y_3608_, 8);
v_maxHeartbeats_3644_ = lean_ctor_get(v___y_3608_, 9);
v_quotContext_3645_ = lean_ctor_get(v___y_3608_, 10);
v_currMacroScope_3646_ = lean_ctor_get(v___y_3608_, 11);
v_diag_3647_ = lean_ctor_get_uint8(v___y_3608_, sizeof(void*)*14);
v_cancelTk_x3f_3648_ = lean_ctor_get(v___y_3608_, 12);
v_suppressElabErrors_3649_ = lean_ctor_get_uint8(v___y_3608_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3650_ = lean_ctor_get(v___y_3608_, 13);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___y_3608_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3652_ = v___y_3608_;
v_isShared_3653_ = v_isSharedCheck_3661_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_inheritedTraceOptions_3650_);
lean_inc(v_cancelTk_x3f_3648_);
lean_inc(v_currMacroScope_3646_);
lean_inc(v_quotContext_3645_);
lean_inc(v_maxHeartbeats_3644_);
lean_inc(v_initHeartbeats_3643_);
lean_inc(v_openDecls_3642_);
lean_inc(v_currNamespace_3641_);
lean_inc(v_ref_3640_);
lean_inc(v_maxRecDepth_3639_);
lean_inc(v_currRecDepth_3638_);
lean_inc(v_options_3637_);
lean_inc(v_fileMap_3636_);
lean_inc(v_fileName_3635_);
lean_dec(v___y_3608_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3661_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; uint8_t v___x_3655_; lean_object* v_ref_3656_; lean_object* v___x_3658_; 
v___x_3654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_3655_ = 1;
v_ref_3656_ = l_Lean_replaceRef(v_p_3589_, v_ref_3640_);
lean_dec(v_ref_3640_);
lean_dec(v_p_3589_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 5, v_ref_3656_);
v___x_3658_ = v___x_3652_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_fileName_3635_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_fileMap_3636_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_options_3637_);
lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_currRecDepth_3638_);
lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_maxRecDepth_3639_);
lean_ctor_set(v_reuseFailAlloc_3660_, 5, v_ref_3656_);
lean_ctor_set(v_reuseFailAlloc_3660_, 6, v_currNamespace_3641_);
lean_ctor_set(v_reuseFailAlloc_3660_, 7, v_openDecls_3642_);
lean_ctor_set(v_reuseFailAlloc_3660_, 8, v_initHeartbeats_3643_);
lean_ctor_set(v_reuseFailAlloc_3660_, 9, v_maxHeartbeats_3644_);
lean_ctor_set(v_reuseFailAlloc_3660_, 10, v_quotContext_3645_);
lean_ctor_set(v_reuseFailAlloc_3660_, 11, v_currMacroScope_3646_);
lean_ctor_set(v_reuseFailAlloc_3660_, 12, v_cancelTk_x3f_3648_);
lean_ctor_set(v_reuseFailAlloc_3660_, 13, v_inheritedTraceOptions_3650_);
lean_ctor_set_uint8(v_reuseFailAlloc_3660_, sizeof(void*)*14, v_diag_3647_);
lean_ctor_set_uint8(v_reuseFailAlloc_3660_, sizeof(void*)*14 + 1, v_suppressElabErrors_3649_);
v___x_3658_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3588_, v_id_3591_, v___y_3603_, v___x_3654_, v_minIndexable_3592_, v___x_3655_, v___x_3655_, v___y_3606_, v___y_3607_, v___x_3658_, v___y_3609_);
return v___x_3659_;
}
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3603_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_3662_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3611_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3611_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
v___jp_3670_:
{
lean_object* v___x_3679_; 
v___x_3679_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3592_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
lean_dec_ref(v___x_3679_);
v___x_3680_ = l_Lean_Meta_Grind_grindExt;
v___x_3681_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3680_, v___y_3678_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref(v___x_3681_);
lean_inc(v___y_3671_);
v___x_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___y_3671_);
v___x_3684_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3682_, v___x_3683_);
lean_dec_ref(v___x_3683_);
v___x_3685_ = lean_box(0);
v___x_3686_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3672_, v___x_3684_, v___x_3685_);
lean_dec(v___y_3672_);
v___x_3687_ = l_List_isEmpty___redArg(v___x_3686_);
if (v___x_3687_ == 0)
{
lean_object* v___x_3688_; 
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3671_);
lean_dec(v_p_3589_);
v___x_3688_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3686_, v_params_3588_);
return v___x_3688_;
}
else
{
lean_object* v___x_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v___x_3686_);
lean_dec_ref(v_params_3588_);
v___x_3689_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3690_ = 0;
v___x_3691_ = l_Lean_MessageData_ofConstName(v___y_3671_, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3689_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3589_, v___x_3694_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
lean_dec(v___y_3678_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec(v_p_3589_);
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_3704_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3681_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3681_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_3712_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3679_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3679_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
v___jp_3720_:
{
lean_object* v___x_3727_; 
v___x_3727_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3592_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_fileName_3728_; lean_object* v_fileMap_3729_; lean_object* v_options_3730_; lean_object* v_currRecDepth_3731_; lean_object* v_maxRecDepth_3732_; lean_object* v_ref_3733_; lean_object* v_currNamespace_3734_; lean_object* v_openDecls_3735_; lean_object* v_initHeartbeats_3736_; lean_object* v_maxHeartbeats_3737_; lean_object* v_quotContext_3738_; lean_object* v_currMacroScope_3739_; uint8_t v_diag_3740_; lean_object* v_cancelTk_x3f_3741_; uint8_t v_suppressElabErrors_3742_; lean_object* v_inheritedTraceOptions_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3769_; 
lean_dec_ref(v___x_3727_);
v_fileName_3728_ = lean_ctor_get(v___y_3725_, 0);
v_fileMap_3729_ = lean_ctor_get(v___y_3725_, 1);
v_options_3730_ = lean_ctor_get(v___y_3725_, 2);
v_currRecDepth_3731_ = lean_ctor_get(v___y_3725_, 3);
v_maxRecDepth_3732_ = lean_ctor_get(v___y_3725_, 4);
v_ref_3733_ = lean_ctor_get(v___y_3725_, 5);
v_currNamespace_3734_ = lean_ctor_get(v___y_3725_, 6);
v_openDecls_3735_ = lean_ctor_get(v___y_3725_, 7);
v_initHeartbeats_3736_ = lean_ctor_get(v___y_3725_, 8);
v_maxHeartbeats_3737_ = lean_ctor_get(v___y_3725_, 9);
v_quotContext_3738_ = lean_ctor_get(v___y_3725_, 10);
v_currMacroScope_3739_ = lean_ctor_get(v___y_3725_, 11);
v_diag_3740_ = lean_ctor_get_uint8(v___y_3725_, sizeof(void*)*14);
v_cancelTk_x3f_3741_ = lean_ctor_get(v___y_3725_, 12);
v_suppressElabErrors_3742_ = lean_ctor_get_uint8(v___y_3725_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3743_ = lean_ctor_get(v___y_3725_, 13);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___y_3725_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3745_ = v___y_3725_;
v_isShared_3746_ = v_isSharedCheck_3769_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_inheritedTraceOptions_3743_);
lean_inc(v_cancelTk_x3f_3741_);
lean_inc(v_currMacroScope_3739_);
lean_inc(v_quotContext_3738_);
lean_inc(v_maxHeartbeats_3737_);
lean_inc(v_initHeartbeats_3736_);
lean_inc(v_openDecls_3735_);
lean_inc(v_currNamespace_3734_);
lean_inc(v_ref_3733_);
lean_inc(v_maxRecDepth_3732_);
lean_inc(v_currRecDepth_3731_);
lean_inc(v_options_3730_);
lean_inc(v_fileMap_3729_);
lean_inc(v_fileName_3728_);
lean_dec(v___y_3725_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3769_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v_ref_3747_; lean_object* v___x_3749_; 
v_ref_3747_ = l_Lean_replaceRef(v_p_3589_, v_ref_3733_);
lean_dec(v_ref_3733_);
lean_dec(v_p_3589_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 5, v_ref_3747_);
v___x_3749_ = v___x_3745_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_fileName_3728_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v_fileMap_3729_);
lean_ctor_set(v_reuseFailAlloc_3768_, 2, v_options_3730_);
lean_ctor_set(v_reuseFailAlloc_3768_, 3, v_currRecDepth_3731_);
lean_ctor_set(v_reuseFailAlloc_3768_, 4, v_maxRecDepth_3732_);
lean_ctor_set(v_reuseFailAlloc_3768_, 5, v_ref_3747_);
lean_ctor_set(v_reuseFailAlloc_3768_, 6, v_currNamespace_3734_);
lean_ctor_set(v_reuseFailAlloc_3768_, 7, v_openDecls_3735_);
lean_ctor_set(v_reuseFailAlloc_3768_, 8, v_initHeartbeats_3736_);
lean_ctor_set(v_reuseFailAlloc_3768_, 9, v_maxHeartbeats_3737_);
lean_ctor_set(v_reuseFailAlloc_3768_, 10, v_quotContext_3738_);
lean_ctor_set(v_reuseFailAlloc_3768_, 11, v_currMacroScope_3739_);
lean_ctor_set(v_reuseFailAlloc_3768_, 12, v_cancelTk_x3f_3741_);
lean_ctor_set(v_reuseFailAlloc_3768_, 13, v_inheritedTraceOptions_3743_);
lean_ctor_set_uint8(v_reuseFailAlloc_3768_, sizeof(void*)*14, v_diag_3740_);
lean_ctor_set_uint8(v_reuseFailAlloc_3768_, sizeof(void*)*14 + 1, v_suppressElabErrors_3742_);
v___x_3749_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3750_; 
lean_inc(v___y_3722_);
v___x_3750_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3722_, v___y_3721_, v___x_3749_, v___y_3726_);
lean_dec(v___y_3726_);
lean_dec_ref(v___x_3749_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3758_; 
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; 
v_unused_3759_ = lean_ctor_get(v___x_3750_, 0);
lean_dec(v_unused_3759_);
v___x_3752_ = v___x_3750_;
v_isShared_3753_ = v_isSharedCheck_3758_;
goto v_resetjp_3751_;
}
else
{
lean_dec(v___x_3750_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3758_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; lean_object* v___x_3756_; 
v___x_3754_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3588_, v___y_3722_, v___y_3721_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v___x_3754_);
v___x_3756_ = v___x_3752_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_dec(v___y_3722_);
lean_dec_ref(v_params_3588_);
v_a_3760_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3750_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3750_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3722_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_3770_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3727_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3727_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
v___jp_3778_:
{
lean_object* v_ctors_3786_; lean_object* v___x_3787_; 
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
v_ctors_3786_ = lean_ctor_get(v___y_3779_, 4);
lean_inc(v_ctors_3786_);
lean_dec_ref(v___y_3779_);
v___x_3787_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3589_, v_id_3591_, v_minIndexable_3592_, v_ctors_3786_, v_params_3588_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v_p_3589_);
return v___x_3787_;
}
v___jp_3788_:
{
lean_object* v___x_3790_; 
lean_inc(v_a_3600_);
lean_inc_ref(v_a_3599_);
lean_inc(v_a_3598_);
lean_inc(v_a_3789_);
v___x_3790_ = l_Lean_Linter_checkDeprecated(v_a_3789_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_dec_ref(v___x_3790_);
if (lean_obj_tag(v_mod_x3f_3590_) == 1)
{
lean_object* v_val_3791_; lean_object* v___x_3792_; 
v_val_3791_ = lean_ctor_get(v_mod_x3f_3590_, 0);
lean_inc(v_val_3791_);
lean_dec_ref(v_mod_x3f_3590_);
lean_inc_ref(v_a_3599_);
v___x_3792_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3791_, v_a_3599_, v_a_3600_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_4002_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3795_ = v___x_3792_;
v_isShared_3796_ = v_isSharedCheck_4002_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3792_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_4002_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
switch(lean_obj_tag(v_a_3793_))
{
case 0:
{
lean_object* v_k_3797_; 
lean_del_object(v___x_3795_);
v_k_3797_ = lean_ctor_get(v_a_3793_, 0);
lean_inc(v_k_3797_);
lean_dec_ref(v_a_3793_);
if (lean_obj_tag(v_k_3797_) == 9)
{
lean_dec(v_id_3591_);
if (v_only_3593_ == 0)
{
lean_object* v_fileName_3798_; lean_object* v_fileMap_3799_; lean_object* v_options_3800_; lean_object* v_currRecDepth_3801_; lean_object* v_maxRecDepth_3802_; lean_object* v_ref_3803_; lean_object* v_currNamespace_3804_; lean_object* v_openDecls_3805_; lean_object* v_initHeartbeats_3806_; lean_object* v_maxHeartbeats_3807_; lean_object* v_quotContext_3808_; lean_object* v_currMacroScope_3809_; uint8_t v_diag_3810_; lean_object* v_cancelTk_x3f_3811_; uint8_t v_suppressElabErrors_3812_; lean_object* v_inheritedTraceOptions_3813_; lean_object* v_ref_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_fileName_3798_ = lean_ctor_get(v_a_3599_, 0);
v_fileMap_3799_ = lean_ctor_get(v_a_3599_, 1);
v_options_3800_ = lean_ctor_get(v_a_3599_, 2);
v_currRecDepth_3801_ = lean_ctor_get(v_a_3599_, 3);
v_maxRecDepth_3802_ = lean_ctor_get(v_a_3599_, 4);
v_ref_3803_ = lean_ctor_get(v_a_3599_, 5);
v_currNamespace_3804_ = lean_ctor_get(v_a_3599_, 6);
v_openDecls_3805_ = lean_ctor_get(v_a_3599_, 7);
v_initHeartbeats_3806_ = lean_ctor_get(v_a_3599_, 8);
v_maxHeartbeats_3807_ = lean_ctor_get(v_a_3599_, 9);
v_quotContext_3808_ = lean_ctor_get(v_a_3599_, 10);
v_currMacroScope_3809_ = lean_ctor_get(v_a_3599_, 11);
v_diag_3810_ = lean_ctor_get_uint8(v_a_3599_, sizeof(void*)*14);
v_cancelTk_x3f_3811_ = lean_ctor_get(v_a_3599_, 12);
v_suppressElabErrors_3812_ = lean_ctor_get_uint8(v_a_3599_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3813_ = lean_ctor_get(v_a_3599_, 13);
v_ref_3814_ = l_Lean_replaceRef(v_p_3589_, v_ref_3803_);
lean_inc_ref(v_inheritedTraceOptions_3813_);
lean_inc(v_cancelTk_x3f_3811_);
lean_inc(v_currMacroScope_3809_);
lean_inc(v_quotContext_3808_);
lean_inc(v_maxHeartbeats_3807_);
lean_inc(v_initHeartbeats_3806_);
lean_inc(v_openDecls_3805_);
lean_inc(v_currNamespace_3804_);
lean_inc(v_maxRecDepth_3802_);
lean_inc(v_currRecDepth_3801_);
lean_inc_ref(v_options_3800_);
lean_inc_ref(v_fileMap_3799_);
lean_inc_ref(v_fileName_3798_);
v___x_3815_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3815_, 0, v_fileName_3798_);
lean_ctor_set(v___x_3815_, 1, v_fileMap_3799_);
lean_ctor_set(v___x_3815_, 2, v_options_3800_);
lean_ctor_set(v___x_3815_, 3, v_currRecDepth_3801_);
lean_ctor_set(v___x_3815_, 4, v_maxRecDepth_3802_);
lean_ctor_set(v___x_3815_, 5, v_ref_3814_);
lean_ctor_set(v___x_3815_, 6, v_currNamespace_3804_);
lean_ctor_set(v___x_3815_, 7, v_openDecls_3805_);
lean_ctor_set(v___x_3815_, 8, v_initHeartbeats_3806_);
lean_ctor_set(v___x_3815_, 9, v_maxHeartbeats_3807_);
lean_ctor_set(v___x_3815_, 10, v_quotContext_3808_);
lean_ctor_set(v___x_3815_, 11, v_currMacroScope_3809_);
lean_ctor_set(v___x_3815_, 12, v_cancelTk_x3f_3811_);
lean_ctor_set(v___x_3815_, 13, v_inheritedTraceOptions_3813_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*14, v_diag_3810_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*14 + 1, v_suppressElabErrors_3812_);
v___x_3816_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3815_, v_a_3600_);
lean_dec_ref(v___x_3815_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_dec_ref(v___x_3816_);
v___y_3671_ = v_a_3789_;
v___y_3672_ = v_k_3797_;
v___y_3673_ = v_a_3595_;
v___y_3674_ = v_a_3596_;
v___y_3675_ = v_a_3597_;
v___y_3676_ = v_a_3598_;
v___y_3677_ = v_a_3599_;
v___y_3678_ = v_a_3600_;
goto v___jp_3670_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec(v_a_3789_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
else
{
v___y_3671_ = v_a_3789_;
v___y_3672_ = v_k_3797_;
v___y_3673_ = v_a_3595_;
v___y_3674_ = v_a_3596_;
v___y_3675_ = v_a_3597_;
v___y_3676_ = v_a_3598_;
v___y_3677_ = v_a_3599_;
v___y_3678_ = v_a_3600_;
goto v___jp_3670_;
}
}
else
{
lean_object* v_fileName_3825_; lean_object* v_fileMap_3826_; lean_object* v_options_3827_; lean_object* v_currRecDepth_3828_; lean_object* v_maxRecDepth_3829_; lean_object* v_ref_3830_; lean_object* v_currNamespace_3831_; lean_object* v_openDecls_3832_; lean_object* v_initHeartbeats_3833_; lean_object* v_maxHeartbeats_3834_; lean_object* v_quotContext_3835_; lean_object* v_currMacroScope_3836_; uint8_t v_diag_3837_; lean_object* v_cancelTk_x3f_3838_; uint8_t v_suppressElabErrors_3839_; lean_object* v_inheritedTraceOptions_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3851_; 
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
v_fileName_3825_ = lean_ctor_get(v_a_3599_, 0);
v_fileMap_3826_ = lean_ctor_get(v_a_3599_, 1);
v_options_3827_ = lean_ctor_get(v_a_3599_, 2);
v_currRecDepth_3828_ = lean_ctor_get(v_a_3599_, 3);
v_maxRecDepth_3829_ = lean_ctor_get(v_a_3599_, 4);
v_ref_3830_ = lean_ctor_get(v_a_3599_, 5);
v_currNamespace_3831_ = lean_ctor_get(v_a_3599_, 6);
v_openDecls_3832_ = lean_ctor_get(v_a_3599_, 7);
v_initHeartbeats_3833_ = lean_ctor_get(v_a_3599_, 8);
v_maxHeartbeats_3834_ = lean_ctor_get(v_a_3599_, 9);
v_quotContext_3835_ = lean_ctor_get(v_a_3599_, 10);
v_currMacroScope_3836_ = lean_ctor_get(v_a_3599_, 11);
v_diag_3837_ = lean_ctor_get_uint8(v_a_3599_, sizeof(void*)*14);
v_cancelTk_x3f_3838_ = lean_ctor_get(v_a_3599_, 12);
v_suppressElabErrors_3839_ = lean_ctor_get_uint8(v_a_3599_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3840_ = lean_ctor_get(v_a_3599_, 13);
v_isSharedCheck_3851_ = !lean_is_exclusive(v_a_3599_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3842_ = v_a_3599_;
v_isShared_3843_ = v_isSharedCheck_3851_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_inheritedTraceOptions_3840_);
lean_inc(v_cancelTk_x3f_3838_);
lean_inc(v_currMacroScope_3836_);
lean_inc(v_quotContext_3835_);
lean_inc(v_maxHeartbeats_3834_);
lean_inc(v_initHeartbeats_3833_);
lean_inc(v_openDecls_3832_);
lean_inc(v_currNamespace_3831_);
lean_inc(v_ref_3830_);
lean_inc(v_maxRecDepth_3829_);
lean_inc(v_currRecDepth_3828_);
lean_inc(v_options_3827_);
lean_inc(v_fileMap_3826_);
lean_inc(v_fileName_3825_);
lean_dec(v_a_3599_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3851_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
uint8_t v___x_3844_; uint8_t v___x_3845_; lean_object* v_ref_3846_; lean_object* v___x_3848_; 
v___x_3844_ = 0;
v___x_3845_ = 1;
v_ref_3846_ = l_Lean_replaceRef(v_p_3589_, v_ref_3830_);
lean_dec(v_ref_3830_);
lean_dec(v_p_3589_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 5, v_ref_3846_);
v___x_3848_ = v___x_3842_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_fileName_3825_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_fileMap_3826_);
lean_ctor_set(v_reuseFailAlloc_3850_, 2, v_options_3827_);
lean_ctor_set(v_reuseFailAlloc_3850_, 3, v_currRecDepth_3828_);
lean_ctor_set(v_reuseFailAlloc_3850_, 4, v_maxRecDepth_3829_);
lean_ctor_set(v_reuseFailAlloc_3850_, 5, v_ref_3846_);
lean_ctor_set(v_reuseFailAlloc_3850_, 6, v_currNamespace_3831_);
lean_ctor_set(v_reuseFailAlloc_3850_, 7, v_openDecls_3832_);
lean_ctor_set(v_reuseFailAlloc_3850_, 8, v_initHeartbeats_3833_);
lean_ctor_set(v_reuseFailAlloc_3850_, 9, v_maxHeartbeats_3834_);
lean_ctor_set(v_reuseFailAlloc_3850_, 10, v_quotContext_3835_);
lean_ctor_set(v_reuseFailAlloc_3850_, 11, v_currMacroScope_3836_);
lean_ctor_set(v_reuseFailAlloc_3850_, 12, v_cancelTk_x3f_3838_);
lean_ctor_set(v_reuseFailAlloc_3850_, 13, v_inheritedTraceOptions_3840_);
lean_ctor_set_uint8(v_reuseFailAlloc_3850_, sizeof(void*)*14, v_diag_3837_);
lean_ctor_set_uint8(v_reuseFailAlloc_3850_, sizeof(void*)*14 + 1, v_suppressElabErrors_3839_);
v___x_3848_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3588_, v_id_3591_, v_a_3789_, v_k_3797_, v_minIndexable_3592_, v___x_3844_, v___x_3845_, v_a_3597_, v_a_3598_, v___x_3848_, v_a_3600_);
return v___x_3849_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3795_);
lean_dec(v_id_3591_);
if (v_incremental_3594_ == 0)
{
uint8_t v_eager_3852_; 
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
v_eager_3852_ = lean_ctor_get_uint8(v_a_3793_, 0);
lean_dec_ref(v_a_3793_);
v___y_3721_ = v_eager_3852_;
v___y_3722_ = v_a_3789_;
v___y_3723_ = v_a_3597_;
v___y_3724_ = v_a_3598_;
v___y_3725_ = v_a_3599_;
v___y_3726_ = v_a_3600_;
goto v___jp_3720_;
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec_ref(v_a_3793_);
lean_dec(v_a_3789_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v___x_3853_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3854_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3853_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3854_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3854_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
case 2:
{
uint8_t v___x_3863_; lean_object* v___x_3864_; 
lean_del_object(v___x_3795_);
v___x_3863_ = 0;
lean_inc(v_a_3600_);
lean_inc_ref(v_a_3599_);
lean_inc(v_a_3598_);
lean_inc_ref(v_a_3597_);
lean_inc(v_a_3789_);
v___x_3864_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3789_, v___x_3863_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref(v___x_3864_);
if (lean_obj_tag(v_a_3865_) == 1)
{
lean_dec(v_a_3789_);
if (v_incremental_3594_ == 0)
{
lean_object* v_val_3866_; 
v_val_3866_ = lean_ctor_get(v_a_3865_, 0);
lean_inc(v_val_3866_);
lean_dec_ref(v_a_3865_);
v___y_3779_ = v_val_3866_;
v___y_3780_ = v_a_3595_;
v___y_3781_ = v_a_3596_;
v___y_3782_ = v_a_3597_;
v___y_3783_ = v_a_3598_;
v___y_3784_ = v_a_3599_;
v___y_3785_ = v_a_3600_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_dec_ref(v_a_3865_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v___x_3867_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3868_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3867_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3868_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3868_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
else
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
lean_dec(v_a_3865_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v___x_3877_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_3878_ = l_Lean_MessageData_ofConstName(v_a_3789_, v___x_3863_);
v___x_3879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3877_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
v___x_3880_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_3881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3881_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v_a_3789_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_3891_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3864_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3864_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
case 3:
{
lean_del_object(v___x_3795_);
v___y_3603_ = v_a_3789_;
v___y_3604_ = v_a_3595_;
v___y_3605_ = v_a_3596_;
v___y_3606_ = v_a_3597_;
v___y_3607_ = v_a_3598_;
v___y_3608_ = v_a_3599_;
v___y_3609_ = v_a_3600_;
goto v___jp_3602_;
}
case 4:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_del_object(v___x_3795_);
lean_dec(v_a_3789_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v___x_3899_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_3900_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3899_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3900_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3900_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
case 5:
{
lean_object* v_prio_3909_; lean_object* v___x_3910_; 
lean_del_object(v___x_3795_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
v_prio_3909_ = lean_ctor_get(v_a_3793_, 0);
lean_inc(v_prio_3909_);
lean_dec_ref(v_a_3793_);
v___x_3910_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3592_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3934_; 
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3934_ == 0)
{
lean_object* v_unused_3935_; 
v_unused_3935_ = lean_ctor_get(v___x_3910_, 0);
lean_dec(v_unused_3935_);
v___x_3912_ = v___x_3910_;
v_isShared_3913_ = v_isSharedCheck_3934_;
goto v_resetjp_3911_;
}
else
{
lean_dec(v___x_3910_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3934_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v_config_3914_; lean_object* v_extensions_3915_; lean_object* v_extra_3916_; lean_object* v_extraInj_3917_; lean_object* v_extraFacts_3918_; lean_object* v_symPrios_3919_; lean_object* v_norm_3920_; lean_object* v_normProcs_3921_; lean_object* v_anchorRefs_x3f_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3933_; 
v_config_3914_ = lean_ctor_get(v_params_3588_, 0);
v_extensions_3915_ = lean_ctor_get(v_params_3588_, 1);
v_extra_3916_ = lean_ctor_get(v_params_3588_, 2);
v_extraInj_3917_ = lean_ctor_get(v_params_3588_, 3);
v_extraFacts_3918_ = lean_ctor_get(v_params_3588_, 4);
v_symPrios_3919_ = lean_ctor_get(v_params_3588_, 5);
v_norm_3920_ = lean_ctor_get(v_params_3588_, 6);
v_normProcs_3921_ = lean_ctor_get(v_params_3588_, 7);
v_anchorRefs_x3f_3922_ = lean_ctor_get(v_params_3588_, 8);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_params_3588_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3924_ = v_params_3588_;
v_isShared_3925_ = v_isSharedCheck_3933_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_anchorRefs_x3f_3922_);
lean_inc(v_normProcs_3921_);
lean_inc(v_norm_3920_);
lean_inc(v_symPrios_3919_);
lean_inc(v_extraFacts_3918_);
lean_inc(v_extraInj_3917_);
lean_inc(v_extra_3916_);
lean_inc(v_extensions_3915_);
lean_inc(v_config_3914_);
lean_dec(v_params_3588_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3933_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3926_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_3919_, v_a_3789_, v_prio_3909_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 5, v___x_3926_);
v___x_3928_ = v___x_3924_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_config_3914_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_extensions_3915_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_extra_3916_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_extraInj_3917_);
lean_ctor_set(v_reuseFailAlloc_3932_, 4, v_extraFacts_3918_);
lean_ctor_set(v_reuseFailAlloc_3932_, 5, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3932_, 6, v_norm_3920_);
lean_ctor_set(v_reuseFailAlloc_3932_, 7, v_normProcs_3921_);
lean_ctor_set(v_reuseFailAlloc_3932_, 8, v_anchorRefs_x3f_3922_);
v___x_3928_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3930_; 
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 0, v___x_3928_);
v___x_3930_ = v___x_3912_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3928_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec(v_prio_3909_);
lean_dec(v_a_3789_);
lean_dec_ref(v_params_3588_);
v_a_3936_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3910_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3910_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
case 6:
{
lean_object* v___x_3944_; 
lean_del_object(v___x_3795_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
v___x_3944_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3789_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3969_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3947_ = v___x_3944_;
v_isShared_3948_ = v_isSharedCheck_3969_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3944_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3969_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v_config_3949_; lean_object* v_extensions_3950_; lean_object* v_extra_3951_; lean_object* v_extraInj_3952_; lean_object* v_extraFacts_3953_; lean_object* v_symPrios_3954_; lean_object* v_norm_3955_; lean_object* v_normProcs_3956_; lean_object* v_anchorRefs_x3f_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3968_; 
v_config_3949_ = lean_ctor_get(v_params_3588_, 0);
v_extensions_3950_ = lean_ctor_get(v_params_3588_, 1);
v_extra_3951_ = lean_ctor_get(v_params_3588_, 2);
v_extraInj_3952_ = lean_ctor_get(v_params_3588_, 3);
v_extraFacts_3953_ = lean_ctor_get(v_params_3588_, 4);
v_symPrios_3954_ = lean_ctor_get(v_params_3588_, 5);
v_norm_3955_ = lean_ctor_get(v_params_3588_, 6);
v_normProcs_3956_ = lean_ctor_get(v_params_3588_, 7);
v_anchorRefs_x3f_3957_ = lean_ctor_get(v_params_3588_, 8);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_params_3588_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3959_ = v_params_3588_;
v_isShared_3960_ = v_isSharedCheck_3968_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_anchorRefs_x3f_3957_);
lean_inc(v_normProcs_3956_);
lean_inc(v_norm_3955_);
lean_inc(v_symPrios_3954_);
lean_inc(v_extraFacts_3953_);
lean_inc(v_extraInj_3952_);
lean_inc(v_extra_3951_);
lean_inc(v_extensions_3950_);
lean_inc(v_config_3949_);
lean_dec(v_params_3588_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3968_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; lean_object* v___x_3963_; 
v___x_3961_ = l_Lean_PersistentArray_push___redArg(v_extraInj_3952_, v_a_3945_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 3, v___x_3961_);
v___x_3963_ = v___x_3959_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_config_3949_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_extensions_3950_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_extra_3951_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v___x_3961_);
lean_ctor_set(v_reuseFailAlloc_3967_, 4, v_extraFacts_3953_);
lean_ctor_set(v_reuseFailAlloc_3967_, 5, v_symPrios_3954_);
lean_ctor_set(v_reuseFailAlloc_3967_, 6, v_norm_3955_);
lean_ctor_set(v_reuseFailAlloc_3967_, 7, v_normProcs_3956_);
lean_ctor_set(v_reuseFailAlloc_3967_, 8, v_anchorRefs_x3f_3957_);
v___x_3963_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3965_; 
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 0, v___x_3963_);
v___x_3965_ = v___x_3947_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec_ref(v_params_3588_);
v_a_3970_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3944_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3944_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
case 7:
{
lean_object* v___x_3978_; lean_object* v___x_3980_; 
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
v___x_3978_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3588_, v_a_3789_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v___x_3978_);
v___x_3980_ = v___x_3795_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
case 8:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec_ref(v_a_3793_);
lean_del_object(v___x_3795_);
lean_dec(v_a_3789_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v___x_3982_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_3983_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3982_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3983_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
default: 
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_del_object(v___x_3795_);
lean_dec(v_a_3789_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v___x_3992_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_3993_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3992_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3993_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3993_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
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
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec(v_a_3789_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_4003_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3792_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3792_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3590_);
v___y_3603_ = v_a_3789_;
v___y_3604_ = v_a_3595_;
v___y_3605_ = v_a_3596_;
v___y_3606_ = v_a_3597_;
v___y_3607_ = v_a_3598_;
v___y_3608_ = v_a_3599_;
v___y_3609_ = v_a_3600_;
goto v___jp_3602_;
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec(v_a_3789_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_mod_x3f_3590_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_4011_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_3790_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_3790_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
v___jp_4019_:
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4030_; 
v_a_4021_ = lean_ctor_get(v___y_4020_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___y_4020_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4023_ = v___y_4020_;
v_isShared_4024_ = v_isSharedCheck_4030_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___y_4020_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4030_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
if (lean_obj_tag(v_a_4021_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4027_; 
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_id_3591_);
lean_dec(v_mod_x3f_3590_);
lean_dec(v_p_3589_);
lean_dec_ref(v_params_3588_);
v_a_4025_ = lean_ctor_get(v_a_4021_, 0);
lean_inc(v_a_4025_);
lean_dec_ref(v_a_4021_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 0, v_a_4025_);
v___x_4027_ = v___x_4023_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_a_4025_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
else
{
lean_object* v_a_4029_; 
lean_del_object(v___x_4023_);
v_a_4029_ = lean_ctor_get(v_a_4021_, 0);
lean_inc(v_a_4029_);
lean_dec_ref(v_a_4021_);
v_a_3789_ = v_a_4029_;
goto v___jp_3788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4109_, lean_object* v_p_4110_, lean_object* v_mod_x3f_4111_, lean_object* v_id_4112_, lean_object* v_minIndexable_4113_, lean_object* v_only_4114_, lean_object* v_incremental_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_){
_start:
{
uint8_t v_minIndexable_boxed_4123_; uint8_t v_only_boxed_4124_; uint8_t v_incremental_boxed_4125_; lean_object* v_res_4126_; 
v_minIndexable_boxed_4123_ = lean_unbox(v_minIndexable_4113_);
v_only_boxed_4124_ = lean_unbox(v_only_4114_);
v_incremental_boxed_4125_ = lean_unbox(v_incremental_4115_);
v_res_4126_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4109_, v_p_4110_, v_mod_x3f_4111_, v_id_4112_, v_minIndexable_boxed_4123_, v_only_boxed_4124_, v_incremental_boxed_4125_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4127_, lean_object* v_id_4128_, uint8_t v_minIndexable_4129_, lean_object* v_as_4130_, lean_object* v_as_x27_4131_, lean_object* v_b_4132_, lean_object* v_a_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v___x_4141_; 
v___x_4141_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4127_, v_id_4128_, v_minIndexable_4129_, v_as_x27_4131_, v_b_4132_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4142_, lean_object* v_id_4143_, lean_object* v_minIndexable_4144_, lean_object* v_as_4145_, lean_object* v_as_x27_4146_, lean_object* v_b_4147_, lean_object* v_a_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
uint8_t v_minIndexable_boxed_4156_; lean_object* v_res_4157_; 
v_minIndexable_boxed_4156_ = lean_unbox(v_minIndexable_4144_);
v_res_4157_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4142_, v_id_4143_, v_minIndexable_boxed_4156_, v_as_4145_, v_as_x27_4146_, v_b_4147_, v_a_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v_as_4145_);
lean_dec(v_p_4142_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4158_, lean_object* v_as_x27_4159_, lean_object* v_b_4160_, lean_object* v_a_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4159_, v_b_4160_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4170_, lean_object* v_as_x27_4171_, lean_object* v_b_4172_, lean_object* v_a_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4170_, v_as_x27_4171_, v_b_4172_, v_a_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v_as_4170_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4182_, lean_object* v_ref_4183_, lean_object* v_msg_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4183_, v_msg_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4193_, lean_object* v_ref_4194_, lean_object* v_msg_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4193_, v_ref_4194_, v_msg_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
lean_dec(v___y_4201_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec(v_ref_4194_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4204_, lean_object* v_id_4205_, uint8_t v_minIndexable_4206_, lean_object* v_as_4207_, lean_object* v_as_x27_4208_, lean_object* v_b_4209_, lean_object* v_a_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4204_, v_id_4205_, v_minIndexable_4206_, v_as_x27_4208_, v_b_4209_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4219_, lean_object* v_id_4220_, lean_object* v_minIndexable_4221_, lean_object* v_as_4222_, lean_object* v_as_x27_4223_, lean_object* v_b_4224_, lean_object* v_a_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
uint8_t v_minIndexable_boxed_4233_; lean_object* v_res_4234_; 
v_minIndexable_boxed_4233_ = lean_unbox(v_minIndexable_4221_);
v_res_4234_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4219_, v_id_4220_, v_minIndexable_boxed_4233_, v_as_4222_, v_as_x27_4223_, v_b_4224_, v_a_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v_as_4222_);
lean_dec(v_p_4219_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4235_, lean_object* v_t_4236_, lean_object* v_k_4237_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4236_, v_k_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4239_, lean_object* v_t_4240_, lean_object* v_k_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4239_, v_t_4240_, v_k_4241_);
lean_dec(v_k_4241_);
lean_dec(v_t_4240_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4243_, uint8_t v_skipAuxDecl_4244_, lean_object* v_auxDeclToFullName_4245_, lean_object* v___x_4246_, lean_object* v_givenNameView_4247_, lean_object* v_as_4248_, lean_object* v_i_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v___x_4251_; 
v___x_4251_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4243_, v_skipAuxDecl_4244_, v_auxDeclToFullName_4245_, v___x_4246_, v_givenNameView_4247_, v_as_4248_, v_i_4249_);
return v___x_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4252_, lean_object* v_skipAuxDecl_4253_, lean_object* v_auxDeclToFullName_4254_, lean_object* v___x_4255_, lean_object* v_givenNameView_4256_, lean_object* v_as_4257_, lean_object* v_i_4258_, lean_object* v_a_4259_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4260_; lean_object* v_res_4261_; 
v_skipAuxDecl_boxed_4260_ = lean_unbox(v_skipAuxDecl_4253_);
v_res_4261_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4252_, v_skipAuxDecl_boxed_4260_, v_auxDeclToFullName_4254_, v___x_4255_, v_givenNameView_4256_, v_as_4257_, v_i_4258_, v_a_4259_);
lean_dec_ref(v_as_4257_);
lean_dec(v_auxDeclToFullName_4254_);
lean_dec(v_givenName_4252_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4262_, lean_object* v_givenName_4263_, lean_object* v_as_4264_, lean_object* v_i_4265_, lean_object* v_a_4266_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4262_, v_givenName_4263_, v_as_4264_, v_i_4265_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4268_, lean_object* v_givenName_4269_, lean_object* v_as_4270_, lean_object* v_i_4271_, lean_object* v_a_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4268_, v_givenName_4269_, v_as_4270_, v_i_4271_, v_a_4272_);
lean_dec_ref(v_as_4270_);
lean_dec(v_givenName_4269_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4274_, uint8_t v_skipAuxDecl_4275_, lean_object* v_auxDeclToFullName_4276_, lean_object* v___x_4277_, lean_object* v_givenNameView_4278_, lean_object* v_as_4279_, lean_object* v_i_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v___x_4282_; 
v___x_4282_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4274_, v_skipAuxDecl_4275_, v_auxDeclToFullName_4276_, v___x_4277_, v_givenNameView_4278_, v_as_4279_, v_i_4280_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4283_, lean_object* v_skipAuxDecl_4284_, lean_object* v_auxDeclToFullName_4285_, lean_object* v___x_4286_, lean_object* v_givenNameView_4287_, lean_object* v_as_4288_, lean_object* v_i_4289_, lean_object* v_a_4290_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4291_; lean_object* v_res_4292_; 
v_skipAuxDecl_boxed_4291_ = lean_unbox(v_skipAuxDecl_4284_);
v_res_4292_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4283_, v_skipAuxDecl_boxed_4291_, v_auxDeclToFullName_4285_, v___x_4286_, v_givenNameView_4287_, v_as_4288_, v_i_4289_, v_a_4290_);
lean_dec_ref(v_as_4288_);
lean_dec(v_auxDeclToFullName_4285_);
lean_dec(v_givenName_4283_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4293_, lean_object* v_givenName_4294_, lean_object* v_as_4295_, lean_object* v_i_4296_, lean_object* v_a_4297_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4293_, v_givenName_4294_, v_as_4295_, v_i_4296_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4299_, lean_object* v_givenName_4300_, lean_object* v_as_4301_, lean_object* v_i_4302_, lean_object* v_a_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4299_, v_givenName_4300_, v_as_4301_, v_i_4302_, v_a_4303_);
lean_dec_ref(v_as_4301_);
lean_dec(v_givenName_4300_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17(lean_object* v_opt_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___redArg(v_opt_4305_, v___y_4310_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17___boxed(lean_object* v_opt_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__17(v_opt_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec_ref(v_opt_4314_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21(lean_object* v_ref_4323_, lean_object* v_msgData_4324_, uint8_t v_severity_4325_, uint8_t v_isSilent_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___redArg(v_ref_4323_, v_msgData_4324_, v_severity_4325_, v_isSilent_4326_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21___boxed(lean_object* v_ref_4335_, lean_object* v_msgData_4336_, lean_object* v_severity_4337_, lean_object* v_isSilent_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
uint8_t v_severity_boxed_4346_; uint8_t v_isSilent_boxed_4347_; lean_object* v_res_4348_; 
v_severity_boxed_4346_ = lean_unbox(v_severity_4337_);
v_isSilent_boxed_4347_ = lean_unbox(v_isSilent_4338_);
v_res_4348_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16_spec__18_spec__20_spec__21(v_ref_4335_, v_msgData_4336_, v_severity_boxed_4346_, v_isSilent_boxed_4347_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v_ref_4335_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4349_, lean_object* v_b_4350_, lean_object* v_____r_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4359_ = lean_box(0);
lean_inc(v___y_4357_);
lean_inc_ref(v___y_4356_);
v___x_4360_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4349_, v___x_4359_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4362_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref(v___x_4360_);
lean_inc(v___y_4357_);
lean_inc_ref(v___y_4356_);
lean_inc(v___y_4355_);
lean_inc(v_a_4361_);
v___x_4362_ = l_Lean_Linter_checkDeprecated(v_a_4361_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4362_) == 0)
{
uint8_t v___x_4363_; lean_object* v___x_4364_; 
lean_dec_ref(v___x_4362_);
v___x_4363_ = 0;
lean_inc(v_a_4361_);
v___x_4364_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4361_, v___x_4363_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4424_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4367_ = v___x_4364_;
v_isShared_4368_ = v_isSharedCheck_4424_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4364_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4424_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
if (lean_obj_tag(v_a_4365_) == 1)
{
lean_object* v_val_4369_; lean_object* v___x_4370_; 
lean_del_object(v___x_4367_);
lean_dec(v_a_4361_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
v_val_4369_ = lean_ctor_get(v_a_4365_, 0);
lean_inc(v_val_4369_);
lean_dec_ref(v_a_4365_);
lean_inc(v_val_4369_);
v___x_4370_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4369_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v___x_4371_; 
lean_dec_ref(v___x_4370_);
v___x_4371_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4350_, v_val_4369_, v___y_4356_, v___y_4357_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4381_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4374_ = v___x_4371_;
v_isShared_4375_ = v_isSharedCheck_4381_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4371_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4381_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4379_; 
v___x_4376_ = lean_box(0);
v___x_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
lean_ctor_set(v___x_4377_, 1, v_a_4372_);
if (v_isShared_4375_ == 0)
{
lean_ctor_set(v___x_4374_, 0, v___x_4377_);
v___x_4379_ = v___x_4374_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4377_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
v_a_4382_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4371_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4371_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v_val_4369_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec_ref(v_b_4350_);
v_a_4390_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4370_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4370_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
else
{
uint8_t v___x_4398_; 
lean_dec(v_a_4365_);
lean_inc(v_a_4361_);
v___x_4398_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4350_, v_a_4361_);
if (v___x_4398_ == 0)
{
lean_object* v___x_4399_; 
lean_del_object(v___x_4367_);
v___x_4399_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4350_, v_a_4361_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4409_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4402_ = v___x_4399_;
v_isShared_4403_ = v_isSharedCheck_4409_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4399_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4409_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
v___x_4404_ = lean_box(0);
v___x_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
lean_ctor_set(v___x_4405_, 1, v_a_4400_);
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 0, v___x_4405_);
v___x_4407_ = v___x_4402_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
v_a_4410_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4399_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4399_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
else
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4422_; 
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
v___x_4418_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4350_, v_a_4361_);
v___x_4419_ = lean_box(0);
v___x_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
lean_ctor_set(v___x_4420_, 1, v___x_4418_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 0, v___x_4420_);
v___x_4422_ = v___x_4367_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4420_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_a_4361_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec_ref(v_b_4350_);
v_a_4425_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4364_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4364_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v_a_4361_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec_ref(v_b_4350_);
v_a_4433_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4362_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4362_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec_ref(v_b_4350_);
v_a_4441_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4360_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4360_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4449_, lean_object* v_b_4450_, lean_object* v_____r_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4449_, v_b_4450_, v_____r_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4463_, lean_object* v_b_4464_, lean_object* v_a_4465_, uint8_t v___x_4466_, uint8_t v_only_4467_, uint8_t v_incremental_4468_, lean_object* v_x_4469_, lean_object* v_mod_x3f_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; uint8_t v___x_4481_; 
v___x_4478_ = lean_unsigned_to_nat(1u);
v___x_4479_ = l_Lean_Syntax_getArg(v___x_4463_, v___x_4478_);
v___x_4480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4479_);
v___x_4481_ = l_Lean_Syntax_isOfKind(v___x_4479_, v___x_4480_);
if (v___x_4481_ == 0)
{
lean_object* v___x_4482_; 
v___x_4482_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4464_, v_a_4465_, v_mod_x3f_4470_, v___x_4479_, v___x_4481_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4492_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4485_ = v___x_4482_;
v_isShared_4486_ = v_isSharedCheck_4492_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v___x_4482_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4492_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4490_; 
v___x_4487_ = lean_box(0);
v___x_4488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4487_);
lean_ctor_set(v___x_4488_, 1, v_a_4483_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 0, v___x_4488_);
v___x_4490_ = v___x_4485_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4488_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
v_a_4493_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4495_ = v___x_4482_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4482_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4493_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
else
{
lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4501_ = l_Lean_TSyntax_getId(v___x_4479_);
lean_inc_ref(v___y_4475_);
lean_inc_ref(v___y_4473_);
v___x_4502_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4501_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4503_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; 
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4503_);
lean_dec_ref(v___x_4502_);
if (lean_obj_tag(v_a_4503_) == 1)
{
lean_object* v_val_4530_; lean_object* v_snd_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4556_; 
v_val_4530_ = lean_ctor_get(v_a_4503_, 0);
lean_inc(v_val_4530_);
lean_dec_ref(v_a_4503_);
v_snd_4531_ = lean_ctor_get(v_val_4530_, 1);
v_isSharedCheck_4556_ = !lean_is_exclusive(v_val_4530_);
if (v_isSharedCheck_4556_ == 0)
{
lean_object* v_unused_4557_; 
v_unused_4557_ = lean_ctor_get(v_val_4530_, 0);
lean_dec(v_unused_4557_);
v___x_4533_ = v_val_4530_;
v_isShared_4534_ = v_isSharedCheck_4556_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_snd_4531_);
lean_dec(v_val_4530_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4556_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
if (lean_obj_tag(v_snd_4531_) == 1)
{
lean_object* v___x_4535_; 
lean_dec_ref(v_snd_4531_);
v___x_4535_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4464_, v_a_4465_, v_mod_x3f_4470_, v___x_4479_, v___x_4466_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4547_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4538_ = v___x_4535_;
v_isShared_4539_ = v_isSharedCheck_4547_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4535_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4547_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4540_; lean_object* v___x_4542_; 
v___x_4540_ = lean_box(0);
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 1, v_a_4536_);
lean_ctor_set(v___x_4533_, 0, v___x_4540_);
v___x_4542_ = v___x_4533_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v___x_4540_);
lean_ctor_set(v_reuseFailAlloc_4546_, 1, v_a_4536_);
v___x_4542_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
lean_object* v___x_4544_; 
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 0, v___x_4542_);
v___x_4544_ = v___x_4538_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4555_; 
lean_del_object(v___x_4533_);
v_a_4548_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4550_ = v___x_4535_;
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4535_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4551_ == 0)
{
v___x_4553_ = v___x_4550_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
else
{
lean_del_object(v___x_4533_);
lean_dec(v_snd_4531_);
v___y_4505_ = v___y_4471_;
v___y_4506_ = v___y_4472_;
v___y_4507_ = v___y_4473_;
v___y_4508_ = v___y_4474_;
v___y_4509_ = v___y_4475_;
v___y_4510_ = v___y_4476_;
goto v___jp_4504_;
}
}
}
else
{
lean_dec(v_a_4503_);
v___y_4505_ = v___y_4471_;
v___y_4506_ = v___y_4472_;
v___y_4507_ = v___y_4473_;
v___y_4508_ = v___y_4474_;
v___y_4509_ = v___y_4475_;
v___y_4510_ = v___y_4476_;
goto v___jp_4504_;
}
v___jp_4504_:
{
lean_object* v___x_4511_; 
v___x_4511_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4464_, v_a_4465_, v_mod_x3f_4470_, v___x_4479_, v___x_4466_, v_only_4467_, v_incremental_4468_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4521_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4514_ = v___x_4511_;
v_isShared_4515_ = v_isSharedCheck_4521_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4511_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4521_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4519_; 
v___x_4516_ = lean_box(0);
v___x_4517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
lean_ctor_set(v___x_4517_, 1, v_a_4512_);
if (v_isShared_4515_ == 0)
{
lean_ctor_set(v___x_4514_, 0, v___x_4517_);
v___x_4519_ = v___x_4514_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4517_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
else
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
v_a_4522_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4524_ = v___x_4511_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4511_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
}
}
else
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4565_; 
lean_dec(v___x_4479_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v_mod_x3f_4470_);
lean_dec(v_a_4465_);
lean_dec_ref(v_b_4464_);
v_a_4558_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4560_ = v___x_4502_;
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4502_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4561_ == 0)
{
v___x_4563_ = v___x_4560_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4558_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4566_, lean_object* v_b_4567_, lean_object* v_a_4568_, lean_object* v___x_4569_, lean_object* v_only_4570_, lean_object* v_incremental_4571_, lean_object* v_x_4572_, lean_object* v_mod_x3f_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
uint8_t v___x_24005__boxed_4581_; uint8_t v_only_boxed_4582_; uint8_t v_incremental_boxed_4583_; lean_object* v_res_4584_; 
v___x_24005__boxed_4581_ = lean_unbox(v___x_4569_);
v_only_boxed_4582_ = lean_unbox(v_only_4570_);
v_incremental_boxed_4583_ = lean_unbox(v_incremental_4571_);
v_res_4584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4566_, v_b_4567_, v_a_4568_, v___x_24005__boxed_4581_, v_only_boxed_4582_, v_incremental_boxed_4583_, v_x_4572_, v_mod_x3f_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
lean_dec(v___x_4566_);
return v_res_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4585_, lean_object* v___x_4586_, lean_object* v_____r_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v___x_4595_; 
v___x_4595_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4585_, v___x_4586_, v___y_4592_, v___y_4593_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4605_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4598_ = v___x_4595_;
v_isShared_4599_ = v_isSharedCheck_4605_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4595_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4605_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4603_; 
v___x_4600_ = lean_box(0);
v___x_4601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4600_);
lean_ctor_set(v___x_4601_, 1, v_a_4596_);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 0, v___x_4601_);
v___x_4603_ = v___x_4598_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v___x_4601_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
v_a_4606_ = lean_ctor_get(v___x_4595_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4595_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4595_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4614_, lean_object* v___x_4615_, lean_object* v_____r_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4614_, v___x_4615_, v_____r_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec(v___x_4615_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4625_, lean_object* v_b_4626_, lean_object* v_a_4627_, uint8_t v___x_4628_, uint8_t v_only_4629_, uint8_t v_incremental_4630_, lean_object* v_x_4631_, lean_object* v_mod_x3f_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; uint8_t v___x_4643_; 
v___x_4640_ = lean_unsigned_to_nat(2u);
v___x_4641_ = l_Lean_Syntax_getArg(v___x_4625_, v___x_4640_);
v___x_4642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4641_);
v___x_4643_ = l_Lean_Syntax_isOfKind(v___x_4641_, v___x_4642_);
if (v___x_4643_ == 0)
{
lean_object* v___x_4644_; 
v___x_4644_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4626_, v_a_4627_, v_mod_x3f_4632_, v___x_4641_, v___x_4628_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4654_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4647_ = v___x_4644_;
v_isShared_4648_ = v_isSharedCheck_4654_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4644_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4654_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4652_; 
v___x_4649_ = lean_box(0);
v___x_4650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
lean_ctor_set(v___x_4650_, 1, v_a_4645_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 0, v___x_4650_);
v___x_4652_ = v___x_4647_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4650_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
else
{
lean_object* v_a_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4662_; 
v_a_4655_ = lean_ctor_get(v___x_4644_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4644_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4657_ = v___x_4644_;
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_a_4655_);
lean_dec(v___x_4644_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4662_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
lean_object* v___x_4660_; 
if (v_isShared_4658_ == 0)
{
v___x_4660_ = v___x_4657_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_a_4655_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
}
else
{
lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4663_ = l_Lean_TSyntax_getId(v___x_4641_);
lean_inc_ref(v___y_4637_);
lean_inc_ref(v___y_4635_);
v___x_4664_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4663_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4672_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref(v___x_4664_);
if (lean_obj_tag(v_a_4665_) == 1)
{
lean_object* v_val_4692_; lean_object* v_snd_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4718_; 
v_val_4692_ = lean_ctor_get(v_a_4665_, 0);
lean_inc(v_val_4692_);
lean_dec_ref(v_a_4665_);
v_snd_4693_ = lean_ctor_get(v_val_4692_, 1);
v_isSharedCheck_4718_ = !lean_is_exclusive(v_val_4692_);
if (v_isSharedCheck_4718_ == 0)
{
lean_object* v_unused_4719_; 
v_unused_4719_ = lean_ctor_get(v_val_4692_, 0);
lean_dec(v_unused_4719_);
v___x_4695_ = v_val_4692_;
v_isShared_4696_ = v_isSharedCheck_4718_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_snd_4693_);
lean_dec(v_val_4692_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4718_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
if (lean_obj_tag(v_snd_4693_) == 1)
{
lean_object* v___x_4697_; 
lean_dec_ref(v_snd_4693_);
v___x_4697_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4626_, v_a_4627_, v_mod_x3f_4632_, v___x_4641_, v___x_4628_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4709_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4700_ = v___x_4697_;
v_isShared_4701_ = v_isSharedCheck_4709_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4697_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4709_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4702_; lean_object* v___x_4704_; 
v___x_4702_ = lean_box(0);
if (v_isShared_4696_ == 0)
{
lean_ctor_set(v___x_4695_, 1, v_a_4698_);
lean_ctor_set(v___x_4695_, 0, v___x_4702_);
v___x_4704_ = v___x_4695_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4702_);
lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_a_4698_);
v___x_4704_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
lean_object* v___x_4706_; 
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 0, v___x_4704_);
v___x_4706_ = v___x_4700_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4704_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
lean_del_object(v___x_4695_);
v_a_4710_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4697_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4697_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
else
{
lean_del_object(v___x_4695_);
lean_dec(v_snd_4693_);
v___y_4667_ = v___y_4633_;
v___y_4668_ = v___y_4634_;
v___y_4669_ = v___y_4635_;
v___y_4670_ = v___y_4636_;
v___y_4671_ = v___y_4637_;
v___y_4672_ = v___y_4638_;
goto v___jp_4666_;
}
}
}
else
{
lean_dec(v_a_4665_);
v___y_4667_ = v___y_4633_;
v___y_4668_ = v___y_4634_;
v___y_4669_ = v___y_4635_;
v___y_4670_ = v___y_4636_;
v___y_4671_ = v___y_4637_;
v___y_4672_ = v___y_4638_;
goto v___jp_4666_;
}
v___jp_4666_:
{
lean_object* v___x_4673_; 
v___x_4673_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4626_, v_a_4627_, v_mod_x3f_4632_, v___x_4641_, v___x_4628_, v_only_4629_, v_incremental_4630_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4683_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4676_ = v___x_4673_;
v_isShared_4677_ = v_isSharedCheck_4683_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4673_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4683_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4681_; 
v___x_4678_ = lean_box(0);
v___x_4679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
lean_ctor_set(v___x_4679_, 1, v_a_4674_);
if (v_isShared_4677_ == 0)
{
lean_ctor_set(v___x_4676_, 0, v___x_4679_);
v___x_4681_ = v___x_4676_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4679_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
v_a_4684_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4673_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4673_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
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
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
lean_dec(v___x_4641_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec(v_mod_x3f_4632_);
lean_dec(v_a_4627_);
lean_dec_ref(v_b_4626_);
v_a_4720_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4664_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4664_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4728_, lean_object* v_b_4729_, lean_object* v_a_4730_, lean_object* v___x_4731_, lean_object* v_only_4732_, lean_object* v_incremental_4733_, lean_object* v_x_4734_, lean_object* v_mod_x3f_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
uint8_t v___x_24284__boxed_4743_; uint8_t v_only_boxed_4744_; uint8_t v_incremental_boxed_4745_; lean_object* v_res_4746_; 
v___x_24284__boxed_4743_ = lean_unbox(v___x_4731_);
v_only_boxed_4744_ = lean_unbox(v_only_4732_);
v_incremental_boxed_4745_ = lean_unbox(v_incremental_4733_);
v_res_4746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4728_, v_b_4729_, v_a_4730_, v___x_24284__boxed_4743_, v_only_boxed_4744_, v_incremental_boxed_4745_, v_x_4734_, v_mod_x3f_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
lean_dec(v___x_4728_);
return v_res_4746_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4755_ = l_Lean_stringToMessageData(v___x_4754_);
return v___x_4755_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15(void){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14));
v___x_4785_ = l_Lean_stringToMessageData(v___x_4784_);
return v___x_4785_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4788_ = l_Lean_stringToMessageData(v___x_4787_);
return v___x_4788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4789_, uint8_t v_only_4790_, uint8_t v_incremental_4791_, lean_object* v_as_4792_, size_t v_sz_4793_, size_t v_i_4794_, lean_object* v_b_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_){
_start:
{
lean_object* v_snd_4804_; lean_object* v___y_4809_; uint8_t v___y_4810_; lean_object* v_a_4814_; lean_object* v___y_4818_; uint8_t v___x_4822_; 
v___x_4822_ = lean_usize_dec_lt(v_i_4794_, v_sz_4793_);
if (v___x_4822_ == 0)
{
lean_object* v___x_4823_; 
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
v___x_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4823_, 0, v_b_4795_);
return v___x_4823_;
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4825_; uint8_t v___x_4826_; 
v_a_4824_ = lean_array_uget_borrowed(v_as_4792_, v_i_4794_);
v___x_4825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4824_);
v___x_4826_ = l_Lean_Syntax_isOfKind(v_a_4824_, v___x_4825_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4827_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4824_);
v___x_4828_ = l_Lean_MessageData_ofSyntax(v_a_4824_);
v___x_4829_ = l_Lean_indentD(v___x_4828_);
v___x_4830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4827_);
lean_ctor_set(v___x_4830_, 1, v___x_4829_);
lean_inc_ref(v___y_4796_);
v___x_4831_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4830_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_dec_ref(v___x_4831_);
v_snd_4804_ = v_b_4795_;
goto v___jp_4803_;
}
else
{
lean_object* v_a_4832_; 
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
lean_inc(v_a_4832_);
lean_dec_ref(v___x_4831_);
v_a_4814_ = v_a_4832_;
goto v___jp_4813_;
}
}
else
{
lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v___x_4833_ = lean_unsigned_to_nat(0u);
v___x_4834_ = l_Lean_Syntax_getArg(v_a_4824_, v___x_4833_);
v___x_4835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_4834_);
v___x_4836_ = l_Lean_Syntax_isOfKind(v___x_4834_, v___x_4835_);
if (v___x_4836_ == 0)
{
lean_object* v___x_4837_; uint8_t v___x_4838_; 
v___x_4837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_4834_);
v___x_4838_ = l_Lean_Syntax_isOfKind(v___x_4834_, v___x_4837_);
if (v___x_4838_ == 0)
{
lean_object* v___x_4839_; uint8_t v___x_4840_; 
v___x_4839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_4834_);
v___x_4840_ = l_Lean_Syntax_isOfKind(v___x_4834_, v___x_4839_);
if (v___x_4840_ == 0)
{
lean_object* v___x_4841_; uint8_t v___x_4842_; 
v___x_4841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_4834_);
v___x_4842_ = l_Lean_Syntax_isOfKind(v___x_4834_, v___x_4841_);
if (v___x_4842_ == 0)
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
lean_dec(v___x_4834_);
v___x_4843_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4824_);
v___x_4844_ = l_Lean_MessageData_ofSyntax(v_a_4824_);
v___x_4845_ = l_Lean_indentD(v___x_4844_);
v___x_4846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4843_);
lean_ctor_set(v___x_4846_, 1, v___x_4845_);
lean_inc_ref(v___y_4796_);
v___x_4847_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4846_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_dec_ref(v___x_4847_);
v_snd_4804_ = v_b_4795_;
goto v___jp_4803_;
}
else
{
lean_object* v_a_4848_; 
v_a_4848_ = lean_ctor_get(v___x_4847_, 0);
lean_inc(v_a_4848_);
lean_dec_ref(v___x_4847_);
v_a_4814_ = v_a_4848_;
goto v___jp_4813_;
}
}
else
{
lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; uint8_t v___x_4852_; 
v___x_4849_ = lean_unsigned_to_nat(1u);
v___x_4850_ = l_Lean_Syntax_getArg(v___x_4834_, v___x_4849_);
lean_dec(v___x_4834_);
v___x_4851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
lean_inc(v___x_4850_);
v___x_4852_ = l_Lean_Syntax_isOfKind(v___x_4850_, v___x_4851_);
if (v___x_4852_ == 0)
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
lean_dec(v___x_4850_);
v___x_4853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4824_);
v___x_4854_ = l_Lean_MessageData_ofSyntax(v_a_4824_);
v___x_4855_ = l_Lean_indentD(v___x_4854_);
v___x_4856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4853_);
lean_ctor_set(v___x_4856_, 1, v___x_4855_);
lean_inc_ref(v___y_4796_);
v___x_4857_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4856_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_dec_ref(v___x_4857_);
v_snd_4804_ = v_b_4795_;
goto v___jp_4803_;
}
else
{
lean_object* v_a_4858_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4858_);
lean_dec_ref(v___x_4857_);
v_a_4814_ = v_a_4858_;
goto v___jp_4813_;
}
}
else
{
if (v_only_4790_ == 0)
{
lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4859_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15);
lean_inc_ref(v___y_4800_);
lean_inc_ref(v___y_4796_);
v___x_4860_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_4850_, v___x_4859_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; lean_object* v___x_4862_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4861_);
lean_dec_ref(v___x_4860_);
lean_inc_ref(v_b_4795_);
v___x_4862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4795_, v___x_4850_, v_a_4861_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
lean_dec(v___x_4850_);
v___y_4818_ = v___x_4862_;
goto v___jp_4817_;
}
else
{
lean_object* v_a_4863_; 
lean_dec(v___x_4850_);
v_a_4863_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4863_);
lean_dec_ref(v___x_4860_);
v_a_4814_ = v_a_4863_;
goto v___jp_4813_;
}
}
else
{
lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4864_ = lean_box(0);
lean_inc_ref(v_b_4795_);
v___x_4865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4795_, v___x_4850_, v___x_4864_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
lean_dec(v___x_4850_);
v___y_4818_ = v___x_4865_;
goto v___jp_4817_;
}
}
}
}
else
{
lean_object* v___x_4866_; lean_object* v___x_4867_; uint8_t v___x_4868_; 
v___x_4866_ = lean_unsigned_to_nat(1u);
v___x_4867_ = l_Lean_Syntax_getArg(v___x_4834_, v___x_4866_);
v___x_4868_ = l_Lean_Syntax_isNone(v___x_4867_);
if (v___x_4868_ == 0)
{
uint8_t v___x_4869_; 
lean_inc(v___x_4867_);
v___x_4869_ = l_Lean_Syntax_matchesNull(v___x_4867_, v___x_4866_);
if (v___x_4869_ == 0)
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
lean_dec(v___x_4867_);
lean_dec(v___x_4834_);
v___x_4870_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4824_);
v___x_4871_ = l_Lean_MessageData_ofSyntax(v_a_4824_);
v___x_4872_ = l_Lean_indentD(v___x_4871_);
v___x_4873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4870_);
lean_ctor_set(v___x_4873_, 1, v___x_4872_);
lean_inc_ref(v___y_4796_);
v___x_4874_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4873_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_dec_ref(v___x_4874_);
v_snd_4804_ = v_b_4795_;
goto v___jp_4803_;
}
else
{
lean_object* v_a_4875_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref(v___x_4874_);
v_a_4814_ = v_a_4875_;
goto v___jp_4813_;
}
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; uint8_t v___x_4878_; 
v___x_4876_ = l_Lean_Syntax_getArg(v___x_4867_, v___x_4833_);
lean_dec(v___x_4867_);
v___x_4877_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4876_);
v___x_4878_ = l_Lean_Syntax_isOfKind(v___x_4876_, v___x_4877_);
if (v___x_4878_ == 0)
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
lean_dec(v___x_4876_);
lean_dec(v___x_4834_);
v___x_4879_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4824_);
v___x_4880_ = l_Lean_MessageData_ofSyntax(v_a_4824_);
v___x_4881_ = l_Lean_indentD(v___x_4880_);
v___x_4882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4879_);
lean_ctor_set(v___x_4882_, 1, v___x_4881_);
lean_inc_ref(v___y_4796_);
v___x_4883_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4882_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_dec_ref(v___x_4883_);
v_snd_4804_ = v_b_4795_;
goto v___jp_4803_;
}
else
{
lean_object* v_a_4884_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
lean_inc(v_a_4884_);
lean_dec_ref(v___x_4883_);
v_a_4814_ = v_a_4884_;
goto v___jp_4813_;
}
}
else
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4885_ = lean_box(0);
v___x_4886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4876_);
lean_inc(v___y_4801_);
lean_inc_ref(v___y_4800_);
lean_inc(v___y_4799_);
lean_inc_ref(v___y_4798_);
lean_inc(v___y_4797_);
lean_inc_ref(v___y_4796_);
lean_inc(v_a_4824_);
lean_inc_ref(v_b_4795_);
v___x_4887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4834_, v_b_4795_, v_a_4824_, v___x_4822_, v_only_4790_, v_incremental_4791_, v___x_4885_, v___x_4886_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
lean_dec(v___x_4834_);
v___y_4818_ = v___x_4887_;
goto v___jp_4817_;
}
}
}
else
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
lean_dec(v___x_4867_);
v___x_4888_ = lean_box(0);
v___x_4889_ = lean_box(0);
lean_inc(v___y_4801_);
lean_inc_ref(v___y_4800_);
lean_inc(v___y_4799_);
lean_inc_ref(v___y_4798_);
lean_inc(v___y_4797_);
lean_inc_ref(v___y_4796_);
lean_inc(v_a_4824_);
lean_inc_ref(v_b_4795_);
v___x_4890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4834_, v_b_4795_, v_a_4824_, v___x_4822_, v_only_4790_, v_incremental_4791_, v___x_4888_, v___x_4889_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
lean_dec(v___x_4834_);
v___y_4818_ = v___x_4890_;
goto v___jp_4817_;
}
}
}
else
{
lean_object* v___x_4891_; uint8_t v___x_4892_; 
v___x_4891_ = l_Lean_Syntax_getArg(v___x_4834_, v___x_4833_);
v___x_4892_ = l_Lean_Syntax_isNone(v___x_4891_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; uint8_t v___x_4894_; 
v___x_4893_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4891_);
v___x_4894_ = l_Lean_Syntax_matchesNull(v___x_4891_, v___x_4893_);
if (v___x_4894_ == 0)
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; 
lean_dec(v___x_4891_);
lean_dec(v___x_4834_);
v___x_4895_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4824_);
v___x_4896_ = l_Lean_MessageData_ofSyntax(v_a_4824_);
v___x_4897_ = l_Lean_indentD(v___x_4896_);
v___x_4898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4895_);
lean_ctor_set(v___x_4898_, 1, v___x_4897_);
lean_inc_ref(v___y_4796_);
v___x_4899_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4898_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_dec_ref(v___x_4899_);
v_snd_4804_ = v_b_4795_;
goto v___jp_4803_;
}
else
{
lean_object* v_a_4900_; 
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
lean_inc(v_a_4900_);
lean_dec_ref(v___x_4899_);
v_a_4814_ = v_a_4900_;
goto v___jp_4813_;
}
}
else
{
lean_object* v___x_4901_; lean_object* v___x_4902_; uint8_t v___x_4903_; 
v___x_4901_ = l_Lean_Syntax_getArg(v___x_4891_, v___x_4833_);
lean_dec(v___x_4891_);
v___x_4902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4901_);
v___x_4903_ = l_Lean_Syntax_isOfKind(v___x_4901_, v___x_4902_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
lean_dec(v___x_4901_);
lean_dec(v___x_4834_);
v___x_4904_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4824_);
v___x_4905_ = l_Lean_MessageData_ofSyntax(v_a_4824_);
v___x_4906_ = l_Lean_indentD(v___x_4905_);
v___x_4907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4904_);
lean_ctor_set(v___x_4907_, 1, v___x_4906_);
lean_inc_ref(v___y_4796_);
v___x_4908_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4907_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_dec_ref(v___x_4908_);
v_snd_4804_ = v_b_4795_;
goto v___jp_4803_;
}
else
{
lean_object* v_a_4909_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
lean_inc(v_a_4909_);
lean_dec_ref(v___x_4908_);
v_a_4814_ = v_a_4909_;
goto v___jp_4813_;
}
}
else
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4910_ = lean_box(0);
v___x_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4901_);
lean_inc(v___y_4801_);
lean_inc_ref(v___y_4800_);
lean_inc(v___y_4799_);
lean_inc_ref(v___y_4798_);
lean_inc(v___y_4797_);
lean_inc_ref(v___y_4796_);
lean_inc(v_a_4824_);
lean_inc_ref(v_b_4795_);
v___x_4912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4834_, v_b_4795_, v_a_4824_, v___x_4836_, v_only_4790_, v_incremental_4791_, v___x_4910_, v___x_4911_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
lean_dec(v___x_4834_);
v___y_4818_ = v___x_4912_;
goto v___jp_4817_;
}
}
}
else
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
lean_dec(v___x_4891_);
v___x_4913_ = lean_box(0);
v___x_4914_ = lean_box(0);
lean_inc(v___y_4801_);
lean_inc_ref(v___y_4800_);
lean_inc(v___y_4799_);
lean_inc_ref(v___y_4798_);
lean_inc(v___y_4797_);
lean_inc_ref(v___y_4796_);
lean_inc(v_a_4824_);
lean_inc_ref(v_b_4795_);
v___x_4915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4834_, v_b_4795_, v_a_4824_, v___x_4836_, v_only_4790_, v_incremental_4791_, v___x_4913_, v___x_4914_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
lean_dec(v___x_4834_);
v___y_4818_ = v___x_4915_;
goto v___jp_4817_;
}
}
}
else
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; uint8_t v___x_4919_; 
v___x_4916_ = lean_unsigned_to_nat(1u);
v___x_4917_ = l_Lean_Syntax_getArg(v___x_4834_, v___x_4916_);
lean_dec(v___x_4834_);
v___x_4918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4917_);
v___x_4919_ = l_Lean_Syntax_isOfKind(v___x_4917_, v___x_4918_);
if (v___x_4919_ == 0)
{
lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
lean_dec(v___x_4917_);
v___x_4920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4824_);
v___x_4921_ = l_Lean_MessageData_ofSyntax(v_a_4824_);
v___x_4922_ = l_Lean_indentD(v___x_4921_);
v___x_4923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4923_, 0, v___x_4920_);
lean_ctor_set(v___x_4923_, 1, v___x_4922_);
lean_inc_ref(v___y_4796_);
v___x_4924_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4923_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4924_) == 0)
{
lean_dec_ref(v___x_4924_);
v_snd_4804_ = v_b_4795_;
goto v___jp_4803_;
}
else
{
lean_object* v_a_4925_; 
v_a_4925_ = lean_ctor_get(v___x_4924_, 0);
lean_inc(v_a_4925_);
lean_dec_ref(v___x_4924_);
v_a_4814_ = v_a_4925_;
goto v___jp_4813_;
}
}
else
{
if (v_incremental_4791_ == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4926_ = lean_box(0);
lean_inc(v___y_4801_);
lean_inc_ref(v___y_4800_);
lean_inc(v___y_4799_);
lean_inc_ref(v___y_4798_);
lean_inc_ref(v_b_4795_);
v___x_4927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4917_, v_b_4795_, v___x_4926_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
v___y_4818_ = v___x_4927_;
goto v___jp_4817_;
}
else
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4928_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
lean_inc_ref(v___y_4800_);
lean_inc_ref(v___y_4796_);
v___x_4929_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4824_, v___x_4928_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4931_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_a_4930_);
lean_dec_ref(v___x_4929_);
lean_inc(v___y_4801_);
lean_inc_ref(v___y_4800_);
lean_inc(v___y_4799_);
lean_inc_ref(v___y_4798_);
lean_inc_ref(v_b_4795_);
v___x_4931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4917_, v_b_4795_, v_a_4930_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
v___y_4818_ = v___x_4931_;
goto v___jp_4817_;
}
else
{
lean_object* v_a_4932_; 
lean_dec(v___x_4917_);
v_a_4932_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_a_4932_);
lean_dec_ref(v___x_4929_);
v_a_4814_ = v_a_4932_;
goto v___jp_4813_;
}
}
}
}
}
}
v___jp_4803_:
{
size_t v___x_4805_; size_t v___x_4806_; 
v___x_4805_ = ((size_t)1ULL);
v___x_4806_ = lean_usize_add(v_i_4794_, v___x_4805_);
v_i_4794_ = v___x_4806_;
v_b_4795_ = v_snd_4804_;
goto _start;
}
v___jp_4808_:
{
if (v___y_4810_ == 0)
{
if (v_lax_4789_ == 0)
{
lean_object* v___x_4811_; 
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec_ref(v_b_4795_);
v___x_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4811_, 0, v___y_4809_);
return v___x_4811_;
}
else
{
lean_dec_ref(v___y_4809_);
v_snd_4804_ = v_b_4795_;
goto v___jp_4803_;
}
}
else
{
lean_object* v___x_4812_; 
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec_ref(v_b_4795_);
v___x_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4812_, 0, v___y_4809_);
return v___x_4812_;
}
}
v___jp_4813_:
{
uint8_t v___x_4815_; 
v___x_4815_ = l_Lean_Exception_isInterrupt(v_a_4814_);
if (v___x_4815_ == 0)
{
uint8_t v___x_4816_; 
lean_inc_ref(v_a_4814_);
v___x_4816_ = l_Lean_Exception_isRuntime(v_a_4814_);
v___y_4809_ = v_a_4814_;
v___y_4810_ = v___x_4816_;
goto v___jp_4808_;
}
else
{
v___y_4809_ = v_a_4814_;
v___y_4810_ = v___x_4815_;
goto v___jp_4808_;
}
}
v___jp_4817_:
{
if (lean_obj_tag(v___y_4818_) == 0)
{
lean_object* v_a_4819_; lean_object* v_snd_4820_; 
lean_dec_ref(v_b_4795_);
v_a_4819_ = lean_ctor_get(v___y_4818_, 0);
lean_inc(v_a_4819_);
lean_dec_ref(v___y_4818_);
v_snd_4820_ = lean_ctor_get(v_a_4819_, 1);
lean_inc(v_snd_4820_);
lean_dec(v_a_4819_);
v_snd_4804_ = v_snd_4820_;
goto v___jp_4803_;
}
else
{
lean_object* v_a_4821_; 
v_a_4821_ = lean_ctor_get(v___y_4818_, 0);
lean_inc(v_a_4821_);
lean_dec_ref(v___y_4818_);
v_a_4814_ = v_a_4821_;
goto v___jp_4813_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_4933_, lean_object* v_only_4934_, lean_object* v_incremental_4935_, lean_object* v_as_4936_, lean_object* v_sz_4937_, lean_object* v_i_4938_, lean_object* v_b_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_){
_start:
{
uint8_t v_lax_boxed_4947_; uint8_t v_only_boxed_4948_; uint8_t v_incremental_boxed_4949_; size_t v_sz_boxed_4950_; size_t v_i_boxed_4951_; lean_object* v_res_4952_; 
v_lax_boxed_4947_ = lean_unbox(v_lax_4933_);
v_only_boxed_4948_ = lean_unbox(v_only_4934_);
v_incremental_boxed_4949_ = lean_unbox(v_incremental_4935_);
v_sz_boxed_4950_ = lean_unbox_usize(v_sz_4937_);
lean_dec(v_sz_4937_);
v_i_boxed_4951_ = lean_unbox_usize(v_i_4938_);
lean_dec(v_i_4938_);
v_res_4952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_4947_, v_only_boxed_4948_, v_incremental_boxed_4949_, v_as_4936_, v_sz_boxed_4950_, v_i_boxed_4951_, v_b_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_);
lean_dec_ref(v_as_4936_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_4953_, lean_object* v_ps_4954_, uint8_t v_only_4955_, uint8_t v_lax_4956_, uint8_t v_incremental_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
size_t v_sz_4965_; size_t v___x_4966_; lean_object* v___x_4967_; 
v_sz_4965_ = lean_array_size(v_ps_4954_);
v___x_4966_ = ((size_t)0ULL);
v___x_4967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_4956_, v_only_4955_, v_incremental_4957_, v_ps_4954_, v_sz_4965_, v___x_4966_, v_params_4953_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_4968_, lean_object* v_ps_4969_, lean_object* v_only_4970_, lean_object* v_lax_4971_, lean_object* v_incremental_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_){
_start:
{
uint8_t v_only_boxed_4980_; uint8_t v_lax_boxed_4981_; uint8_t v_incremental_boxed_4982_; lean_object* v_res_4983_; 
v_only_boxed_4980_ = lean_unbox(v_only_4970_);
v_lax_boxed_4981_ = lean_unbox(v_lax_4971_);
v_incremental_boxed_4982_ = lean_unbox(v_incremental_4972_);
v_res_4983_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_4968_, v_ps_4969_, v_only_boxed_4980_, v_lax_boxed_4981_, v_incremental_boxed_4982_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_);
lean_dec_ref(v_ps_4969_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v_origin_4995_; 
v_origin_4995_ = lean_ctor_get(v_thm_4984_, 5);
if (lean_obj_tag(v_origin_4995_) == 0)
{
lean_object* v_declName_4996_; lean_object* v___x_4997_; 
lean_inc_ref(v_origin_4995_);
lean_dec(v_a_4991_);
lean_dec_ref(v_a_4990_);
lean_dec_ref(v_thm_4984_);
v_declName_4996_ = lean_ctor_get(v_origin_4995_, 0);
lean_inc(v_declName_4996_);
lean_dec_ref(v_origin_4995_);
v___x_4997_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_4996_, v_a_4992_, v_a_4993_);
lean_dec(v_a_4993_);
lean_dec_ref(v_a_4992_);
return v___x_4997_;
}
else
{
lean_object* v_proof_4998_; lean_object* v___x_4999_; 
v_proof_4998_ = lean_ctor_get(v_thm_4984_, 1);
lean_inc_ref(v_proof_4998_);
lean_dec_ref(v_thm_4984_);
v___x_4999_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_4998_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_);
return v___x_4999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_){
_start:
{
lean_object* v_res_5011_; 
v_res_5011_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_);
lean_dec(v_a_5005_);
lean_dec_ref(v_a_5004_);
lean_dec(v_a_5003_);
lean_dec_ref(v_a_5002_);
lean_dec(v_a_5001_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_5012_, size_t v_sz_5013_, size_t v_i_5014_, lean_object* v_b_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
uint8_t v___x_5026_; 
v___x_5026_ = lean_usize_dec_lt(v_i_5014_, v_sz_5013_);
if (v___x_5026_ == 0)
{
lean_object* v___x_5027_; 
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
v___x_5027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5027_, 0, v_b_5015_);
return v___x_5027_;
}
else
{
lean_object* v_snd_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5054_; 
v_snd_5028_ = lean_ctor_get(v_b_5015_, 1);
v_isSharedCheck_5054_ = !lean_is_exclusive(v_b_5015_);
if (v_isSharedCheck_5054_ == 0)
{
lean_object* v_unused_5055_; 
v_unused_5055_ = lean_ctor_get(v_b_5015_, 0);
lean_dec(v_unused_5055_);
v___x_5030_ = v_b_5015_;
v_isShared_5031_ = v_isSharedCheck_5054_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_snd_5028_);
lean_dec(v_b_5015_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5054_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v_a_5032_; lean_object* v___x_5033_; 
v_a_5032_ = lean_array_uget_borrowed(v_as_5012_, v_i_5014_);
lean_inc(v___y_5024_);
lean_inc_ref(v___y_5023_);
lean_inc(v___y_5022_);
lean_inc_ref(v___y_5021_);
lean_inc(v_a_5032_);
v___x_5033_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5032_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_object* v_a_5034_; lean_object* v___x_5035_; lean_object* v_a_5037_; uint8_t v___x_5044_; 
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_a_5034_);
lean_dec_ref(v___x_5033_);
v___x_5035_ = lean_box(0);
v___x_5044_ = lean_unbox(v_a_5034_);
lean_dec(v_a_5034_);
if (v___x_5044_ == 0)
{
v_a_5037_ = v_snd_5028_;
goto v___jp_5036_;
}
else
{
lean_object* v___x_5045_; 
lean_inc(v_a_5032_);
v___x_5045_ = l_Lean_PersistentArray_push___redArg(v_snd_5028_, v_a_5032_);
v_a_5037_ = v___x_5045_;
goto v___jp_5036_;
}
v___jp_5036_:
{
lean_object* v___x_5039_; 
if (v_isShared_5031_ == 0)
{
lean_ctor_set(v___x_5030_, 1, v_a_5037_);
lean_ctor_set(v___x_5030_, 0, v___x_5035_);
v___x_5039_ = v___x_5030_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v___x_5035_);
lean_ctor_set(v_reuseFailAlloc_5043_, 1, v_a_5037_);
v___x_5039_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
size_t v___x_5040_; size_t v___x_5041_; 
v___x_5040_ = ((size_t)1ULL);
v___x_5041_ = lean_usize_add(v_i_5014_, v___x_5040_);
v_i_5014_ = v___x_5041_;
v_b_5015_ = v___x_5039_;
goto _start;
}
}
}
else
{
lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5053_; 
lean_del_object(v___x_5030_);
lean_dec(v_snd_5028_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
v_a_5046_ = lean_ctor_get(v___x_5033_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_5033_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5048_ = v___x_5033_;
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_5033_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5051_; 
if (v_isShared_5049_ == 0)
{
v___x_5051_ = v___x_5048_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5046_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
return v___x_5051_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5056_, lean_object* v_sz_5057_, lean_object* v_i_5058_, lean_object* v_b_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
size_t v_sz_boxed_5070_; size_t v_i_boxed_5071_; lean_object* v_res_5072_; 
v_sz_boxed_5070_ = lean_unbox_usize(v_sz_5057_);
lean_dec(v_sz_5057_);
v_i_boxed_5071_ = lean_unbox_usize(v_i_5058_);
lean_dec(v_i_5058_);
v_res_5072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5056_, v_sz_boxed_5070_, v_i_boxed_5071_, v_b_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
lean_dec(v___y_5064_);
lean_dec_ref(v___y_5063_);
lean_dec(v___y_5062_);
lean_dec_ref(v___y_5061_);
lean_dec(v___y_5060_);
lean_dec_ref(v_as_5056_);
return v_res_5072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5073_, size_t v_sz_5074_, size_t v_i_5075_, lean_object* v_b_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
uint8_t v___x_5087_; 
v___x_5087_ = lean_usize_dec_lt(v_i_5075_, v_sz_5074_);
if (v___x_5087_ == 0)
{
lean_object* v___x_5088_; 
lean_dec(v___y_5085_);
lean_dec_ref(v___y_5084_);
lean_dec(v___y_5083_);
lean_dec_ref(v___y_5082_);
v___x_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5088_, 0, v_b_5076_);
return v___x_5088_;
}
else
{
lean_object* v_snd_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5115_; 
v_snd_5089_ = lean_ctor_get(v_b_5076_, 1);
v_isSharedCheck_5115_ = !lean_is_exclusive(v_b_5076_);
if (v_isSharedCheck_5115_ == 0)
{
lean_object* v_unused_5116_; 
v_unused_5116_ = lean_ctor_get(v_b_5076_, 0);
lean_dec(v_unused_5116_);
v___x_5091_ = v_b_5076_;
v_isShared_5092_ = v_isSharedCheck_5115_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_snd_5089_);
lean_dec(v_b_5076_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5115_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
lean_object* v_a_5093_; lean_object* v___x_5094_; 
v_a_5093_ = lean_array_uget_borrowed(v_as_5073_, v_i_5075_);
lean_inc(v___y_5085_);
lean_inc_ref(v___y_5084_);
lean_inc(v___y_5083_);
lean_inc_ref(v___y_5082_);
lean_inc(v_a_5093_);
v___x_5094_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5093_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v_a_5095_; lean_object* v___x_5096_; lean_object* v_a_5098_; uint8_t v___x_5105_; 
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
lean_inc(v_a_5095_);
lean_dec_ref(v___x_5094_);
v___x_5096_ = lean_box(0);
v___x_5105_ = lean_unbox(v_a_5095_);
lean_dec(v_a_5095_);
if (v___x_5105_ == 0)
{
v_a_5098_ = v_snd_5089_;
goto v___jp_5097_;
}
else
{
lean_object* v___x_5106_; 
lean_inc(v_a_5093_);
v___x_5106_ = l_Lean_PersistentArray_push___redArg(v_snd_5089_, v_a_5093_);
v_a_5098_ = v___x_5106_;
goto v___jp_5097_;
}
v___jp_5097_:
{
lean_object* v___x_5100_; 
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 1, v_a_5098_);
lean_ctor_set(v___x_5091_, 0, v___x_5096_);
v___x_5100_ = v___x_5091_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_5096_);
lean_ctor_set(v_reuseFailAlloc_5104_, 1, v_a_5098_);
v___x_5100_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
size_t v___x_5101_; size_t v___x_5102_; lean_object* v___x_5103_; 
v___x_5101_ = ((size_t)1ULL);
v___x_5102_ = lean_usize_add(v_i_5075_, v___x_5101_);
v___x_5103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5073_, v_sz_5074_, v___x_5102_, v___x_5100_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_);
return v___x_5103_;
}
}
}
else
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
lean_del_object(v___x_5091_);
lean_dec(v_snd_5089_);
lean_dec(v___y_5085_);
lean_dec_ref(v___y_5084_);
lean_dec(v___y_5083_);
lean_dec_ref(v___y_5082_);
v_a_5107_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_5094_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_5094_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_a_5107_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5117_, lean_object* v_sz_5118_, lean_object* v_i_5119_, lean_object* v_b_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
size_t v_sz_boxed_5131_; size_t v_i_boxed_5132_; lean_object* v_res_5133_; 
v_sz_boxed_5131_ = lean_unbox_usize(v_sz_5118_);
lean_dec(v_sz_5118_);
v_i_boxed_5132_ = lean_unbox_usize(v_i_5119_);
lean_dec(v_i_5119_);
v_res_5133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5117_, v_sz_boxed_5131_, v_i_boxed_5132_, v_b_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_);
lean_dec(v___y_5125_);
lean_dec_ref(v___y_5124_);
lean_dec(v___y_5123_);
lean_dec_ref(v___y_5122_);
lean_dec(v___y_5121_);
lean_dec_ref(v_as_5117_);
return v_res_5133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5134_, size_t v_sz_5135_, size_t v_i_5136_, lean_object* v_b_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_){
_start:
{
uint8_t v___x_5148_; 
v___x_5148_ = lean_usize_dec_lt(v_i_5136_, v_sz_5135_);
if (v___x_5148_ == 0)
{
lean_object* v___x_5149_; 
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
v___x_5149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5149_, 0, v_b_5137_);
return v___x_5149_;
}
else
{
lean_object* v_snd_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5176_; 
v_snd_5150_ = lean_ctor_get(v_b_5137_, 1);
v_isSharedCheck_5176_ = !lean_is_exclusive(v_b_5137_);
if (v_isSharedCheck_5176_ == 0)
{
lean_object* v_unused_5177_; 
v_unused_5177_ = lean_ctor_get(v_b_5137_, 0);
lean_dec(v_unused_5177_);
v___x_5152_ = v_b_5137_;
v_isShared_5153_ = v_isSharedCheck_5176_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_snd_5150_);
lean_dec(v_b_5137_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5176_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v_a_5154_; lean_object* v___x_5155_; 
v_a_5154_ = lean_array_uget_borrowed(v_as_5134_, v_i_5136_);
lean_inc(v___y_5146_);
lean_inc_ref(v___y_5145_);
lean_inc(v___y_5144_);
lean_inc_ref(v___y_5143_);
lean_inc(v_a_5154_);
v___x_5155_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5154_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_a_5156_; lean_object* v___x_5157_; lean_object* v_a_5159_; uint8_t v___x_5166_; 
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
lean_inc(v_a_5156_);
lean_dec_ref(v___x_5155_);
v___x_5157_ = lean_box(0);
v___x_5166_ = lean_unbox(v_a_5156_);
lean_dec(v_a_5156_);
if (v___x_5166_ == 0)
{
v_a_5159_ = v_snd_5150_;
goto v___jp_5158_;
}
else
{
lean_object* v___x_5167_; 
lean_inc(v_a_5154_);
v___x_5167_ = l_Lean_PersistentArray_push___redArg(v_snd_5150_, v_a_5154_);
v_a_5159_ = v___x_5167_;
goto v___jp_5158_;
}
v___jp_5158_:
{
lean_object* v___x_5161_; 
if (v_isShared_5153_ == 0)
{
lean_ctor_set(v___x_5152_, 1, v_a_5159_);
lean_ctor_set(v___x_5152_, 0, v___x_5157_);
v___x_5161_ = v___x_5152_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v___x_5157_);
lean_ctor_set(v_reuseFailAlloc_5165_, 1, v_a_5159_);
v___x_5161_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
size_t v___x_5162_; size_t v___x_5163_; 
v___x_5162_ = ((size_t)1ULL);
v___x_5163_ = lean_usize_add(v_i_5136_, v___x_5162_);
v_i_5136_ = v___x_5163_;
v_b_5137_ = v___x_5161_;
goto _start;
}
}
}
else
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5175_; 
lean_del_object(v___x_5152_);
lean_dec(v_snd_5150_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
v_a_5168_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5170_ = v___x_5155_;
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_5155_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5173_; 
if (v_isShared_5171_ == 0)
{
v___x_5173_ = v___x_5170_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_a_5168_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5178_, lean_object* v_sz_5179_, lean_object* v_i_5180_, lean_object* v_b_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
size_t v_sz_boxed_5192_; size_t v_i_boxed_5193_; lean_object* v_res_5194_; 
v_sz_boxed_5192_ = lean_unbox_usize(v_sz_5179_);
lean_dec(v_sz_5179_);
v_i_boxed_5193_ = lean_unbox_usize(v_i_5180_);
lean_dec(v_i_5180_);
v_res_5194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5178_, v_sz_boxed_5192_, v_i_boxed_5193_, v_b_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5183_);
lean_dec(v___y_5182_);
lean_dec_ref(v_as_5178_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5195_, size_t v_sz_5196_, size_t v_i_5197_, lean_object* v_b_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_){
_start:
{
uint8_t v___x_5209_; 
v___x_5209_ = lean_usize_dec_lt(v_i_5197_, v_sz_5196_);
if (v___x_5209_ == 0)
{
lean_object* v___x_5210_; 
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
v___x_5210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5210_, 0, v_b_5198_);
return v___x_5210_;
}
else
{
lean_object* v_snd_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5237_; 
v_snd_5211_ = lean_ctor_get(v_b_5198_, 1);
v_isSharedCheck_5237_ = !lean_is_exclusive(v_b_5198_);
if (v_isSharedCheck_5237_ == 0)
{
lean_object* v_unused_5238_; 
v_unused_5238_ = lean_ctor_get(v_b_5198_, 0);
lean_dec(v_unused_5238_);
v___x_5213_ = v_b_5198_;
v_isShared_5214_ = v_isSharedCheck_5237_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_snd_5211_);
lean_dec(v_b_5198_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5237_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v_a_5215_; lean_object* v___x_5216_; 
v_a_5215_ = lean_array_uget_borrowed(v_as_5195_, v_i_5197_);
lean_inc(v___y_5207_);
lean_inc_ref(v___y_5206_);
lean_inc(v___y_5205_);
lean_inc_ref(v___y_5204_);
lean_inc(v_a_5215_);
v___x_5216_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5215_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
if (lean_obj_tag(v___x_5216_) == 0)
{
lean_object* v_a_5217_; lean_object* v___x_5218_; lean_object* v_a_5220_; uint8_t v___x_5227_; 
v_a_5217_ = lean_ctor_get(v___x_5216_, 0);
lean_inc(v_a_5217_);
lean_dec_ref(v___x_5216_);
v___x_5218_ = lean_box(0);
v___x_5227_ = lean_unbox(v_a_5217_);
lean_dec(v_a_5217_);
if (v___x_5227_ == 0)
{
v_a_5220_ = v_snd_5211_;
goto v___jp_5219_;
}
else
{
lean_object* v___x_5228_; 
lean_inc(v_a_5215_);
v___x_5228_ = l_Lean_PersistentArray_push___redArg(v_snd_5211_, v_a_5215_);
v_a_5220_ = v___x_5228_;
goto v___jp_5219_;
}
v___jp_5219_:
{
lean_object* v___x_5222_; 
if (v_isShared_5214_ == 0)
{
lean_ctor_set(v___x_5213_, 1, v_a_5220_);
lean_ctor_set(v___x_5213_, 0, v___x_5218_);
v___x_5222_ = v___x_5213_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5218_);
lean_ctor_set(v_reuseFailAlloc_5226_, 1, v_a_5220_);
v___x_5222_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
size_t v___x_5223_; size_t v___x_5224_; lean_object* v___x_5225_; 
v___x_5223_ = ((size_t)1ULL);
v___x_5224_ = lean_usize_add(v_i_5197_, v___x_5223_);
v___x_5225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5195_, v_sz_5196_, v___x_5224_, v___x_5222_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
return v___x_5225_;
}
}
}
else
{
lean_object* v_a_5229_; lean_object* v___x_5231_; uint8_t v_isShared_5232_; uint8_t v_isSharedCheck_5236_; 
lean_del_object(v___x_5213_);
lean_dec(v_snd_5211_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
v_a_5229_ = lean_ctor_get(v___x_5216_, 0);
v_isSharedCheck_5236_ = !lean_is_exclusive(v___x_5216_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5231_ = v___x_5216_;
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
else
{
lean_inc(v_a_5229_);
lean_dec(v___x_5216_);
v___x_5231_ = lean_box(0);
v_isShared_5232_ = v_isSharedCheck_5236_;
goto v_resetjp_5230_;
}
v_resetjp_5230_:
{
lean_object* v___x_5234_; 
if (v_isShared_5232_ == 0)
{
v___x_5234_ = v___x_5231_;
goto v_reusejp_5233_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v_a_5229_);
v___x_5234_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5233_;
}
v_reusejp_5233_:
{
return v___x_5234_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5239_, lean_object* v_sz_5240_, lean_object* v_i_5241_, lean_object* v_b_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_){
_start:
{
size_t v_sz_boxed_5253_; size_t v_i_boxed_5254_; lean_object* v_res_5255_; 
v_sz_boxed_5253_ = lean_unbox_usize(v_sz_5240_);
lean_dec(v_sz_5240_);
v_i_boxed_5254_ = lean_unbox_usize(v_i_5241_);
lean_dec(v_i_5241_);
v_res_5255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5239_, v_sz_boxed_5253_, v_i_boxed_5254_, v_b_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec(v___y_5245_);
lean_dec_ref(v___y_5244_);
lean_dec(v___y_5243_);
lean_dec_ref(v_as_5239_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_inh_5256_, lean_object* v_n_5257_, lean_object* v_b_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_){
_start:
{
if (lean_obj_tag(v_n_5257_) == 0)
{
lean_object* v_cs_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5303_; 
v_cs_5269_ = lean_ctor_get(v_n_5257_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v_n_5257_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5271_ = v_n_5257_;
v_isShared_5272_ = v_isSharedCheck_5303_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_cs_5269_);
lean_dec(v_n_5257_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5303_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5273_; lean_object* v___x_5274_; size_t v_sz_5275_; size_t v___x_5276_; lean_object* v___x_5277_; 
v___x_5273_ = lean_box(0);
v___x_5274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5273_);
lean_ctor_set(v___x_5274_, 1, v_b_5258_);
v_sz_5275_ = lean_array_size(v_cs_5269_);
v___x_5276_ = ((size_t)0ULL);
v___x_5277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_inh_5256_, v_cs_5269_, v_sz_5275_, v___x_5276_, v___x_5274_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
lean_dec_ref(v_cs_5269_);
if (lean_obj_tag(v___x_5277_) == 0)
{
lean_object* v_a_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5294_; 
v_a_5278_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5280_ = v___x_5277_;
v_isShared_5281_ = v_isSharedCheck_5294_;
goto v_resetjp_5279_;
}
else
{
lean_inc(v_a_5278_);
lean_dec(v___x_5277_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5294_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
lean_object* v_fst_5282_; 
v_fst_5282_ = lean_ctor_get(v_a_5278_, 0);
if (lean_obj_tag(v_fst_5282_) == 0)
{
lean_object* v_snd_5283_; lean_object* v___x_5285_; 
v_snd_5283_ = lean_ctor_get(v_a_5278_, 1);
lean_inc(v_snd_5283_);
lean_dec(v_a_5278_);
if (v_isShared_5272_ == 0)
{
lean_ctor_set_tag(v___x_5271_, 1);
lean_ctor_set(v___x_5271_, 0, v_snd_5283_);
v___x_5285_ = v___x_5271_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v_snd_5283_);
v___x_5285_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
lean_object* v___x_5287_; 
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 0, v___x_5285_);
v___x_5287_ = v___x_5280_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v___x_5285_);
v___x_5287_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5286_;
}
v_reusejp_5286_:
{
return v___x_5287_;
}
}
}
else
{
lean_object* v_val_5290_; lean_object* v___x_5292_; 
lean_inc_ref(v_fst_5282_);
lean_dec(v_a_5278_);
lean_del_object(v___x_5271_);
v_val_5290_ = lean_ctor_get(v_fst_5282_, 0);
lean_inc(v_val_5290_);
lean_dec_ref(v_fst_5282_);
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 0, v_val_5290_);
v___x_5292_ = v___x_5280_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_val_5290_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
else
{
lean_object* v_a_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5302_; 
lean_del_object(v___x_5271_);
v_a_5295_ = lean_ctor_get(v___x_5277_, 0);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5297_ = v___x_5277_;
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_a_5295_);
lean_dec(v___x_5277_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5302_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5300_; 
if (v_isShared_5298_ == 0)
{
v___x_5300_ = v___x_5297_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5301_; 
v_reuseFailAlloc_5301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_a_5295_);
v___x_5300_ = v_reuseFailAlloc_5301_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
return v___x_5300_;
}
}
}
}
}
else
{
lean_object* v_vs_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5338_; 
v_vs_5304_ = lean_ctor_get(v_n_5257_, 0);
v_isSharedCheck_5338_ = !lean_is_exclusive(v_n_5257_);
if (v_isSharedCheck_5338_ == 0)
{
v___x_5306_ = v_n_5257_;
v_isShared_5307_ = v_isSharedCheck_5338_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_vs_5304_);
lean_dec(v_n_5257_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5338_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5308_; lean_object* v___x_5309_; size_t v_sz_5310_; size_t v___x_5311_; lean_object* v___x_5312_; 
v___x_5308_ = lean_box(0);
v___x_5309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5309_, 0, v___x_5308_);
lean_ctor_set(v___x_5309_, 1, v_b_5258_);
v_sz_5310_ = lean_array_size(v_vs_5304_);
v___x_5311_ = ((size_t)0ULL);
v___x_5312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5304_, v_sz_5310_, v___x_5311_, v___x_5309_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
lean_dec_ref(v_vs_5304_);
if (lean_obj_tag(v___x_5312_) == 0)
{
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5329_; 
v_a_5313_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5315_ = v___x_5312_;
v_isShared_5316_ = v_isSharedCheck_5329_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v___x_5312_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5329_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v_fst_5317_; 
v_fst_5317_ = lean_ctor_get(v_a_5313_, 0);
if (lean_obj_tag(v_fst_5317_) == 0)
{
lean_object* v_snd_5318_; lean_object* v___x_5320_; 
v_snd_5318_ = lean_ctor_get(v_a_5313_, 1);
lean_inc(v_snd_5318_);
lean_dec(v_a_5313_);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 0, v_snd_5318_);
v___x_5320_ = v___x_5306_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_snd_5318_);
v___x_5320_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
lean_object* v___x_5322_; 
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v___x_5320_);
v___x_5322_ = v___x_5315_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v___x_5320_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
}
else
{
lean_object* v_val_5325_; lean_object* v___x_5327_; 
lean_inc_ref(v_fst_5317_);
lean_dec(v_a_5313_);
lean_del_object(v___x_5306_);
v_val_5325_ = lean_ctor_get(v_fst_5317_, 0);
lean_inc(v_val_5325_);
lean_dec_ref(v_fst_5317_);
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v_val_5325_);
v___x_5327_ = v___x_5315_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_val_5325_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
}
}
}
}
else
{
lean_object* v_a_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5337_; 
lean_del_object(v___x_5306_);
v_a_5330_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5332_ = v___x_5312_;
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_a_5330_);
lean_dec(v___x_5312_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5335_; 
if (v_isShared_5333_ == 0)
{
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5330_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_inh_5339_, lean_object* v_as_5340_, size_t v_sz_5341_, size_t v_i_5342_, lean_object* v_b_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_){
_start:
{
uint8_t v___x_5354_; 
v___x_5354_ = lean_usize_dec_lt(v_i_5342_, v_sz_5341_);
if (v___x_5354_ == 0)
{
lean_object* v___x_5355_; 
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
v___x_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5355_, 0, v_b_5343_);
return v___x_5355_;
}
else
{
lean_object* v_snd_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5390_; 
v_snd_5356_ = lean_ctor_get(v_b_5343_, 1);
v_isSharedCheck_5390_ = !lean_is_exclusive(v_b_5343_);
if (v_isSharedCheck_5390_ == 0)
{
lean_object* v_unused_5391_; 
v_unused_5391_ = lean_ctor_get(v_b_5343_, 0);
lean_dec(v_unused_5391_);
v___x_5358_ = v_b_5343_;
v_isShared_5359_ = v_isSharedCheck_5390_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_snd_5356_);
lean_dec(v_b_5343_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5390_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v_a_5360_; lean_object* v___x_5361_; 
v_a_5360_ = lean_array_uget_borrowed(v_as_5340_, v_i_5342_);
lean_inc(v___y_5352_);
lean_inc_ref(v___y_5351_);
lean_inc(v___y_5350_);
lean_inc_ref(v___y_5349_);
lean_inc(v_snd_5356_);
lean_inc(v_a_5360_);
v___x_5361_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_inh_5339_, v_a_5360_, v_snd_5356_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_);
if (lean_obj_tag(v___x_5361_) == 0)
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5381_; 
v_a_5362_ = lean_ctor_get(v___x_5361_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5361_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5364_ = v___x_5361_;
v_isShared_5365_ = v_isSharedCheck_5381_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5361_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5381_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
if (lean_obj_tag(v_a_5362_) == 0)
{
lean_object* v___x_5366_; lean_object* v___x_5368_; 
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
v___x_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5366_, 0, v_a_5362_);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 0, v___x_5366_);
v___x_5368_ = v___x_5358_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5366_);
lean_ctor_set(v_reuseFailAlloc_5372_, 1, v_snd_5356_);
v___x_5368_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
lean_object* v___x_5370_; 
if (v_isShared_5365_ == 0)
{
lean_ctor_set(v___x_5364_, 0, v___x_5368_);
v___x_5370_ = v___x_5364_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v___x_5368_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
else
{
lean_object* v_a_5373_; lean_object* v___x_5374_; lean_object* v___x_5376_; 
lean_del_object(v___x_5364_);
lean_dec(v_snd_5356_);
v_a_5373_ = lean_ctor_get(v_a_5362_, 0);
lean_inc(v_a_5373_);
lean_dec_ref(v_a_5362_);
v___x_5374_ = lean_box(0);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 1, v_a_5373_);
lean_ctor_set(v___x_5358_, 0, v___x_5374_);
v___x_5376_ = v___x_5358_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5374_);
lean_ctor_set(v_reuseFailAlloc_5380_, 1, v_a_5373_);
v___x_5376_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
size_t v___x_5377_; size_t v___x_5378_; 
v___x_5377_ = ((size_t)1ULL);
v___x_5378_ = lean_usize_add(v_i_5342_, v___x_5377_);
v_i_5342_ = v___x_5378_;
v_b_5343_ = v___x_5376_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
lean_del_object(v___x_5358_);
lean_dec(v_snd_5356_);
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
v_a_5382_ = lean_ctor_get(v___x_5361_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5361_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5361_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5361_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_inh_5392_, lean_object* v_as_5393_, lean_object* v_sz_5394_, lean_object* v_i_5395_, lean_object* v_b_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_){
_start:
{
size_t v_sz_boxed_5407_; size_t v_i_boxed_5408_; lean_object* v_res_5409_; 
v_sz_boxed_5407_ = lean_unbox_usize(v_sz_5394_);
lean_dec(v_sz_5394_);
v_i_boxed_5408_ = lean_unbox_usize(v_i_5395_);
lean_dec(v_i_5395_);
v_res_5409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_inh_5392_, v_as_5393_, v_sz_boxed_5407_, v_i_boxed_5408_, v_b_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
lean_dec(v___y_5401_);
lean_dec_ref(v___y_5400_);
lean_dec(v___y_5399_);
lean_dec_ref(v___y_5398_);
lean_dec(v___y_5397_);
lean_dec_ref(v_as_5393_);
lean_dec_ref(v_inh_5392_);
return v_res_5409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_inh_5410_, lean_object* v_n_5411_, lean_object* v_b_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
lean_object* v_res_5423_; 
v_res_5423_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_inh_5410_, v_n_5411_, v_b_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_);
lean_dec(v___y_5417_);
lean_dec_ref(v___y_5416_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
lean_dec(v___y_5413_);
lean_dec_ref(v_inh_5410_);
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5424_, lean_object* v_init_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_){
_start:
{
lean_object* v_root_5436_; lean_object* v_tail_5437_; lean_object* v___x_5438_; 
v_root_5436_ = lean_ctor_get(v_t_5424_, 0);
lean_inc_ref(v_root_5436_);
v_tail_5437_ = lean_ctor_get(v_t_5424_, 1);
lean_inc_ref(v_tail_5437_);
lean_dec_ref(v_t_5424_);
lean_inc(v___y_5434_);
lean_inc_ref(v___y_5433_);
lean_inc(v___y_5432_);
lean_inc_ref(v___y_5431_);
lean_inc_ref(v_init_5425_);
v___x_5438_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5425_, v_root_5436_, v_init_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
lean_dec_ref(v_init_5425_);
if (lean_obj_tag(v___x_5438_) == 0)
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5475_; 
v_a_5439_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5441_ = v___x_5438_;
v_isShared_5442_ = v_isSharedCheck_5475_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5438_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5475_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
if (lean_obj_tag(v_a_5439_) == 0)
{
lean_object* v_a_5443_; lean_object* v___x_5445_; 
lean_dec_ref(v_tail_5437_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
v_a_5443_ = lean_ctor_get(v_a_5439_, 0);
lean_inc(v_a_5443_);
lean_dec_ref(v_a_5439_);
if (v_isShared_5442_ == 0)
{
lean_ctor_set(v___x_5441_, 0, v_a_5443_);
v___x_5445_ = v___x_5441_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_a_5443_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; size_t v_sz_5450_; size_t v___x_5451_; lean_object* v___x_5452_; 
lean_del_object(v___x_5441_);
v_a_5447_ = lean_ctor_get(v_a_5439_, 0);
lean_inc(v_a_5447_);
lean_dec_ref(v_a_5439_);
v___x_5448_ = lean_box(0);
v___x_5449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5449_, 0, v___x_5448_);
lean_ctor_set(v___x_5449_, 1, v_a_5447_);
v_sz_5450_ = lean_array_size(v_tail_5437_);
v___x_5451_ = ((size_t)0ULL);
v___x_5452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5437_, v_sz_5450_, v___x_5451_, v___x_5449_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_);
lean_dec_ref(v_tail_5437_);
if (lean_obj_tag(v___x_5452_) == 0)
{
lean_object* v_a_5453_; lean_object* v___x_5455_; uint8_t v_isShared_5456_; uint8_t v_isSharedCheck_5466_; 
v_a_5453_ = lean_ctor_get(v___x_5452_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___x_5452_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5455_ = v___x_5452_;
v_isShared_5456_ = v_isSharedCheck_5466_;
goto v_resetjp_5454_;
}
else
{
lean_inc(v_a_5453_);
lean_dec(v___x_5452_);
v___x_5455_ = lean_box(0);
v_isShared_5456_ = v_isSharedCheck_5466_;
goto v_resetjp_5454_;
}
v_resetjp_5454_:
{
lean_object* v_fst_5457_; 
v_fst_5457_ = lean_ctor_get(v_a_5453_, 0);
if (lean_obj_tag(v_fst_5457_) == 0)
{
lean_object* v_snd_5458_; lean_object* v___x_5460_; 
v_snd_5458_ = lean_ctor_get(v_a_5453_, 1);
lean_inc(v_snd_5458_);
lean_dec(v_a_5453_);
if (v_isShared_5456_ == 0)
{
lean_ctor_set(v___x_5455_, 0, v_snd_5458_);
v___x_5460_ = v___x_5455_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_snd_5458_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
else
{
lean_object* v_val_5462_; lean_object* v___x_5464_; 
lean_inc_ref(v_fst_5457_);
lean_dec(v_a_5453_);
v_val_5462_ = lean_ctor_get(v_fst_5457_, 0);
lean_inc(v_val_5462_);
lean_dec_ref(v_fst_5457_);
if (v_isShared_5456_ == 0)
{
lean_ctor_set(v___x_5455_, 0, v_val_5462_);
v___x_5464_ = v___x_5455_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v_val_5462_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
}
}
else
{
lean_object* v_a_5467_; lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5474_; 
v_a_5467_ = lean_ctor_get(v___x_5452_, 0);
v_isSharedCheck_5474_ = !lean_is_exclusive(v___x_5452_);
if (v_isSharedCheck_5474_ == 0)
{
v___x_5469_ = v___x_5452_;
v_isShared_5470_ = v_isSharedCheck_5474_;
goto v_resetjp_5468_;
}
else
{
lean_inc(v_a_5467_);
lean_dec(v___x_5452_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5474_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
lean_object* v___x_5472_; 
if (v_isShared_5470_ == 0)
{
v___x_5472_ = v___x_5469_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_a_5467_);
v___x_5472_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
return v___x_5472_;
}
}
}
}
}
}
else
{
lean_object* v_a_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5483_; 
lean_dec_ref(v_tail_5437_);
lean_dec(v___y_5434_);
lean_dec_ref(v___y_5433_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
v_a_5476_ = lean_ctor_get(v___x_5438_, 0);
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5438_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5478_ = v___x_5438_;
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_a_5476_);
lean_dec(v___x_5438_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v___x_5481_; 
if (v_isShared_5479_ == 0)
{
v___x_5481_ = v___x_5478_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_a_5476_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5484_, lean_object* v_init_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_){
_start:
{
lean_object* v_res_5496_; 
v_res_5496_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5484_, v_init_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_);
lean_dec(v___y_5490_);
lean_dec_ref(v___y_5489_);
lean_dec(v___y_5488_);
lean_dec_ref(v___y_5487_);
lean_dec(v___y_5486_);
return v_res_5496_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; 
v___x_5497_ = lean_unsigned_to_nat(32u);
v___x_5498_ = lean_mk_empty_array_with_capacity(v___x_5497_);
v___x_5499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5499_, 0, v___x_5498_);
return v___x_5499_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v_result_5505_; 
v___x_5500_ = ((size_t)5ULL);
v___x_5501_ = lean_unsigned_to_nat(0u);
v___x_5502_ = lean_unsigned_to_nat(32u);
v___x_5503_ = lean_mk_empty_array_with_capacity(v___x_5502_);
v___x_5504_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5505_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5505_, 0, v___x_5504_);
lean_ctor_set(v_result_5505_, 1, v___x_5503_);
lean_ctor_set(v_result_5505_, 2, v___x_5501_);
lean_ctor_set(v_result_5505_, 3, v___x_5501_);
lean_ctor_set_usize(v_result_5505_, 4, v___x_5500_);
return v_result_5505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_){
_start:
{
lean_object* v_result_5517_; lean_object* v___x_5518_; 
v_result_5517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5518_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5506_, v_result_5517_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
return v___x_5518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_){
_start:
{
lean_object* v_res_5530_; 
v_res_5530_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5519_, v_a_5520_, v_a_5521_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_);
lean_dec(v_a_5524_);
lean_dec_ref(v_a_5523_);
lean_dec(v_a_5522_);
lean_dec_ref(v_a_5521_);
lean_dec(v_a_5520_);
return v_res_5530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5533_, lean_object* v_newThms_5534_, lean_object* v_gmt_5535_, lean_object* v_numInstances_5536_, lean_object* v_numDelayedInstances_5537_, lean_object* v_num_5538_, lean_object* v_preInstances_5539_, lean_object* v_nextThmIdx_5540_, lean_object* v_matchEqNames_5541_, lean_object* v_delayedThmInsts_5542_, lean_object* v_nextDeclIdx_5543_, lean_object* v_canon_5544_, lean_object* v_enodeMap_5545_, lean_object* v_exprs_5546_, lean_object* v_parents_5547_, lean_object* v_congrTable_5548_, lean_object* v_appMap_5549_, lean_object* v_indicesFound_5550_, lean_object* v_newFacts_5551_, uint8_t v_inconsistent_5552_, lean_object* v_nextIdx_5553_, lean_object* v_newRawFacts_5554_, lean_object* v_facts_5555_, lean_object* v_extThms_5556_, lean_object* v_inj_5557_, lean_object* v_split_5558_, lean_object* v_clean_5559_, lean_object* v_sstates_5560_, lean_object* v_mvarId_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_){
_start:
{
lean_object* v___x_5572_; 
lean_inc(v___y_5570_);
lean_inc_ref(v___y_5569_);
lean_inc(v___y_5568_);
lean_inc_ref(v___y_5567_);
v___x_5572_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5533_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
if (lean_obj_tag(v___x_5572_) == 0)
{
lean_object* v_a_5573_; lean_object* v___x_5574_; 
v_a_5573_ = lean_ctor_get(v___x_5572_, 0);
lean_inc(v_a_5573_);
lean_dec_ref(v___x_5572_);
v___x_5574_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5534_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
if (lean_obj_tag(v___x_5574_) == 0)
{
lean_object* v_a_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5586_; 
v_a_5575_ = lean_ctor_get(v___x_5574_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v___x_5574_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5577_ = v___x_5574_;
v_isShared_5578_ = v_isSharedCheck_5586_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_a_5575_);
lean_dec(v___x_5574_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5586_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5584_; 
v___x_5579_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5580_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5580_, 0, v___x_5579_);
lean_ctor_set(v___x_5580_, 1, v_gmt_5535_);
lean_ctor_set(v___x_5580_, 2, v_a_5573_);
lean_ctor_set(v___x_5580_, 3, v_a_5575_);
lean_ctor_set(v___x_5580_, 4, v_numInstances_5536_);
lean_ctor_set(v___x_5580_, 5, v_numDelayedInstances_5537_);
lean_ctor_set(v___x_5580_, 6, v_num_5538_);
lean_ctor_set(v___x_5580_, 7, v_preInstances_5539_);
lean_ctor_set(v___x_5580_, 8, v_nextThmIdx_5540_);
lean_ctor_set(v___x_5580_, 9, v_matchEqNames_5541_);
lean_ctor_set(v___x_5580_, 10, v_delayedThmInsts_5542_);
v___x_5581_ = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(v___x_5581_, 0, v_nextDeclIdx_5543_);
lean_ctor_set(v___x_5581_, 1, v_canon_5544_);
lean_ctor_set(v___x_5581_, 2, v_enodeMap_5545_);
lean_ctor_set(v___x_5581_, 3, v_exprs_5546_);
lean_ctor_set(v___x_5581_, 4, v_parents_5547_);
lean_ctor_set(v___x_5581_, 5, v_congrTable_5548_);
lean_ctor_set(v___x_5581_, 6, v_appMap_5549_);
lean_ctor_set(v___x_5581_, 7, v_indicesFound_5550_);
lean_ctor_set(v___x_5581_, 8, v_newFacts_5551_);
lean_ctor_set(v___x_5581_, 9, v_nextIdx_5553_);
lean_ctor_set(v___x_5581_, 10, v_newRawFacts_5554_);
lean_ctor_set(v___x_5581_, 11, v_facts_5555_);
lean_ctor_set(v___x_5581_, 12, v_extThms_5556_);
lean_ctor_set(v___x_5581_, 13, v___x_5580_);
lean_ctor_set(v___x_5581_, 14, v_inj_5557_);
lean_ctor_set(v___x_5581_, 15, v_split_5558_);
lean_ctor_set(v___x_5581_, 16, v_clean_5559_);
lean_ctor_set(v___x_5581_, 17, v_sstates_5560_);
lean_ctor_set_uint8(v___x_5581_, sizeof(void*)*18, v_inconsistent_5552_);
v___x_5582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
lean_ctor_set(v___x_5582_, 1, v_mvarId_5561_);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 0, v___x_5582_);
v___x_5584_ = v___x_5577_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5582_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
else
{
lean_object* v_a_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5594_; 
lean_dec(v_a_5573_);
lean_dec(v_mvarId_5561_);
lean_dec_ref(v_sstates_5560_);
lean_dec_ref(v_clean_5559_);
lean_dec_ref(v_split_5558_);
lean_dec_ref(v_inj_5557_);
lean_dec_ref(v_extThms_5556_);
lean_dec_ref(v_facts_5555_);
lean_dec_ref(v_newRawFacts_5554_);
lean_dec(v_nextIdx_5553_);
lean_dec_ref(v_newFacts_5551_);
lean_dec_ref(v_indicesFound_5550_);
lean_dec_ref(v_appMap_5549_);
lean_dec_ref(v_congrTable_5548_);
lean_dec_ref(v_parents_5547_);
lean_dec_ref(v_exprs_5546_);
lean_dec_ref(v_enodeMap_5545_);
lean_dec_ref(v_canon_5544_);
lean_dec(v_nextDeclIdx_5543_);
lean_dec_ref(v_delayedThmInsts_5542_);
lean_dec_ref(v_matchEqNames_5541_);
lean_dec(v_nextThmIdx_5540_);
lean_dec_ref(v_preInstances_5539_);
lean_dec(v_num_5538_);
lean_dec(v_numDelayedInstances_5537_);
lean_dec(v_numInstances_5536_);
lean_dec(v_gmt_5535_);
v_a_5587_ = lean_ctor_get(v___x_5574_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v___x_5574_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5589_ = v___x_5574_;
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_a_5587_);
lean_dec(v___x_5574_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5592_; 
if (v_isShared_5590_ == 0)
{
v___x_5592_ = v___x_5589_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5587_);
v___x_5592_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
return v___x_5592_;
}
}
}
}
else
{
lean_object* v_a_5595_; lean_object* v___x_5597_; uint8_t v_isShared_5598_; uint8_t v_isSharedCheck_5602_; 
lean_dec(v___y_5570_);
lean_dec_ref(v___y_5569_);
lean_dec(v___y_5568_);
lean_dec_ref(v___y_5567_);
lean_dec(v_mvarId_5561_);
lean_dec_ref(v_sstates_5560_);
lean_dec_ref(v_clean_5559_);
lean_dec_ref(v_split_5558_);
lean_dec_ref(v_inj_5557_);
lean_dec_ref(v_extThms_5556_);
lean_dec_ref(v_facts_5555_);
lean_dec_ref(v_newRawFacts_5554_);
lean_dec(v_nextIdx_5553_);
lean_dec_ref(v_newFacts_5551_);
lean_dec_ref(v_indicesFound_5550_);
lean_dec_ref(v_appMap_5549_);
lean_dec_ref(v_congrTable_5548_);
lean_dec_ref(v_parents_5547_);
lean_dec_ref(v_exprs_5546_);
lean_dec_ref(v_enodeMap_5545_);
lean_dec_ref(v_canon_5544_);
lean_dec(v_nextDeclIdx_5543_);
lean_dec_ref(v_delayedThmInsts_5542_);
lean_dec_ref(v_matchEqNames_5541_);
lean_dec(v_nextThmIdx_5540_);
lean_dec_ref(v_preInstances_5539_);
lean_dec(v_num_5538_);
lean_dec(v_numDelayedInstances_5537_);
lean_dec(v_numInstances_5536_);
lean_dec(v_gmt_5535_);
lean_dec_ref(v_newThms_5534_);
v_a_5595_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5602_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5602_ == 0)
{
v___x_5597_ = v___x_5572_;
v_isShared_5598_ = v_isSharedCheck_5602_;
goto v_resetjp_5596_;
}
else
{
lean_inc(v_a_5595_);
lean_dec(v___x_5572_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5603_ = _args[0];
lean_object* v_newThms_5604_ = _args[1];
lean_object* v_gmt_5605_ = _args[2];
lean_object* v_numInstances_5606_ = _args[3];
lean_object* v_numDelayedInstances_5607_ = _args[4];
lean_object* v_num_5608_ = _args[5];
lean_object* v_preInstances_5609_ = _args[6];
lean_object* v_nextThmIdx_5610_ = _args[7];
lean_object* v_matchEqNames_5611_ = _args[8];
lean_object* v_delayedThmInsts_5612_ = _args[9];
lean_object* v_nextDeclIdx_5613_ = _args[10];
lean_object* v_canon_5614_ = _args[11];
lean_object* v_enodeMap_5615_ = _args[12];
lean_object* v_exprs_5616_ = _args[13];
lean_object* v_parents_5617_ = _args[14];
lean_object* v_congrTable_5618_ = _args[15];
lean_object* v_appMap_5619_ = _args[16];
lean_object* v_indicesFound_5620_ = _args[17];
lean_object* v_newFacts_5621_ = _args[18];
lean_object* v_inconsistent_5622_ = _args[19];
lean_object* v_nextIdx_5623_ = _args[20];
lean_object* v_newRawFacts_5624_ = _args[21];
lean_object* v_facts_5625_ = _args[22];
lean_object* v_extThms_5626_ = _args[23];
lean_object* v_inj_5627_ = _args[24];
lean_object* v_split_5628_ = _args[25];
lean_object* v_clean_5629_ = _args[26];
lean_object* v_sstates_5630_ = _args[27];
lean_object* v_mvarId_5631_ = _args[28];
lean_object* v___y_5632_ = _args[29];
lean_object* v___y_5633_ = _args[30];
lean_object* v___y_5634_ = _args[31];
lean_object* v___y_5635_ = _args[32];
lean_object* v___y_5636_ = _args[33];
lean_object* v___y_5637_ = _args[34];
lean_object* v___y_5638_ = _args[35];
lean_object* v___y_5639_ = _args[36];
lean_object* v___y_5640_ = _args[37];
lean_object* v___y_5641_ = _args[38];
_start:
{
uint8_t v_inconsistent_boxed_5642_; lean_object* v_res_5643_; 
v_inconsistent_boxed_5642_ = lean_unbox(v_inconsistent_5622_);
v_res_5643_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5603_, v_newThms_5604_, v_gmt_5605_, v_numInstances_5606_, v_numDelayedInstances_5607_, v_num_5608_, v_preInstances_5609_, v_nextThmIdx_5610_, v_matchEqNames_5611_, v_delayedThmInsts_5612_, v_nextDeclIdx_5613_, v_canon_5614_, v_enodeMap_5615_, v_exprs_5616_, v_parents_5617_, v_congrTable_5618_, v_appMap_5619_, v_indicesFound_5620_, v_newFacts_5621_, v_inconsistent_boxed_5642_, v_nextIdx_5623_, v_newRawFacts_5624_, v_facts_5625_, v_extThms_5626_, v_inj_5627_, v_split_5628_, v_clean_5629_, v_sstates_5630_, v_mvarId_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_);
lean_dec(v___y_5636_);
lean_dec_ref(v___y_5635_);
lean_dec(v___y_5634_);
lean_dec_ref(v___y_5633_);
lean_dec(v___y_5632_);
return v_res_5643_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5644_; 
v___x_5644_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_5644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5645_, size_t v_i_5646_, lean_object* v_bs_5647_){
_start:
{
uint8_t v___x_5648_; 
v___x_5648_ = lean_usize_dec_lt(v_i_5646_, v_sz_5645_);
if (v___x_5648_ == 0)
{
return v_bs_5647_;
}
else
{
lean_object* v_v_5649_; lean_object* v_casesTypes_5650_; lean_object* v_extThms_5651_; lean_object* v_funCC_5652_; lean_object* v_inj_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5667_; 
v_v_5649_ = lean_array_uget(v_bs_5647_, v_i_5646_);
v_casesTypes_5650_ = lean_ctor_get(v_v_5649_, 0);
v_extThms_5651_ = lean_ctor_get(v_v_5649_, 1);
v_funCC_5652_ = lean_ctor_get(v_v_5649_, 2);
v_inj_5653_ = lean_ctor_get(v_v_5649_, 4);
v_isSharedCheck_5667_ = !lean_is_exclusive(v_v_5649_);
if (v_isSharedCheck_5667_ == 0)
{
lean_object* v_unused_5668_; 
v_unused_5668_ = lean_ctor_get(v_v_5649_, 3);
lean_dec(v_unused_5668_);
v___x_5655_ = v_v_5649_;
v_isShared_5656_ = v_isSharedCheck_5667_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_inj_5653_);
lean_inc(v_funCC_5652_);
lean_inc(v_extThms_5651_);
lean_inc(v_casesTypes_5650_);
lean_dec(v_v_5649_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5667_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
lean_object* v___x_5657_; lean_object* v_bs_x27_5658_; lean_object* v___x_5659_; lean_object* v___x_5661_; 
v___x_5657_ = lean_unsigned_to_nat(0u);
v_bs_x27_5658_ = lean_array_uset(v_bs_5647_, v_i_5646_, v___x_5657_);
v___x_5659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5656_ == 0)
{
lean_ctor_set(v___x_5655_, 3, v___x_5659_);
v___x_5661_ = v___x_5655_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_casesTypes_5650_);
lean_ctor_set(v_reuseFailAlloc_5666_, 1, v_extThms_5651_);
lean_ctor_set(v_reuseFailAlloc_5666_, 2, v_funCC_5652_);
lean_ctor_set(v_reuseFailAlloc_5666_, 3, v___x_5659_);
lean_ctor_set(v_reuseFailAlloc_5666_, 4, v_inj_5653_);
v___x_5661_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
size_t v___x_5662_; size_t v___x_5663_; lean_object* v___x_5664_; 
v___x_5662_ = ((size_t)1ULL);
v___x_5663_ = lean_usize_add(v_i_5646_, v___x_5662_);
v___x_5664_ = lean_array_uset(v_bs_x27_5658_, v_i_5646_, v___x_5661_);
v_i_5646_ = v___x_5663_;
v_bs_5647_ = v___x_5664_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5669_, lean_object* v_i_5670_, lean_object* v_bs_5671_){
_start:
{
size_t v_sz_boxed_5672_; size_t v_i_boxed_5673_; lean_object* v_res_5674_; 
v_sz_boxed_5672_ = lean_unbox_usize(v_sz_5669_);
lean_dec(v_sz_5669_);
v_i_boxed_5673_ = lean_unbox_usize(v_i_5670_);
lean_dec(v_i_5670_);
v_res_5674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5672_, v_i_boxed_5673_, v_bs_5671_);
return v_res_5674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5675_, lean_object* v_ps_5676_, uint8_t v_only_5677_, lean_object* v_k_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_){
_start:
{
lean_object* v___y_5689_; lean_object* v___y_5690_; lean_object* v___y_5691_; lean_object* v___y_5692_; lean_object* v___y_5693_; lean_object* v___y_5694_; lean_object* v___y_5695_; lean_object* v___y_5696_; lean_object* v___y_5697_; uint8_t v___y_5710_; uint8_t v___y_5711_; lean_object* v_params_5712_; lean_object* v___y_5713_; lean_object* v___y_5714_; lean_object* v___y_5715_; lean_object* v___y_5716_; lean_object* v___y_5717_; lean_object* v___y_5718_; lean_object* v___y_5719_; lean_object* v___y_5720_; uint8_t v___y_5835_; 
if (v_only_5677_ == 0)
{
lean_object* v___x_5857_; lean_object* v___x_5858_; uint8_t v___x_5859_; 
v___x_5857_ = lean_array_get_size(v_ps_5676_);
v___x_5858_ = lean_unsigned_to_nat(0u);
v___x_5859_ = lean_nat_dec_eq(v___x_5857_, v___x_5858_);
if (v___x_5859_ == 0)
{
v___y_5835_ = v___x_5859_;
goto v___jp_5834_;
}
else
{
lean_object* v___x_5860_; 
lean_dec_ref(v_params_5675_);
v___x_5860_ = lean_apply_9(v_k_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_, v_a_5683_, v_a_5684_, v_a_5685_, v_a_5686_, lean_box(0));
return v___x_5860_;
}
}
else
{
uint8_t v___x_5861_; 
v___x_5861_ = 0;
v___y_5835_ = v___x_5861_;
goto v___jp_5834_;
}
v___jp_5688_:
{
lean_object* v___x_5698_; lean_object* v___x_5699_; 
v___x_5698_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5698_, 0, v___y_5689_);
lean_inc(v___y_5697_);
lean_inc_ref(v___y_5696_);
lean_inc(v___y_5695_);
lean_inc_ref(v___y_5694_);
lean_inc_ref(v___y_5690_);
v___x_5699_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5698_, v___y_5690_, v___y_5691_, v___y_5694_, v___y_5695_, v___y_5696_, v___y_5697_);
if (lean_obj_tag(v___x_5699_) == 0)
{
lean_object* v___x_5700_; 
lean_dec_ref(v___x_5699_);
v___x_5700_ = lean_apply_9(v_k_5678_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_, v___y_5697_, lean_box(0));
return v___x_5700_;
}
else
{
lean_object* v_a_5701_; lean_object* v___x_5703_; uint8_t v_isShared_5704_; uint8_t v_isSharedCheck_5708_; 
lean_dec(v___y_5697_);
lean_dec_ref(v___y_5696_);
lean_dec(v___y_5695_);
lean_dec_ref(v___y_5694_);
lean_dec(v___y_5693_);
lean_dec_ref(v___y_5692_);
lean_dec(v___y_5691_);
lean_dec_ref(v___y_5690_);
lean_dec_ref(v_k_5678_);
v_a_5701_ = lean_ctor_get(v___x_5699_, 0);
v_isSharedCheck_5708_ = !lean_is_exclusive(v___x_5699_);
if (v_isSharedCheck_5708_ == 0)
{
v___x_5703_ = v___x_5699_;
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
else
{
lean_inc(v_a_5701_);
lean_dec(v___x_5699_);
v___x_5703_ = lean_box(0);
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
v_resetjp_5702_:
{
lean_object* v___x_5706_; 
if (v_isShared_5704_ == 0)
{
v___x_5706_ = v___x_5703_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v_a_5701_);
v___x_5706_ = v_reuseFailAlloc_5707_;
goto v_reusejp_5705_;
}
v_reusejp_5705_:
{
return v___x_5706_;
}
}
}
}
v___jp_5709_:
{
lean_object* v___x_5721_; 
lean_inc(v___y_5720_);
lean_inc_ref(v___y_5719_);
lean_inc(v___y_5718_);
lean_inc_ref(v___y_5717_);
lean_inc(v___y_5716_);
lean_inc_ref(v___y_5715_);
v___x_5721_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5712_, v_ps_5676_, v_only_5677_, v___y_5711_, v___y_5710_, v___y_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_);
if (lean_obj_tag(v___x_5721_) == 0)
{
lean_object* v_a_5722_; lean_object* v_ctx_5723_; lean_object* v_anchorRefs_x3f_5724_; lean_object* v_toContext_5725_; lean_object* v_sctx_5726_; lean_object* v_methods_5727_; uint8_t v_sym_5728_; lean_object* v___x_5730_; uint8_t v_isShared_5731_; uint8_t v_isSharedCheck_5823_; 
v_a_5722_ = lean_ctor_get(v___x_5721_, 0);
lean_inc(v_a_5722_);
lean_dec_ref(v___x_5721_);
v_ctx_5723_ = lean_ctor_get(v___y_5713_, 1);
lean_inc_ref(v_ctx_5723_);
v_anchorRefs_x3f_5724_ = lean_ctor_get(v_a_5722_, 8);
v_toContext_5725_ = lean_ctor_get(v___y_5713_, 0);
v_sctx_5726_ = lean_ctor_get(v___y_5713_, 2);
v_methods_5727_ = lean_ctor_get(v___y_5713_, 3);
v_sym_5728_ = lean_ctor_get_uint8(v___y_5713_, sizeof(void*)*5);
v_isSharedCheck_5823_ = !lean_is_exclusive(v___y_5713_);
if (v_isSharedCheck_5823_ == 0)
{
lean_object* v_unused_5824_; lean_object* v_unused_5825_; 
v_unused_5824_ = lean_ctor_get(v___y_5713_, 4);
lean_dec(v_unused_5824_);
v_unused_5825_ = lean_ctor_get(v___y_5713_, 1);
lean_dec(v_unused_5825_);
v___x_5730_ = v___y_5713_;
v_isShared_5731_ = v_isSharedCheck_5823_;
goto v_resetjp_5729_;
}
else
{
lean_inc(v_methods_5727_);
lean_inc(v_sctx_5726_);
lean_inc(v_toContext_5725_);
lean_dec(v___y_5713_);
v___x_5730_ = lean_box(0);
v_isShared_5731_ = v_isSharedCheck_5823_;
goto v_resetjp_5729_;
}
v_resetjp_5729_:
{
lean_object* v_simp_5732_; lean_object* v_simpMethods_5733_; lean_object* v_config_5734_; uint8_t v_cheapCases_5735_; uint8_t v_reportMVarIssue_5736_; lean_object* v_splitSource_5737_; lean_object* v_symPrios_5738_; lean_object* v_extensions_5739_; uint8_t v_debug_5740_; lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5821_; 
v_simp_5732_ = lean_ctor_get(v_ctx_5723_, 0);
v_simpMethods_5733_ = lean_ctor_get(v_ctx_5723_, 1);
v_config_5734_ = lean_ctor_get(v_ctx_5723_, 2);
v_cheapCases_5735_ = lean_ctor_get_uint8(v_ctx_5723_, sizeof(void*)*7);
v_reportMVarIssue_5736_ = lean_ctor_get_uint8(v_ctx_5723_, sizeof(void*)*7 + 1);
v_splitSource_5737_ = lean_ctor_get(v_ctx_5723_, 4);
v_symPrios_5738_ = lean_ctor_get(v_ctx_5723_, 5);
v_extensions_5739_ = lean_ctor_get(v_ctx_5723_, 6);
v_debug_5740_ = lean_ctor_get_uint8(v_ctx_5723_, sizeof(void*)*7 + 2);
v_isSharedCheck_5821_ = !lean_is_exclusive(v_ctx_5723_);
if (v_isSharedCheck_5821_ == 0)
{
lean_object* v_unused_5822_; 
v_unused_5822_ = lean_ctor_get(v_ctx_5723_, 3);
lean_dec(v_unused_5822_);
v___x_5742_ = v_ctx_5723_;
v_isShared_5743_ = v_isSharedCheck_5821_;
goto v_resetjp_5741_;
}
else
{
lean_inc(v_extensions_5739_);
lean_inc(v_symPrios_5738_);
lean_inc(v_splitSource_5737_);
lean_inc(v_config_5734_);
lean_inc(v_simpMethods_5733_);
lean_inc(v_simp_5732_);
lean_dec(v_ctx_5723_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5821_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
lean_object* v___x_5745_; 
lean_inc(v_anchorRefs_x3f_5724_);
if (v_isShared_5743_ == 0)
{
lean_ctor_set(v___x_5742_, 3, v_anchorRefs_x3f_5724_);
v___x_5745_ = v___x_5742_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5820_; 
v_reuseFailAlloc_5820_ = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_simp_5732_);
lean_ctor_set(v_reuseFailAlloc_5820_, 1, v_simpMethods_5733_);
lean_ctor_set(v_reuseFailAlloc_5820_, 2, v_config_5734_);
lean_ctor_set(v_reuseFailAlloc_5820_, 3, v_anchorRefs_x3f_5724_);
lean_ctor_set(v_reuseFailAlloc_5820_, 4, v_splitSource_5737_);
lean_ctor_set(v_reuseFailAlloc_5820_, 5, v_symPrios_5738_);
lean_ctor_set(v_reuseFailAlloc_5820_, 6, v_extensions_5739_);
lean_ctor_set_uint8(v_reuseFailAlloc_5820_, sizeof(void*)*7, v_cheapCases_5735_);
lean_ctor_set_uint8(v_reuseFailAlloc_5820_, sizeof(void*)*7 + 1, v_reportMVarIssue_5736_);
lean_ctor_set_uint8(v_reuseFailAlloc_5820_, sizeof(void*)*7 + 2, v_debug_5740_);
v___x_5745_ = v_reuseFailAlloc_5820_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
lean_object* v___x_5747_; 
lean_inc(v_a_5722_);
if (v_isShared_5731_ == 0)
{
lean_ctor_set(v___x_5730_, 4, v_a_5722_);
lean_ctor_set(v___x_5730_, 1, v___x_5745_);
v___x_5747_ = v___x_5730_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_toContext_5725_);
lean_ctor_set(v_reuseFailAlloc_5819_, 1, v___x_5745_);
lean_ctor_set(v_reuseFailAlloc_5819_, 2, v_sctx_5726_);
lean_ctor_set(v_reuseFailAlloc_5819_, 3, v_methods_5727_);
lean_ctor_set(v_reuseFailAlloc_5819_, 4, v_a_5722_);
lean_ctor_set_uint8(v_reuseFailAlloc_5819_, sizeof(void*)*5, v_sym_5728_);
v___x_5747_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
if (v_only_5677_ == 0)
{
v___y_5689_ = v_a_5722_;
v___y_5690_ = v___x_5747_;
v___y_5691_ = v___y_5714_;
v___y_5692_ = v___y_5715_;
v___y_5693_ = v___y_5716_;
v___y_5694_ = v___y_5717_;
v___y_5695_ = v___y_5718_;
v___y_5696_ = v___y_5719_;
v___y_5697_ = v___y_5720_;
goto v___jp_5688_;
}
else
{
lean_object* v___x_5748_; 
v___x_5748_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5714_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_);
if (lean_obj_tag(v___x_5748_) == 0)
{
lean_object* v_a_5749_; lean_object* v_toGoalState_5750_; lean_object* v_ematch_5751_; lean_object* v_mvarId_5752_; lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5809_; 
v_a_5749_ = lean_ctor_get(v___x_5748_, 0);
lean_inc(v_a_5749_);
lean_dec_ref(v___x_5748_);
v_toGoalState_5750_ = lean_ctor_get(v_a_5749_, 0);
lean_inc_ref(v_toGoalState_5750_);
v_ematch_5751_ = lean_ctor_get(v_toGoalState_5750_, 13);
lean_inc_ref(v_ematch_5751_);
v_mvarId_5752_ = lean_ctor_get(v_a_5749_, 1);
v_isSharedCheck_5809_ = !lean_is_exclusive(v_a_5749_);
if (v_isSharedCheck_5809_ == 0)
{
lean_object* v_unused_5810_; 
v_unused_5810_ = lean_ctor_get(v_a_5749_, 0);
lean_dec(v_unused_5810_);
v___x_5754_ = v_a_5749_;
v_isShared_5755_ = v_isSharedCheck_5809_;
goto v_resetjp_5753_;
}
else
{
lean_inc(v_mvarId_5752_);
lean_dec(v_a_5749_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5809_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v_nextDeclIdx_5756_; lean_object* v_canon_5757_; lean_object* v_enodeMap_5758_; lean_object* v_exprs_5759_; lean_object* v_parents_5760_; lean_object* v_congrTable_5761_; lean_object* v_appMap_5762_; lean_object* v_indicesFound_5763_; lean_object* v_newFacts_5764_; uint8_t v_inconsistent_5765_; lean_object* v_nextIdx_5766_; lean_object* v_newRawFacts_5767_; lean_object* v_facts_5768_; lean_object* v_extThms_5769_; lean_object* v_inj_5770_; lean_object* v_split_5771_; lean_object* v_clean_5772_; lean_object* v_sstates_5773_; lean_object* v_gmt_5774_; lean_object* v_thms_5775_; lean_object* v_newThms_5776_; lean_object* v_numInstances_5777_; lean_object* v_numDelayedInstances_5778_; lean_object* v_num_5779_; lean_object* v_preInstances_5780_; lean_object* v_nextThmIdx_5781_; lean_object* v_matchEqNames_5782_; lean_object* v_delayedThmInsts_5783_; lean_object* v___x_5784_; lean_object* v___f_5785_; lean_object* v___x_5786_; 
v_nextDeclIdx_5756_ = lean_ctor_get(v_toGoalState_5750_, 0);
lean_inc(v_nextDeclIdx_5756_);
v_canon_5757_ = lean_ctor_get(v_toGoalState_5750_, 1);
lean_inc_ref(v_canon_5757_);
v_enodeMap_5758_ = lean_ctor_get(v_toGoalState_5750_, 2);
lean_inc_ref(v_enodeMap_5758_);
v_exprs_5759_ = lean_ctor_get(v_toGoalState_5750_, 3);
lean_inc_ref(v_exprs_5759_);
v_parents_5760_ = lean_ctor_get(v_toGoalState_5750_, 4);
lean_inc_ref(v_parents_5760_);
v_congrTable_5761_ = lean_ctor_get(v_toGoalState_5750_, 5);
lean_inc_ref(v_congrTable_5761_);
v_appMap_5762_ = lean_ctor_get(v_toGoalState_5750_, 6);
lean_inc_ref(v_appMap_5762_);
v_indicesFound_5763_ = lean_ctor_get(v_toGoalState_5750_, 7);
lean_inc_ref(v_indicesFound_5763_);
v_newFacts_5764_ = lean_ctor_get(v_toGoalState_5750_, 8);
lean_inc_ref(v_newFacts_5764_);
v_inconsistent_5765_ = lean_ctor_get_uint8(v_toGoalState_5750_, sizeof(void*)*18);
v_nextIdx_5766_ = lean_ctor_get(v_toGoalState_5750_, 9);
lean_inc(v_nextIdx_5766_);
v_newRawFacts_5767_ = lean_ctor_get(v_toGoalState_5750_, 10);
lean_inc_ref(v_newRawFacts_5767_);
v_facts_5768_ = lean_ctor_get(v_toGoalState_5750_, 11);
lean_inc_ref(v_facts_5768_);
v_extThms_5769_ = lean_ctor_get(v_toGoalState_5750_, 12);
lean_inc_ref(v_extThms_5769_);
v_inj_5770_ = lean_ctor_get(v_toGoalState_5750_, 14);
lean_inc_ref(v_inj_5770_);
v_split_5771_ = lean_ctor_get(v_toGoalState_5750_, 15);
lean_inc_ref(v_split_5771_);
v_clean_5772_ = lean_ctor_get(v_toGoalState_5750_, 16);
lean_inc_ref(v_clean_5772_);
v_sstates_5773_ = lean_ctor_get(v_toGoalState_5750_, 17);
lean_inc_ref(v_sstates_5773_);
lean_dec_ref(v_toGoalState_5750_);
v_gmt_5774_ = lean_ctor_get(v_ematch_5751_, 1);
lean_inc(v_gmt_5774_);
v_thms_5775_ = lean_ctor_get(v_ematch_5751_, 2);
lean_inc_ref(v_thms_5775_);
v_newThms_5776_ = lean_ctor_get(v_ematch_5751_, 3);
lean_inc_ref(v_newThms_5776_);
v_numInstances_5777_ = lean_ctor_get(v_ematch_5751_, 4);
lean_inc(v_numInstances_5777_);
v_numDelayedInstances_5778_ = lean_ctor_get(v_ematch_5751_, 5);
lean_inc(v_numDelayedInstances_5778_);
v_num_5779_ = lean_ctor_get(v_ematch_5751_, 6);
lean_inc(v_num_5779_);
v_preInstances_5780_ = lean_ctor_get(v_ematch_5751_, 7);
lean_inc_ref(v_preInstances_5780_);
v_nextThmIdx_5781_ = lean_ctor_get(v_ematch_5751_, 8);
lean_inc(v_nextThmIdx_5781_);
v_matchEqNames_5782_ = lean_ctor_get(v_ematch_5751_, 9);
lean_inc_ref(v_matchEqNames_5782_);
v_delayedThmInsts_5783_ = lean_ctor_get(v_ematch_5751_, 10);
lean_inc_ref(v_delayedThmInsts_5783_);
lean_dec_ref(v_ematch_5751_);
v___x_5784_ = lean_box(v_inconsistent_5765_);
v___f_5785_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 39, 29);
lean_closure_set(v___f_5785_, 0, v_thms_5775_);
lean_closure_set(v___f_5785_, 1, v_newThms_5776_);
lean_closure_set(v___f_5785_, 2, v_gmt_5774_);
lean_closure_set(v___f_5785_, 3, v_numInstances_5777_);
lean_closure_set(v___f_5785_, 4, v_numDelayedInstances_5778_);
lean_closure_set(v___f_5785_, 5, v_num_5779_);
lean_closure_set(v___f_5785_, 6, v_preInstances_5780_);
lean_closure_set(v___f_5785_, 7, v_nextThmIdx_5781_);
lean_closure_set(v___f_5785_, 8, v_matchEqNames_5782_);
lean_closure_set(v___f_5785_, 9, v_delayedThmInsts_5783_);
lean_closure_set(v___f_5785_, 10, v_nextDeclIdx_5756_);
lean_closure_set(v___f_5785_, 11, v_canon_5757_);
lean_closure_set(v___f_5785_, 12, v_enodeMap_5758_);
lean_closure_set(v___f_5785_, 13, v_exprs_5759_);
lean_closure_set(v___f_5785_, 14, v_parents_5760_);
lean_closure_set(v___f_5785_, 15, v_congrTable_5761_);
lean_closure_set(v___f_5785_, 16, v_appMap_5762_);
lean_closure_set(v___f_5785_, 17, v_indicesFound_5763_);
lean_closure_set(v___f_5785_, 18, v_newFacts_5764_);
lean_closure_set(v___f_5785_, 19, v___x_5784_);
lean_closure_set(v___f_5785_, 20, v_nextIdx_5766_);
lean_closure_set(v___f_5785_, 21, v_newRawFacts_5767_);
lean_closure_set(v___f_5785_, 22, v_facts_5768_);
lean_closure_set(v___f_5785_, 23, v_extThms_5769_);
lean_closure_set(v___f_5785_, 24, v_inj_5770_);
lean_closure_set(v___f_5785_, 25, v_split_5771_);
lean_closure_set(v___f_5785_, 26, v_clean_5772_);
lean_closure_set(v___f_5785_, 27, v_sstates_5773_);
lean_closure_set(v___f_5785_, 28, v_mvarId_5752_);
lean_inc(v___y_5720_);
lean_inc_ref(v___y_5719_);
lean_inc(v___y_5718_);
lean_inc_ref(v___y_5717_);
lean_inc_ref(v___x_5747_);
v___x_5786_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5785_, v___x_5747_, v___y_5714_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_);
if (lean_obj_tag(v___x_5786_) == 0)
{
lean_object* v_a_5787_; lean_object* v___x_5788_; lean_object* v___x_5790_; 
v_a_5787_ = lean_ctor_get(v___x_5786_, 0);
lean_inc(v_a_5787_);
lean_dec_ref(v___x_5786_);
v___x_5788_ = lean_box(0);
if (v_isShared_5755_ == 0)
{
lean_ctor_set_tag(v___x_5754_, 1);
lean_ctor_set(v___x_5754_, 1, v___x_5788_);
lean_ctor_set(v___x_5754_, 0, v_a_5787_);
v___x_5790_ = v___x_5754_;
goto v_reusejp_5789_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v_a_5787_);
lean_ctor_set(v_reuseFailAlloc_5800_, 1, v___x_5788_);
v___x_5790_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5789_;
}
v_reusejp_5789_:
{
lean_object* v___x_5791_; 
v___x_5791_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5790_, v___y_5714_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_);
if (lean_obj_tag(v___x_5791_) == 0)
{
lean_dec_ref(v___x_5791_);
v___y_5689_ = v_a_5722_;
v___y_5690_ = v___x_5747_;
v___y_5691_ = v___y_5714_;
v___y_5692_ = v___y_5715_;
v___y_5693_ = v___y_5716_;
v___y_5694_ = v___y_5717_;
v___y_5695_ = v___y_5718_;
v___y_5696_ = v___y_5719_;
v___y_5697_ = v___y_5720_;
goto v___jp_5688_;
}
else
{
lean_object* v_a_5792_; lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5799_; 
lean_dec_ref(v___x_5747_);
lean_dec(v_a_5722_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec(v___y_5716_);
lean_dec_ref(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec_ref(v_k_5678_);
v_a_5792_ = lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5799_ = !lean_is_exclusive(v___x_5791_);
if (v_isSharedCheck_5799_ == 0)
{
v___x_5794_ = v___x_5791_;
v_isShared_5795_ = v_isSharedCheck_5799_;
goto v_resetjp_5793_;
}
else
{
lean_inc(v_a_5792_);
lean_dec(v___x_5791_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5799_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
lean_object* v___x_5797_; 
if (v_isShared_5795_ == 0)
{
v___x_5797_ = v___x_5794_;
goto v_reusejp_5796_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_a_5792_);
v___x_5797_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5796_;
}
v_reusejp_5796_:
{
return v___x_5797_;
}
}
}
}
}
else
{
lean_object* v_a_5801_; lean_object* v___x_5803_; uint8_t v_isShared_5804_; uint8_t v_isSharedCheck_5808_; 
lean_del_object(v___x_5754_);
lean_dec_ref(v___x_5747_);
lean_dec(v_a_5722_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec(v___y_5716_);
lean_dec_ref(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec_ref(v_k_5678_);
v_a_5801_ = lean_ctor_get(v___x_5786_, 0);
v_isSharedCheck_5808_ = !lean_is_exclusive(v___x_5786_);
if (v_isSharedCheck_5808_ == 0)
{
v___x_5803_ = v___x_5786_;
v_isShared_5804_ = v_isSharedCheck_5808_;
goto v_resetjp_5802_;
}
else
{
lean_inc(v_a_5801_);
lean_dec(v___x_5786_);
v___x_5803_ = lean_box(0);
v_isShared_5804_ = v_isSharedCheck_5808_;
goto v_resetjp_5802_;
}
v_resetjp_5802_:
{
lean_object* v___x_5806_; 
if (v_isShared_5804_ == 0)
{
v___x_5806_ = v___x_5803_;
goto v_reusejp_5805_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v_a_5801_);
v___x_5806_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5805_;
}
v_reusejp_5805_:
{
return v___x_5806_;
}
}
}
}
}
else
{
lean_object* v_a_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5818_; 
lean_dec_ref(v___x_5747_);
lean_dec(v_a_5722_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec(v___y_5716_);
lean_dec_ref(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec_ref(v_k_5678_);
v_a_5811_ = lean_ctor_get(v___x_5748_, 0);
v_isSharedCheck_5818_ = !lean_is_exclusive(v___x_5748_);
if (v_isSharedCheck_5818_ == 0)
{
v___x_5813_ = v___x_5748_;
v_isShared_5814_ = v_isSharedCheck_5818_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_a_5811_);
lean_dec(v___x_5748_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5818_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
lean_object* v___x_5816_; 
if (v_isShared_5814_ == 0)
{
v___x_5816_ = v___x_5813_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_a_5811_);
v___x_5816_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
return v___x_5816_;
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
lean_object* v_a_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5833_; 
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec(v___y_5716_);
lean_dec_ref(v___y_5715_);
lean_dec(v___y_5714_);
lean_dec_ref(v___y_5713_);
lean_dec_ref(v_k_5678_);
v_a_5826_ = lean_ctor_get(v___x_5721_, 0);
v_isSharedCheck_5833_ = !lean_is_exclusive(v___x_5721_);
if (v_isSharedCheck_5833_ == 0)
{
v___x_5828_ = v___x_5721_;
v_isShared_5829_ = v_isSharedCheck_5833_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_a_5826_);
lean_dec(v___x_5721_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5833_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
lean_object* v___x_5831_; 
if (v_isShared_5829_ == 0)
{
v___x_5831_ = v___x_5828_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5832_; 
v_reuseFailAlloc_5832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_a_5826_);
v___x_5831_ = v_reuseFailAlloc_5832_;
goto v_reusejp_5830_;
}
v_reusejp_5830_:
{
return v___x_5831_;
}
}
}
}
v___jp_5834_:
{
uint8_t v___x_5836_; 
v___x_5836_ = 1;
if (v_only_5677_ == 0)
{
v___y_5710_ = v___x_5836_;
v___y_5711_ = v___y_5835_;
v_params_5712_ = v_params_5675_;
v___y_5713_ = v_a_5679_;
v___y_5714_ = v_a_5680_;
v___y_5715_ = v_a_5681_;
v___y_5716_ = v_a_5682_;
v___y_5717_ = v_a_5683_;
v___y_5718_ = v_a_5684_;
v___y_5719_ = v_a_5685_;
v___y_5720_ = v_a_5686_;
goto v___jp_5709_;
}
else
{
lean_object* v_config_5837_; lean_object* v_extensions_5838_; lean_object* v_extra_5839_; lean_object* v_extraInj_5840_; lean_object* v_extraFacts_5841_; lean_object* v_symPrios_5842_; lean_object* v_norm_5843_; lean_object* v_normProcs_5844_; lean_object* v___x_5846_; uint8_t v_isShared_5847_; uint8_t v_isSharedCheck_5855_; 
v_config_5837_ = lean_ctor_get(v_params_5675_, 0);
v_extensions_5838_ = lean_ctor_get(v_params_5675_, 1);
v_extra_5839_ = lean_ctor_get(v_params_5675_, 2);
v_extraInj_5840_ = lean_ctor_get(v_params_5675_, 3);
v_extraFacts_5841_ = lean_ctor_get(v_params_5675_, 4);
v_symPrios_5842_ = lean_ctor_get(v_params_5675_, 5);
v_norm_5843_ = lean_ctor_get(v_params_5675_, 6);
v_normProcs_5844_ = lean_ctor_get(v_params_5675_, 7);
v_isSharedCheck_5855_ = !lean_is_exclusive(v_params_5675_);
if (v_isSharedCheck_5855_ == 0)
{
lean_object* v_unused_5856_; 
v_unused_5856_ = lean_ctor_get(v_params_5675_, 8);
lean_dec(v_unused_5856_);
v___x_5846_ = v_params_5675_;
v_isShared_5847_ = v_isSharedCheck_5855_;
goto v_resetjp_5845_;
}
else
{
lean_inc(v_normProcs_5844_);
lean_inc(v_norm_5843_);
lean_inc(v_symPrios_5842_);
lean_inc(v_extraFacts_5841_);
lean_inc(v_extraInj_5840_);
lean_inc(v_extra_5839_);
lean_inc(v_extensions_5838_);
lean_inc(v_config_5837_);
lean_dec(v_params_5675_);
v___x_5846_ = lean_box(0);
v_isShared_5847_ = v_isSharedCheck_5855_;
goto v_resetjp_5845_;
}
v_resetjp_5845_:
{
size_t v_sz_5848_; size_t v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v_params_5853_; 
v_sz_5848_ = lean_array_size(v_extensions_5838_);
v___x_5849_ = ((size_t)0ULL);
v___x_5850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5848_, v___x_5849_, v_extensions_5838_);
v___x_5851_ = lean_box(0);
if (v_isShared_5847_ == 0)
{
lean_ctor_set(v___x_5846_, 8, v___x_5851_);
lean_ctor_set(v___x_5846_, 1, v___x_5850_);
v_params_5853_ = v___x_5846_;
goto v_reusejp_5852_;
}
else
{
lean_object* v_reuseFailAlloc_5854_; 
v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_config_5837_);
lean_ctor_set(v_reuseFailAlloc_5854_, 1, v___x_5850_);
lean_ctor_set(v_reuseFailAlloc_5854_, 2, v_extra_5839_);
lean_ctor_set(v_reuseFailAlloc_5854_, 3, v_extraInj_5840_);
lean_ctor_set(v_reuseFailAlloc_5854_, 4, v_extraFacts_5841_);
lean_ctor_set(v_reuseFailAlloc_5854_, 5, v_symPrios_5842_);
lean_ctor_set(v_reuseFailAlloc_5854_, 6, v_norm_5843_);
lean_ctor_set(v_reuseFailAlloc_5854_, 7, v_normProcs_5844_);
lean_ctor_set(v_reuseFailAlloc_5854_, 8, v___x_5851_);
v_params_5853_ = v_reuseFailAlloc_5854_;
goto v_reusejp_5852_;
}
v_reusejp_5852_:
{
v___y_5710_ = v___x_5836_;
v___y_5711_ = v___y_5835_;
v_params_5712_ = v_params_5853_;
v___y_5713_ = v_a_5679_;
v___y_5714_ = v_a_5680_;
v___y_5715_ = v_a_5681_;
v___y_5716_ = v_a_5682_;
v___y_5717_ = v_a_5683_;
v___y_5718_ = v_a_5684_;
v___y_5719_ = v_a_5685_;
v___y_5720_ = v_a_5686_;
goto v___jp_5709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_5862_, lean_object* v_ps_5863_, lean_object* v_only_5864_, lean_object* v_k_5865_, lean_object* v_a_5866_, lean_object* v_a_5867_, lean_object* v_a_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_, lean_object* v_a_5873_, lean_object* v_a_5874_){
_start:
{
uint8_t v_only_boxed_5875_; lean_object* v_res_5876_; 
v_only_boxed_5875_ = lean_unbox(v_only_5864_);
v_res_5876_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5862_, v_ps_5863_, v_only_boxed_5875_, v_k_5865_, v_a_5866_, v_a_5867_, v_a_5868_, v_a_5869_, v_a_5870_, v_a_5871_, v_a_5872_, v_a_5873_);
lean_dec_ref(v_ps_5863_);
return v_res_5876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_5877_, lean_object* v_params_5878_, lean_object* v_ps_5879_, uint8_t v_only_5880_, lean_object* v_k_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_, lean_object* v_a_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_){
_start:
{
lean_object* v___x_5891_; 
v___x_5891_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5878_, v_ps_5879_, v_only_5880_, v_k_5881_, v_a_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_, v_a_5887_, v_a_5888_, v_a_5889_);
return v___x_5891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_5892_, lean_object* v_params_5893_, lean_object* v_ps_5894_, lean_object* v_only_5895_, lean_object* v_k_5896_, lean_object* v_a_5897_, lean_object* v_a_5898_, lean_object* v_a_5899_, lean_object* v_a_5900_, lean_object* v_a_5901_, lean_object* v_a_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_, lean_object* v_a_5905_){
_start:
{
uint8_t v_only_boxed_5906_; lean_object* v_res_5907_; 
v_only_boxed_5906_ = lean_unbox(v_only_5895_);
v_res_5907_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_5892_, v_params_5893_, v_ps_5894_, v_only_boxed_5906_, v_k_5896_, v_a_5897_, v_a_5898_, v_a_5899_, v_a_5900_, v_a_5901_, v_a_5902_, v_a_5903_, v_a_5904_);
lean_dec_ref(v_ps_5894_);
return v_res_5907_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Param(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_Param(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_Param(builtin);
}
#ifdef __cplusplus
}
#endif
