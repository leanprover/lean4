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
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object*);
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
lean_object* l_Lean_Elab_Term_checkDeprecatedCore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`cases` parameter is not supported here"};
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
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "homomorphism rules should be registered using the `@[grind hom]` attribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "homomorphism predicates should be registered using the `@[grind hom_pred]` attribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid use of modifier in `grind` attribute `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "redundant parameter `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "`, `grind` uses local hypotheses automatically"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25;
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
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "invalid anchor, `only` modifier expected"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexnum"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(152, 252, 51, 178, 203, 245, 189, 159)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "invalid `-` occurrence, it can only be used at the `grind` tactic entry point"};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_ctor_set(v___x_89_, 0, v___y_84_);
lean_ctor_set(v___x_89_, 1, v___y_88_);
lean_ctor_set(v___x_89_, 2, v___y_82_);
lean_ctor_set(v___x_89_, 3, v___y_81_);
lean_ctor_set(v___x_89_, 4, v___y_83_);
lean_ctor_set(v___x_89_, 5, v___y_80_);
lean_ctor_set(v___x_89_, 6, v___y_86_);
lean_ctor_set(v___x_89_, 7, v___y_85_);
lean_ctor_set(v___x_89_, 8, v___y_87_);
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
v___y_81_ = v_extraInj_94_;
v___y_82_ = v_extra_93_;
v___y_83_ = v_extraFacts_95_;
v___y_84_ = v_config_91_;
v___y_85_ = v_normProcs_98_;
v___y_86_ = v_norm_97_;
v___y_87_ = v_anchorRefs_x3f_99_;
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
v___y_81_ = v_extraInj_94_;
v___y_82_ = v_extra_93_;
v___y_83_ = v_extraFacts_95_;
v___y_84_ = v_config_91_;
v___y_85_ = v_normProcs_98_;
v___y_86_ = v_norm_97_;
v___y_87_ = v_anchorRefs_x3f_99_;
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
lean_dec_ref_known(v___x_122_, 1);
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
v___x_198_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_ematch_196_, v___x_197_);
lean_dec_ref_known(v___x_197_, 1);
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
v___x_232_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_230_, v___x_231_);
lean_dec_ref_known(v___x_231_, 1);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(lean_object* v_params_306_, lean_object* v___x_307_, uint8_t v___x_308_, lean_object* v_as_309_, size_t v_i_310_, size_t v_stop_311_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = lean_usize_dec_eq(v_i_310_, v_stop_311_);
if (v___x_312_ == 0)
{
uint8_t v___x_313_; uint8_t v___y_315_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_313_ = 1;
v___x_319_ = lean_array_uget_borrowed(v_as_309_, v_i_310_);
lean_inc(v___x_319_);
v___x_320_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_306_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_nat_dec_lt(v___x_321_, v___x_307_);
v___y_315_ = v___x_322_;
goto v___jp_314_;
}
else
{
v___y_315_ = v___x_308_;
goto v___jp_314_;
}
v___jp_314_:
{
if (v___y_315_ == 0)
{
size_t v___x_316_; size_t v___x_317_; 
v___x_316_ = ((size_t)1ULL);
v___x_317_ = lean_usize_add(v_i_310_, v___x_316_);
v_i_310_ = v___x_317_;
goto _start;
}
else
{
return v___x_313_;
}
}
}
else
{
uint8_t v___x_323_; 
v___x_323_ = 0;
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1___boxed(lean_object* v_params_324_, lean_object* v___x_325_, lean_object* v___x_326_, lean_object* v_as_327_, lean_object* v_i_328_, lean_object* v_stop_329_){
_start:
{
uint8_t v___x_1641__boxed_330_; size_t v_i_boxed_331_; size_t v_stop_boxed_332_; uint8_t v_res_333_; lean_object* v_r_334_; 
v___x_1641__boxed_330_ = lean_unbox(v___x_326_);
v_i_boxed_331_ = lean_unbox_usize(v_i_328_);
lean_dec(v_i_328_);
v_stop_boxed_332_ = lean_unbox_usize(v_stop_329_);
lean_dec(v_stop_329_);
v_res_333_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_324_, v___x_325_, v___x_1641__boxed_330_, v_as_327_, v_i_boxed_331_, v_stop_boxed_332_);
lean_dec_ref(v_as_327_);
lean_dec(v___x_325_);
lean_dec_ref(v_params_324_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(lean_object* v_as_335_, size_t v_i_336_, size_t v_stop_337_, lean_object* v_b_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = lean_usize_dec_eq(v_i_336_, v_stop_337_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; 
v___x_340_ = lean_array_uget_borrowed(v_as_335_, v_i_336_);
lean_inc(v___x_340_);
v___x_341_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_b_338_, v___x_340_);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_add(v_i_336_, v___x_342_);
v_i_336_ = v___x_343_;
v_b_338_ = v___x_341_;
goto _start;
}
else
{
return v_b_338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0___boxed(lean_object* v_as_345_, lean_object* v_i_346_, lean_object* v_stop_347_, lean_object* v_b_348_){
_start:
{
size_t v_i_boxed_349_; size_t v_stop_boxed_350_; lean_object* v_res_351_; 
v_i_boxed_349_ = lean_unbox_usize(v_i_346_);
lean_dec(v_i_346_);
v_stop_boxed_350_ = lean_unbox_usize(v_stop_347_);
lean_dec(v_stop_347_);
v_res_351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_as_345_, v_i_boxed_349_, v_stop_boxed_350_, v_b_348_);
lean_dec_ref(v_as_345_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(lean_object* v_params_352_, lean_object* v_declName_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_362_; lean_object* v_env_363_; uint8_t v___x_364_; 
v___x_362_ = lean_st_ref_get(v_a_357_);
v_env_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc_ref(v_env_363_);
lean_dec(v___x_362_);
lean_inc(v_declName_353_);
v___x_364_ = l_Lean_wasOriginallyTheorem(v_env_363_, v_declName_353_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_inc(v_declName_353_);
v___x_365_ = l_Lean_Meta_getEqnsFor_x3f(v_declName_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_410_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_410_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_410_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_410_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
if (lean_obj_tag(v_a_366_) == 1)
{
lean_object* v_val_370_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_val_370_ = lean_ctor_get(v_a_366_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v_a_366_, 1);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_array_get_size(v_val_370_);
v___x_396_ = lean_nat_dec_lt(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_dec(v_declName_353_);
goto v___jp_371_;
}
else
{
if (v___x_396_ == 0)
{
lean_dec(v_declName_353_);
goto v___jp_371_;
}
else
{
size_t v___x_397_; size_t v___x_398_; uint8_t v___x_399_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_395_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_352_, v___x_395_, v___x_364_, v_val_370_, v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_dec(v_declName_353_);
goto v___jp_371_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_353_, v_a_356_, v_a_357_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_dec_ref_known(v___x_400_, 1);
goto v___jp_371_;
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_val_370_);
lean_del_object(v___x_368_);
lean_dec_ref(v_params_352_);
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
v___jp_371_:
{
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_array_get_size(v_val_370_);
v___x_374_ = lean_nat_dec_lt(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_376_; 
lean_dec(v_val_370_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v_params_352_);
v___x_376_ = v___x_368_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_params_352_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
uint8_t v___x_378_; 
v___x_378_ = lean_nat_dec_le(v___x_373_, v___x_373_);
if (v___x_378_ == 0)
{
if (v___x_374_ == 0)
{
lean_object* v___x_380_; 
lean_dec(v_val_370_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v_params_352_);
v___x_380_ = v___x_368_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_params_352_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
else
{
size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_382_ = ((size_t)0ULL);
v___x_383_ = lean_usize_of_nat(v___x_373_);
v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_370_, v___x_382_, v___x_383_, v_params_352_);
lean_dec(v_val_370_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_384_);
v___x_386_ = v___x_368_;
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
else
{
size_t v___x_388_; size_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_388_ = ((size_t)0ULL);
v___x_389_ = lean_usize_of_nat(v___x_373_);
v___x_390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__0(v_val_370_, v___x_388_, v___x_389_, v_params_352_);
lean_dec(v_val_370_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_390_);
v___x_392_ = v___x_368_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v___x_409_; 
lean_del_object(v___x_368_);
lean_dec(v_a_366_);
lean_dec_ref(v_params_352_);
v___x_409_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_353_, v_a_356_, v_a_357_);
return v___x_409_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_declName_353_);
lean_dec_ref(v_params_352_);
v_a_411_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_365_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_365_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
uint8_t v___x_419_; 
lean_inc(v_declName_353_);
v___x_419_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_352_, v_declName_353_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_inc(v_declName_353_);
v___x_420_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_353_, v_a_356_, v_a_357_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_dec_ref_known(v___x_420_, 1);
goto v___jp_359_;
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec(v_declName_353_);
lean_dec_ref(v_params_352_);
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
goto v___jp_359_;
}
}
v___jp_359_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatchCore(v_params_352_, v_declName_353_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch___boxed(lean_object* v_params_429_, lean_object* v_declName_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_params_429_, v_declName_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(lean_object* v_params_437_, lean_object* v_declName_438_){
_start:
{
lean_object* v_config_439_; lean_object* v_extensions_440_; lean_object* v_extra_441_; lean_object* v_extraInj_442_; lean_object* v_extraFacts_443_; lean_object* v_symPrios_444_; lean_object* v_norm_445_; lean_object* v_normProcs_446_; lean_object* v_anchorRefs_x3f_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_config_439_ = lean_ctor_get(v_params_437_, 0);
v_extensions_440_ = lean_ctor_get(v_params_437_, 1);
v_extra_441_ = lean_ctor_get(v_params_437_, 2);
v_extraInj_442_ = lean_ctor_get(v_params_437_, 3);
v_extraFacts_443_ = lean_ctor_get(v_params_437_, 4);
v_symPrios_444_ = lean_ctor_get(v_params_437_, 5);
v_norm_445_ = lean_ctor_get(v_params_437_, 6);
v_normProcs_446_ = lean_ctor_get(v_params_437_, 7);
v_anchorRefs_x3f_447_ = lean_ctor_get(v_params_437_, 8);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_get_size(v_extensions_440_);
v___x_450_ = lean_nat_dec_lt(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_dec(v_declName_438_);
return v_params_437_;
}
else
{
lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_475_; 
lean_inc(v_anchorRefs_x3f_447_);
lean_inc_ref(v_normProcs_446_);
lean_inc_ref(v_norm_445_);
lean_inc_ref(v_symPrios_444_);
lean_inc_ref(v_extraFacts_443_);
lean_inc_ref(v_extraInj_442_);
lean_inc_ref(v_extra_441_);
lean_inc_ref(v_extensions_440_);
lean_inc_ref(v_config_439_);
v_isSharedCheck_475_ = !lean_is_exclusive(v_params_437_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; lean_object* v_unused_480_; lean_object* v_unused_481_; lean_object* v_unused_482_; lean_object* v_unused_483_; lean_object* v_unused_484_; 
v_unused_476_ = lean_ctor_get(v_params_437_, 8);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_params_437_, 7);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_params_437_, 6);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_params_437_, 5);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_params_437_, 4);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_params_437_, 3);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v_params_437_, 2);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v_params_437_, 1);
lean_dec(v_unused_483_);
v_unused_484_ = lean_ctor_get(v_params_437_, 0);
lean_dec(v_unused_484_);
v___x_452_ = v_params_437_;
v_isShared_453_ = v_isSharedCheck_475_;
goto v_resetjp_451_;
}
else
{
lean_dec(v_params_437_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_475_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_v_454_; lean_object* v_casesTypes_455_; lean_object* v_extThms_456_; lean_object* v_funCC_457_; lean_object* v_ematch_458_; lean_object* v_inj_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_474_; 
v_v_454_ = lean_array_fget(v_extensions_440_, v___x_448_);
v_casesTypes_455_ = lean_ctor_get(v_v_454_, 0);
v_extThms_456_ = lean_ctor_get(v_v_454_, 1);
v_funCC_457_ = lean_ctor_get(v_v_454_, 2);
v_ematch_458_ = lean_ctor_get(v_v_454_, 3);
v_inj_459_ = lean_ctor_get(v_v_454_, 4);
v_isSharedCheck_474_ = !lean_is_exclusive(v_v_454_);
if (v_isSharedCheck_474_ == 0)
{
v___x_461_ = v_v_454_;
v_isShared_462_ = v_isSharedCheck_474_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_inj_459_);
lean_inc(v_ematch_458_);
lean_inc(v_funCC_457_);
lean_inc(v_extThms_456_);
lean_inc(v_casesTypes_455_);
lean_dec(v_v_454_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_474_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v_xs_x27_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_463_ = lean_box(0);
v_xs_x27_464_ = lean_array_fset(v_extensions_440_, v___x_448_, v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v_declName_438_);
v___x_466_ = l_Lean_Meta_Grind_Theorems_erase___redArg(v_inj_459_, v___x_465_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 4, v___x_466_);
v___x_468_ = v___x_461_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_casesTypes_455_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_extThms_456_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_funCC_457_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_ematch_458_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v___x_466_);
v___x_468_ = v_reuseFailAlloc_473_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_469_ = lean_array_fset(v_xs_x27_464_, v___x_448_, v___x_468_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_469_);
v___x_471_ = v___x_452_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_config_439_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_extra_441_);
lean_ctor_set(v_reuseFailAlloc_472_, 3, v_extraInj_442_);
lean_ctor_set(v_reuseFailAlloc_472_, 4, v_extraFacts_443_);
lean_ctor_set(v_reuseFailAlloc_472_, 5, v_symPrios_444_);
lean_ctor_set(v_reuseFailAlloc_472_, 6, v_norm_445_);
lean_ctor_set(v_reuseFailAlloc_472_, 7, v_normProcs_446_);
lean_ctor_set(v_reuseFailAlloc_472_, 8, v_anchorRefs_x3f_447_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(lean_object* v_origin_485_, lean_object* v_as_486_, size_t v_sz_487_, size_t v_i_488_, lean_object* v_b_489_){
_start:
{
lean_object* v_a_491_; uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_lt(v_i_488_, v_sz_487_);
if (v___x_495_ == 0)
{
return v_b_489_;
}
else
{
lean_object* v_a_496_; lean_object* v_ematch_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_a_496_ = lean_array_uget_borrowed(v_as_486_, v_i_488_);
v_ematch_497_ = lean_ctor_get(v_a_496_, 3);
v___x_498_ = l_Lean_Meta_Grind_EMatchTheorems_getKindsFor(v_ematch_497_, v_origin_485_);
v___x_499_ = l_List_isEmpty___redArg(v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
v___x_500_ = l_List_appendTR___redArg(v_b_489_, v___x_498_);
v_a_491_ = v___x_500_;
goto v___jp_490_;
}
else
{
lean_dec(v___x_498_);
v_a_491_ = v_b_489_;
goto v___jp_490_;
}
}
v___jp_490_:
{
size_t v___x_492_; size_t v___x_493_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_488_, v___x_492_);
v_i_488_ = v___x_493_;
v_b_489_ = v_a_491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0___boxed(lean_object* v_origin_501_, lean_object* v_as_502_, lean_object* v_sz_503_, lean_object* v_i_504_, lean_object* v_b_505_){
_start:
{
size_t v_sz_boxed_506_; size_t v_i_boxed_507_; lean_object* v_res_508_; 
v_sz_boxed_506_ = lean_unbox_usize(v_sz_503_);
lean_dec(v_sz_503_);
v_i_boxed_507_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_501_, v_as_502_, v_sz_boxed_506_, v_i_boxed_507_, v_b_505_);
lean_dec_ref(v_as_502_);
lean_dec_ref(v_origin_501_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(lean_object* v_s_509_, lean_object* v_origin_510_){
_start:
{
lean_object* v_result_511_; size_t v_sz_512_; size_t v___x_513_; lean_object* v___x_514_; 
v_result_511_ = lean_box(0);
v_sz_512_ = lean_array_size(v_s_509_);
v___x_513_ = ((size_t)0ULL);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor_spec__0(v_origin_510_, v_s_509_, v_sz_512_, v___x_513_, v_result_511_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor___boxed(lean_object* v_s_515_, lean_object* v_origin_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_515_, v_origin_516_);
lean_dec_ref(v_origin_516_);
lean_dec_ref(v_s_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(lean_object* v_upperBound_518_, lean_object* v_s_519_, lean_object* v_origin_520_, lean_object* v_a_521_, lean_object* v_b_522_){
_start:
{
lean_object* v_a_524_; uint8_t v___x_528_; 
v___x_528_ = lean_nat_dec_lt(v_a_521_, v_upperBound_518_);
if (v___x_528_ == 0)
{
lean_dec(v_a_521_);
return v_b_522_;
}
else
{
lean_object* v___x_529_; lean_object* v_ematch_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_529_ = lean_array_fget_borrowed(v_s_519_, v_a_521_);
v_ematch_530_ = lean_ctor_get(v___x_529_, 3);
v___x_531_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_ematch_530_, v_origin_520_);
v___x_532_ = l_List_isEmpty___redArg(v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; 
v___x_533_ = l_List_appendTR___redArg(v_b_522_, v___x_531_);
v_a_524_ = v___x_533_;
goto v___jp_523_;
}
else
{
lean_dec(v___x_531_);
v_a_524_ = v_b_522_;
goto v___jp_523_;
}
}
v___jp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_a_521_, v___x_525_);
lean_dec(v_a_521_);
v_a_521_ = v___x_526_;
v_b_522_ = v_a_524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg___boxed(lean_object* v_upperBound_534_, lean_object* v_s_535_, lean_object* v_origin_536_, lean_object* v_a_537_, lean_object* v_b_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_534_, v_s_535_, v_origin_536_, v_a_537_, v_b_538_);
lean_dec_ref(v_origin_536_);
lean_dec_ref(v_s_535_);
lean_dec(v_upperBound_534_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find(lean_object* v_s_540_, lean_object* v_origin_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_r_544_; lean_object* v___x_545_; 
v___x_542_ = lean_array_get_size(v_s_540_);
v___x_543_ = lean_unsigned_to_nat(0u);
v_r_544_ = lean_box(0);
v___x_545_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v___x_542_, v_s_540_, v_origin_541_, v___x_543_, v_r_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionStateArray_find___boxed(lean_object* v_s_546_, lean_object* v_origin_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Meta_Grind_ExtensionStateArray_find(v_s_546_, v_origin_547_);
lean_dec_ref(v_origin_547_);
lean_dec_ref(v_s_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(lean_object* v_upperBound_549_, lean_object* v_s_550_, lean_object* v_origin_551_, lean_object* v_inst_552_, lean_object* v_R_553_, lean_object* v_a_554_, lean_object* v_b_555_, lean_object* v_c_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___redArg(v_upperBound_549_, v_s_550_, v_origin_551_, v_a_554_, v_b_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0___boxed(lean_object* v_upperBound_558_, lean_object* v_s_559_, lean_object* v_origin_560_, lean_object* v_inst_561_, lean_object* v_R_562_, lean_object* v_a_563_, lean_object* v_b_564_, lean_object* v_c_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_ExtensionStateArray_find_spec__0(v_upperBound_558_, v_s_559_, v_origin_560_, v_inst_561_, v_R_562_, v_a_563_, v_b_564_, v_c_565_);
lean_dec_ref(v_origin_560_);
lean_dec_ref(v_s_559_);
lean_dec(v_upperBound_558_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(lean_object* v_msgData_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; lean_object* v_env_574_; lean_object* v___x_575_; lean_object* v_mctx_576_; lean_object* v_lctx_577_; lean_object* v_options_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_573_ = lean_st_ref_get(v___y_571_);
v_env_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_env_574_);
lean_dec(v___x_573_);
v___x_575_ = lean_st_ref_get(v___y_569_);
v_mctx_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_mctx_576_);
lean_dec(v___x_575_);
v_lctx_577_ = lean_ctor_get(v___y_568_, 2);
v_options_578_ = lean_ctor_get(v___y_570_, 1);
lean_inc_ref(v_options_578_);
lean_inc_ref(v_lctx_577_);
v___x_579_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_579_, 0, v_env_574_);
lean_ctor_set(v___x_579_, 1, v_mctx_576_);
lean_ctor_set(v___x_579_, 2, v_lctx_577_);
lean_ctor_set(v___x_579_, 3, v_options_578_);
v___x_580_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_msgData_567_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msgData_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_588_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_589_, lean_object* v_opt_590_){
_start:
{
lean_object* v_name_591_; lean_object* v_defValue_592_; lean_object* v_map_593_; lean_object* v___x_594_; 
v_name_591_ = lean_ctor_get(v_opt_590_, 0);
v_defValue_592_ = lean_ctor_get(v_opt_590_, 1);
v_map_593_ = lean_ctor_get(v_opts_589_, 0);
v___x_594_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_593_, v_name_591_);
if (lean_obj_tag(v___x_594_) == 0)
{
uint8_t v___x_595_; 
v___x_595_ = lean_unbox(v_defValue_592_);
return v___x_595_;
}
else
{
lean_object* v_val_596_; 
v_val_596_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v___x_594_, 1);
if (lean_obj_tag(v_val_596_) == 1)
{
uint8_t v_v_597_; 
v_v_597_ = lean_ctor_get_uint8(v_val_596_, 0);
lean_dec_ref_known(v_val_596_, 0);
return v_v_597_;
}
else
{
uint8_t v___x_598_; 
lean_dec(v_val_596_);
v___x_598_ = lean_unbox(v_defValue_592_);
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_599_, lean_object* v_opt_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_opts_599_, v_opt_600_);
lean_dec_ref(v_opt_600_);
lean_dec_ref(v_opts_599_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_611_, uint8_t v___y_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_613_) == 1)
{
lean_object* v_pre_614_; 
v_pre_614_ = lean_ctor_get(v_x_613_, 0);
switch(lean_obj_tag(v_pre_614_))
{
case 1:
{
lean_object* v_pre_615_; 
v_pre_615_ = lean_ctor_get(v_pre_614_, 0);
switch(lean_obj_tag(v_pre_615_))
{
case 0:
{
lean_object* v_str_616_; lean_object* v_str_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_str_616_ = lean_ctor_get(v_x_613_, 1);
v_str_617_ = lean_ctor_get(v_pre_614_, 1);
v___x_618_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_619_ = lean_string_dec_eq(v_str_617_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_621_ = lean_string_dec_eq(v_str_617_, v___x_620_);
if (v___x_621_ == 0)
{
return v___x_621_;
}
else
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_623_ = lean_string_dec_eq(v_str_616_, v___x_622_);
if (v___x_623_ == 0)
{
return v___x_623_;
}
else
{
return v_suppressElabErrors_611_;
}
}
}
else
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_625_ = lean_string_dec_eq(v_str_616_, v___x_624_);
if (v___x_625_ == 0)
{
return v___x_625_;
}
else
{
return v_suppressElabErrors_611_;
}
}
}
case 1:
{
lean_object* v_pre_626_; 
v_pre_626_ = lean_ctor_get(v_pre_615_, 0);
if (lean_obj_tag(v_pre_626_) == 0)
{
lean_object* v_str_627_; lean_object* v_str_628_; lean_object* v_str_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_str_627_ = lean_ctor_get(v_x_613_, 1);
v_str_628_ = lean_ctor_get(v_pre_614_, 1);
v_str_629_ = lean_ctor_get(v_pre_615_, 1);
v___x_630_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_631_ = lean_string_dec_eq(v_str_629_, v___x_630_);
if (v___x_631_ == 0)
{
return v___x_631_;
}
else
{
lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_633_ = lean_string_dec_eq(v_str_628_, v___x_632_);
if (v___x_633_ == 0)
{
return v___x_633_;
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_635_ = lean_string_dec_eq(v_str_627_, v___x_634_);
if (v___x_635_ == 0)
{
return v___x_635_;
}
else
{
return v_suppressElabErrors_611_;
}
}
}
}
else
{
return v___y_612_;
}
}
default: 
{
return v___y_612_;
}
}
}
case 0:
{
lean_object* v_str_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_str_636_ = lean_ctor_get(v_x_613_, 1);
v___x_637_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_638_ = lean_string_dec_eq(v_str_636_, v___x_637_);
if (v___x_638_ == 0)
{
return v___x_638_;
}
else
{
return v_suppressElabErrors_611_;
}
}
default: 
{
return v___y_612_;
}
}
}
else
{
return v___y_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_639_, lean_object* v___y_640_, lean_object* v_x_641_){
_start:
{
uint8_t v_suppressElabErrors_boxed_642_; uint8_t v___y_4451__boxed_643_; uint8_t v_res_644_; lean_object* v_r_645_; 
v_suppressElabErrors_boxed_642_ = lean_unbox(v_suppressElabErrors_639_);
v___y_4451__boxed_643_ = lean_unbox(v___y_640_);
v_res_644_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_642_, v___y_4451__boxed_643_, v_x_641_);
lean_dec(v_x_641_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_647_, lean_object* v_msgData_648_, uint8_t v_severity_649_, uint8_t v_isSilent_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; uint8_t v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; uint8_t v___y_696_; uint8_t v___y_697_; uint8_t v___y_698_; lean_object* v___y_699_; lean_object* v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; uint8_t v___y_722_; lean_object* v___y_723_; uint8_t v___y_724_; lean_object* v___y_725_; lean_object* v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; lean_object* v___y_732_; uint8_t v___y_733_; uint8_t v___y_734_; uint8_t v___x_739_; lean_object* v___y_741_; lean_object* v___y_742_; uint8_t v___y_743_; lean_object* v___y_744_; uint8_t v___y_745_; uint8_t v___y_746_; uint8_t v___y_748_; uint8_t v___x_762_; 
v___x_739_ = 2;
v___x_762_ = l_Lean_instBEqMessageSeverity_beq(v_severity_649_, v___x_739_);
if (v___x_762_ == 0)
{
v___y_748_ = v___x_762_;
goto v___jp_747_;
}
else
{
uint8_t v___x_763_; 
lean_inc_ref(v_msgData_648_);
v___x_763_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_648_);
v___y_748_ = v___x_763_;
goto v___jp_747_;
}
v___jp_656_:
{
lean_object* v___x_666_; lean_object* v_currNamespace_667_; lean_object* v_openDecls_668_; lean_object* v_env_669_; lean_object* v_nextMacroScope_670_; lean_object* v_ngen_671_; lean_object* v_auxDeclNGen_672_; lean_object* v_traceState_673_; lean_object* v_cache_674_; lean_object* v_messages_675_; lean_object* v_infoState_676_; lean_object* v_snapshotTasks_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_691_; 
v___x_666_ = lean_st_ref_take(v___y_665_);
v_currNamespace_667_ = lean_ctor_get(v___y_664_, 5);
v_openDecls_668_ = lean_ctor_get(v___y_664_, 6);
v_env_669_ = lean_ctor_get(v___x_666_, 0);
v_nextMacroScope_670_ = lean_ctor_get(v___x_666_, 1);
v_ngen_671_ = lean_ctor_get(v___x_666_, 2);
v_auxDeclNGen_672_ = lean_ctor_get(v___x_666_, 3);
v_traceState_673_ = lean_ctor_get(v___x_666_, 4);
v_cache_674_ = lean_ctor_get(v___x_666_, 5);
v_messages_675_ = lean_ctor_get(v___x_666_, 6);
v_infoState_676_ = lean_ctor_get(v___x_666_, 7);
v_snapshotTasks_677_ = lean_ctor_get(v___x_666_, 8);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_691_ == 0)
{
v___x_679_ = v___x_666_;
v_isShared_680_ = v_isSharedCheck_691_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_snapshotTasks_677_);
lean_inc(v_infoState_676_);
lean_inc(v_messages_675_);
lean_inc(v_cache_674_);
lean_inc(v_traceState_673_);
lean_inc(v_auxDeclNGen_672_);
lean_inc(v_ngen_671_);
lean_inc(v_nextMacroScope_670_);
lean_inc(v_env_669_);
lean_dec(v___x_666_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_691_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
lean_inc(v_openDecls_668_);
lean_inc(v_currNamespace_667_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_currNamespace_667_);
lean_ctor_set(v___x_681_, 1, v_openDecls_668_);
v___x_682_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___y_658_);
lean_inc_ref(v___y_662_);
lean_inc_ref(v___y_657_);
v___x_683_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_683_, 0, v___y_657_);
lean_ctor_set(v___x_683_, 1, v___y_659_);
lean_ctor_set(v___x_683_, 2, v___y_663_);
lean_ctor_set(v___x_683_, 3, v___y_662_);
lean_ctor_set(v___x_683_, 4, v___x_682_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*5, v___y_660_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*5 + 1, v___y_661_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*5 + 2, v_isSilent_650_);
v___x_684_ = l_Lean_MessageLog_add(v___x_683_, v_messages_675_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 6, v___x_684_);
v___x_686_ = v___x_679_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_env_669_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_nextMacroScope_670_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_ngen_671_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_auxDeclNGen_672_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v_traceState_673_);
lean_ctor_set(v_reuseFailAlloc_690_, 5, v_cache_674_);
lean_ctor_set(v_reuseFailAlloc_690_, 6, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_690_, 7, v_infoState_676_);
lean_ctor_set(v_reuseFailAlloc_690_, 8, v_snapshotTasks_677_);
v___x_686_ = v_reuseFailAlloc_690_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_st_ref_put(v___y_665_, v___x_686_);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
}
v___jp_692_:
{
lean_object* v_fileName_700_; lean_object* v_fileMap_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_717_; 
v_fileName_700_ = lean_ctor_get(v___y_695_, 0);
v_fileMap_701_ = lean_ctor_get(v___y_695_, 1);
v___x_702_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_648_);
v___x_703_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_702_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_717_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_717_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_717_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_inc_ref_n(v_fileMap_701_, 2);
v___x_708_ = l_Lean_FileMap_toPosition(v_fileMap_701_, v___y_694_);
lean_dec(v___y_694_);
v___x_709_ = l_Lean_FileMap_toPosition(v_fileMap_701_, v___y_699_);
lean_dec(v___y_699_);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
v___x_711_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_696_ == 0)
{
lean_del_object(v___x_706_);
lean_dec_ref(v___y_693_);
v___y_657_ = v_fileName_700_;
v___y_658_ = v_a_704_;
v___y_659_ = v___x_708_;
v___y_660_ = v___y_697_;
v___y_661_ = v___y_698_;
v___y_662_ = v___x_711_;
v___y_663_ = v___x_710_;
v___y_664_ = v___y_653_;
v___y_665_ = v___y_654_;
goto v___jp_656_;
}
else
{
uint8_t v___x_712_; 
lean_inc(v_a_704_);
v___x_712_ = l_Lean_MessageData_hasTag(v___y_693_, v_a_704_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_715_; 
lean_dec_ref_known(v___x_710_, 1);
lean_dec_ref(v___x_708_);
lean_dec(v_a_704_);
v___x_713_ = lean_box(0);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_713_);
v___x_715_ = v___x_706_;
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
lean_del_object(v___x_706_);
v___y_657_ = v_fileName_700_;
v___y_658_ = v_a_704_;
v___y_659_ = v___x_708_;
v___y_660_ = v___y_697_;
v___y_661_ = v___y_698_;
v___y_662_ = v___x_711_;
v___y_663_ = v___x_710_;
v___y_664_ = v___y_653_;
v___y_665_ = v___y_654_;
goto v___jp_656_;
}
}
}
}
v___jp_718_:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Syntax_getTailPos_x3f(v___y_723_, v___y_722_);
lean_dec(v___y_723_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_inc(v___y_725_);
v___y_693_ = v___y_719_;
v___y_694_ = v___y_725_;
v___y_695_ = v___y_720_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_722_;
v___y_698_ = v___y_724_;
v___y_699_ = v___y_725_;
goto v___jp_692_;
}
else
{
lean_object* v_val_727_; 
v_val_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_val_727_);
lean_dec_ref_known(v___x_726_, 1);
v___y_693_ = v___y_719_;
v___y_694_ = v___y_725_;
v___y_695_ = v___y_720_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_722_;
v___y_698_ = v___y_724_;
v___y_699_ = v_val_727_;
goto v___jp_692_;
}
}
v___jp_728_:
{
lean_object* v_ref_735_; lean_object* v___x_736_; 
v_ref_735_ = l_Lean_replaceRef(v_ref_647_, v___y_732_);
v___x_736_ = l_Lean_Syntax_getPos_x3f(v_ref_735_, v___y_733_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; 
v___x_737_ = lean_unsigned_to_nat(0u);
v___y_719_ = v___y_729_;
v___y_720_ = v___y_730_;
v___y_721_ = v___y_731_;
v___y_722_ = v___y_733_;
v___y_723_ = v_ref_735_;
v___y_724_ = v___y_734_;
v___y_725_ = v___x_737_;
goto v___jp_718_;
}
else
{
lean_object* v_val_738_; 
v_val_738_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v___x_736_, 1);
v___y_719_ = v___y_729_;
v___y_720_ = v___y_730_;
v___y_721_ = v___y_731_;
v___y_722_ = v___y_733_;
v___y_723_ = v_ref_735_;
v___y_724_ = v___y_734_;
v___y_725_ = v_val_738_;
goto v___jp_718_;
}
}
v___jp_740_:
{
if (v___y_746_ == 0)
{
v___y_729_ = v___y_741_;
v___y_730_ = v___y_742_;
v___y_731_ = v___y_743_;
v___y_732_ = v___y_744_;
v___y_733_ = v___y_745_;
v___y_734_ = v_severity_649_;
goto v___jp_728_;
}
else
{
v___y_729_ = v___y_741_;
v___y_730_ = v___y_742_;
v___y_731_ = v___y_743_;
v___y_732_ = v___y_744_;
v___y_733_ = v___y_745_;
v___y_734_ = v___x_739_;
goto v___jp_728_;
}
}
v___jp_747_:
{
if (v___y_748_ == 0)
{
lean_object* v_toCold_749_; lean_object* v_options_750_; lean_object* v_ref_751_; uint8_t v_suppressElabErrors_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___f_755_; uint8_t v___x_756_; uint8_t v___x_757_; 
v_toCold_749_ = lean_ctor_get(v___y_653_, 0);
v_options_750_ = lean_ctor_get(v___y_653_, 1);
v_ref_751_ = lean_ctor_get(v___y_653_, 4);
v_suppressElabErrors_752_ = lean_ctor_get_uint8(v___y_653_, sizeof(void*)*10 + 1);
v___x_753_ = lean_box(v_suppressElabErrors_752_);
v___x_754_ = lean_box(v___y_748_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_755_, 0, v___x_753_);
lean_closure_set(v___f_755_, 1, v___x_754_);
v___x_756_ = 1;
v___x_757_ = l_Lean_instBEqMessageSeverity_beq(v_severity_649_, v___x_756_);
if (v___x_757_ == 0)
{
v___y_741_ = v___f_755_;
v___y_742_ = v_toCold_749_;
v___y_743_ = v_suppressElabErrors_752_;
v___y_744_ = v_ref_751_;
v___y_745_ = v___y_748_;
v___y_746_ = v___x_757_;
goto v___jp_740_;
}
else
{
lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = l_Lean_warningAsError;
v___x_759_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_750_, v___x_758_);
v___y_741_ = v___f_755_;
v___y_742_ = v_toCold_749_;
v___y_743_ = v_suppressElabErrors_752_;
v___y_744_ = v_ref_751_;
v___y_745_ = v___y_748_;
v___y_746_ = v___x_759_;
goto v___jp_740_;
}
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec_ref(v_msgData_648_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_764_, lean_object* v_msgData_765_, lean_object* v_severity_766_, lean_object* v_isSilent_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
uint8_t v_severity_boxed_773_; uint8_t v_isSilent_boxed_774_; lean_object* v_res_775_; 
v_severity_boxed_773_ = lean_unbox(v_severity_766_);
v_isSilent_boxed_774_ = lean_unbox(v_isSilent_767_);
v_res_775_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_764_, v_msgData_765_, v_severity_boxed_773_, v_isSilent_boxed_774_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v_ref_764_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_776_, uint8_t v_severity_777_, uint8_t v_isSilent_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_ref_784_; lean_object* v___x_785_; 
v_ref_784_ = lean_ctor_get(v___y_781_, 4);
v___x_785_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_784_, v_msgData_776_, v_severity_777_, v_isSilent_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_786_, lean_object* v_severity_787_, lean_object* v_isSilent_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v_severity_boxed_794_; uint8_t v_isSilent_boxed_795_; lean_object* v_res_796_; 
v_severity_boxed_794_ = lean_unbox(v_severity_787_);
v_isSilent_boxed_795_ = lean_unbox(v_isSilent_788_);
v_res_796_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_786_, v_severity_boxed_794_, v_isSilent_boxed_795_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
uint8_t v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; 
v___x_803_ = 1;
v___x_804_ = 0;
v___x_805_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_797_, v___x_803_, v___x_804_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
return v_res_812_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
if (lean_obj_tag(v_a_816_) == 0)
{
lean_object* v___x_818_; 
v___x_818_ = l_List_reverse___redArg(v_a_817_);
return v___x_818_;
}
else
{
lean_object* v_head_819_; lean_object* v_tail_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_833_; 
v_head_819_ = lean_ctor_get(v_a_816_, 0);
v_tail_820_ = lean_ctor_get(v_a_816_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_a_816_);
if (v_isSharedCheck_833_ == 0)
{
v___x_822_ = v_a_816_;
v_isShared_823_ = v_isSharedCheck_833_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_tail_820_);
lean_inc(v_head_819_);
lean_dec(v_a_816_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_833_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v_minIndexable_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v_minIndexable_824_ = 0;
v___x_825_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_826_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_819_, v_minIndexable_824_);
lean_dec(v_head_819_);
v___x_827_ = l_Lean_stringToMessageData(v___x_826_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_825_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v_a_817_);
lean_ctor_set(v___x_822_, 0, v___x_828_);
v___x_830_ = v___x_822_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_a_817_);
v___x_830_ = v_reuseFailAlloc_832_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
v_a_816_ = v_tail_820_;
v_a_817_ = v___x_830_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
if (lean_obj_tag(v_a_834_) == 0)
{
lean_object* v___x_836_; 
v___x_836_ = l_List_reverse___redArg(v_a_835_);
return v___x_836_;
}
else
{
lean_object* v_head_837_; lean_object* v_tail_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_846_; 
v_head_837_ = lean_ctor_get(v_a_834_, 0);
v_tail_838_ = lean_ctor_get(v_a_834_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_a_834_);
if (v_isSharedCheck_846_ == 0)
{
v___x_840_ = v_a_834_;
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_tail_838_);
lean_inc(v_head_837_);
lean_dec(v_a_834_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v_a_835_);
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_head_837_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_a_835_);
v___x_843_ = v_reuseFailAlloc_845_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
v_a_834_ = v_tail_838_;
v_a_835_ = v___x_843_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_856_, lean_object* v_declName_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_kinds_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v_ks_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_inc(v_declName_857_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v_declName_857_);
v___x_889_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_856_, v___x_888_);
lean_dec_ref_known(v___x_888_, 1);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_declName_857_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
else
{
lean_object* v_head_892_; lean_object* v_tail_893_; uint8_t v_minIndexable_894_; uint8_t v_gen_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; 
v_head_892_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_head_892_);
v_tail_893_ = lean_ctor_get(v___x_889_, 1);
lean_inc(v_tail_893_);
v_minIndexable_894_ = 0;
if (lean_obj_tag(v_tail_893_) == 0)
{
lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_915_; 
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; lean_object* v_unused_917_; 
v_unused_916_ = lean_ctor_get(v___x_889_, 1);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v___x_889_, 0);
lean_dec(v_unused_917_);
v___x_907_ = v___x_889_;
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
else
{
lean_dec(v___x_889_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_909_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_910_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_892_, v_minIndexable_894_);
lean_dec(v_head_892_);
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
if (v_isShared_908_ == 0)
{
lean_ctor_set_tag(v___x_907_, 7);
lean_ctor_set(v___x_907_, 1, v___x_911_);
lean_ctor_set(v___x_907_, 0, v___x_909_);
v___x_913_ = v___x_907_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
v_kinds_864_ = v___x_913_;
v___y_865_ = v_a_858_;
v___y_866_ = v_a_859_;
v___y_867_ = v_a_860_;
v___y_868_ = v_a_861_;
goto v___jp_863_;
}
}
}
else
{
lean_object* v_head_918_; 
v_head_918_ = lean_ctor_get(v_tail_893_, 0);
switch(lean_obj_tag(v_head_918_))
{
case 1:
{
lean_object* v_tail_919_; 
v_tail_919_ = lean_ctor_get(v_tail_893_, 1);
lean_inc(v_tail_919_);
lean_dec_ref_known(v_tail_893_, 2);
if (lean_obj_tag(v_tail_919_) == 0)
{
if (lean_obj_tag(v_head_892_) == 0)
{
uint8_t v_gen_920_; 
lean_dec_ref_known(v___x_889_, 2);
v_gen_920_ = lean_ctor_get_uint8(v_head_892_, 0);
lean_dec_ref_known(v_head_892_, 0);
v_gen_896_ = v_gen_920_;
v___y_897_ = v_a_858_;
v___y_898_ = v_a_859_;
v___y_899_ = v_a_860_;
v___y_900_ = v_a_861_;
goto v___jp_895_;
}
else
{
lean_dec(v_head_892_);
v_ks_879_ = v___x_889_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
v___y_882_ = v_a_860_;
v___y_883_ = v_a_861_;
goto v___jp_878_;
}
}
else
{
lean_dec(v_tail_919_);
lean_dec(v_head_892_);
v_ks_879_ = v___x_889_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
v___y_882_ = v_a_860_;
v___y_883_ = v_a_861_;
goto v___jp_878_;
}
}
case 0:
{
lean_object* v_tail_921_; 
v_tail_921_ = lean_ctor_get(v_tail_893_, 1);
lean_inc(v_tail_921_);
lean_dec_ref_known(v_tail_893_, 2);
if (lean_obj_tag(v_tail_921_) == 0)
{
if (lean_obj_tag(v_head_892_) == 1)
{
uint8_t v_gen_922_; 
lean_dec_ref_known(v___x_889_, 2);
v_gen_922_ = lean_ctor_get_uint8(v_head_892_, 0);
lean_dec_ref_known(v_head_892_, 0);
v_gen_896_ = v_gen_922_;
v___y_897_ = v_a_858_;
v___y_898_ = v_a_859_;
v___y_899_ = v_a_860_;
v___y_900_ = v_a_861_;
goto v___jp_895_;
}
else
{
lean_dec(v_head_892_);
v_ks_879_ = v___x_889_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
v___y_882_ = v_a_860_;
v___y_883_ = v_a_861_;
goto v___jp_878_;
}
}
else
{
lean_dec(v_tail_921_);
lean_dec(v_head_892_);
v_ks_879_ = v___x_889_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
v___y_882_ = v_a_860_;
v___y_883_ = v_a_861_;
goto v___jp_878_;
}
}
default: 
{
lean_dec_ref_known(v_tail_893_, 2);
lean_dec(v_head_892_);
v_ks_879_ = v___x_889_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
v___y_882_ = v_a_860_;
v___y_883_ = v_a_861_;
goto v___jp_878_;
}
}
}
v___jp_895_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_901_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_902_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_902_, 0, v_gen_896_);
v___x_903_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_902_, v_minIndexable_894_);
lean_dec_ref_known(v___x_902_, 0);
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_901_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v_kinds_864_ = v___x_905_;
v___y_865_ = v___y_897_;
v___y_866_ = v___y_898_;
v___y_867_ = v___y_899_;
v___y_868_ = v___y_900_;
goto v___jp_863_;
}
}
v___jp_863_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_869_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_870_ = l_Lean_MessageData_ofName(v_declName_857_);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v_kinds_864_);
v___x_875_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_876_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_877_;
}
v___jp_878_:
{
lean_object* v___x_884_; lean_object* v_ks_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_884_ = lean_box(0);
v_ks_885_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_879_, v___x_884_);
v___x_886_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_885_, v___x_884_);
v___x_887_ = l_Lean_MessageData_ofList(v___x_886_);
v_kinds_864_ = v___x_887_;
v___y_865_ = v___y_880_;
v___y_866_ = v___y_881_;
v___y_867_ = v___y_882_;
v___y_868_ = v___y_883_;
goto v___jp_863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_923_, lean_object* v_declName_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_923_, v_declName_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec_ref(v_s_923_);
return v_res_930_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_931_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
lean_ctor_set(v___x_936_, 2, v___x_935_);
lean_ctor_set(v___x_936_, 3, v___x_935_);
lean_ctor_set(v___x_936_, 4, v___x_934_);
lean_ctor_set(v___x_936_, 5, v___x_934_);
lean_ctor_set(v___x_936_, 6, v___x_934_);
lean_ctor_set(v___x_936_, 7, v___x_934_);
lean_ctor_set(v___x_936_, 8, v___x_934_);
lean_ctor_set(v___x_936_, 9, v___x_934_);
lean_ctor_set(v___x_936_, 10, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_unsigned_to_nat(32u);
v___x_938_ = lean_mk_empty_array_with_capacity(v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_940_ = ((size_t)5ULL);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_unsigned_to_nat(32u);
v___x_943_ = lean_mk_empty_array_with_capacity(v___x_942_);
v___x_944_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_945_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_943_);
lean_ctor_set(v___x_945_, 2, v___x_941_);
lean_ctor_set(v___x_945_, 3, v___x_941_);
lean_ctor_set_usize(v___x_945_, 4, v___x_940_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_946_ = lean_box(1);
v___x_947_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_948_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
lean_ctor_set(v___x_949_, 2, v___x_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; lean_object* v_env_955_; lean_object* v_options_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_954_ = lean_st_ref_get(v___y_952_);
v_env_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc_ref(v_env_955_);
lean_dec(v___x_954_);
v_options_956_ = lean_ctor_get(v___y_951_, 1);
v___x_957_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_958_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_956_);
v___x_959_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_959_, 0, v_env_955_);
lean_ctor_set(v___x_959_, 1, v___x_957_);
lean_ctor_set(v___x_959_, 2, v___x_958_);
lean_ctor_set(v___x_959_, 3, v_options_956_);
v___x_960_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v_msgData_950_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* v_msgData_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_ref_971_; lean_object* v___x_972_; lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
v_ref_971_ = lean_ctor_get(v___y_968_, 4);
v___x_972_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msg_967_, v___y_968_, v___y_969_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_981_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
lean_inc(v_ref_971_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v_ref_971_);
lean_ctor_set(v___x_977_, 1, v_a_973_);
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 1);
lean_ctor_set(v___x_975_, 0, v___x_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* v_msg_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
return v_res_986_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* v_s_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v_env_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1004_ = lean_st_ref_get(v_a_1002_);
v_env_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc_ref(v_env_1005_);
lean_dec(v___x_1004_);
v___x_1006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
v___x_1007_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(v_s_1000_);
v___x_1008_ = l_Lean_Parser_runParserCategory(v_env_1005_, v___x_1006_, v_s_1000_, v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 1)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; 
lean_dec_ref(v_s_1000_);
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = l_Lean_Meta_Grind_getAttrKindCore(v_a_1009_, v_a_1001_, v_a_1002_);
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
lean_dec_ref(v___x_1008_);
v___x_1011_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
v___x_1012_ = l_Lean_stringToMessageData(v_s_1000_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1013_, v_a_1001_, v_a_1002_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* v_s_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* v_00_u03b1_1020_, lean_object* v_msg_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_1021_, v___y_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_msg_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(v_00_u03b1_1026_, v_msg_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_ref_1038_; lean_object* v___x_1039_; lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1048_; 
v_ref_1038_ = lean_ctor_get(v___y_1035_, 4);
v___x_1039_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
lean_inc(v_ref_1038_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_ref_1038_);
lean_ctor_set(v___x_1044_, 1, v_a_1040_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 1);
lean_ctor_set(v___x_1042_, 0, v___x_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* v_msg_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1055_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t v_minIndexable_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
if (v_minIndexable_1059_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
v___x_1068_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1067_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* v_minIndexable_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
uint8_t v_minIndexable_boxed_1075_; lean_object* v_res_1076_; 
v_minIndexable_boxed_1075_ = lean_unbox(v_minIndexable_1069_);
v_res_1076_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_boxed_1075_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* v_00_u03b1_1077_, lean_object* v_msg_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* v_00_u03b1_1085_, lean_object* v_msg_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(v_00_u03b1_1085_, v_msg_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1114_, lean_object* v_declHint_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v_env_1119_; uint8_t v___x_1120_; 
v___x_1118_ = lean_st_ref_get(v___y_1116_);
v_env_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref(v_env_1119_);
lean_dec(v___x_1118_);
v___x_1120_ = l_Lean_Name_isAnonymous(v_declHint_1115_);
if (v___x_1120_ == 0)
{
uint8_t v_isExporting_1121_; 
v_isExporting_1121_ = lean_ctor_get_uint8(v_env_1119_, sizeof(void*)*8);
if (v_isExporting_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v_env_1119_);
lean_dec(v_declHint_1115_);
v___x_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1122_, 0, v_msg_1114_);
return v___x_1122_;
}
else
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
lean_inc_ref(v_env_1119_);
v___x_1123_ = l_Lean_Environment_setExporting(v_env_1119_, v___x_1120_);
lean_inc(v_declHint_1115_);
lean_inc_ref(v___x_1123_);
v___x_1124_ = l_Lean_Environment_contains(v___x_1123_, v_declHint_1115_, v_isExporting_1121_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v___x_1123_);
lean_dec_ref(v_env_1119_);
lean_dec(v_declHint_1115_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_msg_1114_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_c_1131_; lean_object* v___x_1132_; 
v___x_1126_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1127_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1128_ = l_Lean_Options_empty;
v___x_1129_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1123_);
lean_ctor_set(v___x_1129_, 1, v___x_1126_);
lean_ctor_set(v___x_1129_, 2, v___x_1127_);
lean_ctor_set(v___x_1129_, 3, v___x_1128_);
lean_inc(v_declHint_1115_);
v___x_1130_ = l_Lean_MessageData_ofConstName(v_declHint_1115_, v___x_1120_);
v_c_1131_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1131_, 0, v___x_1129_);
lean_ctor_set(v_c_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1119_, v_declHint_1115_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec_ref(v_env_1119_);
lean_dec(v_declHint_1115_);
v___x_1133_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v_c_1131_);
v___x_1135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_MessageData_note(v___x_1136_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_msg_1114_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
else
{
lean_object* v_val_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1175_; 
v_val_1140_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1142_ = v___x_1132_;
v_isShared_1143_ = v_isSharedCheck_1175_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_val_1140_);
lean_dec(v___x_1132_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1175_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_mod_1147_; uint8_t v___x_1148_; 
v___x_1144_ = lean_box(0);
v___x_1145_ = l_Lean_Environment_header(v_env_1119_);
lean_dec_ref(v_env_1119_);
v___x_1146_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1145_);
v_mod_1147_ = lean_array_get(v___x_1144_, v___x_1146_, v_val_1140_);
lean_dec(v_val_1140_);
lean_dec_ref(v___x_1146_);
v___x_1148_ = l_Lean_isPrivateName(v_declHint_1115_);
lean_dec(v_declHint_1115_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1149_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v_c_1131_);
v___x_1151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = l_Lean_MessageData_ofName(v_mod_1147_);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l_Lean_MessageData_note(v___x_1156_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v_msg_1114_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set_tag(v___x_1142_, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1158_);
v___x_1160_ = v___x_1142_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v_c_1131_);
v___x_1164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = l_Lean_MessageData_ofName(v_mod_1147_);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_MessageData_note(v___x_1169_);
v___x_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_msg_1114_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set_tag(v___x_1142_, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1171_);
v___x_1173_ = v___x_1142_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1176_; 
lean_dec_ref(v_env_1119_);
lean_dec(v_declHint_1115_);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_msg_1114_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1177_, lean_object* v_declHint_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1177_, v_declHint_1178_, v___y_1179_);
lean_dec(v___y_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1182_, lean_object* v_declHint_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1199_; 
v___x_1189_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1182_, v_declHint_1183_, v___y_1187_);
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1199_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1194_ = l_Lean_unknownIdentifierMessageTag;
v___x_1195_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v_a_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1195_);
v___x_1197_ = v___x_1192_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1200_, lean_object* v_declHint_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1200_, v_declHint_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1208_, lean_object* v_msg_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_toCold_1215_; lean_object* v_options_1216_; lean_object* v_currRecDepth_1217_; lean_object* v_maxRecDepth_1218_; lean_object* v_ref_1219_; lean_object* v_currNamespace_1220_; lean_object* v_openDecls_1221_; lean_object* v_initHeartbeats_1222_; lean_object* v_maxHeartbeats_1223_; lean_object* v_currMacroScope_1224_; uint8_t v_diag_1225_; uint8_t v_suppressElabErrors_1226_; lean_object* v_ref_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_toCold_1215_ = lean_ctor_get(v___y_1212_, 0);
v_options_1216_ = lean_ctor_get(v___y_1212_, 1);
v_currRecDepth_1217_ = lean_ctor_get(v___y_1212_, 2);
v_maxRecDepth_1218_ = lean_ctor_get(v___y_1212_, 3);
v_ref_1219_ = lean_ctor_get(v___y_1212_, 4);
v_currNamespace_1220_ = lean_ctor_get(v___y_1212_, 5);
v_openDecls_1221_ = lean_ctor_get(v___y_1212_, 6);
v_initHeartbeats_1222_ = lean_ctor_get(v___y_1212_, 7);
v_maxHeartbeats_1223_ = lean_ctor_get(v___y_1212_, 8);
v_currMacroScope_1224_ = lean_ctor_get(v___y_1212_, 9);
v_diag_1225_ = lean_ctor_get_uint8(v___y_1212_, sizeof(void*)*10);
v_suppressElabErrors_1226_ = lean_ctor_get_uint8(v___y_1212_, sizeof(void*)*10 + 1);
v_ref_1227_ = l_Lean_replaceRef(v_ref_1208_, v_ref_1219_);
lean_inc(v_currMacroScope_1224_);
lean_inc(v_maxHeartbeats_1223_);
lean_inc(v_initHeartbeats_1222_);
lean_inc(v_openDecls_1221_);
lean_inc(v_currNamespace_1220_);
lean_inc(v_maxRecDepth_1218_);
lean_inc(v_currRecDepth_1217_);
lean_inc_ref(v_options_1216_);
lean_inc_ref(v_toCold_1215_);
v___x_1228_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1228_, 0, v_toCold_1215_);
lean_ctor_set(v___x_1228_, 1, v_options_1216_);
lean_ctor_set(v___x_1228_, 2, v_currRecDepth_1217_);
lean_ctor_set(v___x_1228_, 3, v_maxRecDepth_1218_);
lean_ctor_set(v___x_1228_, 4, v_ref_1227_);
lean_ctor_set(v___x_1228_, 5, v_currNamespace_1220_);
lean_ctor_set(v___x_1228_, 6, v_openDecls_1221_);
lean_ctor_set(v___x_1228_, 7, v_initHeartbeats_1222_);
lean_ctor_set(v___x_1228_, 8, v_maxHeartbeats_1223_);
lean_ctor_set(v___x_1228_, 9, v_currMacroScope_1224_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*10, v_diag_1225_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*10 + 1, v_suppressElabErrors_1226_);
v___x_1229_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1209_, v___y_1210_, v___y_1211_, v___x_1228_, v___y_1213_);
lean_dec_ref_known(v___x_1228_, 10);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1230_, lean_object* v_msg_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1230_, v_msg_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v_ref_1230_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1238_, lean_object* v_msg_1239_, lean_object* v_declHint_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v_a_1247_; lean_object* v___x_1248_; 
v___x_1246_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1239_, v_declHint_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1238_, v_a_1247_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1249_, lean_object* v_msg_1250_, lean_object* v_declHint_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1249_, v_msg_1250_, v_declHint_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v_ref_1249_);
return v_res_1257_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1261_, lean_object* v_constName_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1268_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1269_ = 0;
lean_inc(v_constName_1262_);
v___x_1270_ = l_Lean_MessageData_ofConstName(v_constName_1262_, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1268_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1261_, v___x_1273_, v_constName_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1275_, lean_object* v_constName_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1275_, v_constName_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v_ref_1275_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_ref_1289_; lean_object* v___x_1290_; 
v_ref_1289_ = lean_ctor_get(v___y_1286_, 4);
v___x_1290_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1289_, v_constName_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1298_, uint8_t v_skipRealize_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v_env_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_st_ref_get(v___y_1303_);
v_env_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_env_1306_);
lean_dec(v___x_1305_);
lean_inc(v_constName_1298_);
v___x_1307_ = l_Lean_Environment_findAsync_x3f(v_env_1306_, v_constName_1298_, v_skipRealize_1299_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1298_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1308_;
}
else
{
lean_object* v_val_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_constName_1298_);
v_val_1309_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1307_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_val_1309_);
lean_dec(v___x_1307_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set_tag(v___x_1311_, 0);
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_val_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1317_, lean_object* v_skipRealize_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
uint8_t v_skipRealize_boxed_1324_; lean_object* v_res_1325_; 
v_skipRealize_boxed_1324_ = lean_unbox(v_skipRealize_1318_);
v_res_1325_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1317_, v_skipRealize_boxed_1324_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; lean_object* v_env_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1329_ = lean_st_ref_get(v___y_1327_);
v_env_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc_ref(v_env_1330_);
lean_dec(v___x_1329_);
v___x_1331_ = l_Lean_getReducibilityStatusCore(v_env_1330_, v_declName_1326_);
v___x_1332_ = lean_box(v___x_1331_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1334_, v___y_1335_);
lean_dec(v___y_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1360_; 
v___x_1344_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1338_, v___y_1342_);
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1360_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1360_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
if (v___x_1349_ == 0)
{
uint8_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1350_ = 1;
v___x_1351_ = lean_box(v___x_1350_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1351_);
v___x_1353_ = v___x_1347_;
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
else
{
uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1355_ = 0;
v___x_1356_ = lean_box(v___x_1355_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1356_);
v___x_1358_ = v___x_1347_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1367_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1373_ = l_Lean_stringToMessageData(v___x_1372_);
return v___x_1373_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1376_ = l_Lean_stringToMessageData(v___x_1375_);
return v___x_1376_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1379_ = l_Lean_stringToMessageData(v___x_1378_);
return v___x_1379_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1383_, lean_object* v_id_1384_, lean_object* v_declName_1385_, lean_object* v_kind_1386_, uint8_t v_minIndexable_1387_, uint8_t v_suggest_1388_, uint8_t v_warn_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___y_1396_; lean_object* v_thm_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; uint8_t v___x_1451_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___x_1648_; 
v___x_1451_ = 0;
lean_inc(v_declName_1385_);
v___x_1648_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1385_, v___x_1451_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; uint8_t v_kind_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v_kind_1650_ = lean_ctor_get_uint8(v_a_1649_, sizeof(void*)*3);
lean_dec(v_a_1649_);
switch(v_kind_1650_)
{
case 1:
{
v___y_1579_ = v_a_1390_;
v___y_1580_ = v_a_1391_;
v___y_1581_ = v_a_1392_;
v___y_1582_ = v_a_1393_;
goto v___jp_1578_;
}
case 2:
{
v___y_1579_ = v_a_1390_;
v___y_1580_ = v_a_1391_;
v___y_1581_ = v_a_1392_;
v___y_1582_ = v_a_1393_;
goto v___jp_1578_;
}
case 6:
{
v___y_1579_ = v_a_1390_;
v___y_1580_ = v_a_1391_;
v___y_1581_ = v_a_1392_;
v___y_1582_ = v_a_1393_;
goto v___jp_1578_;
}
case 0:
{
lean_object* v___x_1651_; 
lean_dec(v_id_1384_);
lean_inc(v_declName_1385_);
v___x_1651_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1385_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; uint8_t v___x_1653_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = lean_unbox(v_a_1652_);
lean_dec(v_a_1652_);
if (v___x_1653_ == 0)
{
v___y_1509_ = v_a_1390_;
v___y_1510_ = v_a_1391_;
v___y_1511_ = v_a_1392_;
v___y_1512_ = v_a_1393_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_kind_1386_);
lean_dec_ref(v_params_1383_);
v___x_1654_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1655_ = l_Lean_MessageData_ofConstName(v_declName_1385_, v___x_1451_);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1658_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_kind_1386_);
lean_dec(v_declName_1385_);
lean_dec_ref(v_params_1383_);
v_a_1668_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1651_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1651_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
default: 
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec(v_kind_1386_);
lean_dec(v_id_1384_);
lean_dec_ref(v_params_1383_);
v___x_1676_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1677_ = l_Lean_MessageData_ofConstName(v_declName_1385_, v___x_1451_);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1680_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
return v___x_1681_;
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_kind_1386_);
lean_dec(v_declName_1385_);
lean_dec(v_id_1384_);
lean_dec_ref(v_params_1383_);
v_a_1682_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1648_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1648_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
v___jp_1395_:
{
lean_object* v_config_1397_; lean_object* v_extensions_1398_; lean_object* v_extra_1399_; lean_object* v_extraInj_1400_; lean_object* v_extraFacts_1401_; lean_object* v_symPrios_1402_; lean_object* v_norm_1403_; lean_object* v_normProcs_1404_; lean_object* v_anchorRefs_x3f_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1414_; 
v_config_1397_ = lean_ctor_get(v_params_1383_, 0);
v_extensions_1398_ = lean_ctor_get(v_params_1383_, 1);
v_extra_1399_ = lean_ctor_get(v_params_1383_, 2);
v_extraInj_1400_ = lean_ctor_get(v_params_1383_, 3);
v_extraFacts_1401_ = lean_ctor_get(v_params_1383_, 4);
v_symPrios_1402_ = lean_ctor_get(v_params_1383_, 5);
v_norm_1403_ = lean_ctor_get(v_params_1383_, 6);
v_normProcs_1404_ = lean_ctor_get(v_params_1383_, 7);
v_anchorRefs_x3f_1405_ = lean_ctor_get(v_params_1383_, 8);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_params_1383_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1407_ = v_params_1383_;
v_isShared_1408_ = v_isSharedCheck_1414_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_anchorRefs_x3f_1405_);
lean_inc(v_normProcs_1404_);
lean_inc(v_norm_1403_);
lean_inc(v_symPrios_1402_);
lean_inc(v_extraFacts_1401_);
lean_inc(v_extraInj_1400_);
lean_inc(v_extra_1399_);
lean_inc(v_extensions_1398_);
lean_inc(v_config_1397_);
lean_dec(v_params_1383_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1414_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = l_Lean_PersistentArray_push___redArg(v_extra_1399_, v___y_1396_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 2, v___x_1409_);
v___x_1411_ = v___x_1407_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_config_1397_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_extensions_1398_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_extraInj_1400_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_extraFacts_1401_);
lean_ctor_set(v_reuseFailAlloc_1413_, 5, v_symPrios_1402_);
lean_ctor_set(v_reuseFailAlloc_1413_, 6, v_norm_1403_);
lean_ctor_set(v_reuseFailAlloc_1413_, 7, v_normProcs_1404_);
lean_ctor_set(v_reuseFailAlloc_1413_, 8, v_anchorRefs_x3f_1405_);
v___x_1411_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
}
}
v___jp_1415_:
{
if (v_warn_1389_ == 0)
{
lean_dec(v_declName_1385_);
v___y_1396_ = v_thm_1416_;
goto v___jp_1395_;
}
else
{
lean_object* v_extensions_1421_; lean_object* v_patterns_1422_; lean_object* v_origin_1423_; lean_object* v_cnstrs_1424_; uint8_t v___x_1425_; 
v_extensions_1421_ = lean_ctor_get(v_params_1383_, 1);
v_patterns_1422_ = lean_ctor_get(v_thm_1416_, 3);
v_origin_1423_ = lean_ctor_get(v_thm_1416_, 5);
v_cnstrs_1424_ = lean_ctor_get(v_thm_1416_, 7);
v___x_1425_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1421_, v_origin_1423_, v_patterns_1422_, v_cnstrs_1424_);
if (v___x_1425_ == 0)
{
lean_dec(v_declName_1385_);
v___y_1396_ = v_thm_1416_;
goto v___jp_1395_;
}
else
{
lean_object* v___x_1426_; 
v___x_1426_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1421_, v_declName_1385_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_dec_ref_known(v___x_1426_, 1);
v___y_1396_ = v_thm_1416_;
goto v___jp_1395_;
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_dec_ref(v_thm_1416_);
lean_dec_ref(v_params_1383_);
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
}
v___jp_1435_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1447_ = l_Lean_PersistentArray_push___redArg(v___y_1440_, v___y_1444_);
v___x_1448_ = l_Lean_PersistentArray_push___redArg(v___x_1447_, v___y_1443_);
v___x_1449_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1438_);
lean_ctor_set(v___x_1449_, 1, v___y_1446_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
lean_ctor_set(v___x_1449_, 3, v___y_1436_);
lean_ctor_set(v___x_1449_, 4, v___y_1445_);
lean_ctor_set(v___x_1449_, 5, v___y_1437_);
lean_ctor_set(v___x_1449_, 6, v___y_1441_);
lean_ctor_set(v___x_1449_, 7, v___y_1442_);
lean_ctor_set(v___x_1449_, 8, v___y_1439_);
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
v___jp_1452_:
{
lean_object* v___x_1457_; 
v___x_1457_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1387_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v___x_1458_; 
lean_dec_ref_known(v___x_1457_, 1);
lean_inc(v_declName_1385_);
v___x_1458_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1385_, v___x_1451_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1491_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1491_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1491_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
if (lean_obj_tag(v_a_1459_) == 1)
{
lean_object* v_val_1463_; lean_object* v_config_1464_; lean_object* v_extensions_1465_; lean_object* v_extra_1466_; lean_object* v_extraInj_1467_; lean_object* v_extraFacts_1468_; lean_object* v_symPrios_1469_; lean_object* v_norm_1470_; lean_object* v_normProcs_1471_; lean_object* v_anchorRefs_x3f_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1484_; 
lean_dec(v_declName_1385_);
v_val_1463_ = lean_ctor_get(v_a_1459_, 0);
lean_inc(v_val_1463_);
lean_dec_ref_known(v_a_1459_, 1);
v_config_1464_ = lean_ctor_get(v_params_1383_, 0);
v_extensions_1465_ = lean_ctor_get(v_params_1383_, 1);
v_extra_1466_ = lean_ctor_get(v_params_1383_, 2);
v_extraInj_1467_ = lean_ctor_get(v_params_1383_, 3);
v_extraFacts_1468_ = lean_ctor_get(v_params_1383_, 4);
v_symPrios_1469_ = lean_ctor_get(v_params_1383_, 5);
v_norm_1470_ = lean_ctor_get(v_params_1383_, 6);
v_normProcs_1471_ = lean_ctor_get(v_params_1383_, 7);
v_anchorRefs_x3f_1472_ = lean_ctor_get(v_params_1383_, 8);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_params_1383_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1474_ = v_params_1383_;
v_isShared_1475_ = v_isSharedCheck_1484_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_anchorRefs_x3f_1472_);
lean_inc(v_normProcs_1471_);
lean_inc(v_norm_1470_);
lean_inc(v_symPrios_1469_);
lean_inc(v_extraFacts_1468_);
lean_inc(v_extraInj_1467_);
lean_inc(v_extra_1466_);
lean_inc(v_extensions_1465_);
lean_inc(v_config_1464_);
lean_dec(v_params_1383_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1484_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1476_ = l_Lean_Array_toPArray_x27___redArg(v_val_1463_);
lean_dec(v_val_1463_);
v___x_1477_ = l_Lean_PersistentArray_append___redArg(v_extra_1466_, v___x_1476_);
lean_dec_ref(v___x_1476_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 2, v___x_1477_);
v___x_1479_ = v___x_1474_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_config_1464_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_extensions_1465_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v_extraInj_1467_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v_extraFacts_1468_);
lean_ctor_set(v_reuseFailAlloc_1483_, 5, v_symPrios_1469_);
lean_ctor_set(v_reuseFailAlloc_1483_, 6, v_norm_1470_);
lean_ctor_set(v_reuseFailAlloc_1483_, 7, v_normProcs_1471_);
lean_ctor_set(v_reuseFailAlloc_1483_, 8, v_anchorRefs_x3f_1472_);
v___x_1479_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1481_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1479_);
v___x_1481_ = v___x_1461_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_del_object(v___x_1461_);
lean_dec(v_a_1459_);
lean_dec_ref(v_params_1383_);
v___x_1485_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1486_ = l_Lean_MessageData_ofConstName(v_declName_1385_, v___x_1451_);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1489_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1490_;
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_declName_1385_);
lean_dec_ref(v_params_1383_);
v_a_1492_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1458_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1458_);
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
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_declName_1385_);
lean_dec_ref(v_params_1383_);
v_a_1500_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1457_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1457_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
v___jp_1508_:
{
uint8_t v___x_1513_; 
v___x_1513_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1386_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; 
v___x_1514_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1386_);
lean_dec(v_kind_1386_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v_params_1383_);
v___x_1515_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1516_ = l_Lean_MessageData_ofConstName(v_declName_1385_, v___x_1451_);
v___x_1517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1519_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
else
{
v___y_1453_ = v___y_1509_;
v___y_1454_ = v___y_1510_;
v___y_1455_ = v___y_1511_;
v___y_1456_ = v___y_1512_;
goto v___jp_1452_;
}
}
else
{
lean_dec(v_kind_1386_);
v___y_1453_ = v___y_1509_;
v___y_1454_ = v___y_1510_;
v___y_1455_ = v___y_1511_;
v___y_1456_ = v___y_1512_;
goto v___jp_1452_;
}
}
v___jp_1529_:
{
lean_object* v_symPrios_1534_; lean_object* v___x_1535_; 
v_symPrios_1534_ = lean_ctor_get(v_params_1383_, 5);
lean_inc_ref(v_symPrios_1534_);
lean_inc(v_declName_1385_);
v___x_1535_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1385_, v_kind_1386_, v_symPrios_1534_, v___x_1451_, v_minIndexable_1387_, v___y_1531_, v___y_1530_, v___y_1533_, v___y_1532_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v_thm_1416_ = v_a_1536_;
v___y_1417_ = v___y_1531_;
v___y_1418_ = v___y_1530_;
v___y_1419_ = v___y_1533_;
v___y_1420_ = v___y_1532_;
goto v___jp_1415_;
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec(v_declName_1385_);
lean_dec_ref(v_params_1383_);
v_a_1537_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1535_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1535_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
v___jp_1545_:
{
if (v_suggest_1388_ == 0)
{
lean_dec(v_id_1384_);
v___y_1530_ = v___y_1547_;
v___y_1531_ = v___y_1546_;
v___y_1532_ = v___y_1549_;
v___y_1533_ = v___y_1548_;
goto v___jp_1529_;
}
else
{
lean_object* v_options_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_options_1550_ = lean_ctor_get(v___y_1548_, 1);
v___x_1551_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1552_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v_symPrios_1553_; lean_object* v___x_1554_; 
lean_dec(v_kind_1386_);
v_symPrios_1553_ = lean_ctor_get(v_params_1383_, 5);
lean_inc_ref(v_symPrios_1553_);
lean_inc(v_declName_1385_);
v___x_1554_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1384_, v_declName_1385_, v_symPrios_1553_, v_minIndexable_1387_, v_suggest_1388_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v_thm_1416_ = v_a_1555_;
v___y_1417_ = v___y_1546_;
v___y_1418_ = v___y_1547_;
v___y_1419_ = v___y_1548_;
v___y_1420_ = v___y_1549_;
goto v___jp_1415_;
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_declName_1385_);
lean_dec_ref(v_params_1383_);
v_a_1556_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1554_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1554_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_dec(v_id_1384_);
v___y_1530_ = v___y_1547_;
v___y_1531_ = v___y_1546_;
v___y_1532_ = v___y_1549_;
v___y_1533_ = v___y_1548_;
goto v___jp_1529_;
}
}
}
v___jp_1564_:
{
lean_object* v___x_1569_; 
v___x_1569_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1387_, v___y_1566_, v___y_1568_, v___y_1567_, v___y_1565_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_dec_ref_known(v___x_1569_, 1);
v___y_1546_ = v___y_1566_;
v___y_1547_ = v___y_1568_;
v___y_1548_ = v___y_1567_;
v___y_1549_ = v___y_1565_;
goto v___jp_1545_;
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_kind_1386_);
lean_dec(v_declName_1385_);
lean_dec(v_id_1384_);
lean_dec_ref(v_params_1383_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
v___jp_1578_:
{
if (lean_obj_tag(v_kind_1386_) == 2)
{
uint8_t v_gen_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_id_1384_);
v_gen_1583_ = lean_ctor_get_uint8(v_kind_1386_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_kind_1386_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1585_ = v_kind_1386_;
v_isShared_1586_ = v_isSharedCheck_1647_;
goto v_resetjp_1584_;
}
else
{
lean_dec(v_kind_1386_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1647_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; 
v___x_1587_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1387_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_config_1588_; lean_object* v_extensions_1589_; lean_object* v_extra_1590_; lean_object* v_extraInj_1591_; lean_object* v_extraFacts_1592_; lean_object* v_symPrios_1593_; lean_object* v_norm_1594_; lean_object* v_normProcs_1595_; lean_object* v_anchorRefs_x3f_1596_; lean_object* v___x_1598_; 
lean_dec_ref_known(v___x_1587_, 1);
v_config_1588_ = lean_ctor_get(v_params_1383_, 0);
lean_inc_ref(v_config_1588_);
v_extensions_1589_ = lean_ctor_get(v_params_1383_, 1);
lean_inc_ref(v_extensions_1589_);
v_extra_1590_ = lean_ctor_get(v_params_1383_, 2);
lean_inc_ref(v_extra_1590_);
v_extraInj_1591_ = lean_ctor_get(v_params_1383_, 3);
lean_inc_ref(v_extraInj_1591_);
v_extraFacts_1592_ = lean_ctor_get(v_params_1383_, 4);
lean_inc_ref(v_extraFacts_1592_);
v_symPrios_1593_ = lean_ctor_get(v_params_1383_, 5);
lean_inc_ref(v_symPrios_1593_);
v_norm_1594_ = lean_ctor_get(v_params_1383_, 6);
lean_inc_ref(v_norm_1594_);
v_normProcs_1595_ = lean_ctor_get(v_params_1383_, 7);
lean_inc_ref(v_normProcs_1595_);
v_anchorRefs_x3f_1596_ = lean_ctor_get(v_params_1383_, 8);
lean_inc(v_anchorRefs_x3f_1596_);
lean_dec_ref(v_params_1383_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set_tag(v___x_1585_, 0);
v___x_1598_ = v___x_1585_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1638_, 0, v_gen_1583_);
v___x_1598_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
lean_inc_ref(v_symPrios_1593_);
lean_inc(v_declName_1385_);
v___x_1599_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1385_, v___x_1598_, v_symPrios_1593_, v___x_1451_, v___x_1451_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1599_, 1);
v___x_1601_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1601_, 0, v_gen_1583_);
lean_inc_ref(v_symPrios_1593_);
lean_inc(v_declName_1385_);
v___x_1602_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1385_, v___x_1601_, v_symPrios_1593_, v___x_1451_, v___x_1451_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1602_) == 0)
{
if (v_warn_1389_ == 0)
{
lean_object* v_a_1603_; 
lean_dec(v_declName_1385_);
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1602_, 1);
v___y_1436_ = v_extraInj_1591_;
v___y_1437_ = v_symPrios_1593_;
v___y_1438_ = v_config_1588_;
v___y_1439_ = v_anchorRefs_x3f_1596_;
v___y_1440_ = v_extra_1590_;
v___y_1441_ = v_norm_1594_;
v___y_1442_ = v_normProcs_1595_;
v___y_1443_ = v_a_1603_;
v___y_1444_ = v_a_1600_;
v___y_1445_ = v_extraFacts_1592_;
v___y_1446_ = v_extensions_1589_;
goto v___jp_1435_;
}
else
{
lean_object* v_a_1604_; lean_object* v_patterns_1605_; lean_object* v_origin_1606_; lean_object* v_cnstrs_1607_; uint8_t v___x_1608_; 
v_a_1604_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1602_, 1);
v_patterns_1605_ = lean_ctor_get(v_a_1600_, 3);
v_origin_1606_ = lean_ctor_get(v_a_1600_, 5);
v_cnstrs_1607_ = lean_ctor_get(v_a_1600_, 7);
v___x_1608_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1589_, v_origin_1606_, v_patterns_1605_, v_cnstrs_1607_);
if (v___x_1608_ == 0)
{
lean_dec(v_declName_1385_);
v___y_1436_ = v_extraInj_1591_;
v___y_1437_ = v_symPrios_1593_;
v___y_1438_ = v_config_1588_;
v___y_1439_ = v_anchorRefs_x3f_1596_;
v___y_1440_ = v_extra_1590_;
v___y_1441_ = v_norm_1594_;
v___y_1442_ = v_normProcs_1595_;
v___y_1443_ = v_a_1604_;
v___y_1444_ = v_a_1600_;
v___y_1445_ = v_extraFacts_1592_;
v___y_1446_ = v_extensions_1589_;
goto v___jp_1435_;
}
else
{
lean_object* v_patterns_1609_; lean_object* v_origin_1610_; lean_object* v_cnstrs_1611_; uint8_t v___x_1612_; 
v_patterns_1609_ = lean_ctor_get(v_a_1604_, 3);
v_origin_1610_ = lean_ctor_get(v_a_1604_, 5);
v_cnstrs_1611_ = lean_ctor_get(v_a_1604_, 7);
v___x_1612_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1589_, v_origin_1610_, v_patterns_1609_, v_cnstrs_1611_);
if (v___x_1612_ == 0)
{
lean_dec(v_declName_1385_);
v___y_1436_ = v_extraInj_1591_;
v___y_1437_ = v_symPrios_1593_;
v___y_1438_ = v_config_1588_;
v___y_1439_ = v_anchorRefs_x3f_1596_;
v___y_1440_ = v_extra_1590_;
v___y_1441_ = v_norm_1594_;
v___y_1442_ = v_normProcs_1595_;
v___y_1443_ = v_a_1604_;
v___y_1444_ = v_a_1600_;
v___y_1445_ = v_extraFacts_1592_;
v___y_1446_ = v_extensions_1589_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1589_, v_declName_1385_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_dec_ref_known(v___x_1613_, 1);
v___y_1436_ = v_extraInj_1591_;
v___y_1437_ = v_symPrios_1593_;
v___y_1438_ = v_config_1588_;
v___y_1439_ = v_anchorRefs_x3f_1596_;
v___y_1440_ = v_extra_1590_;
v___y_1441_ = v_norm_1594_;
v___y_1442_ = v_normProcs_1595_;
v___y_1443_ = v_a_1604_;
v___y_1444_ = v_a_1600_;
v___y_1445_ = v_extraFacts_1592_;
v___y_1446_ = v_extensions_1589_;
goto v___jp_1435_;
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v_a_1604_);
lean_dec(v_a_1600_);
lean_dec(v_anchorRefs_x3f_1596_);
lean_dec_ref(v_normProcs_1595_);
lean_dec_ref(v_norm_1594_);
lean_dec_ref(v_symPrios_1593_);
lean_dec_ref(v_extraFacts_1592_);
lean_dec_ref(v_extraInj_1591_);
lean_dec_ref(v_extra_1590_);
lean_dec_ref(v_extensions_1589_);
lean_dec_ref(v_config_1588_);
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
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
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_a_1600_);
lean_dec(v_anchorRefs_x3f_1596_);
lean_dec_ref(v_normProcs_1595_);
lean_dec_ref(v_norm_1594_);
lean_dec_ref(v_symPrios_1593_);
lean_dec_ref(v_extraFacts_1592_);
lean_dec_ref(v_extraInj_1591_);
lean_dec_ref(v_extra_1590_);
lean_dec_ref(v_extensions_1589_);
lean_dec_ref(v_config_1588_);
lean_dec(v_declName_1385_);
v_a_1622_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1602_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1602_);
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
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec(v_anchorRefs_x3f_1596_);
lean_dec_ref(v_normProcs_1595_);
lean_dec_ref(v_norm_1594_);
lean_dec_ref(v_symPrios_1593_);
lean_dec_ref(v_extraFacts_1592_);
lean_dec_ref(v_extraInj_1591_);
lean_dec_ref(v_extra_1590_);
lean_dec_ref(v_extensions_1589_);
lean_dec_ref(v_config_1588_);
lean_dec(v_declName_1385_);
v_a_1630_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1599_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1599_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_del_object(v___x_1585_);
lean_dec(v_declName_1385_);
lean_dec_ref(v_params_1383_);
v_a_1639_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1587_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1587_);
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
}
else
{
switch(lean_obj_tag(v_kind_1386_))
{
case 0:
{
v___y_1565_ = v___y_1582_;
v___y_1566_ = v___y_1579_;
v___y_1567_ = v___y_1581_;
v___y_1568_ = v___y_1580_;
goto v___jp_1564_;
}
case 1:
{
v___y_1565_ = v___y_1582_;
v___y_1566_ = v___y_1579_;
v___y_1567_ = v___y_1581_;
v___y_1568_ = v___y_1580_;
goto v___jp_1564_;
}
default: 
{
v___y_1546_ = v___y_1579_;
v___y_1547_ = v___y_1580_;
v___y_1548_ = v___y_1581_;
v___y_1549_ = v___y_1582_;
goto v___jp_1545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1690_, lean_object* v_id_1691_, lean_object* v_declName_1692_, lean_object* v_kind_1693_, lean_object* v_minIndexable_1694_, lean_object* v_suggest_1695_, lean_object* v_warn_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
uint8_t v_minIndexable_boxed_1702_; uint8_t v_suggest_boxed_1703_; uint8_t v_warn_boxed_1704_; lean_object* v_res_1705_; 
v_minIndexable_boxed_1702_ = lean_unbox(v_minIndexable_1694_);
v_suggest_boxed_1703_ = lean_unbox(v_suggest_1695_);
v_warn_boxed_1704_ = lean_unbox(v_warn_1696_);
v_res_1705_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1690_, v_id_1691_, v_declName_1692_, v_kind_1693_, v_minIndexable_boxed_1702_, v_suggest_boxed_1703_, v_warn_boxed_1704_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1706_, v___y_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1720_, lean_object* v_constName_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1728_, lean_object* v_constName_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1728_, v_constName_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1736_, lean_object* v_ref_1737_, lean_object* v_constName_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1737_, v_constName_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_ref_1746_, lean_object* v_constName_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1745_, v_ref_1746_, v_constName_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v_ref_1746_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1754_, lean_object* v_ref_1755_, lean_object* v_msg_1756_, lean_object* v_declHint_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1755_, v_msg_1756_, v_declHint_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1764_, lean_object* v_ref_1765_, lean_object* v_msg_1766_, lean_object* v_declHint_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1764_, v_ref_1765_, v_msg_1766_, v_declHint_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v_ref_1765_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1774_, lean_object* v_declHint_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1774_, v_declHint_1775_, v___y_1779_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1782_, lean_object* v_declHint_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1782_, v_declHint_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1790_, lean_object* v_ref_1791_, lean_object* v_msg_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1791_, v_msg_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1799_, lean_object* v_ref_1800_, lean_object* v_msg_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1799_, v_ref_1800_, v_msg_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v_ref_1800_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1810_, lean_object* v_val_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_config_1815_; lean_object* v_extensions_1816_; lean_object* v_extra_1817_; lean_object* v_extraInj_1818_; lean_object* v_extraFacts_1819_; lean_object* v_symPrios_1820_; lean_object* v_norm_1821_; lean_object* v_normProcs_1822_; lean_object* v_anchorRefs_x3f_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1853_; 
v_config_1815_ = lean_ctor_get(v_params_1810_, 0);
v_extensions_1816_ = lean_ctor_get(v_params_1810_, 1);
v_extra_1817_ = lean_ctor_get(v_params_1810_, 2);
v_extraInj_1818_ = lean_ctor_get(v_params_1810_, 3);
v_extraFacts_1819_ = lean_ctor_get(v_params_1810_, 4);
v_symPrios_1820_ = lean_ctor_get(v_params_1810_, 5);
v_norm_1821_ = lean_ctor_get(v_params_1810_, 6);
v_normProcs_1822_ = lean_ctor_get(v_params_1810_, 7);
v_anchorRefs_x3f_1823_ = lean_ctor_get(v_params_1810_, 8);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_params_1810_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1825_ = v_params_1810_;
v_isShared_1826_ = v_isSharedCheck_1853_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_anchorRefs_x3f_1823_);
lean_inc(v_normProcs_1822_);
lean_inc(v_norm_1821_);
lean_inc(v_symPrios_1820_);
lean_inc(v_extraFacts_1819_);
lean_inc(v_extraInj_1818_);
lean_inc(v_extra_1817_);
lean_inc(v_extensions_1816_);
lean_inc(v_config_1815_);
lean_dec(v_params_1810_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1853_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___y_1828_; 
if (lean_obj_tag(v_anchorRefs_x3f_1823_) == 0)
{
lean_object* v___x_1851_; 
v___x_1851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1828_ = v___x_1851_;
goto v___jp_1827_;
}
else
{
lean_object* v_val_1852_; 
v_val_1852_ = lean_ctor_get(v_anchorRefs_x3f_1823_, 0);
lean_inc(v_val_1852_);
lean_dec_ref_known(v_anchorRefs_x3f_1823_, 1);
v___y_1828_ = v_val_1852_;
goto v___jp_1827_;
}
v___jp_1827_:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1842_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1842_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1842_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1834_ = lean_array_push(v___y_1828_, v_a_1830_);
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 8, v___x_1835_);
v___x_1837_ = v___x_1825_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_config_1815_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_extensions_1816_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_extra_1817_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_extraInj_1818_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_extraFacts_1819_);
lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_symPrios_1820_);
lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_norm_1821_);
lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_normProcs_1822_);
lean_ctor_set(v_reuseFailAlloc_1841_, 8, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1837_);
v___x_1839_ = v___x_1832_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec_ref(v___y_1828_);
lean_del_object(v___x_1825_);
lean_dec_ref(v_normProcs_1822_);
lean_dec_ref(v_norm_1821_);
lean_dec_ref(v_symPrios_1820_);
lean_dec_ref(v_extraFacts_1819_);
lean_dec_ref(v_extraInj_1818_);
lean_dec_ref(v_extra_1817_);
lean_dec_ref(v_extensions_1816_);
lean_dec_ref(v_config_1815_);
v_a_1843_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1829_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1829_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1854_, lean_object* v_val_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1854_, v_val_1855_, v_a_1856_, v_a_1857_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_val_1855_);
return v_res_1859_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1862_ = l_Lean_stringToMessageData(v___x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v_config_1867_; uint8_t v_revert_1868_; 
v_config_1867_ = lean_ctor_get(v_params_1863_, 0);
v_revert_1868_ = lean_ctor_get_uint8(v_config_1867_, sizeof(void*)*14 + 30);
if (v_revert_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_box(0);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
return v___x_1870_;
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_1872_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1871_, v_a_1864_, v_a_1865_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec_ref(v_params_1873_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_1878_, lean_object* v___y_1879_){
_start:
{
uint8_t v___x_1881_; 
v___x_1881_ = l_Lean_Expr_hasMVar(v_e_1878_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_e_1878_);
return v___x_1882_;
}
else
{
lean_object* v___x_1883_; lean_object* v_mctx_1884_; lean_object* v___x_1885_; lean_object* v_fst_1886_; lean_object* v_snd_1887_; lean_object* v___x_1888_; lean_object* v_cache_1889_; lean_object* v_zetaDeltaFVarIds_1890_; lean_object* v_postponed_1891_; lean_object* v_diag_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1901_; 
v___x_1883_ = lean_st_ref_get(v___y_1879_);
v_mctx_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc_ref(v_mctx_1884_);
lean_dec(v___x_1883_);
v___x_1885_ = l_Lean_instantiateMVarsCore(v_mctx_1884_, v_e_1878_);
v_fst_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_fst_1886_);
v_snd_1887_ = lean_ctor_get(v___x_1885_, 1);
lean_inc(v_snd_1887_);
lean_dec_ref(v___x_1885_);
v___x_1888_ = lean_st_ref_take(v___y_1879_);
v_cache_1889_ = lean_ctor_get(v___x_1888_, 1);
v_zetaDeltaFVarIds_1890_ = lean_ctor_get(v___x_1888_, 2);
v_postponed_1891_ = lean_ctor_get(v___x_1888_, 3);
v_diag_1892_ = lean_ctor_get(v___x_1888_, 4);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v___x_1888_, 0);
lean_dec(v_unused_1902_);
v___x_1894_ = v___x_1888_;
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_diag_1892_);
lean_inc(v_postponed_1891_);
lean_inc(v_zetaDeltaFVarIds_1890_);
lean_inc(v_cache_1889_);
lean_dec(v___x_1888_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v_snd_1887_);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_snd_1887_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_cache_1889_);
lean_ctor_set(v_reuseFailAlloc_1900_, 2, v_zetaDeltaFVarIds_1890_);
lean_ctor_set(v_reuseFailAlloc_1900_, 3, v_postponed_1891_);
lean_ctor_set(v_reuseFailAlloc_1900_, 4, v_diag_1892_);
v___x_1897_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_st_ref_put(v___y_1879_, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v_fst_1886_);
return v___x_1899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1903_, v___y_1904_);
lean_dec(v___y_1904_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1907_, v___y_1911_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(lean_object* v_p_1927_, lean_object* v_term_1928_, lean_object* v___x_1929_, uint8_t v___x_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_toCold_1938_; lean_object* v_options_1939_; lean_object* v_currRecDepth_1940_; lean_object* v_maxRecDepth_1941_; lean_object* v_ref_1942_; lean_object* v_currNamespace_1943_; lean_object* v_openDecls_1944_; lean_object* v_initHeartbeats_1945_; lean_object* v_maxHeartbeats_1946_; lean_object* v_currMacroScope_1947_; uint8_t v_diag_1948_; uint8_t v_suppressElabErrors_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_2017_; 
v_toCold_1938_ = lean_ctor_get(v___y_1935_, 0);
v_options_1939_ = lean_ctor_get(v___y_1935_, 1);
v_currRecDepth_1940_ = lean_ctor_get(v___y_1935_, 2);
v_maxRecDepth_1941_ = lean_ctor_get(v___y_1935_, 3);
v_ref_1942_ = lean_ctor_get(v___y_1935_, 4);
v_currNamespace_1943_ = lean_ctor_get(v___y_1935_, 5);
v_openDecls_1944_ = lean_ctor_get(v___y_1935_, 6);
v_initHeartbeats_1945_ = lean_ctor_get(v___y_1935_, 7);
v_maxHeartbeats_1946_ = lean_ctor_get(v___y_1935_, 8);
v_currMacroScope_1947_ = lean_ctor_get(v___y_1935_, 9);
v_diag_1948_ = lean_ctor_get_uint8(v___y_1935_, sizeof(void*)*10);
v_suppressElabErrors_1949_ = lean_ctor_get_uint8(v___y_1935_, sizeof(void*)*10 + 1);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___y_1935_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1951_ = v___y_1935_;
v_isShared_1952_ = v_isSharedCheck_2017_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_currMacroScope_1947_);
lean_inc(v_maxHeartbeats_1946_);
lean_inc(v_initHeartbeats_1945_);
lean_inc(v_openDecls_1944_);
lean_inc(v_currNamespace_1943_);
lean_inc(v_ref_1942_);
lean_inc(v_maxRecDepth_1941_);
lean_inc(v_currRecDepth_1940_);
lean_inc(v_options_1939_);
lean_inc(v_toCold_1938_);
lean_dec(v___y_1935_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_2017_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_ref_1953_; lean_object* v___x_1955_; 
v_ref_1953_ = l_Lean_replaceRef(v_p_1927_, v_ref_1942_);
lean_dec(v_ref_1942_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 4, v_ref_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_toCold_1938_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_options_1939_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_currRecDepth_1940_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_maxRecDepth_1941_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v_ref_1953_);
lean_ctor_set(v_reuseFailAlloc_2016_, 5, v_currNamespace_1943_);
lean_ctor_set(v_reuseFailAlloc_2016_, 6, v_openDecls_1944_);
lean_ctor_set(v_reuseFailAlloc_2016_, 7, v_initHeartbeats_1945_);
lean_ctor_set(v_reuseFailAlloc_2016_, 8, v_maxHeartbeats_1946_);
lean_ctor_set(v_reuseFailAlloc_2016_, 9, v_currMacroScope_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_2016_, sizeof(void*)*10, v_diag_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_2016_, sizeof(void*)*10 + 1, v_suppressElabErrors_1949_);
v___x_1955_ = v_reuseFailAlloc_2016_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_Elab_Term_elabTerm(v_term_1928_, v___x_1929_, v___x_1930_, v___x_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___x_1955_, v___y_1936_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v___x_1958_ = 1;
v___x_1959_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1958_, v___x_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___x_1955_, v___y_1936_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v___x_1960_; lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1999_; 
lean_dec_ref_known(v___x_1959_, 1);
v___x_1960_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_1957_, v___y_1934_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1999_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1999_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
uint8_t v___x_1965_; 
v___x_1965_ = l_Lean_Expr_hasSyntheticSorry(v_a_1961_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1966_ = l_Lean_Expr_eta(v_a_1961_);
v___x_1967_ = l_Lean_Expr_hasMVar(v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
lean_dec_ref(v___x_1955_);
v___x_1968_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0));
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v___x_1966_);
v___x_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1970_);
v___x_1972_ = v___x_1963_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
else
{
lean_object* v___x_1974_; 
lean_del_object(v___x_1963_);
v___x_1974_ = l_Lean_Meta_abstractMVars(v___x_1966_, v___x_1930_, v___y_1933_, v___y_1934_, v___x_1955_, v___y_1936_);
lean_dec_ref(v___x_1955_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1986_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1986_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1986_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v_paramNames_1979_; lean_object* v_expr_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v_paramNames_1979_ = lean_ctor_get(v_a_1975_, 0);
lean_inc_ref(v_paramNames_1979_);
v_expr_1980_ = lean_ctor_get(v_a_1975_, 2);
lean_inc_ref(v_expr_1980_);
lean_dec(v_a_1975_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_paramNames_1979_);
lean_ctor_set(v___x_1981_, 1, v_expr_1980_);
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1982_);
v___x_1984_ = v___x_1977_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_a_1987_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1974_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1974_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
lean_dec(v_a_1961_);
lean_dec_ref(v___x_1955_);
v___x_1995_ = lean_box(0);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1995_);
v___x_1997_ = v___x_1963_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
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
lean_dec(v_a_1957_);
lean_dec_ref(v___x_1955_);
v_a_2000_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1959_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1959_);
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
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v___x_1955_);
v_a_2008_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1956_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1956_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v_p_2018_, lean_object* v_term_2019_, lean_object* v___x_2020_, lean_object* v___x_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
uint8_t v___x_12432__boxed_2029_; lean_object* v_res_2030_; 
v___x_12432__boxed_2029_ = lean_unbox(v___x_2021_);
v_res_2030_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v_p_2018_, v_term_2019_, v___x_2020_, v___x_12432__boxed_2029_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v_p_2018_);
return v_res_2030_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2));
v___x_2036_ = l_Lean_stringToMessageData(v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_params_2037_, lean_object* v_p_2038_, lean_object* v_fst_2039_, lean_object* v_snd_2040_, uint8_t v___x_2041_, uint8_t v_minIndexable_2042_, lean_object* v_kind_2043_, lean_object* v_idx_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_symPrios_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; 
v_symPrios_2050_ = lean_ctor_get(v_params_2037_, 5);
lean_inc_ref(v_symPrios_2050_);
lean_dec_ref(v_params_2037_);
v___x_2051_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1));
v___x_2052_ = lean_name_append_index_after(v___x_2051_, v_idx_2044_);
v___x_2053_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v_p_2038_);
v___x_2054_ = 0;
v___x_2055_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2053_, v_fst_2039_, v_snd_2040_, v_kind_2043_, v_symPrios_2050_, v___x_2041_, v___x_2054_, v_minIndexable_2042_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2066_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2066_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2066_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
if (lean_obj_tag(v_a_2056_) == 1)
{
lean_object* v_val_2060_; lean_object* v___x_2062_; 
v_val_2060_ = lean_ctor_get(v_a_2056_, 0);
lean_inc(v_val_2060_);
lean_dec_ref_known(v_a_2056_, 1);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v_val_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_val_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_del_object(v___x_2058_);
lean_dec(v_a_2056_);
v___x_2064_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3);
v___x_2065_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2064_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
return v___x_2065_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2055_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2055_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_params_2075_, lean_object* v_p_2076_, lean_object* v_fst_2077_, lean_object* v_snd_2078_, lean_object* v___x_2079_, lean_object* v_minIndexable_2080_, lean_object* v_kind_2081_, lean_object* v_idx_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
uint8_t v___x_12606__boxed_2088_; uint8_t v_minIndexable_boxed_2089_; lean_object* v_res_2090_; 
v___x_12606__boxed_2088_ = lean_unbox(v___x_2079_);
v_minIndexable_boxed_2089_ = lean_unbox(v_minIndexable_2080_);
v_res_2090_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_params_2075_, v_p_2076_, v_fst_2077_, v_snd_2078_, v___x_12606__boxed_2088_, v_minIndexable_boxed_2089_, v_kind_2081_, v_idx_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2090_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_box(1);
v___x_2092_ = l_Lean_MessageData_ofFormat(v___x_2091_);
return v___x_2092_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2));
v___x_2097_ = l_Lean_MessageData_ofFormat(v___x_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object* v_x_2098_, lean_object* v_x_2099_){
_start:
{
if (lean_obj_tag(v_x_2099_) == 0)
{
return v_x_2098_;
}
else
{
lean_object* v_head_2100_; lean_object* v_tail_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2123_; 
v_head_2100_ = lean_ctor_get(v_x_2099_, 0);
v_tail_2101_ = lean_ctor_get(v_x_2099_, 1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_x_2099_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2103_ = v_x_2099_;
v_isShared_2104_ = v_isSharedCheck_2123_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_tail_2101_);
lean_inc(v_head_2100_);
lean_dec(v_x_2099_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2123_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v_before_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2121_; 
v_before_2105_ = lean_ctor_get(v_head_2100_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_head_2100_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; 
v_unused_2122_ = lean_ctor_get(v_head_2100_, 1);
lean_dec(v_unused_2122_);
v___x_2107_ = v_head_2100_;
v_isShared_2108_ = v_isSharedCheck_2121_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_before_2105_);
lean_dec(v_head_2100_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2121_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2108_ == 0)
{
lean_ctor_set_tag(v___x_2107_, 7);
lean_ctor_set(v___x_2107_, 1, v___x_2109_);
lean_ctor_set(v___x_2107_, 0, v_x_2098_);
v___x_2111_ = v___x_2107_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_x_2098_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
v___x_2112_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3);
if (v_isShared_2104_ == 0)
{
lean_ctor_set_tag(v___x_2103_, 7);
lean_ctor_set(v___x_2103_, 1, v___x_2112_);
lean_ctor_set(v___x_2103_, 0, v___x_2111_);
v___x_2114_ = v___x_2103_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = l_Lean_MessageData_ofSyntax(v_before_2105_);
v___x_2116_ = l_Lean_indentD(v___x_2115_);
v___x_2117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2114_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v_x_2098_ = v___x_2117_;
v_x_2099_ = v_tail_2101_;
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
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1));
v___x_2128_ = l_Lean_MessageData_ofFormat(v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object* v_msgData_2129_, lean_object* v_macroStack_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_options_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v_options_2133_ = lean_ctor_get(v___y_2131_, 1);
v___x_2134_ = l_Lean_Elab_pp_macroStack;
v___x_2135_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2133_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec(v_macroStack_2130_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_msgData_2129_);
return v___x_2136_;
}
else
{
if (lean_obj_tag(v_macroStack_2130_) == 0)
{
lean_object* v___x_2137_; 
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v_msgData_2129_);
return v___x_2137_;
}
else
{
lean_object* v_head_2138_; lean_object* v_after_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2154_; 
v_head_2138_ = lean_ctor_get(v_macroStack_2130_, 0);
lean_inc(v_head_2138_);
v_after_2139_ = lean_ctor_get(v_head_2138_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_head_2138_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_head_2138_, 0);
lean_dec(v_unused_2155_);
v___x_2141_ = v_head_2138_;
v_isShared_2142_ = v_isSharedCheck_2154_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_after_2139_);
lean_dec(v_head_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2154_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2143_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2142_ == 0)
{
lean_ctor_set_tag(v___x_2141_, 7);
lean_ctor_set(v___x_2141_, 1, v___x_2143_);
lean_ctor_set(v___x_2141_, 0, v_msgData_2129_);
v___x_2145_ = v___x_2141_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_msgData_2129_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v_msgData_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2146_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_MessageData_ofSyntax(v_after_2139_);
v___x_2149_ = l_Lean_indentD(v___x_2148_);
v_msgData_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2150_, 0, v___x_2147_);
lean_ctor_set(v_msgData_2150_, 1, v___x_2149_);
v___x_2151_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(v_msgData_2150_, v_macroStack_2130_);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2156_, lean_object* v_macroStack_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2156_, v_macroStack_2157_, v___y_2158_);
lean_dec_ref(v___y_2158_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object* v_msg_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_ref_2169_; lean_object* v___x_2170_; lean_object* v_a_2171_; lean_object* v_macroStack_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2183_; 
v_ref_2169_ = lean_ctor_get(v___y_2166_, 4);
v___x_2170_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2161_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2170_);
v_macroStack_2172_ = lean_ctor_get(v___y_2162_, 1);
v___x_2173_ = l_Lean_Elab_getBetterRef(v_ref_2169_, v_macroStack_2172_);
lean_inc(v_macroStack_2172_);
v___x_2174_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_a_2171_, v_macroStack_2172_, v___y_2166_);
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2183_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2183_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2173_);
lean_ctor_set(v___x_2179_, 1, v_a_2175_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set_tag(v___x_2177_, 1);
lean_ctor_set(v___x_2177_, 0, v___x_2179_);
v___x_2181_ = v___x_2177_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v_msg_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2192_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7));
v___x_2206_ = l_Lean_stringToMessageData(v___x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2207_, lean_object* v_p_2208_, lean_object* v_mod_x3f_2209_, lean_object* v_term_2210_, uint8_t v_minIndexable_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2282_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v_kind_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v_toCold_2517_; lean_object* v_options_2518_; lean_object* v_currRecDepth_2519_; lean_object* v_maxRecDepth_2520_; lean_object* v_ref_2521_; lean_object* v_currNamespace_2522_; lean_object* v_openDecls_2523_; lean_object* v_initHeartbeats_2524_; lean_object* v_maxHeartbeats_2525_; lean_object* v_currMacroScope_2526_; uint8_t v_diag_2527_; uint8_t v_suppressElabErrors_2528_; lean_object* v_ref_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v_toCold_2517_ = lean_ctor_get(v_a_2216_, 0);
v_options_2518_ = lean_ctor_get(v_a_2216_, 1);
v_currRecDepth_2519_ = lean_ctor_get(v_a_2216_, 2);
v_maxRecDepth_2520_ = lean_ctor_get(v_a_2216_, 3);
v_ref_2521_ = lean_ctor_get(v_a_2216_, 4);
v_currNamespace_2522_ = lean_ctor_get(v_a_2216_, 5);
v_openDecls_2523_ = lean_ctor_get(v_a_2216_, 6);
v_initHeartbeats_2524_ = lean_ctor_get(v_a_2216_, 7);
v_maxHeartbeats_2525_ = lean_ctor_get(v_a_2216_, 8);
v_currMacroScope_2526_ = lean_ctor_get(v_a_2216_, 9);
v_diag_2527_ = lean_ctor_get_uint8(v_a_2216_, sizeof(void*)*10);
v_suppressElabErrors_2528_ = lean_ctor_get_uint8(v_a_2216_, sizeof(void*)*10 + 1);
v_ref_2529_ = l_Lean_replaceRef(v_p_2208_, v_ref_2521_);
lean_inc(v_currMacroScope_2526_);
lean_inc(v_maxHeartbeats_2525_);
lean_inc(v_initHeartbeats_2524_);
lean_inc(v_openDecls_2523_);
lean_inc(v_currNamespace_2522_);
lean_inc(v_maxRecDepth_2520_);
lean_inc(v_currRecDepth_2519_);
lean_inc_ref(v_options_2518_);
lean_inc_ref(v_toCold_2517_);
v___x_2530_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2530_, 0, v_toCold_2517_);
lean_ctor_set(v___x_2530_, 1, v_options_2518_);
lean_ctor_set(v___x_2530_, 2, v_currRecDepth_2519_);
lean_ctor_set(v___x_2530_, 3, v_maxRecDepth_2520_);
lean_ctor_set(v___x_2530_, 4, v_ref_2529_);
lean_ctor_set(v___x_2530_, 5, v_currNamespace_2522_);
lean_ctor_set(v___x_2530_, 6, v_openDecls_2523_);
lean_ctor_set(v___x_2530_, 7, v_initHeartbeats_2524_);
lean_ctor_set(v___x_2530_, 8, v_maxHeartbeats_2525_);
lean_ctor_set(v___x_2530_, 9, v_currMacroScope_2526_);
lean_ctor_set_uint8(v___x_2530_, sizeof(void*)*10, v_diag_2527_);
lean_ctor_set_uint8(v___x_2530_, sizeof(void*)*10 + 1, v_suppressElabErrors_2528_);
v___x_2531_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2207_, v___x_2530_, v_a_2217_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_dec_ref_known(v___x_2531_, 1);
if (lean_obj_tag(v_mod_x3f_2209_) == 1)
{
lean_object* v_val_2532_; lean_object* v___x_2533_; 
v_val_2532_ = lean_ctor_get(v_mod_x3f_2209_, 0);
lean_inc(v_val_2532_);
v___x_2533_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2532_, v___x_2530_, v_a_2217_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
switch(lean_obj_tag(v_a_2534_))
{
case 0:
{
lean_object* v_k_2552_; 
v_k_2552_ = lean_ctor_get(v_a_2534_, 0);
lean_inc(v_k_2552_);
lean_dec_ref_known(v_a_2534_, 1);
if (lean_obj_tag(v_k_2552_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2209_, 1);
lean_dec(v_term_2210_);
lean_dec(v_p_2208_);
lean_dec_ref(v_params_2207_);
v___y_2536_ = v_a_2212_;
v___y_2537_ = v_a_2213_;
v___y_2538_ = v_a_2214_;
v___y_2539_ = v_a_2215_;
v___y_2540_ = v___x_2530_;
v___y_2541_ = v_a_2217_;
goto v___jp_2535_;
}
else
{
v_kind_2444_ = v_k_2552_;
v___y_2445_ = v_a_2212_;
v___y_2446_ = v_a_2213_;
v___y_2447_ = v_a_2214_;
v___y_2448_ = v_a_2215_;
v___y_2449_ = v___x_2530_;
v___y_2450_ = v_a_2217_;
goto v___jp_2443_;
}
}
case 1:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref_known(v_a_2534_, 0);
lean_dec_ref_known(v_mod_x3f_2209_, 1);
lean_dec(v_term_2210_);
lean_dec(v_p_2208_);
lean_dec_ref(v_params_2207_);
v___x_2553_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2554_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2553_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v___x_2530_, v_a_2217_);
lean_dec_ref_known(v___x_2530_, 10);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
case 3:
{
v___y_2510_ = v_a_2212_;
v___y_2511_ = v_a_2213_;
v___y_2512_ = v_a_2214_;
v___y_2513_ = v_a_2215_;
v___y_2514_ = v___x_2530_;
v___y_2515_ = v_a_2217_;
goto v___jp_2509_;
}
case 5:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref_known(v_a_2534_, 1);
lean_dec_ref_known(v_mod_x3f_2209_, 1);
lean_dec(v_term_2210_);
lean_dec(v_p_2208_);
lean_dec_ref(v_params_2207_);
v___x_2563_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2564_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2563_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v___x_2530_, v_a_2217_);
lean_dec_ref_known(v___x_2530_, 10);
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
case 8:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_dec_ref_known(v_a_2534_, 0);
lean_dec_ref_known(v_mod_x3f_2209_, 1);
lean_dec(v_term_2210_);
lean_dec(v_p_2208_);
lean_dec_ref(v_params_2207_);
v___x_2573_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2574_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2573_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v___x_2530_, v_a_2217_);
lean_dec_ref_known(v___x_2530_, 10);
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
default: 
{
lean_dec(v_a_2534_);
lean_dec_ref_known(v_mod_x3f_2209_, 1);
lean_dec(v_term_2210_);
lean_dec(v_p_2208_);
lean_dec_ref(v_params_2207_);
v___y_2536_ = v_a_2212_;
v___y_2537_ = v_a_2213_;
v___y_2538_ = v_a_2214_;
v___y_2539_ = v_a_2215_;
v___y_2540_ = v___x_2530_;
v___y_2541_ = v_a_2217_;
goto v___jp_2535_;
}
}
v___jp_2535_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v___x_2542_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2543_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2542_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec_ref(v___y_2540_);
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
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec_ref_known(v_mod_x3f_2209_, 1);
lean_dec_ref_known(v___x_2530_, 10);
lean_dec(v_term_2210_);
lean_dec(v_p_2208_);
lean_dec_ref(v_params_2207_);
v_a_2583_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2533_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2533_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
v___y_2510_ = v_a_2212_;
v___y_2511_ = v_a_2213_;
v___y_2512_ = v_a_2214_;
v___y_2513_ = v_a_2215_;
v___y_2514_ = v___x_2530_;
v___y_2515_ = v_a_2217_;
goto v___jp_2509_;
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref_known(v___x_2530_, 10);
lean_dec(v_term_2210_);
lean_dec(v_mod_x3f_2209_);
lean_dec(v_p_2208_);
lean_dec_ref(v_params_2207_);
v_a_2591_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2531_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2531_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
v___jp_2219_:
{
lean_object* v___x_2236_; 
lean_inc(v___y_2235_);
lean_inc(v___y_2233_);
lean_inc_ref(v___y_2232_);
v___x_2236_ = lean_apply_7(v___y_2223_, v___y_2225_, v___y_2229_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, lean_box(0));
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2246_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2241_ = l_Lean_PersistentArray_push___redArg(v___y_2221_, v_a_2237_);
v___x_2242_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2242_, 0, v___y_2224_);
lean_ctor_set(v___x_2242_, 1, v___y_2228_);
lean_ctor_set(v___x_2242_, 2, v___x_2241_);
lean_ctor_set(v___x_2242_, 3, v___y_2220_);
lean_ctor_set(v___x_2242_, 4, v___y_2230_);
lean_ctor_set(v___x_2242_, 5, v___y_2226_);
lean_ctor_set(v___x_2242_, 6, v___y_2222_);
lean_ctor_set(v___x_2242_, 7, v___y_2231_);
lean_ctor_set(v___x_2242_, 8, v___y_2227_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2242_);
v___x_2244_ = v___x_2239_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v___y_2220_);
v_a_2247_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2236_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2236_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
v___jp_2255_:
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2211_, v___y_2270_, v___y_2265_, v___y_2269_, v___y_2258_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_dec_ref_known(v___x_2272_, 1);
v___y_2220_ = v___y_2256_;
v___y_2221_ = v___y_2267_;
v___y_2222_ = v___y_2257_;
v___y_2223_ = v___y_2268_;
v___y_2224_ = v___y_2259_;
v___y_2225_ = v___y_2260_;
v___y_2226_ = v___y_2261_;
v___y_2227_ = v___y_2262_;
v___y_2228_ = v___y_2264_;
v___y_2229_ = v___y_2263_;
v___y_2230_ = v___y_2271_;
v___y_2231_ = v___y_2266_;
v___y_2232_ = v___y_2270_;
v___y_2233_ = v___y_2265_;
v___y_2234_ = v___y_2269_;
v___y_2235_ = v___y_2258_;
goto v___jp_2219_;
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v___y_2271_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___y_2256_);
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
v___jp_2281_:
{
lean_object* v_config_2283_; lean_object* v_extensions_2284_; lean_object* v_extra_2285_; lean_object* v_extraInj_2286_; lean_object* v_extraFacts_2287_; lean_object* v_symPrios_2288_; lean_object* v_norm_2289_; lean_object* v_normProcs_2290_; lean_object* v_anchorRefs_x3f_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2300_; 
v_config_2283_ = lean_ctor_get(v_params_2207_, 0);
v_extensions_2284_ = lean_ctor_get(v_params_2207_, 1);
v_extra_2285_ = lean_ctor_get(v_params_2207_, 2);
v_extraInj_2286_ = lean_ctor_get(v_params_2207_, 3);
v_extraFacts_2287_ = lean_ctor_get(v_params_2207_, 4);
v_symPrios_2288_ = lean_ctor_get(v_params_2207_, 5);
v_norm_2289_ = lean_ctor_get(v_params_2207_, 6);
v_normProcs_2290_ = lean_ctor_get(v_params_2207_, 7);
v_anchorRefs_x3f_2291_ = lean_ctor_get(v_params_2207_, 8);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_params_2207_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2293_ = v_params_2207_;
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_anchorRefs_x3f_2291_);
lean_inc(v_normProcs_2290_);
lean_inc(v_norm_2289_);
lean_inc(v_symPrios_2288_);
lean_inc(v_extraFacts_2287_);
lean_inc(v_extraInj_2286_);
lean_inc(v_extra_2285_);
lean_inc(v_extensions_2284_);
lean_inc(v_config_2283_);
lean_dec(v_params_2207_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2295_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2287_, v___y_2282_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 4, v___x_2295_);
v___x_2297_ = v___x_2293_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_config_2283_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_extensions_2284_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v_extra_2285_);
lean_ctor_set(v_reuseFailAlloc_2299_, 3, v_extraInj_2286_);
lean_ctor_set(v_reuseFailAlloc_2299_, 4, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2299_, 5, v_symPrios_2288_);
lean_ctor_set(v_reuseFailAlloc_2299_, 6, v_norm_2289_);
lean_ctor_set(v_reuseFailAlloc_2299_, 7, v_normProcs_2290_);
lean_ctor_set(v_reuseFailAlloc_2299_, 8, v_anchorRefs_x3f_2291_);
v___x_2297_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
}
}
v___jp_2301_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2311_ = lean_array_get_size(v___y_2302_);
lean_dec_ref(v___y_2302_);
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_nat_dec_eq(v___x_2311_, v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v___y_2304_);
lean_dec_ref(v_params_2207_);
v___x_2314_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2315_ = l_Lean_indentExpr(v___y_2303_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2316_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec_ref(v___y_2309_);
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
else
{
lean_dec_ref(v___y_2309_);
lean_dec_ref(v___y_2303_);
v___y_2282_ = v___y_2304_;
goto v___jp_2281_;
}
}
v___jp_2326_:
{
uint8_t v___x_2338_; 
v___x_2338_ = l_Lean_Expr_isForall(v___y_2329_);
if (v___x_2338_ == 0)
{
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2328_);
if (lean_obj_tag(v_mod_x3f_2209_) == 0)
{
v___y_2302_ = v___y_2327_;
v___y_2303_ = v___y_2329_;
v___y_2304_ = v___y_2331_;
v___y_2305_ = v___y_2332_;
v___y_2306_ = v___y_2333_;
v___y_2307_ = v___y_2334_;
v___y_2308_ = v___y_2335_;
v___y_2309_ = v___y_2336_;
v___y_2310_ = v___y_2337_;
goto v___jp_2301_;
}
else
{
lean_dec_ref_known(v_mod_x3f_2209_, 1);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v___y_2331_);
lean_dec_ref(v___y_2327_);
lean_dec_ref(v_params_2207_);
v___x_2339_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2340_ = l_Lean_indentExpr(v___y_2329_);
v___x_2341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2341_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec_ref(v___y_2336_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
else
{
v___y_2302_ = v___y_2327_;
v___y_2303_ = v___y_2329_;
v___y_2304_ = v___y_2331_;
v___y_2305_ = v___y_2332_;
v___y_2306_ = v___y_2333_;
v___y_2307_ = v___y_2334_;
v___y_2308_ = v___y_2335_;
v___y_2309_ = v___y_2336_;
v___y_2310_ = v___y_2337_;
goto v___jp_2301_;
}
}
}
else
{
lean_object* v_extra_2351_; 
lean_dec_ref(v___y_2331_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v___y_2327_);
lean_dec(v_mod_x3f_2209_);
v_extra_2351_ = lean_ctor_get(v_params_2207_, 2);
lean_inc_ref(v_extra_2351_);
if (lean_obj_tag(v___y_2330_) == 2)
{
lean_object* v_config_2352_; lean_object* v_extensions_2353_; lean_object* v_extraInj_2354_; lean_object* v_extraFacts_2355_; lean_object* v_symPrios_2356_; lean_object* v_norm_2357_; lean_object* v_normProcs_2358_; lean_object* v_anchorRefs_x3f_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2414_; 
v_config_2352_ = lean_ctor_get(v_params_2207_, 0);
v_extensions_2353_ = lean_ctor_get(v_params_2207_, 1);
v_extraInj_2354_ = lean_ctor_get(v_params_2207_, 3);
v_extraFacts_2355_ = lean_ctor_get(v_params_2207_, 4);
v_symPrios_2356_ = lean_ctor_get(v_params_2207_, 5);
v_norm_2357_ = lean_ctor_get(v_params_2207_, 6);
v_normProcs_2358_ = lean_ctor_get(v_params_2207_, 7);
v_anchorRefs_x3f_2359_ = lean_ctor_get(v_params_2207_, 8);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_params_2207_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v_params_2207_, 2);
lean_dec(v_unused_2415_);
v___x_2361_ = v_params_2207_;
v_isShared_2362_ = v_isSharedCheck_2414_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_anchorRefs_x3f_2359_);
lean_inc(v_normProcs_2358_);
lean_inc(v_norm_2357_);
lean_inc(v_symPrios_2356_);
lean_inc(v_extraFacts_2355_);
lean_inc(v_extraInj_2354_);
lean_inc(v_extensions_2353_);
lean_inc(v_config_2352_);
lean_dec(v_params_2207_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2414_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_size_2363_; uint8_t v_gen_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2413_; 
v_size_2363_ = lean_ctor_get(v_extra_2351_, 2);
v_gen_2364_ = lean_ctor_get_uint8(v___y_2330_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___y_2330_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2366_ = v___y_2330_;
v_isShared_2367_ = v_isSharedCheck_2413_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v___y_2330_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2413_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; 
v___x_2368_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2211_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v___x_2370_; 
lean_dec_ref_known(v___x_2368_, 1);
if (v_isShared_2367_ == 0)
{
lean_ctor_set_tag(v___x_2366_, 0);
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2404_, 0, v_gen_2364_);
v___x_2370_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2371_; 
lean_inc_ref(v___y_2328_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2336_);
lean_inc(v___y_2335_);
lean_inc_ref(v___y_2334_);
lean_inc(v_size_2363_);
v___x_2371_ = lean_apply_7(v___y_2328_, v___x_2370_, v_size_2363_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, lean_box(0));
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2373_, 0, v_gen_2364_);
lean_inc(v___y_2337_);
lean_inc(v___y_2335_);
lean_inc_ref(v___y_2334_);
lean_inc(v_size_2363_);
v___x_2374_ = lean_apply_7(v___y_2328_, v___x_2373_, v_size_2363_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, lean_box(0));
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2387_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2387_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2387_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2379_ = l_Lean_PersistentArray_push___redArg(v_extra_2351_, v_a_2372_);
v___x_2380_ = l_Lean_PersistentArray_push___redArg(v___x_2379_, v_a_2375_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 2, v___x_2380_);
v___x_2382_ = v___x_2361_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_config_2352_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_extensions_2353_);
lean_ctor_set(v_reuseFailAlloc_2386_, 2, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2386_, 3, v_extraInj_2354_);
lean_ctor_set(v_reuseFailAlloc_2386_, 4, v_extraFacts_2355_);
lean_ctor_set(v_reuseFailAlloc_2386_, 5, v_symPrios_2356_);
lean_ctor_set(v_reuseFailAlloc_2386_, 6, v_norm_2357_);
lean_ctor_set(v_reuseFailAlloc_2386_, 7, v_normProcs_2358_);
lean_ctor_set(v_reuseFailAlloc_2386_, 8, v_anchorRefs_x3f_2359_);
v___x_2382_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2384_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2382_);
v___x_2384_ = v___x_2377_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec(v_a_2372_);
lean_del_object(v___x_2361_);
lean_dec(v_anchorRefs_x3f_2359_);
lean_dec_ref(v_normProcs_2358_);
lean_dec_ref(v_norm_2357_);
lean_dec_ref(v_symPrios_2356_);
lean_dec_ref(v_extraFacts_2355_);
lean_dec_ref(v_extraInj_2354_);
lean_dec_ref(v_extensions_2353_);
lean_dec_ref(v_config_2352_);
lean_dec_ref(v_extra_2351_);
v_a_2388_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2374_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2374_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_del_object(v___x_2361_);
lean_dec(v_anchorRefs_x3f_2359_);
lean_dec_ref(v_normProcs_2358_);
lean_dec_ref(v_norm_2357_);
lean_dec_ref(v_symPrios_2356_);
lean_dec_ref(v_extraFacts_2355_);
lean_dec_ref(v_extraInj_2354_);
lean_dec_ref(v_extensions_2353_);
lean_dec_ref(v_config_2352_);
lean_dec_ref(v_extra_2351_);
lean_dec_ref(v___y_2336_);
lean_dec_ref(v___y_2328_);
v_a_2396_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2371_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2371_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_del_object(v___x_2366_);
lean_del_object(v___x_2361_);
lean_dec(v_anchorRefs_x3f_2359_);
lean_dec_ref(v_normProcs_2358_);
lean_dec_ref(v_norm_2357_);
lean_dec_ref(v_symPrios_2356_);
lean_dec_ref(v_extraFacts_2355_);
lean_dec_ref(v_extraInj_2354_);
lean_dec_ref(v_extensions_2353_);
lean_dec_ref(v_config_2352_);
lean_dec_ref(v_extra_2351_);
lean_dec_ref(v___y_2336_);
lean_dec_ref(v___y_2328_);
v_a_2405_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2368_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2368_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
else
{
switch(lean_obj_tag(v___y_2330_))
{
case 0:
{
lean_object* v_config_2416_; lean_object* v_extensions_2417_; lean_object* v_extraInj_2418_; lean_object* v_extraFacts_2419_; lean_object* v_symPrios_2420_; lean_object* v_norm_2421_; lean_object* v_normProcs_2422_; lean_object* v_anchorRefs_x3f_2423_; lean_object* v_size_2424_; 
v_config_2416_ = lean_ctor_get(v_params_2207_, 0);
lean_inc_ref(v_config_2416_);
v_extensions_2417_ = lean_ctor_get(v_params_2207_, 1);
lean_inc_ref(v_extensions_2417_);
v_extraInj_2418_ = lean_ctor_get(v_params_2207_, 3);
lean_inc_ref(v_extraInj_2418_);
v_extraFacts_2419_ = lean_ctor_get(v_params_2207_, 4);
lean_inc_ref(v_extraFacts_2419_);
v_symPrios_2420_ = lean_ctor_get(v_params_2207_, 5);
lean_inc_ref(v_symPrios_2420_);
v_norm_2421_ = lean_ctor_get(v_params_2207_, 6);
lean_inc_ref(v_norm_2421_);
v_normProcs_2422_ = lean_ctor_get(v_params_2207_, 7);
lean_inc_ref(v_normProcs_2422_);
v_anchorRefs_x3f_2423_ = lean_ctor_get(v_params_2207_, 8);
lean_inc(v_anchorRefs_x3f_2423_);
lean_dec_ref(v_params_2207_);
v_size_2424_ = lean_ctor_get(v_extra_2351_, 2);
lean_inc(v_size_2424_);
v___y_2256_ = v_extraInj_2418_;
v___y_2257_ = v_norm_2421_;
v___y_2258_ = v___y_2337_;
v___y_2259_ = v_config_2416_;
v___y_2260_ = v___y_2330_;
v___y_2261_ = v_symPrios_2420_;
v___y_2262_ = v_anchorRefs_x3f_2423_;
v___y_2263_ = v_size_2424_;
v___y_2264_ = v_extensions_2417_;
v___y_2265_ = v___y_2335_;
v___y_2266_ = v_normProcs_2422_;
v___y_2267_ = v_extra_2351_;
v___y_2268_ = v___y_2328_;
v___y_2269_ = v___y_2336_;
v___y_2270_ = v___y_2334_;
v___y_2271_ = v_extraFacts_2419_;
goto v___jp_2255_;
}
case 1:
{
lean_object* v_config_2425_; lean_object* v_extensions_2426_; lean_object* v_extraInj_2427_; lean_object* v_extraFacts_2428_; lean_object* v_symPrios_2429_; lean_object* v_norm_2430_; lean_object* v_normProcs_2431_; lean_object* v_anchorRefs_x3f_2432_; lean_object* v_size_2433_; 
v_config_2425_ = lean_ctor_get(v_params_2207_, 0);
lean_inc_ref(v_config_2425_);
v_extensions_2426_ = lean_ctor_get(v_params_2207_, 1);
lean_inc_ref(v_extensions_2426_);
v_extraInj_2427_ = lean_ctor_get(v_params_2207_, 3);
lean_inc_ref(v_extraInj_2427_);
v_extraFacts_2428_ = lean_ctor_get(v_params_2207_, 4);
lean_inc_ref(v_extraFacts_2428_);
v_symPrios_2429_ = lean_ctor_get(v_params_2207_, 5);
lean_inc_ref(v_symPrios_2429_);
v_norm_2430_ = lean_ctor_get(v_params_2207_, 6);
lean_inc_ref(v_norm_2430_);
v_normProcs_2431_ = lean_ctor_get(v_params_2207_, 7);
lean_inc_ref(v_normProcs_2431_);
v_anchorRefs_x3f_2432_ = lean_ctor_get(v_params_2207_, 8);
lean_inc(v_anchorRefs_x3f_2432_);
lean_dec_ref(v_params_2207_);
v_size_2433_ = lean_ctor_get(v_extra_2351_, 2);
lean_inc(v_size_2433_);
v___y_2256_ = v_extraInj_2427_;
v___y_2257_ = v_norm_2430_;
v___y_2258_ = v___y_2337_;
v___y_2259_ = v_config_2425_;
v___y_2260_ = v___y_2330_;
v___y_2261_ = v_symPrios_2429_;
v___y_2262_ = v_anchorRefs_x3f_2432_;
v___y_2263_ = v_size_2433_;
v___y_2264_ = v_extensions_2426_;
v___y_2265_ = v___y_2335_;
v___y_2266_ = v_normProcs_2431_;
v___y_2267_ = v_extra_2351_;
v___y_2268_ = v___y_2328_;
v___y_2269_ = v___y_2336_;
v___y_2270_ = v___y_2334_;
v___y_2271_ = v_extraFacts_2428_;
goto v___jp_2255_;
}
default: 
{
lean_object* v_config_2434_; lean_object* v_extensions_2435_; lean_object* v_extraInj_2436_; lean_object* v_extraFacts_2437_; lean_object* v_symPrios_2438_; lean_object* v_norm_2439_; lean_object* v_normProcs_2440_; lean_object* v_anchorRefs_x3f_2441_; lean_object* v_size_2442_; 
v_config_2434_ = lean_ctor_get(v_params_2207_, 0);
lean_inc_ref(v_config_2434_);
v_extensions_2435_ = lean_ctor_get(v_params_2207_, 1);
lean_inc_ref(v_extensions_2435_);
v_extraInj_2436_ = lean_ctor_get(v_params_2207_, 3);
lean_inc_ref(v_extraInj_2436_);
v_extraFacts_2437_ = lean_ctor_get(v_params_2207_, 4);
lean_inc_ref(v_extraFacts_2437_);
v_symPrios_2438_ = lean_ctor_get(v_params_2207_, 5);
lean_inc_ref(v_symPrios_2438_);
v_norm_2439_ = lean_ctor_get(v_params_2207_, 6);
lean_inc_ref(v_norm_2439_);
v_normProcs_2440_ = lean_ctor_get(v_params_2207_, 7);
lean_inc_ref(v_normProcs_2440_);
v_anchorRefs_x3f_2441_ = lean_ctor_get(v_params_2207_, 8);
lean_inc(v_anchorRefs_x3f_2441_);
lean_dec_ref(v_params_2207_);
v_size_2442_ = lean_ctor_get(v_extra_2351_, 2);
lean_inc(v_size_2442_);
v___y_2220_ = v_extraInj_2436_;
v___y_2221_ = v_extra_2351_;
v___y_2222_ = v_norm_2439_;
v___y_2223_ = v___y_2328_;
v___y_2224_ = v_config_2434_;
v___y_2225_ = v___y_2330_;
v___y_2226_ = v_symPrios_2438_;
v___y_2227_ = v_anchorRefs_x3f_2441_;
v___y_2228_ = v_extensions_2435_;
v___y_2229_ = v_size_2442_;
v___y_2230_ = v_extraFacts_2437_;
v___y_2231_ = v_normProcs_2440_;
v___y_2232_ = v___y_2334_;
v___y_2233_ = v___y_2335_;
v___y_2234_ = v___y_2336_;
v___y_2235_ = v___y_2337_;
goto v___jp_2219_;
}
}
}
}
}
v___jp_2443_:
{
lean_object* v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___f_2454_; lean_object* v___x_2455_; 
v___x_2451_ = lean_box(0);
v___x_2452_ = 1;
v___x_2453_ = lean_box(v___x_2452_);
lean_inc(v_p_2208_);
v___f_2454_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2454_, 0, v_p_2208_);
lean_closure_set(v___f_2454_, 1, v_term_2210_);
lean_closure_set(v___f_2454_, 2, v___x_2451_);
lean_closure_set(v___f_2454_, 3, v___x_2453_);
v___x_2455_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2454_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2500_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2500_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2500_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
if (lean_obj_tag(v_a_2456_) == 1)
{
lean_object* v_val_2460_; lean_object* v_fst_2461_; lean_object* v_snd_2462_; lean_object* v___x_2463_; 
lean_del_object(v___x_2458_);
v_val_2460_ = lean_ctor_get(v_a_2456_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v_a_2456_, 1);
v_fst_2461_ = lean_ctor_get(v_val_2460_, 0);
lean_inc(v_fst_2461_);
v_snd_2462_ = lean_ctor_get(v_val_2460_, 1);
lean_inc_n(v_snd_2462_, 2);
lean_dec(v_val_2460_);
lean_inc(v___y_2450_);
lean_inc_ref(v___y_2449_);
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
v___x_2463_ = lean_infer_type(v_snd_2462_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2465_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc_n(v_a_2464_, 2);
lean_dec_ref_known(v___x_2463_, 1);
v___x_2465_ = l_Lean_Meta_isProp(v_a_2464_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___f_2469_; uint8_t v___x_2470_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = lean_box(v___x_2452_);
v___x_2468_ = lean_box(v_minIndexable_2211_);
lean_inc(v_snd_2462_);
lean_inc(v_fst_2461_);
lean_inc_ref(v_params_2207_);
v___f_2469_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2469_, 0, v_params_2207_);
lean_closure_set(v___f_2469_, 1, v_p_2208_);
lean_closure_set(v___f_2469_, 2, v_fst_2461_);
lean_closure_set(v___f_2469_, 3, v_snd_2462_);
lean_closure_set(v___f_2469_, 4, v___x_2467_);
lean_closure_set(v___f_2469_, 5, v___x_2468_);
v___x_2470_ = lean_unbox(v_a_2466_);
lean_dec(v_a_2466_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v___f_2469_);
lean_dec(v_a_2464_);
lean_dec(v_snd_2462_);
lean_dec(v_fst_2461_);
lean_dec(v_kind_2444_);
lean_dec(v_mod_x3f_2209_);
lean_dec_ref(v_params_2207_);
v___x_2471_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2472_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2471_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec_ref(v___y_2449_);
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
else
{
v___y_2327_ = v_fst_2461_;
v___y_2328_ = v___f_2469_;
v___y_2329_ = v_a_2464_;
v___y_2330_ = v_kind_2444_;
v___y_2331_ = v_snd_2462_;
v___y_2332_ = v___y_2445_;
v___y_2333_ = v___y_2446_;
v___y_2334_ = v___y_2447_;
v___y_2335_ = v___y_2448_;
v___y_2336_ = v___y_2449_;
v___y_2337_ = v___y_2450_;
goto v___jp_2326_;
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_a_2464_);
lean_dec(v_snd_2462_);
lean_dec(v_fst_2461_);
lean_dec_ref(v___y_2449_);
lean_dec(v_kind_2444_);
lean_dec(v_mod_x3f_2209_);
lean_dec(v_p_2208_);
lean_dec_ref(v_params_2207_);
v_a_2481_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2465_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2465_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec(v_snd_2462_);
lean_dec(v_fst_2461_);
lean_dec_ref(v___y_2449_);
lean_dec(v_kind_2444_);
lean_dec(v_mod_x3f_2209_);
lean_dec(v_p_2208_);
lean_dec_ref(v_params_2207_);
v_a_2489_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2463_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2463_);
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
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_2498_; 
lean_dec(v_a_2456_);
lean_dec_ref(v___y_2449_);
lean_dec(v_kind_2444_);
lean_dec(v_mod_x3f_2209_);
lean_dec(v_p_2208_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v_params_2207_);
v___x_2498_ = v___x_2458_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_params_2207_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec_ref(v___y_2449_);
lean_dec(v_kind_2444_);
lean_dec(v_mod_x3f_2209_);
lean_dec(v_p_2208_);
lean_dec_ref(v_params_2207_);
v_a_2501_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2455_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2455_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
v___jp_2509_:
{
lean_object* v___x_2516_; 
v___x_2516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_kind_2444_ = v___x_2516_;
v___y_2445_ = v___y_2510_;
v___y_2446_ = v___y_2511_;
v___y_2447_ = v___y_2512_;
v___y_2448_ = v___y_2513_;
v___y_2449_ = v___y_2514_;
v___y_2450_ = v___y_2515_;
goto v___jp_2443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2599_, lean_object* v_p_2600_, lean_object* v_mod_x3f_2601_, lean_object* v_term_2602_, lean_object* v_minIndexable_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
uint8_t v_minIndexable_boxed_2611_; lean_object* v_res_2612_; 
v_minIndexable_boxed_2611_ = lean_unbox(v_minIndexable_2603_);
v_res_2612_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2599_, v_p_2600_, v_mod_x3f_2601_, v_term_2602_, v_minIndexable_boxed_2611_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec_ref(v_a_2604_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object* v_00_u03b1_2613_, lean_object* v_msg_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v_00_u03b1_2623_, lean_object* v_msg_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v_00_u03b1_2623_, v_msg_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object* v_msgData_2633_, lean_object* v_macroStack_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2633_, v_macroStack_2634_, v___y_2639_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object* v_msgData_2643_, lean_object* v_macroStack_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(v_msgData_2643_, v_macroStack_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2653_, lean_object* v_val_2654_, lean_object* v___x_2655_, lean_object* v_____r_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; lean_object* v_ext_2665_; lean_object* v_toEnvExtension_2666_; lean_object* v_env_2667_; lean_object* v_config_2668_; lean_object* v_extensions_2669_; lean_object* v_extra_2670_; lean_object* v_extraInj_2671_; lean_object* v_extraFacts_2672_; lean_object* v_symPrios_2673_; lean_object* v_norm_2674_; lean_object* v_normProcs_2675_; lean_object* v_anchorRefs_x3f_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2688_; 
v___x_2664_ = lean_st_ref_get(v___y_2662_);
v_ext_2665_ = lean_ctor_get(v_val_2654_, 1);
v_toEnvExtension_2666_ = lean_ctor_get(v_ext_2665_, 0);
v_env_2667_ = lean_ctor_get(v___x_2664_, 0);
lean_inc_ref(v_env_2667_);
lean_dec(v___x_2664_);
v_config_2668_ = lean_ctor_get(v_params_2653_, 0);
v_extensions_2669_ = lean_ctor_get(v_params_2653_, 1);
v_extra_2670_ = lean_ctor_get(v_params_2653_, 2);
v_extraInj_2671_ = lean_ctor_get(v_params_2653_, 3);
v_extraFacts_2672_ = lean_ctor_get(v_params_2653_, 4);
v_symPrios_2673_ = lean_ctor_get(v_params_2653_, 5);
v_norm_2674_ = lean_ctor_get(v_params_2653_, 6);
v_normProcs_2675_ = lean_ctor_get(v_params_2653_, 7);
v_anchorRefs_x3f_2676_ = lean_ctor_get(v_params_2653_, 8);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_params_2653_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2678_ = v_params_2653_;
v_isShared_2679_ = v_isSharedCheck_2688_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_anchorRefs_x3f_2676_);
lean_inc(v_normProcs_2675_);
lean_inc(v_norm_2674_);
lean_inc(v_symPrios_2673_);
lean_inc(v_extraFacts_2672_);
lean_inc(v_extraInj_2671_);
lean_inc(v_extra_2670_);
lean_inc(v_extensions_2669_);
lean_inc(v_config_2668_);
lean_dec(v_params_2653_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2688_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v_asyncMode_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v_asyncMode_2680_ = lean_ctor_get(v_toEnvExtension_2666_, 2);
v___x_2681_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2655_, v_val_2654_, v_env_2667_, v_asyncMode_2680_);
v___x_2682_ = lean_array_push(v_extensions_2669_, v___x_2681_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2682_);
v___x_2684_ = v___x_2678_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_config_2668_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_extra_2670_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v_extraInj_2671_);
lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_extraFacts_2672_);
lean_ctor_set(v_reuseFailAlloc_2687_, 5, v_symPrios_2673_);
lean_ctor_set(v_reuseFailAlloc_2687_, 6, v_norm_2674_);
lean_ctor_set(v_reuseFailAlloc_2687_, 7, v_normProcs_2675_);
lean_ctor_set(v_reuseFailAlloc_2687_, 8, v_anchorRefs_x3f_2676_);
v___x_2684_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
return v___x_2686_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2689_, lean_object* v_val_2690_, lean_object* v___x_2691_, lean_object* v_____r_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2689_, v_val_2690_, v___x_2691_, v_____r_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec_ref(v___x_2691_);
lean_dec_ref(v_val_2690_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2701_, lean_object* v_id_2702_, uint8_t v_minIndexable_2703_, lean_object* v_as_x27_2704_, lean_object* v_b_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
if (lean_obj_tag(v_as_x27_2704_) == 0)
{
lean_object* v___x_2711_; 
lean_dec(v_id_2702_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v_b_2705_);
return v___x_2711_;
}
else
{
lean_object* v_head_2712_; lean_object* v_tail_2713_; lean_object* v_toCold_2714_; lean_object* v_options_2715_; lean_object* v_currRecDepth_2716_; lean_object* v_maxRecDepth_2717_; lean_object* v_ref_2718_; lean_object* v_currNamespace_2719_; lean_object* v_openDecls_2720_; lean_object* v_initHeartbeats_2721_; lean_object* v_maxHeartbeats_2722_; lean_object* v_currMacroScope_2723_; uint8_t v_diag_2724_; uint8_t v_suppressElabErrors_2725_; uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v_ref_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_head_2712_ = lean_ctor_get(v_as_x27_2704_, 0);
v_tail_2713_ = lean_ctor_get(v_as_x27_2704_, 1);
v_toCold_2714_ = lean_ctor_get(v___y_2708_, 0);
v_options_2715_ = lean_ctor_get(v___y_2708_, 1);
v_currRecDepth_2716_ = lean_ctor_get(v___y_2708_, 2);
v_maxRecDepth_2717_ = lean_ctor_get(v___y_2708_, 3);
v_ref_2718_ = lean_ctor_get(v___y_2708_, 4);
v_currNamespace_2719_ = lean_ctor_get(v___y_2708_, 5);
v_openDecls_2720_ = lean_ctor_get(v___y_2708_, 6);
v_initHeartbeats_2721_ = lean_ctor_get(v___y_2708_, 7);
v_maxHeartbeats_2722_ = lean_ctor_get(v___y_2708_, 8);
v_currMacroScope_2723_ = lean_ctor_get(v___y_2708_, 9);
v_diag_2724_ = lean_ctor_get_uint8(v___y_2708_, sizeof(void*)*10);
v_suppressElabErrors_2725_ = lean_ctor_get_uint8(v___y_2708_, sizeof(void*)*10 + 1);
v___x_2726_ = 0;
v___x_2727_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_2728_ = l_Lean_replaceRef(v_p_2701_, v_ref_2718_);
lean_inc(v_currMacroScope_2723_);
lean_inc(v_maxHeartbeats_2722_);
lean_inc(v_initHeartbeats_2721_);
lean_inc(v_openDecls_2720_);
lean_inc(v_currNamespace_2719_);
lean_inc(v_maxRecDepth_2717_);
lean_inc(v_currRecDepth_2716_);
lean_inc_ref(v_options_2715_);
lean_inc_ref(v_toCold_2714_);
v___x_2729_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2729_, 0, v_toCold_2714_);
lean_ctor_set(v___x_2729_, 1, v_options_2715_);
lean_ctor_set(v___x_2729_, 2, v_currRecDepth_2716_);
lean_ctor_set(v___x_2729_, 3, v_maxRecDepth_2717_);
lean_ctor_set(v___x_2729_, 4, v_ref_2728_);
lean_ctor_set(v___x_2729_, 5, v_currNamespace_2719_);
lean_ctor_set(v___x_2729_, 6, v_openDecls_2720_);
lean_ctor_set(v___x_2729_, 7, v_initHeartbeats_2721_);
lean_ctor_set(v___x_2729_, 8, v_maxHeartbeats_2722_);
lean_ctor_set(v___x_2729_, 9, v_currMacroScope_2723_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*10, v_diag_2724_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*10 + 1, v_suppressElabErrors_2725_);
lean_inc(v_head_2712_);
lean_inc(v_id_2702_);
v___x_2730_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2705_, v_id_2702_, v_head_2712_, v___x_2727_, v_minIndexable_2703_, v___x_2726_, v___x_2726_, v___y_2706_, v___y_2707_, v___x_2729_, v___y_2709_);
lean_dec_ref_known(v___x_2729_, 10);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v_as_x27_2704_ = v_tail_2713_;
v_b_2705_ = v_a_2731_;
goto _start;
}
else
{
lean_dec(v_id_2702_);
return v___x_2730_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2733_, lean_object* v_id_2734_, lean_object* v_minIndexable_2735_, lean_object* v_as_x27_2736_, lean_object* v_b_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
uint8_t v_minIndexable_boxed_2743_; lean_object* v_res_2744_; 
v_minIndexable_boxed_2743_ = lean_unbox(v_minIndexable_2735_);
v_res_2744_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2733_, v_id_2734_, v_minIndexable_boxed_2743_, v_as_x27_2736_, v_b_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v_as_x27_2736_);
lean_dec(v_p_2733_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
if (lean_obj_tag(v_a_2746_) == 0)
{
lean_object* v___x_2748_; 
v___x_2748_ = l_List_reverse___redArg(v_a_2747_);
return v___x_2748_;
}
else
{
lean_object* v_head_2749_; lean_object* v_tail_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2761_; 
v_head_2749_ = lean_ctor_get(v_a_2746_, 0);
v_tail_2750_ = lean_ctor_get(v_a_2746_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_a_2746_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2752_ = v_a_2746_;
v_isShared_2753_ = v_isSharedCheck_2761_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_tail_2750_);
lean_inc(v_head_2749_);
lean_dec(v_a_2746_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2761_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v_kind_2754_; uint8_t v___x_2755_; 
v_kind_2754_ = lean_ctor_get(v_head_2749_, 6);
v___x_2755_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2754_, v_k_2745_);
if (v___x_2755_ == 0)
{
lean_del_object(v___x_2752_);
lean_dec(v_head_2749_);
v_a_2746_ = v_tail_2750_;
goto _start;
}
else
{
lean_object* v___x_2758_; 
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 1, v_a_2747_);
v___x_2758_ = v___x_2752_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_head_2749_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v_a_2747_);
v___x_2758_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
v_a_2746_ = v_tail_2750_;
v_a_2747_ = v___x_2758_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2762_, v_a_2763_, v_a_2764_);
lean_dec(v_k_2762_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_2766_, lean_object* v_msg_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_toCold_2775_; lean_object* v_options_2776_; lean_object* v_currRecDepth_2777_; lean_object* v_maxRecDepth_2778_; lean_object* v_ref_2779_; lean_object* v_currNamespace_2780_; lean_object* v_openDecls_2781_; lean_object* v_initHeartbeats_2782_; lean_object* v_maxHeartbeats_2783_; lean_object* v_currMacroScope_2784_; uint8_t v_diag_2785_; uint8_t v_suppressElabErrors_2786_; lean_object* v_ref_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_toCold_2775_ = lean_ctor_get(v___y_2772_, 0);
v_options_2776_ = lean_ctor_get(v___y_2772_, 1);
v_currRecDepth_2777_ = lean_ctor_get(v___y_2772_, 2);
v_maxRecDepth_2778_ = lean_ctor_get(v___y_2772_, 3);
v_ref_2779_ = lean_ctor_get(v___y_2772_, 4);
v_currNamespace_2780_ = lean_ctor_get(v___y_2772_, 5);
v_openDecls_2781_ = lean_ctor_get(v___y_2772_, 6);
v_initHeartbeats_2782_ = lean_ctor_get(v___y_2772_, 7);
v_maxHeartbeats_2783_ = lean_ctor_get(v___y_2772_, 8);
v_currMacroScope_2784_ = lean_ctor_get(v___y_2772_, 9);
v_diag_2785_ = lean_ctor_get_uint8(v___y_2772_, sizeof(void*)*10);
v_suppressElabErrors_2786_ = lean_ctor_get_uint8(v___y_2772_, sizeof(void*)*10 + 1);
v_ref_2787_ = l_Lean_replaceRef(v_ref_2766_, v_ref_2779_);
lean_inc(v_currMacroScope_2784_);
lean_inc(v_maxHeartbeats_2783_);
lean_inc(v_initHeartbeats_2782_);
lean_inc(v_openDecls_2781_);
lean_inc(v_currNamespace_2780_);
lean_inc(v_maxRecDepth_2778_);
lean_inc(v_currRecDepth_2777_);
lean_inc_ref(v_options_2776_);
lean_inc_ref(v_toCold_2775_);
v___x_2788_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2788_, 0, v_toCold_2775_);
lean_ctor_set(v___x_2788_, 1, v_options_2776_);
lean_ctor_set(v___x_2788_, 2, v_currRecDepth_2777_);
lean_ctor_set(v___x_2788_, 3, v_maxRecDepth_2778_);
lean_ctor_set(v___x_2788_, 4, v_ref_2787_);
lean_ctor_set(v___x_2788_, 5, v_currNamespace_2780_);
lean_ctor_set(v___x_2788_, 6, v_openDecls_2781_);
lean_ctor_set(v___x_2788_, 7, v_initHeartbeats_2782_);
lean_ctor_set(v___x_2788_, 8, v_maxHeartbeats_2783_);
lean_ctor_set(v___x_2788_, 9, v_currMacroScope_2784_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*10, v_diag_2785_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*10 + 1, v_suppressElabErrors_2786_);
v___x_2789_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___x_2788_, v___y_2773_);
lean_dec_ref_known(v___x_2788_, 10);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_2790_, lean_object* v_msg_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_2790_, v_msg_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v_ref_2790_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_2800_, lean_object* v_id_2801_, uint8_t v_minIndexable_2802_, lean_object* v_as_x27_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
if (lean_obj_tag(v_as_x27_2803_) == 0)
{
lean_object* v___x_2810_; 
lean_dec(v_id_2801_);
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_b_2804_);
return v___x_2810_;
}
else
{
lean_object* v_head_2811_; lean_object* v_tail_2812_; lean_object* v_toCold_2813_; lean_object* v_options_2814_; lean_object* v_currRecDepth_2815_; lean_object* v_maxRecDepth_2816_; lean_object* v_ref_2817_; lean_object* v_currNamespace_2818_; lean_object* v_openDecls_2819_; lean_object* v_initHeartbeats_2820_; lean_object* v_maxHeartbeats_2821_; lean_object* v_currMacroScope_2822_; uint8_t v_diag_2823_; uint8_t v_suppressElabErrors_2824_; uint8_t v___x_2825_; uint8_t v___x_2826_; lean_object* v___x_2827_; lean_object* v_ref_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_head_2811_ = lean_ctor_get(v_as_x27_2803_, 0);
v_tail_2812_ = lean_ctor_get(v_as_x27_2803_, 1);
v_toCold_2813_ = lean_ctor_get(v___y_2807_, 0);
v_options_2814_ = lean_ctor_get(v___y_2807_, 1);
v_currRecDepth_2815_ = lean_ctor_get(v___y_2807_, 2);
v_maxRecDepth_2816_ = lean_ctor_get(v___y_2807_, 3);
v_ref_2817_ = lean_ctor_get(v___y_2807_, 4);
v_currNamespace_2818_ = lean_ctor_get(v___y_2807_, 5);
v_openDecls_2819_ = lean_ctor_get(v___y_2807_, 6);
v_initHeartbeats_2820_ = lean_ctor_get(v___y_2807_, 7);
v_maxHeartbeats_2821_ = lean_ctor_get(v___y_2807_, 8);
v_currMacroScope_2822_ = lean_ctor_get(v___y_2807_, 9);
v_diag_2823_ = lean_ctor_get_uint8(v___y_2807_, sizeof(void*)*10);
v_suppressElabErrors_2824_ = lean_ctor_get_uint8(v___y_2807_, sizeof(void*)*10 + 1);
v___x_2825_ = 0;
v___x_2826_ = 1;
v___x_2827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_2828_ = l_Lean_replaceRef(v_p_2800_, v_ref_2817_);
lean_inc(v_currMacroScope_2822_);
lean_inc(v_maxHeartbeats_2821_);
lean_inc(v_initHeartbeats_2820_);
lean_inc(v_openDecls_2819_);
lean_inc(v_currNamespace_2818_);
lean_inc(v_maxRecDepth_2816_);
lean_inc(v_currRecDepth_2815_);
lean_inc_ref(v_options_2814_);
lean_inc_ref(v_toCold_2813_);
v___x_2829_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2829_, 0, v_toCold_2813_);
lean_ctor_set(v___x_2829_, 1, v_options_2814_);
lean_ctor_set(v___x_2829_, 2, v_currRecDepth_2815_);
lean_ctor_set(v___x_2829_, 3, v_maxRecDepth_2816_);
lean_ctor_set(v___x_2829_, 4, v_ref_2828_);
lean_ctor_set(v___x_2829_, 5, v_currNamespace_2818_);
lean_ctor_set(v___x_2829_, 6, v_openDecls_2819_);
lean_ctor_set(v___x_2829_, 7, v_initHeartbeats_2820_);
lean_ctor_set(v___x_2829_, 8, v_maxHeartbeats_2821_);
lean_ctor_set(v___x_2829_, 9, v_currMacroScope_2822_);
lean_ctor_set_uint8(v___x_2829_, sizeof(void*)*10, v_diag_2823_);
lean_ctor_set_uint8(v___x_2829_, sizeof(void*)*10 + 1, v_suppressElabErrors_2824_);
lean_inc(v_head_2811_);
lean_inc(v_id_2801_);
v___x_2830_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2804_, v_id_2801_, v_head_2811_, v___x_2827_, v_minIndexable_2802_, v___x_2825_, v___x_2826_, v___y_2805_, v___y_2806_, v___x_2829_, v___y_2808_);
lean_dec_ref_known(v___x_2829_, 10);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v_as_x27_2803_ = v_tail_2812_;
v_b_2804_ = v_a_2831_;
goto _start;
}
else
{
lean_dec(v_id_2801_);
return v___x_2830_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_2833_, lean_object* v_id_2834_, lean_object* v_minIndexable_2835_, lean_object* v_as_x27_2836_, lean_object* v_b_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
uint8_t v_minIndexable_boxed_2843_; lean_object* v_res_2844_; 
v_minIndexable_boxed_2843_ = lean_unbox(v_minIndexable_2835_);
v_res_2844_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_2833_, v_id_2834_, v_minIndexable_boxed_2843_, v_as_x27_2836_, v_b_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v_as_x27_2836_);
lean_dec(v_p_2833_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_2845_){
_start:
{
if (lean_obj_tag(v_x_2845_) == 0)
{
lean_object* v___x_2846_; 
v___x_2846_ = lean_box(0);
return v___x_2846_;
}
else
{
lean_object* v_head_2847_; lean_object* v_tail_2848_; lean_object* v_fst_2849_; uint8_t v___x_2850_; 
v_head_2847_ = lean_ctor_get(v_x_2845_, 0);
v_tail_2848_ = lean_ctor_get(v_x_2845_, 1);
v_fst_2849_ = lean_ctor_get(v_head_2847_, 0);
v___x_2850_ = l_Lean_isPrivateName(v_fst_2849_);
if (v___x_2850_ == 0)
{
v_x_2845_ = v_tail_2848_;
goto _start;
}
else
{
lean_object* v___x_2852_; 
lean_inc(v_head_2847_);
v___x_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_head_2847_);
return v___x_2852_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_2853_);
lean_dec(v_x_2853_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_2855_, lean_object* v_msgData_2856_, uint8_t v_severity_2857_, uint8_t v_isSilent_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; uint8_t v___y_2868_; uint8_t v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; uint8_t v___y_2904_; uint8_t v___y_2905_; uint8_t v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; uint8_t v___y_2930_; uint8_t v___y_2931_; uint8_t v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; uint8_t v___y_2940_; uint8_t v___y_2941_; uint8_t v___y_2942_; uint8_t v___x_2947_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; uint8_t v___y_2952_; uint8_t v___y_2953_; uint8_t v___y_2954_; uint8_t v___y_2956_; uint8_t v___x_2970_; 
v___x_2947_ = 2;
v___x_2970_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2857_, v___x_2947_);
if (v___x_2970_ == 0)
{
v___y_2956_ = v___x_2970_;
goto v___jp_2955_;
}
else
{
uint8_t v___x_2971_; 
lean_inc_ref(v_msgData_2856_);
v___x_2971_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2856_);
v___y_2956_ = v___x_2971_;
goto v___jp_2955_;
}
v___jp_2864_:
{
lean_object* v___x_2874_; lean_object* v_currNamespace_2875_; lean_object* v_openDecls_2876_; lean_object* v_env_2877_; lean_object* v_nextMacroScope_2878_; lean_object* v_ngen_2879_; lean_object* v_auxDeclNGen_2880_; lean_object* v_traceState_2881_; lean_object* v_cache_2882_; lean_object* v_messages_2883_; lean_object* v_infoState_2884_; lean_object* v_snapshotTasks_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2899_; 
v___x_2874_ = lean_st_ref_take(v___y_2873_);
v_currNamespace_2875_ = lean_ctor_get(v___y_2872_, 5);
v_openDecls_2876_ = lean_ctor_get(v___y_2872_, 6);
v_env_2877_ = lean_ctor_get(v___x_2874_, 0);
v_nextMacroScope_2878_ = lean_ctor_get(v___x_2874_, 1);
v_ngen_2879_ = lean_ctor_get(v___x_2874_, 2);
v_auxDeclNGen_2880_ = lean_ctor_get(v___x_2874_, 3);
v_traceState_2881_ = lean_ctor_get(v___x_2874_, 4);
v_cache_2882_ = lean_ctor_get(v___x_2874_, 5);
v_messages_2883_ = lean_ctor_get(v___x_2874_, 6);
v_infoState_2884_ = lean_ctor_get(v___x_2874_, 7);
v_snapshotTasks_2885_ = lean_ctor_get(v___x_2874_, 8);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2887_ = v___x_2874_;
v_isShared_2888_ = v_isSharedCheck_2899_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_snapshotTasks_2885_);
lean_inc(v_infoState_2884_);
lean_inc(v_messages_2883_);
lean_inc(v_cache_2882_);
lean_inc(v_traceState_2881_);
lean_inc(v_auxDeclNGen_2880_);
lean_inc(v_ngen_2879_);
lean_inc(v_nextMacroScope_2878_);
lean_inc(v_env_2877_);
lean_dec(v___x_2874_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2899_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2894_; 
lean_inc(v_openDecls_2876_);
lean_inc(v_currNamespace_2875_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v_currNamespace_2875_);
lean_ctor_set(v___x_2889_, 1, v_openDecls_2876_);
v___x_2890_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set(v___x_2890_, 1, v___y_2870_);
lean_inc_ref(v___y_2867_);
lean_inc_ref(v___y_2866_);
v___x_2891_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2891_, 0, v___y_2866_);
lean_ctor_set(v___x_2891_, 1, v___y_2871_);
lean_ctor_set(v___x_2891_, 2, v___y_2865_);
lean_ctor_set(v___x_2891_, 3, v___y_2867_);
lean_ctor_set(v___x_2891_, 4, v___x_2890_);
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*5, v___y_2869_);
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*5 + 1, v___y_2868_);
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*5 + 2, v_isSilent_2858_);
v___x_2892_ = l_Lean_MessageLog_add(v___x_2891_, v_messages_2883_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 6, v___x_2892_);
v___x_2894_ = v___x_2887_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_env_2877_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_nextMacroScope_2878_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v_ngen_2879_);
lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_auxDeclNGen_2880_);
lean_ctor_set(v_reuseFailAlloc_2898_, 4, v_traceState_2881_);
lean_ctor_set(v_reuseFailAlloc_2898_, 5, v_cache_2882_);
lean_ctor_set(v_reuseFailAlloc_2898_, 6, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2898_, 7, v_infoState_2884_);
lean_ctor_set(v_reuseFailAlloc_2898_, 8, v_snapshotTasks_2885_);
v___x_2894_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2895_ = lean_st_ref_put(v___y_2873_, v___x_2894_);
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
}
}
v___jp_2900_:
{
lean_object* v_fileName_2908_; lean_object* v_fileMap_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2925_; 
v_fileName_2908_ = lean_ctor_get(v___y_2902_, 0);
v_fileMap_2909_ = lean_ctor_get(v___y_2902_, 1);
v___x_2910_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2856_);
v___x_2911_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_2910_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2925_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2925_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
lean_inc_ref_n(v_fileMap_2909_, 2);
v___x_2916_ = l_Lean_FileMap_toPosition(v_fileMap_2909_, v___y_2903_);
lean_dec(v___y_2903_);
v___x_2917_ = l_Lean_FileMap_toPosition(v_fileMap_2909_, v___y_2907_);
lean_dec(v___y_2907_);
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
v___x_2919_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_2906_ == 0)
{
lean_del_object(v___x_2914_);
lean_dec_ref(v___y_2901_);
v___y_2865_ = v___x_2918_;
v___y_2866_ = v_fileName_2908_;
v___y_2867_ = v___x_2919_;
v___y_2868_ = v___y_2905_;
v___y_2869_ = v___y_2904_;
v___y_2870_ = v_a_2912_;
v___y_2871_ = v___x_2916_;
v___y_2872_ = v___y_2861_;
v___y_2873_ = v___y_2862_;
goto v___jp_2864_;
}
else
{
uint8_t v___x_2920_; 
lean_inc(v_a_2912_);
v___x_2920_ = l_Lean_MessageData_hasTag(v___y_2901_, v_a_2912_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2923_; 
lean_dec_ref_known(v___x_2918_, 1);
lean_dec_ref(v___x_2916_);
lean_dec(v_a_2912_);
v___x_2921_ = lean_box(0);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2921_);
v___x_2923_ = v___x_2914_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
else
{
lean_del_object(v___x_2914_);
v___y_2865_ = v___x_2918_;
v___y_2866_ = v_fileName_2908_;
v___y_2867_ = v___x_2919_;
v___y_2868_ = v___y_2905_;
v___y_2869_ = v___y_2904_;
v___y_2870_ = v_a_2912_;
v___y_2871_ = v___x_2916_;
v___y_2872_ = v___y_2861_;
v___y_2873_ = v___y_2862_;
goto v___jp_2864_;
}
}
}
}
v___jp_2926_:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_Syntax_getTailPos_x3f(v___y_2929_, v___y_2931_);
lean_dec(v___y_2929_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_inc(v___y_2933_);
v___y_2901_ = v___y_2927_;
v___y_2902_ = v___y_2928_;
v___y_2903_ = v___y_2933_;
v___y_2904_ = v___y_2931_;
v___y_2905_ = v___y_2930_;
v___y_2906_ = v___y_2932_;
v___y_2907_ = v___y_2933_;
goto v___jp_2900_;
}
else
{
lean_object* v_val_2935_; 
v_val_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_val_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___y_2901_ = v___y_2927_;
v___y_2902_ = v___y_2928_;
v___y_2903_ = v___y_2933_;
v___y_2904_ = v___y_2931_;
v___y_2905_ = v___y_2930_;
v___y_2906_ = v___y_2932_;
v___y_2907_ = v_val_2935_;
goto v___jp_2900_;
}
}
v___jp_2936_:
{
lean_object* v_ref_2943_; lean_object* v___x_2944_; 
v_ref_2943_ = l_Lean_replaceRef(v_ref_2855_, v___y_2939_);
v___x_2944_ = l_Lean_Syntax_getPos_x3f(v_ref_2943_, v___y_2940_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_unsigned_to_nat(0u);
v___y_2927_ = v___y_2937_;
v___y_2928_ = v___y_2938_;
v___y_2929_ = v_ref_2943_;
v___y_2930_ = v___y_2942_;
v___y_2931_ = v___y_2940_;
v___y_2932_ = v___y_2941_;
v___y_2933_ = v___x_2945_;
goto v___jp_2926_;
}
else
{
lean_object* v_val_2946_; 
v_val_2946_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_val_2946_);
lean_dec_ref_known(v___x_2944_, 1);
v___y_2927_ = v___y_2937_;
v___y_2928_ = v___y_2938_;
v___y_2929_ = v_ref_2943_;
v___y_2930_ = v___y_2942_;
v___y_2931_ = v___y_2940_;
v___y_2932_ = v___y_2941_;
v___y_2933_ = v_val_2946_;
goto v___jp_2926_;
}
}
v___jp_2948_:
{
if (v___y_2954_ == 0)
{
v___y_2937_ = v___y_2951_;
v___y_2938_ = v___y_2950_;
v___y_2939_ = v___y_2949_;
v___y_2940_ = v___y_2953_;
v___y_2941_ = v___y_2952_;
v___y_2942_ = v_severity_2857_;
goto v___jp_2936_;
}
else
{
v___y_2937_ = v___y_2951_;
v___y_2938_ = v___y_2950_;
v___y_2939_ = v___y_2949_;
v___y_2940_ = v___y_2953_;
v___y_2941_ = v___y_2952_;
v___y_2942_ = v___x_2947_;
goto v___jp_2936_;
}
}
v___jp_2955_:
{
if (v___y_2956_ == 0)
{
lean_object* v_toCold_2957_; lean_object* v_options_2958_; lean_object* v_ref_2959_; uint8_t v_suppressElabErrors_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___f_2963_; uint8_t v___x_2964_; uint8_t v___x_2965_; 
v_toCold_2957_ = lean_ctor_get(v___y_2861_, 0);
v_options_2958_ = lean_ctor_get(v___y_2861_, 1);
v_ref_2959_ = lean_ctor_get(v___y_2861_, 4);
v_suppressElabErrors_2960_ = lean_ctor_get_uint8(v___y_2861_, sizeof(void*)*10 + 1);
v___x_2961_ = lean_box(v_suppressElabErrors_2960_);
v___x_2962_ = lean_box(v___y_2956_);
v___f_2963_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2963_, 0, v___x_2961_);
lean_closure_set(v___f_2963_, 1, v___x_2962_);
v___x_2964_ = 1;
v___x_2965_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2857_, v___x_2964_);
if (v___x_2965_ == 0)
{
v___y_2949_ = v_ref_2959_;
v___y_2950_ = v_toCold_2957_;
v___y_2951_ = v___f_2963_;
v___y_2952_ = v_suppressElabErrors_2960_;
v___y_2953_ = v___y_2956_;
v___y_2954_ = v___x_2965_;
goto v___jp_2948_;
}
else
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = l_Lean_warningAsError;
v___x_2967_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2958_, v___x_2966_);
v___y_2949_ = v_ref_2959_;
v___y_2950_ = v_toCold_2957_;
v___y_2951_ = v___f_2963_;
v___y_2952_ = v_suppressElabErrors_2960_;
v___y_2953_ = v___y_2956_;
v___y_2954_ = v___x_2967_;
goto v___jp_2948_;
}
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_dec_ref(v_msgData_2856_);
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
return v___x_2969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_2972_, lean_object* v_msgData_2973_, lean_object* v_severity_2974_, lean_object* v_isSilent_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
uint8_t v_severity_boxed_2981_; uint8_t v_isSilent_boxed_2982_; lean_object* v_res_2983_; 
v_severity_boxed_2981_ = lean_unbox(v_severity_2974_);
v_isSilent_boxed_2982_ = lean_unbox(v_isSilent_2975_);
v_res_2983_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_2972_, v_msgData_2973_, v_severity_boxed_2981_, v_isSilent_boxed_2982_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v_ref_2972_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_2984_, uint8_t v_severity_2985_, uint8_t v_isSilent_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_ref_2994_; lean_object* v___x_2995_; 
v_ref_2994_ = lean_ctor_get(v___y_2991_, 4);
v___x_2995_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_2994_, v_msgData_2984_, v_severity_2985_, v_isSilent_2986_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_2996_, lean_object* v_severity_2997_, lean_object* v_isSilent_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
uint8_t v_severity_boxed_3006_; uint8_t v_isSilent_boxed_3007_; lean_object* v_res_3008_; 
v_severity_boxed_3006_ = lean_unbox(v_severity_2997_);
v_isSilent_boxed_3007_ = lean_unbox(v_isSilent_2998_);
v_res_3008_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_2996_, v_severity_boxed_3006_, v_isSilent_boxed_3007_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
uint8_t v___x_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; 
v___x_3017_ = 1;
v___x_3018_ = 0;
v___x_3019_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3009_, v___x_3017_, v___x_3018_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_options_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_options_3032_ = lean_ctor_get(v___y_3030_, 1);
v___x_3033_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_3032_, v_opt_3029_);
v___x_3034_ = lean_box(v___x_3033_);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3036_, v___y_3037_);
lean_dec_ref(v___y_3037_);
lean_dec_ref(v_opt_3036_);
return v_res_3039_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3042_ = l_Lean_stringToMessageData(v___x_3041_);
return v___x_3042_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3045_ = l_Lean_stringToMessageData(v___x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v___x_3054_; lean_object* v_env_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3077_; 
v___x_3054_ = lean_st_ref_get(v___y_3052_);
v_env_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc_ref(v_env_3055_);
lean_dec(v___x_3054_);
v___x_3056_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3057_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3056_, v___y_3051_);
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3077_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3077_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
uint8_t v_isExporting_3067_; 
v_isExporting_3067_ = lean_ctor_get_uint8(v_env_3055_, sizeof(void*)*8);
lean_dec_ref(v_env_3055_);
if (v_isExporting_3067_ == 0)
{
lean_dec(v_a_3058_);
lean_dec(v_id_3046_);
goto v___jp_3062_;
}
else
{
uint8_t v___x_3068_; 
v___x_3068_ = l_Lean_isPrivateName(v_id_3046_);
if (v___x_3068_ == 0)
{
lean_dec(v_a_3058_);
lean_dec(v_id_3046_);
goto v___jp_3062_;
}
else
{
uint8_t v___x_3069_; 
v___x_3069_ = lean_unbox(v_a_3058_);
lean_dec(v_a_3058_);
if (v___x_3069_ == 0)
{
lean_dec(v_id_3046_);
goto v___jp_3062_;
}
else
{
lean_object* v___x_3070_; uint8_t v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_del_object(v___x_3060_);
v___x_3070_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3071_ = 0;
v___x_3072_ = l_Lean_MessageData_ofConstName(v_id_3046_, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3070_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3075_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
return v___x_3076_;
}
}
}
v___jp_3062_:
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = lean_box(0);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3063_);
v___x_3065_ = v___x_3060_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3087_, uint8_t v_enableLog_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v_env_3097_; lean_object* v_options_3098_; lean_object* v_currNamespace_3099_; lean_object* v_openDecls_3100_; lean_object* v___x_3101_; lean_object* v_env_3102_; lean_object* v_res_3103_; 
v___x_3096_ = lean_st_ref_get(v___y_3094_);
v_env_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc_ref(v_env_3097_);
lean_dec(v___x_3096_);
v_options_3098_ = lean_ctor_get(v___y_3093_, 1);
v_currNamespace_3099_ = lean_ctor_get(v___y_3093_, 5);
v_openDecls_3100_ = lean_ctor_get(v___y_3093_, 6);
v___x_3101_ = lean_st_ref_get(v___y_3094_);
v_env_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc_ref(v_env_3102_);
lean_dec(v___x_3101_);
lean_inc(v_openDecls_3100_);
lean_inc(v_currNamespace_3099_);
v_res_3103_ = l_Lean_ResolveName_resolveGlobalName(v_env_3097_, v_options_3098_, v_currNamespace_3099_, v_openDecls_3100_, v_id_3087_);
if (v_enableLog_3088_ == 0)
{
lean_object* v___x_3104_; 
lean_dec_ref(v_env_3102_);
v___x_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3104_, 0, v_res_3103_);
return v___x_3104_;
}
else
{
uint8_t v_isExporting_3105_; 
v_isExporting_3105_ = lean_ctor_get_uint8(v_env_3102_, sizeof(void*)*8);
lean_dec_ref(v_env_3102_);
if (v_isExporting_3105_ == 0)
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3106_, 0, v_res_3103_);
return v___x_3106_;
}
else
{
lean_object* v___x_3107_; 
v___x_3107_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3103_);
if (lean_obj_tag(v___x_3107_) == 1)
{
lean_object* v_val_3108_; lean_object* v_fst_3109_; lean_object* v___x_3110_; 
v_val_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_val_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v_fst_3109_ = lean_ctor_get(v_val_3108_, 0);
lean_inc(v_fst_3109_);
lean_dec(v_val_3108_);
v___x_3110_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3109_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___x_3110_, 0);
lean_dec(v_unused_3118_);
v___x_3112_ = v___x_3110_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_dec(v___x_3110_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v_res_3103_);
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_res_3103_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_res_3103_);
v_a_3119_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3110_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3110_);
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
else
{
lean_object* v___x_3127_; 
lean_dec(v___x_3107_);
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v_res_3103_);
return v___x_3127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3128_, lean_object* v_enableLog_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
uint8_t v_enableLog_boxed_3137_; lean_object* v_res_3138_; 
v_enableLog_boxed_3137_ = lean_unbox(v_enableLog_3129_);
v_res_3138_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3128_, v_enableLog_boxed_3137_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3139_, lean_object* v_a_3140_){
_start:
{
if (lean_obj_tag(v_a_3139_) == 0)
{
lean_object* v___x_3141_; 
v___x_3141_ = l_List_reverse___redArg(v_a_3140_);
return v___x_3141_;
}
else
{
lean_object* v_head_3142_; lean_object* v_tail_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3154_; 
v_head_3142_ = lean_ctor_get(v_a_3139_, 0);
v_tail_3143_ = lean_ctor_get(v_a_3139_, 1);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_a_3139_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3145_ = v_a_3139_;
v_isShared_3146_ = v_isSharedCheck_3154_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_tail_3143_);
lean_inc(v_head_3142_);
lean_dec(v_a_3139_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3154_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v_snd_3147_; uint8_t v___x_3148_; 
v_snd_3147_ = lean_ctor_get(v_head_3142_, 1);
v___x_3148_ = l_List_isEmpty___redArg(v_snd_3147_);
if (v___x_3148_ == 0)
{
lean_del_object(v___x_3145_);
lean_dec(v_head_3142_);
v_a_3139_ = v_tail_3143_;
goto _start;
}
else
{
lean_object* v___x_3151_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 1, v_a_3140_);
v___x_3151_ = v___x_3145_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_head_3142_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_a_3140_);
v___x_3151_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
v_a_3139_ = v_tail_3143_;
v_a_3140_ = v___x_3151_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3155_, lean_object* v_findLocalDecl_x3f_3156_, lean_object* v_n_3157_, lean_object* v_projs_3158_, uint8_t v_globalDeclFound_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___y_3168_; lean_object* v___y_3169_; uint8_t v_globalDeclFoundNext_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v_imported_3179_; lean_object* v_ctx_3180_; lean_object* v_scopes_3181_; lean_object* v_givenNameView_3182_; uint8_t v___y_3184_; 
v_imported_3179_ = lean_ctor_get(v_view_3155_, 1);
v_ctx_3180_ = lean_ctor_get(v_view_3155_, 2);
v_scopes_3181_ = lean_ctor_get(v_view_3155_, 3);
lean_inc(v_scopes_3181_);
lean_inc(v_ctx_3180_);
lean_inc(v_imported_3179_);
lean_inc(v_n_3157_);
v_givenNameView_3182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3182_, 0, v_n_3157_);
lean_ctor_set(v_givenNameView_3182_, 1, v_imported_3179_);
lean_ctor_set(v_givenNameView_3182_, 2, v_ctx_3180_);
lean_ctor_set(v_givenNameView_3182_, 3, v_scopes_3181_);
if (v_globalDeclFound_3159_ == 0)
{
v___y_3184_ = v_globalDeclFound_3159_;
goto v___jp_3183_;
}
else
{
uint8_t v___x_3219_; 
v___x_3219_ = l_List_isEmpty___redArg(v_projs_3158_);
if (v___x_3219_ == 0)
{
v___y_3184_ = v_globalDeclFound_3159_;
goto v___jp_3183_;
}
else
{
uint8_t v___x_3220_; 
v___x_3220_ = 0;
v___y_3184_ = v___x_3220_;
goto v___jp_3183_;
}
}
v___jp_3167_:
{
lean_object* v___x_3177_; 
v___x_3177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___y_3168_);
lean_ctor_set(v___x_3177_, 1, v_projs_3158_);
v_n_3157_ = v___y_3169_;
v_projs_3158_ = v___x_3177_;
v_globalDeclFound_3159_ = v_globalDeclFoundNext_3170_;
v___y_3160_ = v___y_3171_;
v___y_3161_ = v___y_3172_;
v___y_3162_ = v___y_3173_;
v___y_3163_ = v___y_3174_;
v___y_3164_ = v___y_3175_;
v___y_3165_ = v___y_3176_;
goto _start;
}
v___jp_3183_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = lean_box(v___y_3184_);
lean_inc_ref(v_findLocalDecl_x3f_3156_);
lean_inc_ref(v_givenNameView_3182_);
v___x_3186_ = lean_apply_2(v_findLocalDecl_x3f_3156_, v_givenNameView_3182_, v___x_3185_);
if (lean_obj_tag(v___x_3186_) == 0)
{
if (lean_obj_tag(v_n_3157_) == 1)
{
if (v_globalDeclFound_3159_ == 0)
{
lean_object* v_pre_3187_; lean_object* v_str_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_pre_3187_ = lean_ctor_get(v_n_3157_, 0);
lean_inc(v_pre_3187_);
v_str_3188_ = lean_ctor_get(v_n_3157_, 1);
lean_inc_ref(v_str_3188_);
lean_dec_ref_known(v_n_3157_, 2);
v___x_3189_ = l_Lean_MacroScopesView_review(v_givenNameView_3182_);
v___x_3190_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3189_, v_globalDeclFound_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3192_; lean_object* v_r_3193_; uint8_t v___x_3194_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref_known(v___x_3190_, 1);
v___x_3192_ = lean_box(0);
v_r_3193_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3191_, v___x_3192_);
v___x_3194_ = l_List_isEmpty___redArg(v_r_3193_);
lean_dec(v_r_3193_);
if (v___x_3194_ == 0)
{
uint8_t v_globalDeclFoundNext_3195_; 
v_globalDeclFoundNext_3195_ = 1;
v___y_3168_ = v_str_3188_;
v___y_3169_ = v_pre_3187_;
v_globalDeclFoundNext_3170_ = v_globalDeclFoundNext_3195_;
v___y_3171_ = v___y_3160_;
v___y_3172_ = v___y_3161_;
v___y_3173_ = v___y_3162_;
v___y_3174_ = v___y_3163_;
v___y_3175_ = v___y_3164_;
v___y_3176_ = v___y_3165_;
goto v___jp_3167_;
}
else
{
v___y_3168_ = v_str_3188_;
v___y_3169_ = v_pre_3187_;
v_globalDeclFoundNext_3170_ = v_globalDeclFound_3159_;
v___y_3171_ = v___y_3160_;
v___y_3172_ = v___y_3161_;
v___y_3173_ = v___y_3162_;
v___y_3174_ = v___y_3163_;
v___y_3175_ = v___y_3164_;
v___y_3176_ = v___y_3165_;
goto v___jp_3167_;
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref(v_str_3188_);
lean_dec(v_pre_3187_);
lean_dec(v_projs_3158_);
lean_dec_ref(v_findLocalDecl_x3f_3156_);
v_a_3196_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3190_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3190_);
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
lean_object* v_pre_3204_; lean_object* v_str_3205_; 
lean_dec_ref_known(v_givenNameView_3182_, 4);
v_pre_3204_ = lean_ctor_get(v_n_3157_, 0);
lean_inc(v_pre_3204_);
v_str_3205_ = lean_ctor_get(v_n_3157_, 1);
lean_inc_ref(v_str_3205_);
lean_dec_ref_known(v_n_3157_, 2);
v___y_3168_ = v_str_3205_;
v___y_3169_ = v_pre_3204_;
v_globalDeclFoundNext_3170_ = v_globalDeclFound_3159_;
v___y_3171_ = v___y_3160_;
v___y_3172_ = v___y_3161_;
v___y_3173_ = v___y_3162_;
v___y_3174_ = v___y_3163_;
v___y_3175_ = v___y_3164_;
v___y_3176_ = v___y_3165_;
goto v___jp_3167_;
}
}
else
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
lean_dec_ref_known(v_givenNameView_3182_, 4);
lean_dec(v_projs_3158_);
lean_dec(v_n_3157_);
lean_dec_ref(v_findLocalDecl_x3f_3156_);
v___x_3206_ = lean_box(0);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
}
else
{
lean_object* v_val_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3218_; 
lean_dec_ref_known(v_givenNameView_3182_, 4);
lean_dec(v_n_3157_);
lean_dec_ref(v_findLocalDecl_x3f_3156_);
v_val_3208_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3210_ = v___x_3186_;
v_isShared_3211_ = v_isSharedCheck_3218_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_val_3208_);
lean_dec(v___x_3186_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3218_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3212_ = l_Lean_LocalDecl_toExpr(v_val_3208_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v_projs_3158_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v___x_3213_);
v___x_3215_ = v___x_3210_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3213_);
v___x_3215_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
return v___x_3216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3221_, lean_object* v_findLocalDecl_x3f_3222_, lean_object* v_n_3223_, lean_object* v_projs_3224_, lean_object* v_globalDeclFound_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
uint8_t v_globalDeclFound_boxed_3233_; lean_object* v_res_3234_; 
v_globalDeclFound_boxed_3233_ = lean_unbox(v_globalDeclFound_3225_);
v_res_3234_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3221_, v_findLocalDecl_x3f_3222_, v_n_3223_, v_projs_3224_, v_globalDeclFound_boxed_3233_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v_view_3221_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3235_, lean_object* v_givenName_3236_, lean_object* v_as_3237_, lean_object* v_i_3238_){
_start:
{
lean_object* v_zero_3239_; uint8_t v_isZero_3240_; 
v_zero_3239_ = lean_unsigned_to_nat(0u);
v_isZero_3240_ = lean_nat_dec_eq(v_i_3238_, v_zero_3239_);
if (v_isZero_3240_ == 1)
{
lean_object* v___x_3241_; 
lean_dec(v_i_3238_);
v___x_3241_ = lean_box(0);
return v___x_3241_;
}
else
{
lean_object* v_one_3242_; lean_object* v_n_3243_; lean_object* v___y_3245_; lean_object* v___x_3247_; 
v_one_3242_ = lean_unsigned_to_nat(1u);
v_n_3243_ = lean_nat_sub(v_i_3238_, v_one_3242_);
lean_dec(v_i_3238_);
v___x_3247_ = lean_array_fget_borrowed(v_as_3237_, v_n_3243_);
if (lean_obj_tag(v___x_3247_) == 0)
{
v___y_3245_ = v___x_3247_;
goto v___jp_3244_;
}
else
{
lean_object* v_val_3248_; uint8_t v___x_3249_; 
v_val_3248_ = lean_ctor_get(v___x_3247_, 0);
v___x_3249_ = l_Lean_LocalDecl_isAuxDecl(v_val_3248_);
if (v___x_3249_ == 0)
{
v___y_3245_ = v_localDecl_x3f_3235_;
goto v___jp_3244_;
}
else
{
lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = l_Lean_LocalDecl_userName(v_val_3248_);
v___x_3251_ = lean_name_eq(v___x_3250_, v_givenName_3236_);
lean_dec(v___x_3250_);
if (v___x_3251_ == 0)
{
v_i_3238_ = v_n_3243_;
goto _start;
}
else
{
v___y_3245_ = v___x_3247_;
goto v___jp_3244_;
}
}
}
v___jp_3244_:
{
if (lean_obj_tag(v___y_3245_) == 0)
{
v_i_3238_ = v_n_3243_;
goto _start;
}
else
{
lean_dec(v_n_3243_);
lean_inc_ref(v___y_3245_);
return v___y_3245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3253_, lean_object* v_givenName_3254_, lean_object* v_as_3255_, lean_object* v_i_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3253_, v_givenName_3254_, v_as_3255_, v_i_3256_);
lean_dec_ref(v_as_3255_);
lean_dec(v_givenName_3254_);
lean_dec(v_localDecl_x3f_3253_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3258_, lean_object* v_givenName_3259_, lean_object* v_as_3260_, lean_object* v_i_3261_){
_start:
{
lean_object* v_zero_3262_; uint8_t v_isZero_3263_; 
v_zero_3262_ = lean_unsigned_to_nat(0u);
v_isZero_3263_ = lean_nat_dec_eq(v_i_3261_, v_zero_3262_);
if (v_isZero_3263_ == 1)
{
lean_object* v___x_3264_; 
lean_dec(v_i_3261_);
v___x_3264_ = lean_box(0);
return v___x_3264_;
}
else
{
lean_object* v_one_3265_; lean_object* v_n_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_one_3265_ = lean_unsigned_to_nat(1u);
v_n_3266_ = lean_nat_sub(v_i_3261_, v_one_3265_);
lean_dec(v_i_3261_);
v___x_3267_ = lean_array_fget_borrowed(v_as_3260_, v_n_3266_);
v___x_3268_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3258_, v_givenName_3259_, v___x_3267_);
if (lean_obj_tag(v___x_3268_) == 0)
{
v_i_3261_ = v_n_3266_;
goto _start;
}
else
{
lean_dec(v_n_3266_);
return v___x_3268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3270_, lean_object* v_givenName_3271_, lean_object* v_x_3272_){
_start:
{
if (lean_obj_tag(v_x_3272_) == 0)
{
lean_object* v_cs_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v_cs_3273_ = lean_ctor_get(v_x_3272_, 0);
v___x_3274_ = lean_array_get_size(v_cs_3273_);
v___x_3275_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3270_, v_givenName_3271_, v_cs_3273_, v___x_3274_);
return v___x_3275_;
}
else
{
lean_object* v_vs_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v_vs_3276_ = lean_ctor_get(v_x_3272_, 0);
v___x_3277_ = lean_array_get_size(v_vs_3276_);
v___x_3278_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3270_, v_givenName_3271_, v_vs_3276_, v___x_3277_);
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3279_, lean_object* v_givenName_3280_, lean_object* v_x_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3279_, v_givenName_3280_, v_x_3281_);
lean_dec_ref(v_x_3281_);
lean_dec(v_givenName_3280_);
lean_dec(v_localDecl_x3f_3279_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3283_, lean_object* v_givenName_3284_, lean_object* v_as_3285_, lean_object* v_i_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3283_, v_givenName_3284_, v_as_3285_, v_i_3286_);
lean_dec_ref(v_as_3285_);
lean_dec(v_givenName_3284_);
lean_dec(v_localDecl_x3f_3283_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3288_, lean_object* v_givenName_3289_, lean_object* v_t_3290_){
_start:
{
lean_object* v_root_3291_; lean_object* v_tail_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_root_3291_ = lean_ctor_get(v_t_3290_, 0);
v_tail_3292_ = lean_ctor_get(v_t_3290_, 1);
v___x_3293_ = lean_array_get_size(v_tail_3292_);
v___x_3294_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3288_, v_givenName_3289_, v_tail_3292_, v___x_3293_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3288_, v_givenName_3289_, v_root_3291_);
return v___x_3295_;
}
else
{
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3296_, lean_object* v_givenName_3297_, lean_object* v_t_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3296_, v_givenName_3297_, v_t_3298_);
lean_dec_ref(v_t_3298_);
lean_dec(v_givenName_3297_);
lean_dec(v_localDecl_x3f_3296_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3300_, lean_object* v_k_3301_){
_start:
{
if (lean_obj_tag(v_t_3300_) == 0)
{
lean_object* v_k_3302_; lean_object* v_v_3303_; lean_object* v_l_3304_; lean_object* v_r_3305_; uint8_t v___x_3306_; 
v_k_3302_ = lean_ctor_get(v_t_3300_, 1);
v_v_3303_ = lean_ctor_get(v_t_3300_, 2);
v_l_3304_ = lean_ctor_get(v_t_3300_, 3);
v_r_3305_ = lean_ctor_get(v_t_3300_, 4);
v___x_3306_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3301_, v_k_3302_);
switch(v___x_3306_)
{
case 0:
{
v_t_3300_ = v_l_3304_;
goto _start;
}
case 1:
{
lean_object* v___x_3308_; 
lean_inc(v_v_3303_);
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v_v_3303_);
return v___x_3308_;
}
default: 
{
v_t_3300_ = v_r_3305_;
goto _start;
}
}
}
else
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_box(0);
return v___x_3310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3311_, lean_object* v_k_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3311_, v_k_3312_);
lean_dec(v_k_3312_);
lean_dec(v_t_3311_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3314_, lean_object* v_givenName_3315_){
_start:
{
lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = l_Lean_LocalDecl_userName(v_localDecl_3314_);
v___x_3317_ = lean_name_eq(v___x_3316_, v_givenName_3315_);
lean_dec(v___x_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; 
lean_dec_ref(v_localDecl_3314_);
v___x_3318_ = lean_box(0);
return v___x_3318_;
}
else
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_localDecl_3314_);
return v___x_3319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3320_, lean_object* v_givenName_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3320_, v_givenName_3321_);
lean_dec(v_givenName_3321_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3323_, uint8_t v_skipAuxDecl_3324_, lean_object* v_auxDeclToFullName_3325_, lean_object* v___x_3326_, lean_object* v_givenNameView_3327_, lean_object* v_as_3328_, lean_object* v_i_3329_){
_start:
{
lean_object* v_zero_3330_; uint8_t v_isZero_3331_; 
v_zero_3330_ = lean_unsigned_to_nat(0u);
v_isZero_3331_ = lean_nat_dec_eq(v_i_3329_, v_zero_3330_);
if (v_isZero_3331_ == 1)
{
lean_object* v___x_3332_; 
lean_dec(v_i_3329_);
lean_dec_ref(v_givenNameView_3327_);
lean_dec(v___x_3326_);
v___x_3332_ = lean_box(0);
return v___x_3332_;
}
else
{
lean_object* v_one_3333_; lean_object* v_n_3334_; lean_object* v___y_3336_; lean_object* v___x_3338_; 
v_one_3333_ = lean_unsigned_to_nat(1u);
v_n_3334_ = lean_nat_sub(v_i_3329_, v_one_3333_);
lean_dec(v_i_3329_);
v___x_3338_ = lean_array_fget_borrowed(v_as_3328_, v_n_3334_);
if (lean_obj_tag(v___x_3338_) == 0)
{
v___y_3336_ = v___x_3338_;
goto v___jp_3335_;
}
else
{
lean_object* v_val_3339_; uint8_t v___x_3340_; 
v_val_3339_ = lean_ctor_get(v___x_3338_, 0);
v___x_3340_ = l_Lean_LocalDecl_isAuxDecl(v_val_3339_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
lean_inc(v_val_3339_);
v___x_3341_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3339_, v_givenName_3323_);
v___y_3336_ = v___x_3341_;
goto v___jp_3335_;
}
else
{
if (v_skipAuxDecl_3324_ == 0)
{
if (v___x_3340_ == 0)
{
v_i_3329_ = v_n_3334_;
goto _start;
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = l_Lean_LocalDecl_fvarId(v_val_3339_);
v___x_3344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3325_, v___x_3343_);
lean_dec(v___x_3343_);
if (lean_obj_tag(v___x_3344_) == 1)
{
lean_object* v_val_3345_; lean_object* v_fullDeclView_3346_; lean_object* v___y_3348_; lean_object* v_name_3369_; lean_object* v___x_3370_; 
v_val_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v_fullDeclView_3346_ = l_Lean_extractMacroScopes(v_val_3345_);
v_name_3369_ = lean_ctor_get(v_fullDeclView_3346_, 0);
lean_inc_n(v_name_3369_, 2);
v___x_3370_ = l_Lean_privateToUserName_x3f(v_name_3369_);
if (lean_obj_tag(v___x_3370_) == 0)
{
v___y_3348_ = v_name_3369_;
goto v___jp_3347_;
}
else
{
lean_object* v_val_3371_; 
lean_dec(v_name_3369_);
v_val_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_val_3371_);
lean_dec_ref_known(v___x_3370_, 1);
v___y_3348_ = v_val_3371_;
goto v___jp_3347_;
}
v___jp_3347_:
{
lean_object* v_imported_3349_; lean_object* v_ctx_3350_; lean_object* v_scopes_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3367_; 
v_imported_3349_ = lean_ctor_get(v_fullDeclView_3346_, 1);
v_ctx_3350_ = lean_ctor_get(v_fullDeclView_3346_, 2);
v_scopes_3351_ = lean_ctor_get(v_fullDeclView_3346_, 3);
v_isSharedCheck_3367_ = !lean_is_exclusive(v_fullDeclView_3346_);
if (v_isSharedCheck_3367_ == 0)
{
lean_object* v_unused_3368_; 
v_unused_3368_ = lean_ctor_get(v_fullDeclView_3346_, 0);
lean_dec(v_unused_3368_);
v___x_3353_ = v_fullDeclView_3346_;
v_isShared_3354_ = v_isSharedCheck_3367_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_scopes_3351_);
lean_inc(v_ctx_3350_);
lean_inc(v_imported_3349_);
lean_dec(v_fullDeclView_3346_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3367_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v_fullDeclView_3356_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v___y_3348_);
v_fullDeclView_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___y_3348_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_imported_3349_);
lean_ctor_set(v_reuseFailAlloc_3366_, 2, v_ctx_3350_);
lean_ctor_set(v_reuseFailAlloc_3366_, 3, v_scopes_3351_);
v_fullDeclView_3356_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v_fullDeclName_3357_; uint8_t v___x_3358_; 
lean_inc_ref(v_fullDeclView_3356_);
v_fullDeclName_3357_ = l_Lean_MacroScopesView_review(v_fullDeclView_3356_);
v___x_3358_ = l_Lean_Name_isPrefixOf(v___x_3326_, v_fullDeclName_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; 
lean_dec_ref(v_fullDeclView_3356_);
lean_inc(v___x_3326_);
lean_inc_ref(v_givenNameView_3327_);
lean_inc(v_val_3339_);
v___x_3359_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3339_, v_givenNameView_3327_, v_fullDeclName_3357_, v___x_3326_);
lean_dec(v_fullDeclName_3357_);
v___y_3336_ = v___x_3359_;
goto v___jp_3335_;
}
else
{
lean_object* v___x_3360_; lean_object* v_localDeclNameView_3361_; uint8_t v___x_3362_; 
lean_dec(v_fullDeclName_3357_);
v___x_3360_ = l_Lean_LocalDecl_userName(v_val_3339_);
v_localDeclNameView_3361_ = l_Lean_extractMacroScopes(v___x_3360_);
v___x_3362_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3361_, v_givenNameView_3327_);
lean_dec_ref(v_localDeclNameView_3361_);
if (v___x_3362_ == 0)
{
lean_dec_ref(v_fullDeclView_3356_);
v_i_3329_ = v_n_3334_;
goto _start;
}
else
{
uint8_t v___x_3364_; 
v___x_3364_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3327_, v_fullDeclView_3356_);
lean_dec_ref(v_fullDeclView_3356_);
if (v___x_3364_ == 0)
{
v_i_3329_ = v_n_3334_;
goto _start;
}
else
{
lean_inc_ref(v___x_3338_);
v___y_3336_ = v___x_3338_;
goto v___jp_3335_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3372_; 
lean_dec(v___x_3344_);
lean_inc(v_val_3339_);
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3339_, v_givenName_3323_);
v___y_3336_ = v___x_3372_;
goto v___jp_3335_;
}
}
}
else
{
v_i_3329_ = v_n_3334_;
goto _start;
}
}
}
v___jp_3335_:
{
if (lean_obj_tag(v___y_3336_) == 0)
{
v_i_3329_ = v_n_3334_;
goto _start;
}
else
{
lean_dec(v_n_3334_);
lean_dec_ref(v_givenNameView_3327_);
lean_dec(v___x_3326_);
return v___y_3336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3374_, lean_object* v_skipAuxDecl_3375_, lean_object* v_auxDeclToFullName_3376_, lean_object* v___x_3377_, lean_object* v_givenNameView_3378_, lean_object* v_as_3379_, lean_object* v_i_3380_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3381_; lean_object* v_res_3382_; 
v_skipAuxDecl_boxed_3381_ = lean_unbox(v_skipAuxDecl_3375_);
v_res_3382_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3374_, v_skipAuxDecl_boxed_3381_, v_auxDeclToFullName_3376_, v___x_3377_, v_givenNameView_3378_, v_as_3379_, v_i_3380_);
lean_dec_ref(v_as_3379_);
lean_dec(v_auxDeclToFullName_3376_);
lean_dec(v_givenName_3374_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3383_, uint8_t v_skipAuxDecl_3384_, lean_object* v_auxDeclToFullName_3385_, lean_object* v___x_3386_, lean_object* v_givenNameView_3387_, lean_object* v_as_3388_, lean_object* v_i_3389_){
_start:
{
lean_object* v_zero_3390_; uint8_t v_isZero_3391_; 
v_zero_3390_ = lean_unsigned_to_nat(0u);
v_isZero_3391_ = lean_nat_dec_eq(v_i_3389_, v_zero_3390_);
if (v_isZero_3391_ == 1)
{
lean_object* v___x_3392_; 
lean_dec(v_i_3389_);
lean_dec_ref(v_givenNameView_3387_);
lean_dec(v___x_3386_);
v___x_3392_ = lean_box(0);
return v___x_3392_;
}
else
{
lean_object* v_one_3393_; lean_object* v_n_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v_one_3393_ = lean_unsigned_to_nat(1u);
v_n_3394_ = lean_nat_sub(v_i_3389_, v_one_3393_);
lean_dec(v_i_3389_);
v___x_3395_ = lean_array_fget_borrowed(v_as_3388_, v_n_3394_);
lean_inc_ref(v_givenNameView_3387_);
lean_inc(v___x_3386_);
v___x_3396_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3383_, v_skipAuxDecl_3384_, v_auxDeclToFullName_3385_, v___x_3386_, v_givenNameView_3387_, v___x_3395_);
if (lean_obj_tag(v___x_3396_) == 0)
{
v_i_3389_ = v_n_3394_;
goto _start;
}
else
{
lean_dec(v_n_3394_);
lean_dec_ref(v_givenNameView_3387_);
lean_dec(v___x_3386_);
return v___x_3396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3398_, uint8_t v_skipAuxDecl_3399_, lean_object* v_auxDeclToFullName_3400_, lean_object* v___x_3401_, lean_object* v_givenNameView_3402_, lean_object* v_x_3403_){
_start:
{
if (lean_obj_tag(v_x_3403_) == 0)
{
lean_object* v_cs_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v_cs_3404_ = lean_ctor_get(v_x_3403_, 0);
v___x_3405_ = lean_array_get_size(v_cs_3404_);
v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3398_, v_skipAuxDecl_3399_, v_auxDeclToFullName_3400_, v___x_3401_, v_givenNameView_3402_, v_cs_3404_, v___x_3405_);
return v___x_3406_;
}
else
{
lean_object* v_vs_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_vs_3407_ = lean_ctor_get(v_x_3403_, 0);
v___x_3408_ = lean_array_get_size(v_vs_3407_);
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3398_, v_skipAuxDecl_3399_, v_auxDeclToFullName_3400_, v___x_3401_, v_givenNameView_3402_, v_vs_3407_, v___x_3408_);
return v___x_3409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3410_, lean_object* v_skipAuxDecl_3411_, lean_object* v_auxDeclToFullName_3412_, lean_object* v___x_3413_, lean_object* v_givenNameView_3414_, lean_object* v_x_3415_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3416_; lean_object* v_res_3417_; 
v_skipAuxDecl_boxed_3416_ = lean_unbox(v_skipAuxDecl_3411_);
v_res_3417_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3410_, v_skipAuxDecl_boxed_3416_, v_auxDeclToFullName_3412_, v___x_3413_, v_givenNameView_3414_, v_x_3415_);
lean_dec_ref(v_x_3415_);
lean_dec(v_auxDeclToFullName_3412_);
lean_dec(v_givenName_3410_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3418_, lean_object* v_skipAuxDecl_3419_, lean_object* v_auxDeclToFullName_3420_, lean_object* v___x_3421_, lean_object* v_givenNameView_3422_, lean_object* v_as_3423_, lean_object* v_i_3424_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3425_; lean_object* v_res_3426_; 
v_skipAuxDecl_boxed_3425_ = lean_unbox(v_skipAuxDecl_3419_);
v_res_3426_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3418_, v_skipAuxDecl_boxed_3425_, v_auxDeclToFullName_3420_, v___x_3421_, v_givenNameView_3422_, v_as_3423_, v_i_3424_);
lean_dec_ref(v_as_3423_);
lean_dec(v_auxDeclToFullName_3420_);
lean_dec(v_givenName_3418_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3427_, uint8_t v_skipAuxDecl_3428_, lean_object* v_auxDeclToFullName_3429_, lean_object* v___x_3430_, lean_object* v_givenNameView_3431_, lean_object* v_t_3432_){
_start:
{
lean_object* v_root_3433_; lean_object* v_tail_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v_root_3433_ = lean_ctor_get(v_t_3432_, 0);
v_tail_3434_ = lean_ctor_get(v_t_3432_, 1);
v___x_3435_ = lean_array_get_size(v_tail_3434_);
lean_inc_ref(v_givenNameView_3431_);
lean_inc(v___x_3430_);
v___x_3436_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3427_, v_skipAuxDecl_3428_, v_auxDeclToFullName_3429_, v___x_3430_, v_givenNameView_3431_, v_tail_3434_, v___x_3435_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v___x_3437_; 
v___x_3437_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3427_, v_skipAuxDecl_3428_, v_auxDeclToFullName_3429_, v___x_3430_, v_givenNameView_3431_, v_root_3433_);
return v___x_3437_;
}
else
{
lean_dec_ref(v_givenNameView_3431_);
lean_dec(v___x_3430_);
return v___x_3436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3438_, lean_object* v_skipAuxDecl_3439_, lean_object* v_auxDeclToFullName_3440_, lean_object* v___x_3441_, lean_object* v_givenNameView_3442_, lean_object* v_t_3443_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3444_; lean_object* v_res_3445_; 
v_skipAuxDecl_boxed_3444_ = lean_unbox(v_skipAuxDecl_3439_);
v_res_3445_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3438_, v_skipAuxDecl_boxed_3444_, v_auxDeclToFullName_3440_, v___x_3441_, v_givenNameView_3442_, v_t_3443_);
lean_dec_ref(v_t_3443_);
lean_dec(v_auxDeclToFullName_3440_);
lean_dec(v_givenName_3438_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3446_, lean_object* v_currNamespace_3447_, lean_object* v_decls_3448_, lean_object* v_givenNameView_3449_, uint8_t v_skipAuxDecl_3450_){
_start:
{
lean_object* v_givenName_3451_; lean_object* v_localDecl_x3f_3452_; 
lean_inc_ref(v_givenNameView_3449_);
v_givenName_3451_ = l_Lean_MacroScopesView_review(v_givenNameView_3449_);
v_localDecl_x3f_3452_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3451_, v_skipAuxDecl_3450_, v_auxDeclToFullName_3446_, v_currNamespace_3447_, v_givenNameView_3449_, v_decls_3448_);
if (lean_obj_tag(v_localDecl_x3f_3452_) == 0)
{
if (v_skipAuxDecl_3450_ == 0)
{
lean_object* v___x_3453_; 
v___x_3453_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3452_, v_givenName_3451_, v_decls_3448_);
lean_dec(v_givenName_3451_);
return v___x_3453_;
}
else
{
lean_dec(v_givenName_3451_);
return v_localDecl_x3f_3452_;
}
}
else
{
lean_dec(v_givenName_3451_);
return v_localDecl_x3f_3452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3454_, lean_object* v_currNamespace_3455_, lean_object* v_decls_3456_, lean_object* v_givenNameView_3457_, lean_object* v_skipAuxDecl_3458_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3459_; lean_object* v_res_3460_; 
v_skipAuxDecl_boxed_3459_ = lean_unbox(v_skipAuxDecl_3458_);
v_res_3460_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3454_, v_currNamespace_3455_, v_decls_3456_, v_givenNameView_3457_, v_skipAuxDecl_boxed_3459_);
lean_dec_ref(v_decls_3456_);
lean_dec(v_auxDeclToFullName_3454_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_lctx_3469_; lean_object* v_decls_3470_; lean_object* v_auxDeclToFullName_3471_; lean_object* v_currNamespace_3472_; lean_object* v_view_3473_; lean_object* v_name_3474_; lean_object* v_findLocalDecl_x3f_3475_; lean_object* v___x_3476_; uint8_t v___x_3477_; lean_object* v___x_3478_; 
v_lctx_3469_ = lean_ctor_get(v___y_3464_, 2);
v_decls_3470_ = lean_ctor_get(v_lctx_3469_, 1);
v_auxDeclToFullName_3471_ = lean_ctor_get(v_lctx_3469_, 2);
v_currNamespace_3472_ = lean_ctor_get(v___y_3466_, 5);
v_view_3473_ = l_Lean_extractMacroScopes(v_n_3461_);
v_name_3474_ = lean_ctor_get(v_view_3473_, 0);
lean_inc(v_name_3474_);
lean_inc_ref(v_decls_3470_);
lean_inc(v_currNamespace_3472_);
lean_inc(v_auxDeclToFullName_3471_);
v_findLocalDecl_x3f_3475_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3475_, 0, v_auxDeclToFullName_3471_);
lean_closure_set(v_findLocalDecl_x3f_3475_, 1, v_currNamespace_3472_);
lean_closure_set(v_findLocalDecl_x3f_3475_, 2, v_decls_3470_);
v___x_3476_ = lean_box(0);
v___x_3477_ = 0;
v___x_3478_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3473_, v_findLocalDecl_x3f_3475_, v_name_3474_, v___x_3476_, v___x_3477_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
lean_dec_ref(v_view_3473_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3488_, lean_object* v_b_3489_){
_start:
{
if (lean_obj_tag(v_as_x27_3488_) == 0)
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3491_, 0, v_b_3489_);
return v___x_3491_;
}
else
{
lean_object* v_head_3492_; lean_object* v_tail_3493_; lean_object* v_config_3494_; lean_object* v_extensions_3495_; lean_object* v_extra_3496_; lean_object* v_extraInj_3497_; lean_object* v_extraFacts_3498_; lean_object* v_symPrios_3499_; lean_object* v_norm_3500_; lean_object* v_normProcs_3501_; lean_object* v_anchorRefs_x3f_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3511_; 
v_head_3492_ = lean_ctor_get(v_as_x27_3488_, 0);
v_tail_3493_ = lean_ctor_get(v_as_x27_3488_, 1);
v_config_3494_ = lean_ctor_get(v_b_3489_, 0);
v_extensions_3495_ = lean_ctor_get(v_b_3489_, 1);
v_extra_3496_ = lean_ctor_get(v_b_3489_, 2);
v_extraInj_3497_ = lean_ctor_get(v_b_3489_, 3);
v_extraFacts_3498_ = lean_ctor_get(v_b_3489_, 4);
v_symPrios_3499_ = lean_ctor_get(v_b_3489_, 5);
v_norm_3500_ = lean_ctor_get(v_b_3489_, 6);
v_normProcs_3501_ = lean_ctor_get(v_b_3489_, 7);
v_anchorRefs_x3f_3502_ = lean_ctor_get(v_b_3489_, 8);
v_isSharedCheck_3511_ = !lean_is_exclusive(v_b_3489_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3504_ = v_b_3489_;
v_isShared_3505_ = v_isSharedCheck_3511_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_anchorRefs_x3f_3502_);
lean_inc(v_normProcs_3501_);
lean_inc(v_norm_3500_);
lean_inc(v_symPrios_3499_);
lean_inc(v_extraFacts_3498_);
lean_inc(v_extraInj_3497_);
lean_inc(v_extra_3496_);
lean_inc(v_extensions_3495_);
lean_inc(v_config_3494_);
lean_dec(v_b_3489_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3511_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_inc(v_head_3492_);
v___x_3506_ = l_Lean_PersistentArray_push___redArg(v_extra_3496_, v_head_3492_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 2, v___x_3506_);
v___x_3508_ = v___x_3504_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_config_3494_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_extensions_3495_);
lean_ctor_set(v_reuseFailAlloc_3510_, 2, v___x_3506_);
lean_ctor_set(v_reuseFailAlloc_3510_, 3, v_extraInj_3497_);
lean_ctor_set(v_reuseFailAlloc_3510_, 4, v_extraFacts_3498_);
lean_ctor_set(v_reuseFailAlloc_3510_, 5, v_symPrios_3499_);
lean_ctor_set(v_reuseFailAlloc_3510_, 6, v_norm_3500_);
lean_ctor_set(v_reuseFailAlloc_3510_, 7, v_normProcs_3501_);
lean_ctor_set(v_reuseFailAlloc_3510_, 8, v_anchorRefs_x3f_3502_);
v___x_3508_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
v_as_x27_3488_ = v_tail_3493_;
v_b_3489_ = v___x_3508_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3512_, lean_object* v_b_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3512_, v_b_3513_);
lean_dec(v_as_x27_3512_);
return v_res_3515_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3518_ = l_Lean_stringToMessageData(v___x_3517_);
return v___x_3518_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3521_ = l_Lean_stringToMessageData(v___x_3520_);
return v___x_3521_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3524_ = l_Lean_stringToMessageData(v___x_3523_);
return v___x_3524_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3527_ = l_Lean_stringToMessageData(v___x_3526_);
return v___x_3527_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3530_ = l_Lean_stringToMessageData(v___x_3529_);
return v___x_3530_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3533_ = l_Lean_stringToMessageData(v___x_3532_);
return v___x_3533_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3536_ = l_Lean_stringToMessageData(v___x_3535_);
return v___x_3536_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3539_ = l_Lean_stringToMessageData(v___x_3538_);
return v___x_3539_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3542_ = l_Lean_stringToMessageData(v___x_3541_);
return v___x_3542_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3545_ = l_Lean_stringToMessageData(v___x_3544_);
return v___x_3545_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3548_ = l_Lean_stringToMessageData(v___x_3547_);
return v___x_3548_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3551_ = l_Lean_stringToMessageData(v___x_3550_);
return v___x_3551_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3554_ = l_Lean_stringToMessageData(v___x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3555_, lean_object* v_p_3556_, lean_object* v_mod_x3f_3557_, lean_object* v_id_3558_, uint8_t v_minIndexable_3559_, uint8_t v_only_3560_, uint8_t v_incremental_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
uint8_t v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; uint8_t v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v_a_3736_; lean_object* v___y_3973_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3984_ = lean_box(0);
lean_inc(v_id_3558_);
v___x_3985_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3558_, v___x_3984_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3985_, 1);
v_a_3736_ = v_a_3986_;
goto v___jp_3735_;
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_4062_; 
v_a_3987_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_3989_ = v___x_3985_;
v_isShared_3990_ = v_isSharedCheck_4062_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3985_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_4062_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3991_; uint8_t v___y_3993_; uint8_t v___x_4060_; 
v___x_3991_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4060_ = l_Lean_Exception_isInterrupt(v_a_3987_);
if (v___x_4060_ == 0)
{
uint8_t v___x_4061_; 
lean_inc(v_a_3987_);
v___x_4061_ = l_Lean_Exception_isRuntime(v_a_3987_);
v___y_3993_ = v___x_4061_;
goto v___jp_3992_;
}
else
{
v___y_3993_ = v___x_4060_;
goto v___jp_3992_;
}
v___jp_3992_:
{
if (v___y_3993_ == 0)
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
lean_del_object(v___x_3989_);
v___x_3994_ = l_Lean_TSyntax_getId(v_id_3558_);
lean_inc(v___x_3994_);
v___x_3995_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_3994_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_3996_);
lean_dec_ref_known(v___x_3995_, 1);
if (lean_obj_tag(v_a_3996_) == 0)
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_3994_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4026_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4000_ = v___x_3997_;
v_isShared_4001_ = v_isSharedCheck_4026_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4026_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
if (lean_obj_tag(v_a_3998_) == 1)
{
lean_del_object(v___x_4000_);
lean_dec(v_a_3987_);
if (lean_obj_tag(v_mod_x3f_3557_) == 1)
{
lean_object* v_val_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec_ref_known(v_a_3998_, 1);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_val_4002_ = lean_ctor_get(v_mod_x3f_3557_, 0);
lean_inc(v_val_4002_);
lean_dec_ref_known(v_mod_x3f_3557_, 1);
v___x_4003_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4004_ = l_Lean_MessageData_ofName(v___x_3994_);
v___x_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4003_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
v___x_4006_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4005_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
v___x_4008_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4002_, v___x_4007_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec(v_val_4002_);
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_4008_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_4008_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
else
{
lean_object* v_val_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_dec(v___x_3994_);
v_val_4017_ = lean_ctor_get(v_a_3998_, 0);
lean_inc(v_val_4017_);
lean_dec_ref_known(v_a_3998_, 1);
v___x_4018_ = lean_box(0);
lean_inc_ref(v_params_3555_);
v___x_4019_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3555_, v_val_4017_, v___x_3991_, v___x_4018_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec(v_val_4017_);
v___y_3973_ = v___x_4019_;
goto v___jp_3972_;
}
}
else
{
lean_object* v___x_4020_; uint8_t v___x_4021_; 
lean_dec(v_a_3998_);
v___x_4020_ = l_Lean_Name_getPrefix(v___x_3994_);
lean_dec(v___x_3994_);
v___x_4021_ = l_Lean_Name_isAnonymous(v___x_4020_);
lean_dec(v___x_4020_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; 
lean_del_object(v___x_4000_);
lean_dec(v_a_3987_);
v___x_4022_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3555_, v_p_3556_, v_mod_x3f_3557_, v_id_3558_, v_minIndexable_3559_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
return v___x_4022_;
}
else
{
lean_object* v___x_4024_; 
lean_dec(v_id_3558_);
lean_dec(v_mod_x3f_3557_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set_tag(v___x_4000_, 1);
lean_ctor_set(v___x_4000_, 0, v_a_3987_);
v___x_4024_ = v___x_4000_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_3987_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec(v___x_3994_);
lean_dec(v_a_3987_);
lean_dec(v_id_3558_);
lean_dec(v_mod_x3f_3557_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_4027_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_3997_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_3997_);
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
else
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec_ref_known(v_a_3996_, 1);
lean_dec(v___x_3994_);
lean_dec(v_a_3987_);
lean_dec(v_mod_x3f_3557_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v___x_4035_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3558_);
v___x_4036_ = l_Lean_MessageData_ofSyntax(v_id_3558_);
v___x_4037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4035_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_4039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4037_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
v___x_4040_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3558_, v___x_4039_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec(v_id_3558_);
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4040_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4040_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec(v___x_3994_);
lean_dec(v_a_3987_);
lean_dec(v_id_3558_);
lean_dec(v_mod_x3f_3557_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_4049_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_3995_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_3995_);
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
else
{
lean_object* v___x_4058_; 
lean_dec(v_id_3558_);
lean_dec(v_mod_x3f_3557_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
if (v_isShared_3990_ == 0)
{
v___x_4058_ = v___x_3989_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_3987_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
}
v___jp_3569_:
{
uint8_t v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = 0;
lean_inc(v___y_3571_);
v___x_3579_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3571_, v___x_3578_, v___y_3576_, v___y_3577_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
if (lean_obj_tag(v_a_3580_) == 1)
{
lean_object* v_val_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
lean_dec(v___y_3571_);
v_val_3581_ = lean_ctor_get(v_a_3580_, 0);
lean_inc_n(v_val_3581_, 2);
lean_dec_ref_known(v_a_3580_, 1);
v___x_3582_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3555_, v_val_3581_, v___x_3578_);
v___x_3583_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3581_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3594_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3586_ = v___x_3583_;
v_isShared_3587_ = v_isSharedCheck_3594_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3583_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3594_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
if (lean_obj_tag(v_a_3584_) == 1)
{
lean_object* v_val_3588_; lean_object* v_ctors_3589_; lean_object* v___x_3590_; 
lean_del_object(v___x_3586_);
v_val_3588_ = lean_ctor_get(v_a_3584_, 0);
lean_inc(v_val_3588_);
lean_dec_ref_known(v_a_3584_, 1);
v_ctors_3589_ = lean_ctor_get(v_val_3588_, 4);
lean_inc(v_ctors_3589_);
lean_dec(v_val_3588_);
v___x_3590_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3556_, v_id_3558_, v_minIndexable_3559_, v_ctors_3589_, v___x_3582_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec(v_ctors_3589_);
lean_dec(v_p_3556_);
return v___x_3590_;
}
else
{
lean_object* v___x_3592_; 
lean_dec(v_a_3584_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3582_);
v___x_3592_ = v___x_3586_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3582_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec_ref(v___x_3582_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
v_a_3595_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3583_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3583_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_toCold_3603_; lean_object* v_options_3604_; lean_object* v_currRecDepth_3605_; lean_object* v_maxRecDepth_3606_; lean_object* v_ref_3607_; lean_object* v_currNamespace_3608_; lean_object* v_openDecls_3609_; lean_object* v_initHeartbeats_3610_; lean_object* v_maxHeartbeats_3611_; lean_object* v_currMacroScope_3612_; uint8_t v_diag_3613_; uint8_t v_suppressElabErrors_3614_; lean_object* v___x_3615_; lean_object* v_ref_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_dec(v_a_3580_);
v_toCold_3603_ = lean_ctor_get(v___y_3576_, 0);
v_options_3604_ = lean_ctor_get(v___y_3576_, 1);
v_currRecDepth_3605_ = lean_ctor_get(v___y_3576_, 2);
v_maxRecDepth_3606_ = lean_ctor_get(v___y_3576_, 3);
v_ref_3607_ = lean_ctor_get(v___y_3576_, 4);
v_currNamespace_3608_ = lean_ctor_get(v___y_3576_, 5);
v_openDecls_3609_ = lean_ctor_get(v___y_3576_, 6);
v_initHeartbeats_3610_ = lean_ctor_get(v___y_3576_, 7);
v_maxHeartbeats_3611_ = lean_ctor_get(v___y_3576_, 8);
v_currMacroScope_3612_ = lean_ctor_get(v___y_3576_, 9);
v_diag_3613_ = lean_ctor_get_uint8(v___y_3576_, sizeof(void*)*10);
v_suppressElabErrors_3614_ = lean_ctor_get_uint8(v___y_3576_, sizeof(void*)*10 + 1);
v___x_3615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_3616_ = l_Lean_replaceRef(v_p_3556_, v_ref_3607_);
lean_dec(v_p_3556_);
lean_inc(v_currMacroScope_3612_);
lean_inc(v_maxHeartbeats_3611_);
lean_inc(v_initHeartbeats_3610_);
lean_inc(v_openDecls_3609_);
lean_inc(v_currNamespace_3608_);
lean_inc(v_maxRecDepth_3606_);
lean_inc(v_currRecDepth_3605_);
lean_inc_ref(v_options_3604_);
lean_inc_ref(v_toCold_3603_);
v___x_3617_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3617_, 0, v_toCold_3603_);
lean_ctor_set(v___x_3617_, 1, v_options_3604_);
lean_ctor_set(v___x_3617_, 2, v_currRecDepth_3605_);
lean_ctor_set(v___x_3617_, 3, v_maxRecDepth_3606_);
lean_ctor_set(v___x_3617_, 4, v_ref_3616_);
lean_ctor_set(v___x_3617_, 5, v_currNamespace_3608_);
lean_ctor_set(v___x_3617_, 6, v_openDecls_3609_);
lean_ctor_set(v___x_3617_, 7, v_initHeartbeats_3610_);
lean_ctor_set(v___x_3617_, 8, v_maxHeartbeats_3611_);
lean_ctor_set(v___x_3617_, 9, v_currMacroScope_3612_);
lean_ctor_set_uint8(v___x_3617_, sizeof(void*)*10, v_diag_3613_);
lean_ctor_set_uint8(v___x_3617_, sizeof(void*)*10 + 1, v_suppressElabErrors_3614_);
v___x_3618_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3555_, v_id_3558_, v___y_3571_, v___x_3615_, v_minIndexable_3559_, v___y_3570_, v___y_3570_, v___y_3574_, v___y_3575_, v___x_3617_, v___y_3577_);
lean_dec_ref_known(v___x_3617_, 10);
return v___x_3618_;
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec(v___y_3571_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_3619_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3579_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3579_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
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
v___jp_3627_:
{
lean_object* v___x_3636_; 
v___x_3636_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3559_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
lean_dec_ref_known(v___x_3636_, 1);
v___x_3637_ = l_Lean_Meta_Grind_grindExt;
v___x_3638_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3637_, v___y_3635_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3638_, 1);
lean_inc(v___y_3629_);
v___x_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3640_, 0, v___y_3629_);
v___x_3641_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3639_, v___x_3640_);
lean_dec_ref_known(v___x_3640_, 1);
lean_dec(v_a_3639_);
v___x_3642_ = lean_box(0);
v___x_3643_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3628_, v___x_3641_, v___x_3642_);
lean_dec(v___y_3628_);
v___x_3644_ = l_List_isEmpty___redArg(v___x_3643_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; 
lean_dec(v___y_3629_);
lean_dec(v_p_3556_);
v___x_3645_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3643_, v_params_3555_);
lean_dec(v___x_3643_);
return v___x_3645_;
}
else
{
lean_object* v___x_3646_; uint8_t v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_dec(v___x_3643_);
lean_dec_ref(v_params_3555_);
v___x_3646_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3647_ = 0;
v___x_3648_ = l_Lean_MessageData_ofConstName(v___y_3629_, v___x_3647_);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3646_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3556_, v___x_3651_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v_p_3556_);
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_3661_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3638_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3638_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_dec(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_3669_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3636_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3636_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
v___jp_3677_:
{
lean_object* v___x_3684_; 
v___x_3684_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3559_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_toCold_3685_; lean_object* v_options_3686_; lean_object* v_currRecDepth_3687_; lean_object* v_maxRecDepth_3688_; lean_object* v_ref_3689_; lean_object* v_currNamespace_3690_; lean_object* v_openDecls_3691_; lean_object* v_initHeartbeats_3692_; lean_object* v_maxHeartbeats_3693_; lean_object* v_currMacroScope_3694_; uint8_t v_diag_3695_; uint8_t v_suppressElabErrors_3696_; lean_object* v_ref_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec_ref_known(v___x_3684_, 1);
v_toCold_3685_ = lean_ctor_get(v___y_3682_, 0);
v_options_3686_ = lean_ctor_get(v___y_3682_, 1);
v_currRecDepth_3687_ = lean_ctor_get(v___y_3682_, 2);
v_maxRecDepth_3688_ = lean_ctor_get(v___y_3682_, 3);
v_ref_3689_ = lean_ctor_get(v___y_3682_, 4);
v_currNamespace_3690_ = lean_ctor_get(v___y_3682_, 5);
v_openDecls_3691_ = lean_ctor_get(v___y_3682_, 6);
v_initHeartbeats_3692_ = lean_ctor_get(v___y_3682_, 7);
v_maxHeartbeats_3693_ = lean_ctor_get(v___y_3682_, 8);
v_currMacroScope_3694_ = lean_ctor_get(v___y_3682_, 9);
v_diag_3695_ = lean_ctor_get_uint8(v___y_3682_, sizeof(void*)*10);
v_suppressElabErrors_3696_ = lean_ctor_get_uint8(v___y_3682_, sizeof(void*)*10 + 1);
v_ref_3697_ = l_Lean_replaceRef(v_p_3556_, v_ref_3689_);
lean_dec(v_p_3556_);
lean_inc(v_currMacroScope_3694_);
lean_inc(v_maxHeartbeats_3693_);
lean_inc(v_initHeartbeats_3692_);
lean_inc(v_openDecls_3691_);
lean_inc(v_currNamespace_3690_);
lean_inc(v_maxRecDepth_3688_);
lean_inc(v_currRecDepth_3687_);
lean_inc_ref(v_options_3686_);
lean_inc_ref(v_toCold_3685_);
v___x_3698_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3698_, 0, v_toCold_3685_);
lean_ctor_set(v___x_3698_, 1, v_options_3686_);
lean_ctor_set(v___x_3698_, 2, v_currRecDepth_3687_);
lean_ctor_set(v___x_3698_, 3, v_maxRecDepth_3688_);
lean_ctor_set(v___x_3698_, 4, v_ref_3697_);
lean_ctor_set(v___x_3698_, 5, v_currNamespace_3690_);
lean_ctor_set(v___x_3698_, 6, v_openDecls_3691_);
lean_ctor_set(v___x_3698_, 7, v_initHeartbeats_3692_);
lean_ctor_set(v___x_3698_, 8, v_maxHeartbeats_3693_);
lean_ctor_set(v___x_3698_, 9, v_currMacroScope_3694_);
lean_ctor_set_uint8(v___x_3698_, sizeof(void*)*10, v_diag_3695_);
lean_ctor_set_uint8(v___x_3698_, sizeof(void*)*10 + 1, v_suppressElabErrors_3696_);
lean_inc(v___y_3679_);
v___x_3699_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3679_, v___y_3678_, v___x_3698_, v___y_3683_);
lean_dec_ref_known(v___x_3698_, 10);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3707_; 
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; 
v_unused_3708_ = lean_ctor_get(v___x_3699_, 0);
lean_dec(v_unused_3708_);
v___x_3701_ = v___x_3699_;
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
else
{
lean_dec(v___x_3699_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3555_, v___y_3679_, v___y_3678_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3703_);
v___x_3705_ = v___x_3701_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec(v___y_3679_);
lean_dec_ref(v_params_3555_);
v_a_3709_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3699_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3699_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec(v___y_3679_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_3717_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3684_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3684_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
v___jp_3725_:
{
lean_object* v_ctors_3733_; lean_object* v___x_3734_; 
v_ctors_3733_ = lean_ctor_get(v___y_3726_, 4);
lean_inc(v_ctors_3733_);
lean_dec_ref(v___y_3726_);
v___x_3734_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3556_, v_id_3558_, v_minIndexable_3559_, v_ctors_3733_, v_params_3555_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v_ctors_3733_);
lean_dec(v_p_3556_);
return v___x_3734_;
}
v___jp_3735_:
{
uint8_t v___x_3737_; lean_object* v___x_3738_; 
v___x_3737_ = 1;
lean_inc(v_a_3736_);
v___x_3738_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_3736_, v___x_3737_, v_a_3562_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_dec_ref_known(v___x_3738_, 1);
if (lean_obj_tag(v_mod_x3f_3557_) == 1)
{
lean_object* v_val_3739_; lean_object* v___x_3740_; 
v_val_3739_ = lean_ctor_get(v_mod_x3f_3557_, 0);
lean_inc(v_val_3739_);
lean_dec_ref_known(v_mod_x3f_3557_, 1);
v___x_3740_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3739_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3955_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3743_ = v___x_3740_;
v_isShared_3744_ = v_isSharedCheck_3955_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3740_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3955_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
switch(lean_obj_tag(v_a_3741_))
{
case 0:
{
lean_object* v_k_3745_; 
lean_del_object(v___x_3743_);
v_k_3745_ = lean_ctor_get(v_a_3741_, 0);
lean_inc(v_k_3745_);
lean_dec_ref_known(v_a_3741_, 1);
if (lean_obj_tag(v_k_3745_) == 9)
{
lean_dec(v_id_3558_);
if (v_only_3560_ == 0)
{
lean_object* v_toCold_3746_; lean_object* v_options_3747_; lean_object* v_currRecDepth_3748_; lean_object* v_maxRecDepth_3749_; lean_object* v_ref_3750_; lean_object* v_currNamespace_3751_; lean_object* v_openDecls_3752_; lean_object* v_initHeartbeats_3753_; lean_object* v_maxHeartbeats_3754_; lean_object* v_currMacroScope_3755_; uint8_t v_diag_3756_; uint8_t v_suppressElabErrors_3757_; lean_object* v_ref_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v_toCold_3746_ = lean_ctor_get(v_a_3566_, 0);
v_options_3747_ = lean_ctor_get(v_a_3566_, 1);
v_currRecDepth_3748_ = lean_ctor_get(v_a_3566_, 2);
v_maxRecDepth_3749_ = lean_ctor_get(v_a_3566_, 3);
v_ref_3750_ = lean_ctor_get(v_a_3566_, 4);
v_currNamespace_3751_ = lean_ctor_get(v_a_3566_, 5);
v_openDecls_3752_ = lean_ctor_get(v_a_3566_, 6);
v_initHeartbeats_3753_ = lean_ctor_get(v_a_3566_, 7);
v_maxHeartbeats_3754_ = lean_ctor_get(v_a_3566_, 8);
v_currMacroScope_3755_ = lean_ctor_get(v_a_3566_, 9);
v_diag_3756_ = lean_ctor_get_uint8(v_a_3566_, sizeof(void*)*10);
v_suppressElabErrors_3757_ = lean_ctor_get_uint8(v_a_3566_, sizeof(void*)*10 + 1);
v_ref_3758_ = l_Lean_replaceRef(v_p_3556_, v_ref_3750_);
lean_inc(v_currMacroScope_3755_);
lean_inc(v_maxHeartbeats_3754_);
lean_inc(v_initHeartbeats_3753_);
lean_inc(v_openDecls_3752_);
lean_inc(v_currNamespace_3751_);
lean_inc(v_maxRecDepth_3749_);
lean_inc(v_currRecDepth_3748_);
lean_inc_ref(v_options_3747_);
lean_inc_ref(v_toCold_3746_);
v___x_3759_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3759_, 0, v_toCold_3746_);
lean_ctor_set(v___x_3759_, 1, v_options_3747_);
lean_ctor_set(v___x_3759_, 2, v_currRecDepth_3748_);
lean_ctor_set(v___x_3759_, 3, v_maxRecDepth_3749_);
lean_ctor_set(v___x_3759_, 4, v_ref_3758_);
lean_ctor_set(v___x_3759_, 5, v_currNamespace_3751_);
lean_ctor_set(v___x_3759_, 6, v_openDecls_3752_);
lean_ctor_set(v___x_3759_, 7, v_initHeartbeats_3753_);
lean_ctor_set(v___x_3759_, 8, v_maxHeartbeats_3754_);
lean_ctor_set(v___x_3759_, 9, v_currMacroScope_3755_);
lean_ctor_set_uint8(v___x_3759_, sizeof(void*)*10, v_diag_3756_);
lean_ctor_set_uint8(v___x_3759_, sizeof(void*)*10 + 1, v_suppressElabErrors_3757_);
v___x_3760_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3759_, v_a_3567_);
lean_dec_ref_known(v___x_3759_, 10);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_dec_ref_known(v___x_3760_, 1);
v___y_3628_ = v_k_3745_;
v___y_3629_ = v_a_3736_;
v___y_3630_ = v_a_3562_;
v___y_3631_ = v_a_3563_;
v___y_3632_ = v_a_3564_;
v___y_3633_ = v_a_3565_;
v___y_3634_ = v_a_3566_;
v___y_3635_ = v_a_3567_;
goto v___jp_3627_;
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3736_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
v___y_3628_ = v_k_3745_;
v___y_3629_ = v_a_3736_;
v___y_3630_ = v_a_3562_;
v___y_3631_ = v_a_3563_;
v___y_3632_ = v_a_3564_;
v___y_3633_ = v_a_3565_;
v___y_3634_ = v_a_3566_;
v___y_3635_ = v_a_3567_;
goto v___jp_3627_;
}
}
else
{
lean_object* v_toCold_3769_; lean_object* v_options_3770_; lean_object* v_currRecDepth_3771_; lean_object* v_maxRecDepth_3772_; lean_object* v_ref_3773_; lean_object* v_currNamespace_3774_; lean_object* v_openDecls_3775_; lean_object* v_initHeartbeats_3776_; lean_object* v_maxHeartbeats_3777_; lean_object* v_currMacroScope_3778_; uint8_t v_diag_3779_; uint8_t v_suppressElabErrors_3780_; uint8_t v___x_3781_; lean_object* v_ref_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_toCold_3769_ = lean_ctor_get(v_a_3566_, 0);
v_options_3770_ = lean_ctor_get(v_a_3566_, 1);
v_currRecDepth_3771_ = lean_ctor_get(v_a_3566_, 2);
v_maxRecDepth_3772_ = lean_ctor_get(v_a_3566_, 3);
v_ref_3773_ = lean_ctor_get(v_a_3566_, 4);
v_currNamespace_3774_ = lean_ctor_get(v_a_3566_, 5);
v_openDecls_3775_ = lean_ctor_get(v_a_3566_, 6);
v_initHeartbeats_3776_ = lean_ctor_get(v_a_3566_, 7);
v_maxHeartbeats_3777_ = lean_ctor_get(v_a_3566_, 8);
v_currMacroScope_3778_ = lean_ctor_get(v_a_3566_, 9);
v_diag_3779_ = lean_ctor_get_uint8(v_a_3566_, sizeof(void*)*10);
v_suppressElabErrors_3780_ = lean_ctor_get_uint8(v_a_3566_, sizeof(void*)*10 + 1);
v___x_3781_ = 0;
v_ref_3782_ = l_Lean_replaceRef(v_p_3556_, v_ref_3773_);
lean_dec(v_p_3556_);
lean_inc(v_currMacroScope_3778_);
lean_inc(v_maxHeartbeats_3777_);
lean_inc(v_initHeartbeats_3776_);
lean_inc(v_openDecls_3775_);
lean_inc(v_currNamespace_3774_);
lean_inc(v_maxRecDepth_3772_);
lean_inc(v_currRecDepth_3771_);
lean_inc_ref(v_options_3770_);
lean_inc_ref(v_toCold_3769_);
v___x_3783_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3783_, 0, v_toCold_3769_);
lean_ctor_set(v___x_3783_, 1, v_options_3770_);
lean_ctor_set(v___x_3783_, 2, v_currRecDepth_3771_);
lean_ctor_set(v___x_3783_, 3, v_maxRecDepth_3772_);
lean_ctor_set(v___x_3783_, 4, v_ref_3782_);
lean_ctor_set(v___x_3783_, 5, v_currNamespace_3774_);
lean_ctor_set(v___x_3783_, 6, v_openDecls_3775_);
lean_ctor_set(v___x_3783_, 7, v_initHeartbeats_3776_);
lean_ctor_set(v___x_3783_, 8, v_maxHeartbeats_3777_);
lean_ctor_set(v___x_3783_, 9, v_currMacroScope_3778_);
lean_ctor_set_uint8(v___x_3783_, sizeof(void*)*10, v_diag_3779_);
lean_ctor_set_uint8(v___x_3783_, sizeof(void*)*10 + 1, v_suppressElabErrors_3780_);
v___x_3784_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3555_, v_id_3558_, v_a_3736_, v_k_3745_, v_minIndexable_3559_, v___x_3781_, v___x_3737_, v_a_3564_, v_a_3565_, v___x_3783_, v_a_3567_);
lean_dec_ref_known(v___x_3783_, 10);
return v___x_3784_;
}
}
case 1:
{
lean_del_object(v___x_3743_);
lean_dec(v_id_3558_);
if (v_incremental_3561_ == 0)
{
uint8_t v_eager_3785_; 
v_eager_3785_ = lean_ctor_get_uint8(v_a_3741_, 0);
lean_dec_ref_known(v_a_3741_, 0);
v___y_3678_ = v_eager_3785_;
v___y_3679_ = v_a_3736_;
v___y_3680_ = v_a_3564_;
v___y_3681_ = v_a_3565_;
v___y_3682_ = v_a_3566_;
v___y_3683_ = v_a_3567_;
goto v___jp_3677_;
}
else
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref_known(v_a_3741_, 0);
lean_dec(v_a_3736_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v___x_3786_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3787_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3786_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
case 2:
{
uint8_t v___x_3796_; lean_object* v___x_3797_; 
lean_del_object(v___x_3743_);
v___x_3796_ = 0;
lean_inc(v_a_3736_);
v___x_3797_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3736_, v___x_3796_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
if (lean_obj_tag(v_a_3798_) == 1)
{
lean_dec(v_a_3736_);
if (v_incremental_3561_ == 0)
{
lean_object* v_val_3799_; 
v_val_3799_ = lean_ctor_get(v_a_3798_, 0);
lean_inc(v_val_3799_);
lean_dec_ref_known(v_a_3798_, 1);
v___y_3726_ = v_val_3799_;
v___y_3727_ = v_a_3562_;
v___y_3728_ = v_a_3563_;
v___y_3729_ = v_a_3564_;
v___y_3730_ = v_a_3565_;
v___y_3731_ = v_a_3566_;
v___y_3732_ = v_a_3567_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref_known(v_a_3798_, 1);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v___x_3800_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3801_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3800_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec(v_a_3798_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v___x_3810_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_3811_ = l_Lean_MessageData_ofConstName(v_a_3736_, v___x_3796_);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3814_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3815_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec(v_a_3736_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_3824_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3797_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3797_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
case 3:
{
lean_del_object(v___x_3743_);
v___y_3570_ = v___x_3737_;
v___y_3571_ = v_a_3736_;
v___y_3572_ = v_a_3562_;
v___y_3573_ = v_a_3563_;
v___y_3574_ = v_a_3564_;
v___y_3575_ = v_a_3565_;
v___y_3576_ = v_a_3566_;
v___y_3577_ = v_a_3567_;
goto v___jp_3569_;
}
case 4:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_del_object(v___x_3743_);
lean_dec(v_a_3736_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v___x_3832_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_3833_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3832_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
case 5:
{
lean_object* v_prio_3842_; lean_object* v___x_3843_; 
lean_del_object(v___x_3743_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
v_prio_3842_ = lean_ctor_get(v_a_3741_, 0);
lean_inc(v_prio_3842_);
lean_dec_ref_known(v_a_3741_, 1);
v___x_3843_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3559_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3867_; 
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3867_ == 0)
{
lean_object* v_unused_3868_; 
v_unused_3868_ = lean_ctor_get(v___x_3843_, 0);
lean_dec(v_unused_3868_);
v___x_3845_ = v___x_3843_;
v_isShared_3846_ = v_isSharedCheck_3867_;
goto v_resetjp_3844_;
}
else
{
lean_dec(v___x_3843_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3867_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v_config_3847_; lean_object* v_extensions_3848_; lean_object* v_extra_3849_; lean_object* v_extraInj_3850_; lean_object* v_extraFacts_3851_; lean_object* v_symPrios_3852_; lean_object* v_norm_3853_; lean_object* v_normProcs_3854_; lean_object* v_anchorRefs_x3f_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3866_; 
v_config_3847_ = lean_ctor_get(v_params_3555_, 0);
v_extensions_3848_ = lean_ctor_get(v_params_3555_, 1);
v_extra_3849_ = lean_ctor_get(v_params_3555_, 2);
v_extraInj_3850_ = lean_ctor_get(v_params_3555_, 3);
v_extraFacts_3851_ = lean_ctor_get(v_params_3555_, 4);
v_symPrios_3852_ = lean_ctor_get(v_params_3555_, 5);
v_norm_3853_ = lean_ctor_get(v_params_3555_, 6);
v_normProcs_3854_ = lean_ctor_get(v_params_3555_, 7);
v_anchorRefs_x3f_3855_ = lean_ctor_get(v_params_3555_, 8);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_params_3555_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3857_ = v_params_3555_;
v_isShared_3858_ = v_isSharedCheck_3866_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_anchorRefs_x3f_3855_);
lean_inc(v_normProcs_3854_);
lean_inc(v_norm_3853_);
lean_inc(v_symPrios_3852_);
lean_inc(v_extraFacts_3851_);
lean_inc(v_extraInj_3850_);
lean_inc(v_extra_3849_);
lean_inc(v_extensions_3848_);
lean_inc(v_config_3847_);
lean_dec(v_params_3555_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3866_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3859_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_3852_, v_a_3736_, v_prio_3842_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 5, v___x_3859_);
v___x_3861_ = v___x_3857_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_config_3847_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_extensions_3848_);
lean_ctor_set(v_reuseFailAlloc_3865_, 2, v_extra_3849_);
lean_ctor_set(v_reuseFailAlloc_3865_, 3, v_extraInj_3850_);
lean_ctor_set(v_reuseFailAlloc_3865_, 4, v_extraFacts_3851_);
lean_ctor_set(v_reuseFailAlloc_3865_, 5, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3865_, 6, v_norm_3853_);
lean_ctor_set(v_reuseFailAlloc_3865_, 7, v_normProcs_3854_);
lean_ctor_set(v_reuseFailAlloc_3865_, 8, v_anchorRefs_x3f_3855_);
v___x_3861_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3863_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3861_);
v___x_3863_ = v___x_3845_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_dec(v_prio_3842_);
lean_dec(v_a_3736_);
lean_dec_ref(v_params_3555_);
v_a_3869_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3843_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3843_);
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
case 6:
{
lean_object* v___x_3877_; 
lean_del_object(v___x_3743_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
v___x_3877_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3736_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3902_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3902_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3902_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v_config_3882_; lean_object* v_extensions_3883_; lean_object* v_extra_3884_; lean_object* v_extraInj_3885_; lean_object* v_extraFacts_3886_; lean_object* v_symPrios_3887_; lean_object* v_norm_3888_; lean_object* v_normProcs_3889_; lean_object* v_anchorRefs_x3f_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3901_; 
v_config_3882_ = lean_ctor_get(v_params_3555_, 0);
v_extensions_3883_ = lean_ctor_get(v_params_3555_, 1);
v_extra_3884_ = lean_ctor_get(v_params_3555_, 2);
v_extraInj_3885_ = lean_ctor_get(v_params_3555_, 3);
v_extraFacts_3886_ = lean_ctor_get(v_params_3555_, 4);
v_symPrios_3887_ = lean_ctor_get(v_params_3555_, 5);
v_norm_3888_ = lean_ctor_get(v_params_3555_, 6);
v_normProcs_3889_ = lean_ctor_get(v_params_3555_, 7);
v_anchorRefs_x3f_3890_ = lean_ctor_get(v_params_3555_, 8);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_params_3555_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3892_ = v_params_3555_;
v_isShared_3893_ = v_isSharedCheck_3901_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_anchorRefs_x3f_3890_);
lean_inc(v_normProcs_3889_);
lean_inc(v_norm_3888_);
lean_inc(v_symPrios_3887_);
lean_inc(v_extraFacts_3886_);
lean_inc(v_extraInj_3885_);
lean_inc(v_extra_3884_);
lean_inc(v_extensions_3883_);
lean_inc(v_config_3882_);
lean_dec(v_params_3555_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3901_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3894_ = l_Lean_PersistentArray_push___redArg(v_extraInj_3885_, v_a_3878_);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 3, v___x_3894_);
v___x_3896_ = v___x_3892_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_config_3882_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v_extensions_3883_);
lean_ctor_set(v_reuseFailAlloc_3900_, 2, v_extra_3884_);
lean_ctor_set(v_reuseFailAlloc_3900_, 3, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3900_, 4, v_extraFacts_3886_);
lean_ctor_set(v_reuseFailAlloc_3900_, 5, v_symPrios_3887_);
lean_ctor_set(v_reuseFailAlloc_3900_, 6, v_norm_3888_);
lean_ctor_set(v_reuseFailAlloc_3900_, 7, v_normProcs_3889_);
lean_ctor_set(v_reuseFailAlloc_3900_, 8, v_anchorRefs_x3f_3890_);
v___x_3896_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3898_; 
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 0, v___x_3896_);
v___x_3898_ = v___x_3880_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec_ref(v_params_3555_);
v_a_3903_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3877_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3877_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
case 7:
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
v___x_3911_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3555_, v_a_3736_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v___x_3911_);
v___x_3913_ = v___x_3743_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
case 8:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_dec_ref_known(v_a_3741_, 0);
lean_del_object(v___x_3743_);
lean_dec(v_a_3736_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v___x_3915_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_3916_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3915_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3916_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3916_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
case 9:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_del_object(v___x_3743_);
lean_dec(v_a_3736_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v___x_3925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_3926_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3925_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3926_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3926_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
case 10:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_del_object(v___x_3743_);
lean_dec(v_a_3736_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v___x_3935_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_3936_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3935_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3936_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3936_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
default: 
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_del_object(v___x_3743_);
lean_dec(v_a_3736_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v___x_3945_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_3946_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3945_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3946_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3946_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3946_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec(v_a_3736_);
lean_dec(v_id_3558_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_3956_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3740_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3740_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3557_);
v___y_3570_ = v___x_3737_;
v___y_3571_ = v_a_3736_;
v___y_3572_ = v_a_3562_;
v___y_3573_ = v_a_3563_;
v___y_3574_ = v_a_3564_;
v___y_3575_ = v_a_3565_;
v___y_3576_ = v_a_3566_;
v___y_3577_ = v_a_3567_;
goto v___jp_3569_;
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec(v_a_3736_);
lean_dec(v_id_3558_);
lean_dec(v_mod_x3f_3557_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_3964_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3738_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3738_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
v___jp_3972_:
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3983_; 
v_a_3974_ = lean_ctor_get(v___y_3973_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___y_3973_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3976_ = v___y_3973_;
v_isShared_3977_ = v_isSharedCheck_3983_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___y_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3983_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
if (lean_obj_tag(v_a_3974_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3980_; 
lean_dec(v_id_3558_);
lean_dec(v_mod_x3f_3557_);
lean_dec(v_p_3556_);
lean_dec_ref(v_params_3555_);
v_a_3978_ = lean_ctor_get(v_a_3974_, 0);
lean_inc(v_a_3978_);
lean_dec_ref_known(v_a_3974_, 1);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v_a_3978_);
v___x_3980_ = v___x_3976_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
else
{
lean_object* v_a_3982_; 
lean_del_object(v___x_3976_);
v_a_3982_ = lean_ctor_get(v_a_3974_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v_a_3974_, 1);
v_a_3736_ = v_a_3982_;
goto v___jp_3735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4063_, lean_object* v_p_4064_, lean_object* v_mod_x3f_4065_, lean_object* v_id_4066_, lean_object* v_minIndexable_4067_, lean_object* v_only_4068_, lean_object* v_incremental_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_){
_start:
{
uint8_t v_minIndexable_boxed_4077_; uint8_t v_only_boxed_4078_; uint8_t v_incremental_boxed_4079_; lean_object* v_res_4080_; 
v_minIndexable_boxed_4077_ = lean_unbox(v_minIndexable_4067_);
v_only_boxed_4078_ = lean_unbox(v_only_4068_);
v_incremental_boxed_4079_ = lean_unbox(v_incremental_4069_);
v_res_4080_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4063_, v_p_4064_, v_mod_x3f_4065_, v_id_4066_, v_minIndexable_boxed_4077_, v_only_boxed_4078_, v_incremental_boxed_4079_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
lean_dec(v_a_4073_);
lean_dec_ref(v_a_4072_);
lean_dec(v_a_4071_);
lean_dec_ref(v_a_4070_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4081_, lean_object* v_id_4082_, uint8_t v_minIndexable_4083_, lean_object* v_as_4084_, lean_object* v_as_x27_4085_, lean_object* v_b_4086_, lean_object* v_a_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4081_, v_id_4082_, v_minIndexable_4083_, v_as_x27_4085_, v_b_4086_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4096_, lean_object* v_id_4097_, lean_object* v_minIndexable_4098_, lean_object* v_as_4099_, lean_object* v_as_x27_4100_, lean_object* v_b_4101_, lean_object* v_a_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
uint8_t v_minIndexable_boxed_4110_; lean_object* v_res_4111_; 
v_minIndexable_boxed_4110_ = lean_unbox(v_minIndexable_4098_);
v_res_4111_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4096_, v_id_4097_, v_minIndexable_boxed_4110_, v_as_4099_, v_as_x27_4100_, v_b_4101_, v_a_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v_as_x27_4100_);
lean_dec(v_as_4099_);
lean_dec(v_p_4096_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4112_, lean_object* v_as_x27_4113_, lean_object* v_b_4114_, lean_object* v_a_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4113_, v_b_4114_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4124_, lean_object* v_as_x27_4125_, lean_object* v_b_4126_, lean_object* v_a_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4124_, v_as_x27_4125_, v_b_4126_, v_a_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v_as_x27_4125_);
lean_dec(v_as_4124_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4136_, lean_object* v_ref_4137_, lean_object* v_msg_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4137_, v_msg_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4147_, lean_object* v_ref_4148_, lean_object* v_msg_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4147_, v_ref_4148_, v_msg_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v_ref_4148_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4158_, lean_object* v_id_4159_, uint8_t v_minIndexable_4160_, lean_object* v_as_4161_, lean_object* v_as_x27_4162_, lean_object* v_b_4163_, lean_object* v_a_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4158_, v_id_4159_, v_minIndexable_4160_, v_as_x27_4162_, v_b_4163_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4173_, lean_object* v_id_4174_, lean_object* v_minIndexable_4175_, lean_object* v_as_4176_, lean_object* v_as_x27_4177_, lean_object* v_b_4178_, lean_object* v_a_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
uint8_t v_minIndexable_boxed_4187_; lean_object* v_res_4188_; 
v_minIndexable_boxed_4187_ = lean_unbox(v_minIndexable_4175_);
v_res_4188_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4173_, v_id_4174_, v_minIndexable_boxed_4187_, v_as_4176_, v_as_x27_4177_, v_b_4178_, v_a_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v_as_x27_4177_);
lean_dec(v_as_4176_);
lean_dec(v_p_4173_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4189_, lean_object* v_t_4190_, lean_object* v_k_4191_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4190_, v_k_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4193_, lean_object* v_t_4194_, lean_object* v_k_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4193_, v_t_4194_, v_k_4195_);
lean_dec(v_k_4195_);
lean_dec(v_t_4194_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4197_, uint8_t v_skipAuxDecl_4198_, lean_object* v_auxDeclToFullName_4199_, lean_object* v___x_4200_, lean_object* v_givenNameView_4201_, lean_object* v_as_4202_, lean_object* v_i_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4197_, v_skipAuxDecl_4198_, v_auxDeclToFullName_4199_, v___x_4200_, v_givenNameView_4201_, v_as_4202_, v_i_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4206_, lean_object* v_skipAuxDecl_4207_, lean_object* v_auxDeclToFullName_4208_, lean_object* v___x_4209_, lean_object* v_givenNameView_4210_, lean_object* v_as_4211_, lean_object* v_i_4212_, lean_object* v_a_4213_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4214_; lean_object* v_res_4215_; 
v_skipAuxDecl_boxed_4214_ = lean_unbox(v_skipAuxDecl_4207_);
v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4206_, v_skipAuxDecl_boxed_4214_, v_auxDeclToFullName_4208_, v___x_4209_, v_givenNameView_4210_, v_as_4211_, v_i_4212_, v_a_4213_);
lean_dec_ref(v_as_4211_);
lean_dec(v_auxDeclToFullName_4208_);
lean_dec(v_givenName_4206_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4216_, lean_object* v_givenName_4217_, lean_object* v_as_4218_, lean_object* v_i_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4216_, v_givenName_4217_, v_as_4218_, v_i_4219_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4222_, lean_object* v_givenName_4223_, lean_object* v_as_4224_, lean_object* v_i_4225_, lean_object* v_a_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4222_, v_givenName_4223_, v_as_4224_, v_i_4225_, v_a_4226_);
lean_dec_ref(v_as_4224_);
lean_dec(v_givenName_4223_);
lean_dec(v_localDecl_x3f_4222_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4228_, uint8_t v_skipAuxDecl_4229_, lean_object* v_auxDeclToFullName_4230_, lean_object* v___x_4231_, lean_object* v_givenNameView_4232_, lean_object* v_as_4233_, lean_object* v_i_4234_, lean_object* v_a_4235_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4228_, v_skipAuxDecl_4229_, v_auxDeclToFullName_4230_, v___x_4231_, v_givenNameView_4232_, v_as_4233_, v_i_4234_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4237_, lean_object* v_skipAuxDecl_4238_, lean_object* v_auxDeclToFullName_4239_, lean_object* v___x_4240_, lean_object* v_givenNameView_4241_, lean_object* v_as_4242_, lean_object* v_i_4243_, lean_object* v_a_4244_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4245_; lean_object* v_res_4246_; 
v_skipAuxDecl_boxed_4245_ = lean_unbox(v_skipAuxDecl_4238_);
v_res_4246_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4237_, v_skipAuxDecl_boxed_4245_, v_auxDeclToFullName_4239_, v___x_4240_, v_givenNameView_4241_, v_as_4242_, v_i_4243_, v_a_4244_);
lean_dec_ref(v_as_4242_);
lean_dec(v_auxDeclToFullName_4239_);
lean_dec(v_givenName_4237_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4247_, lean_object* v_givenName_4248_, lean_object* v_as_4249_, lean_object* v_i_4250_, lean_object* v_a_4251_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4247_, v_givenName_4248_, v_as_4249_, v_i_4250_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4253_, lean_object* v_givenName_4254_, lean_object* v_as_4255_, lean_object* v_i_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4253_, v_givenName_4254_, v_as_4255_, v_i_4256_, v_a_4257_);
lean_dec_ref(v_as_4255_);
lean_dec(v_givenName_4254_);
lean_dec(v_localDecl_x3f_4253_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4259_, v___y_4264_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v_opt_4268_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4277_, lean_object* v_msgData_4278_, uint8_t v_severity_4279_, uint8_t v_isSilent_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4277_, v_msgData_4278_, v_severity_4279_, v_isSilent_4280_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4289_, lean_object* v_msgData_4290_, lean_object* v_severity_4291_, lean_object* v_isSilent_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
uint8_t v_severity_boxed_4300_; uint8_t v_isSilent_boxed_4301_; lean_object* v_res_4302_; 
v_severity_boxed_4300_ = lean_unbox(v_severity_4291_);
v_isSilent_boxed_4301_ = lean_unbox(v_isSilent_4292_);
v_res_4302_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4289_, v_msgData_4290_, v_severity_boxed_4300_, v_isSilent_boxed_4301_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v_ref_4289_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4303_, uint8_t v___x_4304_, lean_object* v_b_4305_, lean_object* v_____r_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4314_ = lean_box(0);
v___x_4315_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4303_, v___x_4314_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4317_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc_n(v_a_4316_, 2);
lean_dec_ref_known(v___x_4315_, 1);
v___x_4317_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4316_, v___x_4304_, v___y_4307_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4317_) == 0)
{
uint8_t v___x_4318_; lean_object* v___x_4319_; 
lean_dec_ref_known(v___x_4317_, 1);
v___x_4318_ = 0;
lean_inc(v_a_4316_);
v___x_4319_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4316_, v___x_4318_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4379_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4322_ = v___x_4319_;
v_isShared_4323_ = v_isSharedCheck_4379_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4379_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
if (lean_obj_tag(v_a_4320_) == 1)
{
lean_object* v_val_4324_; lean_object* v___x_4325_; 
lean_del_object(v___x_4322_);
lean_dec(v_a_4316_);
v_val_4324_ = lean_ctor_get(v_a_4320_, 0);
lean_inc_n(v_val_4324_, 2);
lean_dec_ref_known(v_a_4320_, 1);
v___x_4325_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4324_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v___x_4326_; 
lean_dec_ref_known(v___x_4325_, 1);
v___x_4326_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4305_, v_val_4324_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4336_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4329_ = v___x_4326_;
v_isShared_4330_ = v_isSharedCheck_4336_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4326_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4336_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4334_; 
v___x_4331_ = lean_box(0);
v___x_4332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4331_);
lean_ctor_set(v___x_4332_, 1, v_a_4327_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v___x_4332_);
v___x_4334_ = v___x_4329_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4332_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
v_a_4337_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4326_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4326_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
else
{
lean_object* v_a_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4352_; 
lean_dec(v_val_4324_);
lean_dec_ref(v_b_4305_);
v_a_4345_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4347_ = v___x_4325_;
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_a_4345_);
lean_dec(v___x_4325_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4350_; 
if (v_isShared_4348_ == 0)
{
v___x_4350_ = v___x_4347_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_a_4345_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
else
{
uint8_t v___x_4353_; 
lean_dec(v_a_4320_);
lean_inc(v_a_4316_);
v___x_4353_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4305_, v_a_4316_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; 
lean_del_object(v___x_4322_);
v___x_4354_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4305_, v_a_4316_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4364_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4357_ = v___x_4354_;
v_isShared_4358_ = v_isSharedCheck_4364_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4354_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4364_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4362_; 
v___x_4359_ = lean_box(0);
v___x_4360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
lean_ctor_set(v___x_4360_, 1, v_a_4355_);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 0, v___x_4360_);
v___x_4362_ = v___x_4357_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4360_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
v_a_4365_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4354_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4354_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4377_; 
v___x_4373_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4305_, v_a_4316_);
v___x_4374_ = lean_box(0);
v___x_4375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4374_);
lean_ctor_set(v___x_4375_, 1, v___x_4373_);
if (v_isShared_4323_ == 0)
{
lean_ctor_set(v___x_4322_, 0, v___x_4375_);
v___x_4377_ = v___x_4322_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4375_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_a_4316_);
lean_dec_ref(v_b_4305_);
v_a_4380_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4319_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4319_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec(v_a_4316_);
lean_dec_ref(v_b_4305_);
v_a_4388_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4317_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4317_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec_ref(v_b_4305_);
v_a_4396_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4315_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4315_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4404_, lean_object* v___x_4405_, lean_object* v_b_4406_, lean_object* v_____r_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
uint8_t v___x_17487__boxed_4415_; lean_object* v_res_4416_; 
v___x_17487__boxed_4415_ = lean_unbox(v___x_4405_);
v_res_4416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4404_, v___x_17487__boxed_4415_, v_b_4406_, v_____r_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4420_, lean_object* v_b_4421_, lean_object* v_a_4422_, uint8_t v___x_4423_, uint8_t v_only_4424_, uint8_t v_incremental_4425_, lean_object* v_x_4426_, lean_object* v_mod_x3f_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4435_ = lean_unsigned_to_nat(1u);
v___x_4436_ = l_Lean_Syntax_getArg(v___x_4420_, v___x_4435_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4497_; uint8_t v___x_4498_; 
v___x_4497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4436_);
v___x_4498_ = l_Lean_Syntax_isOfKind(v___x_4436_, v___x_4497_);
if (v___x_4498_ == 0)
{
lean_object* v___x_4499_; 
v___x_4499_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4421_, v_a_4422_, v_mod_x3f_4427_, v___x_4436_, v___x_4423_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4509_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4502_ = v___x_4499_;
v_isShared_4503_ = v_isSharedCheck_4509_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4499_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4509_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4507_; 
v___x_4504_ = lean_box(0);
v___x_4505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
lean_ctor_set(v___x_4505_, 1, v_a_4500_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v___x_4505_);
v___x_4507_ = v___x_4502_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4505_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
v_a_4510_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4499_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4499_);
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
else
{
goto v___jp_4457_;
}
}
else
{
goto v___jp_4457_;
}
v___jp_4437_:
{
lean_object* v___x_4438_; 
v___x_4438_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4421_, v_a_4422_, v_mod_x3f_4427_, v___x_4436_, v___x_4423_, v_only_4424_, v_incremental_4425_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4448_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4441_ = v___x_4438_;
v_isShared_4442_ = v_isSharedCheck_4448_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4438_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4448_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4446_; 
v___x_4443_ = lean_box(0);
v___x_4444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
lean_ctor_set(v___x_4444_, 1, v_a_4439_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 0, v___x_4444_);
v___x_4446_ = v___x_4441_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4444_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
v_a_4449_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4438_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4438_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
v___jp_4457_:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = l_Lean_TSyntax_getId(v___x_4436_);
v___x_4459_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4458_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
if (lean_obj_tag(v_a_4460_) == 1)
{
lean_object* v_val_4461_; lean_object* v_snd_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4487_; 
v_val_4461_ = lean_ctor_get(v_a_4460_, 0);
lean_inc(v_val_4461_);
lean_dec_ref_known(v_a_4460_, 1);
v_snd_4462_ = lean_ctor_get(v_val_4461_, 1);
v_isSharedCheck_4487_ = !lean_is_exclusive(v_val_4461_);
if (v_isSharedCheck_4487_ == 0)
{
lean_object* v_unused_4488_; 
v_unused_4488_ = lean_ctor_get(v_val_4461_, 0);
lean_dec(v_unused_4488_);
v___x_4464_ = v_val_4461_;
v_isShared_4465_ = v_isSharedCheck_4487_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_snd_4462_);
lean_dec(v_val_4461_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4487_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
if (lean_obj_tag(v_snd_4462_) == 1)
{
lean_object* v___x_4466_; 
lean_dec_ref_known(v_snd_4462_, 2);
v___x_4466_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4421_, v_a_4422_, v_mod_x3f_4427_, v___x_4436_, v___x_4423_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4478_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4469_ = v___x_4466_;
v_isShared_4470_ = v_isSharedCheck_4478_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4466_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4478_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4471_; lean_object* v___x_4473_; 
v___x_4471_ = lean_box(0);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 1, v_a_4467_);
lean_ctor_set(v___x_4464_, 0, v___x_4471_);
v___x_4473_ = v___x_4464_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4471_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_a_4467_);
v___x_4473_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
lean_object* v___x_4475_; 
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 0, v___x_4473_);
v___x_4475_ = v___x_4469_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
else
{
lean_object* v_a_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4486_; 
lean_del_object(v___x_4464_);
v_a_4479_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4481_ = v___x_4466_;
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_a_4479_);
lean_dec(v___x_4466_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4484_; 
if (v_isShared_4482_ == 0)
{
v___x_4484_ = v___x_4481_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4479_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
}
else
{
lean_del_object(v___x_4464_);
lean_dec(v_snd_4462_);
goto v___jp_4437_;
}
}
}
else
{
lean_dec(v_a_4460_);
goto v___jp_4437_;
}
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec(v___x_4436_);
lean_dec(v_mod_x3f_4427_);
lean_dec(v_a_4422_);
lean_dec_ref(v_b_4421_);
v_a_4489_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4459_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4459_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4518_, lean_object* v_b_4519_, lean_object* v_a_4520_, lean_object* v___x_4521_, lean_object* v_only_4522_, lean_object* v_incremental_4523_, lean_object* v_x_4524_, lean_object* v_mod_x3f_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
uint8_t v___x_17705__boxed_4533_; uint8_t v_only_boxed_4534_; uint8_t v_incremental_boxed_4535_; lean_object* v_res_4536_; 
v___x_17705__boxed_4533_ = lean_unbox(v___x_4521_);
v_only_boxed_4534_ = lean_unbox(v_only_4522_);
v_incremental_boxed_4535_ = lean_unbox(v_incremental_4523_);
v_res_4536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4518_, v_b_4519_, v_a_4520_, v___x_17705__boxed_4533_, v_only_boxed_4534_, v_incremental_boxed_4535_, v_x_4524_, v_mod_x3f_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___x_4518_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4537_, lean_object* v___x_4538_, lean_object* v_____r_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v___x_4547_; 
v___x_4547_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4537_, v___x_4538_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4547_) == 0)
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4557_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4550_ = v___x_4547_;
v_isShared_4551_ = v_isSharedCheck_4557_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4547_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4557_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4555_; 
v___x_4552_ = lean_box(0);
v___x_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
lean_ctor_set(v___x_4553_, 1, v_a_4548_);
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v___x_4553_);
v___x_4555_ = v___x_4550_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4553_);
v___x_4555_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
return v___x_4555_;
}
}
}
else
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4565_; 
v_a_4558_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4560_ = v___x_4547_;
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4547_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4566_, lean_object* v___x_4567_, lean_object* v_____r_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
lean_object* v_res_4576_; 
v_res_4576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4566_, v___x_4567_, v_____r_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___x_4567_);
return v_res_4576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4577_, lean_object* v_b_4578_, lean_object* v_a_4579_, uint8_t v___x_4580_, uint8_t v_only_4581_, uint8_t v_incremental_4582_, uint8_t v___x_4583_, lean_object* v_x_4584_, lean_object* v_mod_x3f_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4593_ = lean_unsigned_to_nat(2u);
v___x_4594_ = l_Lean_Syntax_getArg(v___x_4577_, v___x_4593_);
if (v___x_4583_ == 0)
{
lean_object* v___x_4655_; uint8_t v___x_4656_; 
v___x_4655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4594_);
v___x_4656_ = l_Lean_Syntax_isOfKind(v___x_4594_, v___x_4655_);
if (v___x_4656_ == 0)
{
lean_object* v___x_4657_; 
v___x_4657_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4578_, v_a_4579_, v_mod_x3f_4585_, v___x_4594_, v___x_4580_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4667_; 
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4660_ = v___x_4657_;
v_isShared_4661_ = v_isSharedCheck_4667_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4657_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4667_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4665_; 
v___x_4662_ = lean_box(0);
v___x_4663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
lean_ctor_set(v___x_4663_, 1, v_a_4658_);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 0, v___x_4663_);
v___x_4665_ = v___x_4660_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4663_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
else
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
v_a_4668_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4657_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4657_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
else
{
goto v___jp_4615_;
}
}
else
{
goto v___jp_4615_;
}
v___jp_4595_:
{
lean_object* v___x_4596_; 
v___x_4596_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4578_, v_a_4579_, v_mod_x3f_4585_, v___x_4594_, v___x_4580_, v_only_4581_, v_incremental_4582_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4606_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4606_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4606_ == 0)
{
v___x_4599_ = v___x_4596_;
v_isShared_4600_ = v_isSharedCheck_4606_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4596_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4606_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4604_; 
v___x_4601_ = lean_box(0);
v___x_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4601_);
lean_ctor_set(v___x_4602_, 1, v_a_4597_);
if (v_isShared_4600_ == 0)
{
lean_ctor_set(v___x_4599_, 0, v___x_4602_);
v___x_4604_ = v___x_4599_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4605_; 
v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4602_);
v___x_4604_ = v_reuseFailAlloc_4605_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
return v___x_4604_;
}
}
}
else
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
v_a_4607_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4596_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4596_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
}
v___jp_4615_:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = l_Lean_TSyntax_getId(v___x_4594_);
v___x_4617_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4616_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v_a_4618_; 
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
lean_inc(v_a_4618_);
lean_dec_ref_known(v___x_4617_, 1);
if (lean_obj_tag(v_a_4618_) == 1)
{
lean_object* v_val_4619_; lean_object* v_snd_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4645_; 
v_val_4619_ = lean_ctor_get(v_a_4618_, 0);
lean_inc(v_val_4619_);
lean_dec_ref_known(v_a_4618_, 1);
v_snd_4620_ = lean_ctor_get(v_val_4619_, 1);
v_isSharedCheck_4645_ = !lean_is_exclusive(v_val_4619_);
if (v_isSharedCheck_4645_ == 0)
{
lean_object* v_unused_4646_; 
v_unused_4646_ = lean_ctor_get(v_val_4619_, 0);
lean_dec(v_unused_4646_);
v___x_4622_ = v_val_4619_;
v_isShared_4623_ = v_isSharedCheck_4645_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_snd_4620_);
lean_dec(v_val_4619_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4645_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
if (lean_obj_tag(v_snd_4620_) == 1)
{
lean_object* v___x_4624_; 
lean_dec_ref_known(v_snd_4620_, 2);
v___x_4624_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4578_, v_a_4579_, v_mod_x3f_4585_, v___x_4594_, v___x_4580_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
if (lean_obj_tag(v___x_4624_) == 0)
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4636_; 
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4627_ = v___x_4624_;
v_isShared_4628_ = v_isSharedCheck_4636_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4624_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4636_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4629_; lean_object* v___x_4631_; 
v___x_4629_ = lean_box(0);
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 1, v_a_4625_);
lean_ctor_set(v___x_4622_, 0, v___x_4629_);
v___x_4631_ = v___x_4622_;
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
lean_object* v___x_4633_; 
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 0, v___x_4631_);
v___x_4633_ = v___x_4627_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_del_object(v___x_4622_);
v_a_4637_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4624_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4624_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
else
{
lean_del_object(v___x_4622_);
lean_dec(v_snd_4620_);
goto v___jp_4595_;
}
}
}
else
{
lean_dec(v_a_4618_);
goto v___jp_4595_;
}
}
else
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
lean_dec(v___x_4594_);
lean_dec(v_mod_x3f_4585_);
lean_dec(v_a_4579_);
lean_dec_ref(v_b_4578_);
v_a_4647_ = lean_ctor_get(v___x_4617_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4617_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4649_ = v___x_4617_;
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v___x_4617_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4676_, lean_object* v_b_4677_, lean_object* v_a_4678_, lean_object* v___x_4679_, lean_object* v_only_4680_, lean_object* v_incremental_4681_, lean_object* v___x_4682_, lean_object* v_x_4683_, lean_object* v_mod_x3f_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
uint8_t v___x_17974__boxed_4692_; uint8_t v_only_boxed_4693_; uint8_t v_incremental_boxed_4694_; uint8_t v___x_17975__boxed_4695_; lean_object* v_res_4696_; 
v___x_17974__boxed_4692_ = lean_unbox(v___x_4679_);
v_only_boxed_4693_ = lean_unbox(v_only_4680_);
v_incremental_boxed_4694_ = lean_unbox(v_incremental_4681_);
v___x_17975__boxed_4695_ = lean_unbox(v___x_4682_);
v_res_4696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4676_, v_b_4677_, v_a_4678_, v___x_17974__boxed_4692_, v_only_boxed_4693_, v_incremental_boxed_4694_, v___x_17975__boxed_4695_, v_x_4683_, v_mod_x3f_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
lean_dec(v___y_4686_);
lean_dec_ref(v___y_4685_);
lean_dec(v___x_4676_);
return v_res_4696_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4705_ = l_Lean_stringToMessageData(v___x_4704_);
return v___x_4705_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12));
v___x_4732_ = l_Lean_stringToMessageData(v___x_4731_);
return v___x_4732_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4738_ = l_Lean_stringToMessageData(v___x_4737_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4739_, uint8_t v_only_4740_, uint8_t v_incremental_4741_, lean_object* v_as_4742_, size_t v_sz_4743_, size_t v_i_4744_, lean_object* v_b_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v_snd_4754_; lean_object* v___y_4759_; uint8_t v___y_4760_; lean_object* v_a_4764_; lean_object* v___y_4768_; uint8_t v___x_4772_; 
v___x_4772_ = lean_usize_dec_lt(v_i_4744_, v_sz_4743_);
if (v___x_4772_ == 0)
{
lean_object* v___x_4773_; 
v___x_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4773_, 0, v_b_4745_);
return v___x_4773_;
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4775_; uint8_t v___x_4776_; 
v_a_4774_ = lean_array_uget_borrowed(v_as_4742_, v_i_4744_);
v___x_4775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4774_);
v___x_4776_ = l_Lean_Syntax_isOfKind(v_a_4774_, v___x_4775_);
if (v___x_4776_ == 0)
{
lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4777_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4774_);
v___x_4778_ = l_Lean_MessageData_ofSyntax(v_a_4774_);
v___x_4779_ = l_Lean_indentD(v___x_4778_);
v___x_4780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4777_);
lean_ctor_set(v___x_4780_, 1, v___x_4779_);
v___x_4781_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4780_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_dec_ref_known(v___x_4781_, 1);
v_snd_4754_ = v_b_4745_;
goto v___jp_4753_;
}
else
{
lean_object* v_a_4782_; 
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
lean_inc(v_a_4782_);
lean_dec_ref_known(v___x_4781_, 1);
v_a_4764_ = v_a_4782_;
goto v___jp_4763_;
}
}
else
{
lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; 
v___x_4783_ = lean_unsigned_to_nat(0u);
v___x_4784_ = l_Lean_Syntax_getArg(v_a_4774_, v___x_4783_);
v___x_4785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_4784_);
v___x_4786_ = l_Lean_Syntax_isOfKind(v___x_4784_, v___x_4785_);
if (v___x_4786_ == 0)
{
lean_object* v___x_4787_; uint8_t v___x_4788_; 
v___x_4787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_4784_);
v___x_4788_ = l_Lean_Syntax_isOfKind(v___x_4784_, v___x_4787_);
if (v___x_4788_ == 0)
{
lean_object* v___x_4789_; uint8_t v___x_4790_; 
v___x_4789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_4784_);
v___x_4790_ = l_Lean_Syntax_isOfKind(v___x_4784_, v___x_4789_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; uint8_t v___x_4792_; 
v___x_4791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_4784_);
v___x_4792_ = l_Lean_Syntax_isOfKind(v___x_4784_, v___x_4791_);
if (v___x_4792_ == 0)
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
lean_dec(v___x_4784_);
v___x_4793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4774_);
v___x_4794_ = l_Lean_MessageData_ofSyntax(v_a_4774_);
v___x_4795_ = l_Lean_indentD(v___x_4794_);
v___x_4796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4793_);
lean_ctor_set(v___x_4796_, 1, v___x_4795_);
v___x_4797_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4796_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_dec_ref_known(v___x_4797_, 1);
v_snd_4754_ = v_b_4745_;
goto v___jp_4753_;
}
else
{
lean_object* v_a_4798_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_a_4798_);
lean_dec_ref_known(v___x_4797_, 1);
v_a_4764_ = v_a_4798_;
goto v___jp_4763_;
}
}
else
{
lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4799_ = lean_unsigned_to_nat(1u);
v___x_4800_ = l_Lean_Syntax_getArg(v___x_4784_, v___x_4799_);
lean_dec(v___x_4784_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4809_; uint8_t v___x_4810_; 
v___x_4809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15));
lean_inc(v___x_4800_);
v___x_4810_ = l_Lean_Syntax_isOfKind(v___x_4800_, v___x_4809_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
lean_dec(v___x_4800_);
v___x_4811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4774_);
v___x_4812_ = l_Lean_MessageData_ofSyntax(v_a_4774_);
v___x_4813_ = l_Lean_indentD(v___x_4812_);
v___x_4814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4811_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
v___x_4815_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4814_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_dec_ref_known(v___x_4815_, 1);
v_snd_4754_ = v_b_4745_;
goto v___jp_4753_;
}
else
{
lean_object* v_a_4816_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
lean_inc(v_a_4816_);
lean_dec_ref_known(v___x_4815_, 1);
v_a_4764_ = v_a_4816_;
goto v___jp_4763_;
}
}
else
{
goto v___jp_4801_;
}
}
else
{
goto v___jp_4801_;
}
v___jp_4801_:
{
if (v_only_4740_ == 0)
{
lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4802_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13);
v___x_4803_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_4800_, v___x_4802_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4805_; 
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4804_);
lean_dec_ref_known(v___x_4803_, 1);
lean_inc_ref(v_b_4745_);
v___x_4805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4745_, v___x_4800_, v_a_4804_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v___x_4800_);
v___y_4768_ = v___x_4805_;
goto v___jp_4767_;
}
else
{
lean_object* v_a_4806_; 
lean_dec(v___x_4800_);
v_a_4806_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4806_);
lean_dec_ref_known(v___x_4803_, 1);
v_a_4764_ = v_a_4806_;
goto v___jp_4763_;
}
}
else
{
lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4807_ = lean_box(0);
lean_inc_ref(v_b_4745_);
v___x_4808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4745_, v___x_4800_, v___x_4807_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v___x_4800_);
v___y_4768_ = v___x_4808_;
goto v___jp_4767_;
}
}
}
}
else
{
lean_object* v___x_4817_; lean_object* v___x_4818_; uint8_t v___x_4819_; 
v___x_4817_ = lean_unsigned_to_nat(1u);
v___x_4818_ = l_Lean_Syntax_getArg(v___x_4784_, v___x_4817_);
v___x_4819_ = l_Lean_Syntax_isNone(v___x_4818_);
if (v___x_4819_ == 0)
{
uint8_t v___x_4820_; 
lean_inc(v___x_4818_);
v___x_4820_ = l_Lean_Syntax_matchesNull(v___x_4818_, v___x_4817_);
if (v___x_4820_ == 0)
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
lean_dec(v___x_4818_);
lean_dec(v___x_4784_);
v___x_4821_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4774_);
v___x_4822_ = l_Lean_MessageData_ofSyntax(v_a_4774_);
v___x_4823_ = l_Lean_indentD(v___x_4822_);
v___x_4824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4821_);
lean_ctor_set(v___x_4824_, 1, v___x_4823_);
v___x_4825_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4824_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_dec_ref_known(v___x_4825_, 1);
v_snd_4754_ = v_b_4745_;
goto v___jp_4753_;
}
else
{
lean_object* v_a_4826_; 
v_a_4826_ = lean_ctor_get(v___x_4825_, 0);
lean_inc(v_a_4826_);
lean_dec_ref_known(v___x_4825_, 1);
v_a_4764_ = v_a_4826_;
goto v___jp_4763_;
}
}
else
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Lean_Syntax_getArg(v___x_4818_, v___x_4783_);
lean_dec(v___x_4818_);
if (v___x_4819_ == 0)
{
lean_object* v___x_4832_; uint8_t v___x_4833_; 
v___x_4832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4827_);
v___x_4833_ = l_Lean_Syntax_isOfKind(v___x_4827_, v___x_4832_);
if (v___x_4833_ == 0)
{
lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
lean_dec(v___x_4827_);
lean_dec(v___x_4784_);
v___x_4834_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4774_);
v___x_4835_ = l_Lean_MessageData_ofSyntax(v_a_4774_);
v___x_4836_ = l_Lean_indentD(v___x_4835_);
v___x_4837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4834_);
lean_ctor_set(v___x_4837_, 1, v___x_4836_);
v___x_4838_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4837_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_dec_ref_known(v___x_4838_, 1);
v_snd_4754_ = v_b_4745_;
goto v___jp_4753_;
}
else
{
lean_object* v_a_4839_; 
v_a_4839_ = lean_ctor_get(v___x_4838_, 0);
lean_inc(v_a_4839_);
lean_dec_ref_known(v___x_4838_, 1);
v_a_4764_ = v_a_4839_;
goto v___jp_4763_;
}
}
else
{
goto v___jp_4828_;
}
}
else
{
goto v___jp_4828_;
}
v___jp_4828_:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4829_ = lean_box(0);
v___x_4830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4827_);
lean_inc(v_a_4774_);
lean_inc_ref(v_b_4745_);
v___x_4831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4784_, v_b_4745_, v_a_4774_, v___x_4776_, v_only_4740_, v_incremental_4741_, v___x_4788_, v___x_4829_, v___x_4830_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v___x_4784_);
v___y_4768_ = v___x_4831_;
goto v___jp_4767_;
}
}
}
else
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
lean_dec(v___x_4818_);
v___x_4840_ = lean_box(0);
v___x_4841_ = lean_box(0);
lean_inc(v_a_4774_);
lean_inc_ref(v_b_4745_);
v___x_4842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4784_, v_b_4745_, v_a_4774_, v___x_4776_, v_only_4740_, v_incremental_4741_, v___x_4788_, v___x_4840_, v___x_4841_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v___x_4784_);
v___y_4768_ = v___x_4842_;
goto v___jp_4767_;
}
}
}
else
{
lean_object* v___x_4843_; uint8_t v___x_4844_; 
v___x_4843_ = l_Lean_Syntax_getArg(v___x_4784_, v___x_4783_);
v___x_4844_ = l_Lean_Syntax_isNone(v___x_4843_);
if (v___x_4844_ == 0)
{
lean_object* v___x_4845_; uint8_t v___x_4846_; 
v___x_4845_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4843_);
v___x_4846_ = l_Lean_Syntax_matchesNull(v___x_4843_, v___x_4845_);
if (v___x_4846_ == 0)
{
lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; 
lean_dec(v___x_4843_);
lean_dec(v___x_4784_);
v___x_4847_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4774_);
v___x_4848_ = l_Lean_MessageData_ofSyntax(v_a_4774_);
v___x_4849_ = l_Lean_indentD(v___x_4848_);
v___x_4850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4847_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
v___x_4851_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4850_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_dec_ref_known(v___x_4851_, 1);
v_snd_4754_ = v_b_4745_;
goto v___jp_4753_;
}
else
{
lean_object* v_a_4852_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4851_, 1);
v_a_4764_ = v_a_4852_;
goto v___jp_4763_;
}
}
else
{
lean_object* v___x_4853_; 
v___x_4853_ = l_Lean_Syntax_getArg(v___x_4843_, v___x_4783_);
lean_dec(v___x_4843_);
if (v___x_4844_ == 0)
{
lean_object* v___x_4858_; uint8_t v___x_4859_; 
v___x_4858_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4853_);
v___x_4859_ = l_Lean_Syntax_isOfKind(v___x_4853_, v___x_4858_);
if (v___x_4859_ == 0)
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
lean_dec(v___x_4853_);
lean_dec(v___x_4784_);
v___x_4860_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4774_);
v___x_4861_ = l_Lean_MessageData_ofSyntax(v_a_4774_);
v___x_4862_ = l_Lean_indentD(v___x_4861_);
v___x_4863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4860_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
v___x_4864_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4863_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_dec_ref_known(v___x_4864_, 1);
v_snd_4754_ = v_b_4745_;
goto v___jp_4753_;
}
else
{
lean_object* v_a_4865_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc(v_a_4865_);
lean_dec_ref_known(v___x_4864_, 1);
v_a_4764_ = v_a_4865_;
goto v___jp_4763_;
}
}
else
{
goto v___jp_4854_;
}
}
else
{
goto v___jp_4854_;
}
v___jp_4854_:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4855_ = lean_box(0);
v___x_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4853_);
lean_inc(v_a_4774_);
lean_inc_ref(v_b_4745_);
v___x_4857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4784_, v_b_4745_, v_a_4774_, v___x_4786_, v_only_4740_, v_incremental_4741_, v___x_4855_, v___x_4856_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v___x_4784_);
v___y_4768_ = v___x_4857_;
goto v___jp_4767_;
}
}
}
else
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
lean_dec(v___x_4843_);
v___x_4866_ = lean_box(0);
v___x_4867_ = lean_box(0);
lean_inc(v_a_4774_);
lean_inc_ref(v_b_4745_);
v___x_4868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4784_, v_b_4745_, v_a_4774_, v___x_4786_, v_only_4740_, v_incremental_4741_, v___x_4866_, v___x_4867_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v___x_4784_);
v___y_4768_ = v___x_4868_;
goto v___jp_4767_;
}
}
}
else
{
lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; uint8_t v___x_4872_; 
v___x_4869_ = lean_unsigned_to_nat(1u);
v___x_4870_ = l_Lean_Syntax_getArg(v___x_4784_, v___x_4869_);
lean_dec(v___x_4784_);
v___x_4871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4870_);
v___x_4872_ = l_Lean_Syntax_isOfKind(v___x_4870_, v___x_4871_);
if (v___x_4872_ == 0)
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
lean_dec(v___x_4870_);
v___x_4873_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4774_);
v___x_4874_ = l_Lean_MessageData_ofSyntax(v_a_4774_);
v___x_4875_ = l_Lean_indentD(v___x_4874_);
v___x_4876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4873_);
lean_ctor_set(v___x_4876_, 1, v___x_4875_);
v___x_4877_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4876_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_dec_ref_known(v___x_4877_, 1);
v_snd_4754_ = v_b_4745_;
goto v___jp_4753_;
}
else
{
lean_object* v_a_4878_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4877_, 1);
v_a_4764_ = v_a_4878_;
goto v___jp_4763_;
}
}
else
{
if (v_incremental_4741_ == 0)
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = lean_box(0);
lean_inc_ref(v_b_4745_);
v___x_4880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4870_, v___x_4776_, v_b_4745_, v___x_4879_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
v___y_4768_ = v___x_4880_;
goto v___jp_4767_;
}
else
{
lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4881_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_4882_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4774_, v___x_4881_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v___x_4884_; 
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
lean_inc(v_a_4883_);
lean_dec_ref_known(v___x_4882_, 1);
lean_inc_ref(v_b_4745_);
v___x_4884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4870_, v___x_4776_, v_b_4745_, v_a_4883_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
v___y_4768_ = v___x_4884_;
goto v___jp_4767_;
}
else
{
lean_object* v_a_4885_; 
lean_dec(v___x_4870_);
v_a_4885_ = lean_ctor_get(v___x_4882_, 0);
lean_inc(v_a_4885_);
lean_dec_ref_known(v___x_4882_, 1);
v_a_4764_ = v_a_4885_;
goto v___jp_4763_;
}
}
}
}
}
}
v___jp_4753_:
{
size_t v___x_4755_; size_t v___x_4756_; 
v___x_4755_ = ((size_t)1ULL);
v___x_4756_ = lean_usize_add(v_i_4744_, v___x_4755_);
v_i_4744_ = v___x_4756_;
v_b_4745_ = v_snd_4754_;
goto _start;
}
v___jp_4758_:
{
if (v___y_4760_ == 0)
{
if (v_lax_4739_ == 0)
{
lean_object* v___x_4761_; 
lean_dec_ref(v_b_4745_);
v___x_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4761_, 0, v___y_4759_);
return v___x_4761_;
}
else
{
lean_dec_ref(v___y_4759_);
v_snd_4754_ = v_b_4745_;
goto v___jp_4753_;
}
}
else
{
lean_object* v___x_4762_; 
lean_dec_ref(v_b_4745_);
v___x_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4762_, 0, v___y_4759_);
return v___x_4762_;
}
}
v___jp_4763_:
{
uint8_t v___x_4765_; 
v___x_4765_ = l_Lean_Exception_isInterrupt(v_a_4764_);
if (v___x_4765_ == 0)
{
uint8_t v___x_4766_; 
lean_inc_ref(v_a_4764_);
v___x_4766_ = l_Lean_Exception_isRuntime(v_a_4764_);
v___y_4759_ = v_a_4764_;
v___y_4760_ = v___x_4766_;
goto v___jp_4758_;
}
else
{
v___y_4759_ = v_a_4764_;
v___y_4760_ = v___x_4765_;
goto v___jp_4758_;
}
}
v___jp_4767_:
{
if (lean_obj_tag(v___y_4768_) == 0)
{
lean_object* v_a_4769_; lean_object* v_snd_4770_; 
lean_dec_ref(v_b_4745_);
v_a_4769_ = lean_ctor_get(v___y_4768_, 0);
lean_inc(v_a_4769_);
lean_dec_ref_known(v___y_4768_, 1);
v_snd_4770_ = lean_ctor_get(v_a_4769_, 1);
lean_inc(v_snd_4770_);
lean_dec(v_a_4769_);
v_snd_4754_ = v_snd_4770_;
goto v___jp_4753_;
}
else
{
lean_object* v_a_4771_; 
v_a_4771_ = lean_ctor_get(v___y_4768_, 0);
lean_inc(v_a_4771_);
lean_dec_ref_known(v___y_4768_, 1);
v_a_4764_ = v_a_4771_;
goto v___jp_4763_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_4886_, lean_object* v_only_4887_, lean_object* v_incremental_4888_, lean_object* v_as_4889_, lean_object* v_sz_4890_, lean_object* v_i_4891_, lean_object* v_b_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_){
_start:
{
uint8_t v_lax_boxed_4900_; uint8_t v_only_boxed_4901_; uint8_t v_incremental_boxed_4902_; size_t v_sz_boxed_4903_; size_t v_i_boxed_4904_; lean_object* v_res_4905_; 
v_lax_boxed_4900_ = lean_unbox(v_lax_4886_);
v_only_boxed_4901_ = lean_unbox(v_only_4887_);
v_incremental_boxed_4902_ = lean_unbox(v_incremental_4888_);
v_sz_boxed_4903_ = lean_unbox_usize(v_sz_4890_);
lean_dec(v_sz_4890_);
v_i_boxed_4904_ = lean_unbox_usize(v_i_4891_);
lean_dec(v_i_4891_);
v_res_4905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_4900_, v_only_boxed_4901_, v_incremental_boxed_4902_, v_as_4889_, v_sz_boxed_4903_, v_i_boxed_4904_, v_b_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
lean_dec(v___y_4894_);
lean_dec_ref(v___y_4893_);
lean_dec_ref(v_as_4889_);
return v_res_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_4906_, lean_object* v_ps_4907_, uint8_t v_only_4908_, uint8_t v_lax_4909_, uint8_t v_incremental_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_){
_start:
{
size_t v_sz_4918_; size_t v___x_4919_; lean_object* v___x_4920_; 
v_sz_4918_ = lean_array_size(v_ps_4907_);
v___x_4919_ = ((size_t)0ULL);
v___x_4920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_4909_, v_only_4908_, v_incremental_4910_, v_ps_4907_, v_sz_4918_, v___x_4919_, v_params_4906_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_4921_, lean_object* v_ps_4922_, lean_object* v_only_4923_, lean_object* v_lax_4924_, lean_object* v_incremental_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
uint8_t v_only_boxed_4933_; uint8_t v_lax_boxed_4934_; uint8_t v_incremental_boxed_4935_; lean_object* v_res_4936_; 
v_only_boxed_4933_ = lean_unbox(v_only_4923_);
v_lax_boxed_4934_ = lean_unbox(v_lax_4924_);
v_incremental_boxed_4935_ = lean_unbox(v_incremental_4925_);
v_res_4936_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_4921_, v_ps_4922_, v_only_boxed_4933_, v_lax_boxed_4934_, v_incremental_boxed_4935_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
lean_dec(v_a_4929_);
lean_dec_ref(v_a_4928_);
lean_dec(v_a_4927_);
lean_dec_ref(v_a_4926_);
lean_dec_ref(v_ps_4922_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_){
_start:
{
lean_object* v_origin_4948_; 
v_origin_4948_ = lean_ctor_get(v_thm_4937_, 5);
if (lean_obj_tag(v_origin_4948_) == 0)
{
lean_object* v_declName_4949_; lean_object* v___x_4950_; 
lean_inc_ref(v_origin_4948_);
lean_dec_ref(v_thm_4937_);
v_declName_4949_ = lean_ctor_get(v_origin_4948_, 0);
lean_inc(v_declName_4949_);
lean_dec_ref_known(v_origin_4948_, 1);
v___x_4950_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_4949_, v_a_4945_, v_a_4946_);
return v___x_4950_;
}
else
{
lean_object* v_proof_4951_; lean_object* v___x_4952_; 
v_proof_4951_ = lean_ctor_get(v_thm_4937_, 1);
lean_inc_ref(v_proof_4951_);
lean_dec_ref(v_thm_4937_);
v___x_4952_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_4951_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
return v___x_4952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
lean_dec(v_a_4962_);
lean_dec_ref(v_a_4961_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_4965_, size_t v_sz_4966_, size_t v_i_4967_, lean_object* v_b_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
uint8_t v___x_4979_; 
v___x_4979_ = lean_usize_dec_lt(v_i_4967_, v_sz_4966_);
if (v___x_4979_ == 0)
{
lean_object* v___x_4980_; 
v___x_4980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4980_, 0, v_b_4968_);
return v___x_4980_;
}
else
{
lean_object* v_snd_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_5007_; 
v_snd_4981_ = lean_ctor_get(v_b_4968_, 1);
v_isSharedCheck_5007_ = !lean_is_exclusive(v_b_4968_);
if (v_isSharedCheck_5007_ == 0)
{
lean_object* v_unused_5008_; 
v_unused_5008_ = lean_ctor_get(v_b_4968_, 0);
lean_dec(v_unused_5008_);
v___x_4983_ = v_b_4968_;
v_isShared_4984_ = v_isSharedCheck_5007_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_snd_4981_);
lean_dec(v_b_4968_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_5007_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v_a_4985_; lean_object* v___x_4986_; 
v_a_4985_ = lean_array_uget_borrowed(v_as_4965_, v_i_4967_);
lean_inc(v_a_4985_);
v___x_4986_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_4985_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4988_; lean_object* v_a_4990_; uint8_t v___x_4997_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v___x_4988_ = lean_box(0);
v___x_4997_ = lean_unbox(v_a_4987_);
lean_dec(v_a_4987_);
if (v___x_4997_ == 0)
{
v_a_4990_ = v_snd_4981_;
goto v___jp_4989_;
}
else
{
lean_object* v___x_4998_; 
lean_inc(v_a_4985_);
v___x_4998_ = l_Lean_PersistentArray_push___redArg(v_snd_4981_, v_a_4985_);
v_a_4990_ = v___x_4998_;
goto v___jp_4989_;
}
v___jp_4989_:
{
lean_object* v___x_4992_; 
if (v_isShared_4984_ == 0)
{
lean_ctor_set(v___x_4983_, 1, v_a_4990_);
lean_ctor_set(v___x_4983_, 0, v___x_4988_);
v___x_4992_ = v___x_4983_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4988_);
lean_ctor_set(v_reuseFailAlloc_4996_, 1, v_a_4990_);
v___x_4992_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
size_t v___x_4993_; size_t v___x_4994_; 
v___x_4993_ = ((size_t)1ULL);
v___x_4994_ = lean_usize_add(v_i_4967_, v___x_4993_);
v_i_4967_ = v___x_4994_;
v_b_4968_ = v___x_4992_;
goto _start;
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_del_object(v___x_4983_);
lean_dec(v_snd_4981_);
v_a_4999_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4986_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4986_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5009_, lean_object* v_sz_5010_, lean_object* v_i_5011_, lean_object* v_b_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_){
_start:
{
size_t v_sz_boxed_5023_; size_t v_i_boxed_5024_; lean_object* v_res_5025_; 
v_sz_boxed_5023_ = lean_unbox_usize(v_sz_5010_);
lean_dec(v_sz_5010_);
v_i_boxed_5024_ = lean_unbox_usize(v_i_5011_);
lean_dec(v_i_5011_);
v_res_5025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5009_, v_sz_boxed_5023_, v_i_boxed_5024_, v_b_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
lean_dec(v___y_5013_);
lean_dec_ref(v_as_5009_);
return v_res_5025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5026_, size_t v_sz_5027_, size_t v_i_5028_, lean_object* v_b_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_){
_start:
{
uint8_t v___x_5040_; 
v___x_5040_ = lean_usize_dec_lt(v_i_5028_, v_sz_5027_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; 
v___x_5041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5041_, 0, v_b_5029_);
return v___x_5041_;
}
else
{
lean_object* v_snd_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5068_; 
v_snd_5042_ = lean_ctor_get(v_b_5029_, 1);
v_isSharedCheck_5068_ = !lean_is_exclusive(v_b_5029_);
if (v_isSharedCheck_5068_ == 0)
{
lean_object* v_unused_5069_; 
v_unused_5069_ = lean_ctor_get(v_b_5029_, 0);
lean_dec(v_unused_5069_);
v___x_5044_ = v_b_5029_;
v_isShared_5045_ = v_isSharedCheck_5068_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_snd_5042_);
lean_dec(v_b_5029_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5068_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v_a_5046_; lean_object* v___x_5047_; 
v_a_5046_ = lean_array_uget_borrowed(v_as_5026_, v_i_5028_);
lean_inc(v_a_5046_);
v___x_5047_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5046_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5049_; lean_object* v_a_5051_; uint8_t v___x_5058_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
lean_inc(v_a_5048_);
lean_dec_ref_known(v___x_5047_, 1);
v___x_5049_ = lean_box(0);
v___x_5058_ = lean_unbox(v_a_5048_);
lean_dec(v_a_5048_);
if (v___x_5058_ == 0)
{
v_a_5051_ = v_snd_5042_;
goto v___jp_5050_;
}
else
{
lean_object* v___x_5059_; 
lean_inc(v_a_5046_);
v___x_5059_ = l_Lean_PersistentArray_push___redArg(v_snd_5042_, v_a_5046_);
v_a_5051_ = v___x_5059_;
goto v___jp_5050_;
}
v___jp_5050_:
{
lean_object* v___x_5053_; 
if (v_isShared_5045_ == 0)
{
lean_ctor_set(v___x_5044_, 1, v_a_5051_);
lean_ctor_set(v___x_5044_, 0, v___x_5049_);
v___x_5053_ = v___x_5044_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5057_, 0, v___x_5049_);
lean_ctor_set(v_reuseFailAlloc_5057_, 1, v_a_5051_);
v___x_5053_ = v_reuseFailAlloc_5057_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
size_t v___x_5054_; size_t v___x_5055_; lean_object* v___x_5056_; 
v___x_5054_ = ((size_t)1ULL);
v___x_5055_ = lean_usize_add(v_i_5028_, v___x_5054_);
v___x_5056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5026_, v_sz_5027_, v___x_5055_, v___x_5053_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
return v___x_5056_;
}
}
}
else
{
lean_object* v_a_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5067_; 
lean_del_object(v___x_5044_);
lean_dec(v_snd_5042_);
v_a_5060_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5062_ = v___x_5047_;
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_a_5060_);
lean_dec(v___x_5047_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5065_; 
if (v_isShared_5063_ == 0)
{
v___x_5065_ = v___x_5062_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5070_, lean_object* v_sz_5071_, lean_object* v_i_5072_, lean_object* v_b_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_){
_start:
{
size_t v_sz_boxed_5084_; size_t v_i_boxed_5085_; lean_object* v_res_5086_; 
v_sz_boxed_5084_ = lean_unbox_usize(v_sz_5071_);
lean_dec(v_sz_5071_);
v_i_boxed_5085_ = lean_unbox_usize(v_i_5072_);
lean_dec(v_i_5072_);
v_res_5086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5070_, v_sz_boxed_5084_, v_i_boxed_5085_, v_b_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v_as_5070_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5087_, size_t v_sz_5088_, size_t v_i_5089_, lean_object* v_b_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_){
_start:
{
uint8_t v___x_5101_; 
v___x_5101_ = lean_usize_dec_lt(v_i_5089_, v_sz_5088_);
if (v___x_5101_ == 0)
{
lean_object* v___x_5102_; 
v___x_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5102_, 0, v_b_5090_);
return v___x_5102_;
}
else
{
lean_object* v_snd_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5129_; 
v_snd_5103_ = lean_ctor_get(v_b_5090_, 1);
v_isSharedCheck_5129_ = !lean_is_exclusive(v_b_5090_);
if (v_isSharedCheck_5129_ == 0)
{
lean_object* v_unused_5130_; 
v_unused_5130_ = lean_ctor_get(v_b_5090_, 0);
lean_dec(v_unused_5130_);
v___x_5105_ = v_b_5090_;
v_isShared_5106_ = v_isSharedCheck_5129_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_snd_5103_);
lean_dec(v_b_5090_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5129_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v_a_5107_; lean_object* v___x_5108_; 
v_a_5107_ = lean_array_uget_borrowed(v_as_5087_, v_i_5089_);
lean_inc(v_a_5107_);
v___x_5108_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5107_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; lean_object* v___x_5110_; lean_object* v_a_5112_; uint8_t v___x_5119_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5109_);
lean_dec_ref_known(v___x_5108_, 1);
v___x_5110_ = lean_box(0);
v___x_5119_ = lean_unbox(v_a_5109_);
lean_dec(v_a_5109_);
if (v___x_5119_ == 0)
{
v_a_5112_ = v_snd_5103_;
goto v___jp_5111_;
}
else
{
lean_object* v___x_5120_; 
lean_inc(v_a_5107_);
v___x_5120_ = l_Lean_PersistentArray_push___redArg(v_snd_5103_, v_a_5107_);
v_a_5112_ = v___x_5120_;
goto v___jp_5111_;
}
v___jp_5111_:
{
lean_object* v___x_5114_; 
if (v_isShared_5106_ == 0)
{
lean_ctor_set(v___x_5105_, 1, v_a_5112_);
lean_ctor_set(v___x_5105_, 0, v___x_5110_);
v___x_5114_ = v___x_5105_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5110_);
lean_ctor_set(v_reuseFailAlloc_5118_, 1, v_a_5112_);
v___x_5114_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
size_t v___x_5115_; size_t v___x_5116_; 
v___x_5115_ = ((size_t)1ULL);
v___x_5116_ = lean_usize_add(v_i_5089_, v___x_5115_);
v_i_5089_ = v___x_5116_;
v_b_5090_ = v___x_5114_;
goto _start;
}
}
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
lean_del_object(v___x_5105_);
lean_dec(v_snd_5103_);
v_a_5121_ = lean_ctor_get(v___x_5108_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5108_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5108_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5108_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5131_, lean_object* v_sz_5132_, lean_object* v_i_5133_, lean_object* v_b_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_){
_start:
{
size_t v_sz_boxed_5145_; size_t v_i_boxed_5146_; lean_object* v_res_5147_; 
v_sz_boxed_5145_ = lean_unbox_usize(v_sz_5132_);
lean_dec(v_sz_5132_);
v_i_boxed_5146_ = lean_unbox_usize(v_i_5133_);
lean_dec(v_i_5133_);
v_res_5147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5131_, v_sz_boxed_5145_, v_i_boxed_5146_, v_b_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
lean_dec(v___y_5137_);
lean_dec_ref(v___y_5136_);
lean_dec(v___y_5135_);
lean_dec_ref(v_as_5131_);
return v_res_5147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5148_, size_t v_sz_5149_, size_t v_i_5150_, lean_object* v_b_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
uint8_t v___x_5162_; 
v___x_5162_ = lean_usize_dec_lt(v_i_5150_, v_sz_5149_);
if (v___x_5162_ == 0)
{
lean_object* v___x_5163_; 
v___x_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5163_, 0, v_b_5151_);
return v___x_5163_;
}
else
{
lean_object* v_snd_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5190_; 
v_snd_5164_ = lean_ctor_get(v_b_5151_, 1);
v_isSharedCheck_5190_ = !lean_is_exclusive(v_b_5151_);
if (v_isSharedCheck_5190_ == 0)
{
lean_object* v_unused_5191_; 
v_unused_5191_ = lean_ctor_get(v_b_5151_, 0);
lean_dec(v_unused_5191_);
v___x_5166_ = v_b_5151_;
v_isShared_5167_ = v_isSharedCheck_5190_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_snd_5164_);
lean_dec(v_b_5151_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5190_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v_a_5168_; lean_object* v___x_5169_; 
v_a_5168_ = lean_array_uget_borrowed(v_as_5148_, v_i_5150_);
lean_inc(v_a_5168_);
v___x_5169_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5168_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v_a_5170_; lean_object* v___x_5171_; lean_object* v_a_5173_; uint8_t v___x_5180_; 
v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_a_5170_);
lean_dec_ref_known(v___x_5169_, 1);
v___x_5171_ = lean_box(0);
v___x_5180_ = lean_unbox(v_a_5170_);
lean_dec(v_a_5170_);
if (v___x_5180_ == 0)
{
v_a_5173_ = v_snd_5164_;
goto v___jp_5172_;
}
else
{
lean_object* v___x_5181_; 
lean_inc(v_a_5168_);
v___x_5181_ = l_Lean_PersistentArray_push___redArg(v_snd_5164_, v_a_5168_);
v_a_5173_ = v___x_5181_;
goto v___jp_5172_;
}
v___jp_5172_:
{
lean_object* v___x_5175_; 
if (v_isShared_5167_ == 0)
{
lean_ctor_set(v___x_5166_, 1, v_a_5173_);
lean_ctor_set(v___x_5166_, 0, v___x_5171_);
v___x_5175_ = v___x_5166_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5171_);
lean_ctor_set(v_reuseFailAlloc_5179_, 1, v_a_5173_);
v___x_5175_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
size_t v___x_5176_; size_t v___x_5177_; lean_object* v___x_5178_; 
v___x_5176_ = ((size_t)1ULL);
v___x_5177_ = lean_usize_add(v_i_5150_, v___x_5176_);
v___x_5178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5148_, v_sz_5149_, v___x_5177_, v___x_5175_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
return v___x_5178_;
}
}
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
lean_del_object(v___x_5166_);
lean_dec(v_snd_5164_);
v_a_5182_ = lean_ctor_get(v___x_5169_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5169_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5169_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5169_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5192_, lean_object* v_sz_5193_, lean_object* v_i_5194_, lean_object* v_b_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
size_t v_sz_boxed_5206_; size_t v_i_boxed_5207_; lean_object* v_res_5208_; 
v_sz_boxed_5206_ = lean_unbox_usize(v_sz_5193_);
lean_dec(v_sz_5193_);
v_i_boxed_5207_ = lean_unbox_usize(v_i_5194_);
lean_dec(v_i_5194_);
v_res_5208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5192_, v_sz_boxed_5206_, v_i_boxed_5207_, v_b_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
lean_dec(v___y_5200_);
lean_dec_ref(v___y_5199_);
lean_dec(v___y_5198_);
lean_dec_ref(v___y_5197_);
lean_dec(v___y_5196_);
lean_dec_ref(v_as_5192_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5209_, lean_object* v_n_5210_, lean_object* v_b_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_){
_start:
{
if (lean_obj_tag(v_n_5210_) == 0)
{
lean_object* v_cs_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; size_t v_sz_5225_; size_t v___x_5226_; lean_object* v___x_5227_; 
v_cs_5222_ = lean_ctor_get(v_n_5210_, 0);
v___x_5223_ = lean_box(0);
v___x_5224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5223_);
lean_ctor_set(v___x_5224_, 1, v_b_5211_);
v_sz_5225_ = lean_array_size(v_cs_5222_);
v___x_5226_ = ((size_t)0ULL);
v___x_5227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5209_, v_cs_5222_, v_sz_5225_, v___x_5226_, v___x_5224_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5242_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5230_ = v___x_5227_;
v_isShared_5231_ = v_isSharedCheck_5242_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5227_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5242_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v_fst_5232_; 
v_fst_5232_ = lean_ctor_get(v_a_5228_, 0);
if (lean_obj_tag(v_fst_5232_) == 0)
{
lean_object* v_snd_5233_; lean_object* v___x_5234_; lean_object* v___x_5236_; 
v_snd_5233_ = lean_ctor_get(v_a_5228_, 1);
lean_inc(v_snd_5233_);
lean_dec(v_a_5228_);
v___x_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5234_, 0, v_snd_5233_);
if (v_isShared_5231_ == 0)
{
lean_ctor_set(v___x_5230_, 0, v___x_5234_);
v___x_5236_ = v___x_5230_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v___x_5234_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
return v___x_5236_;
}
}
else
{
lean_object* v_val_5238_; lean_object* v___x_5240_; 
lean_inc_ref(v_fst_5232_);
lean_dec(v_a_5228_);
v_val_5238_ = lean_ctor_get(v_fst_5232_, 0);
lean_inc(v_val_5238_);
lean_dec_ref_known(v_fst_5232_, 1);
if (v_isShared_5231_ == 0)
{
lean_ctor_set(v___x_5230_, 0, v_val_5238_);
v___x_5240_ = v___x_5230_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_val_5238_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
}
else
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5250_; 
v_a_5243_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5227_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5227_);
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
else
{
lean_object* v_vs_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; size_t v_sz_5254_; size_t v___x_5255_; lean_object* v___x_5256_; 
v_vs_5251_ = lean_ctor_get(v_n_5210_, 0);
v___x_5252_ = lean_box(0);
v___x_5253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5253_, 0, v___x_5252_);
lean_ctor_set(v___x_5253_, 1, v_b_5211_);
v_sz_5254_ = lean_array_size(v_vs_5251_);
v___x_5255_ = ((size_t)0ULL);
v___x_5256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5251_, v_sz_5254_, v___x_5255_, v___x_5253_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_);
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5271_; 
v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5271_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5259_ = v___x_5256_;
v_isShared_5260_ = v_isSharedCheck_5271_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5256_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5271_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v_fst_5261_; 
v_fst_5261_ = lean_ctor_get(v_a_5257_, 0);
if (lean_obj_tag(v_fst_5261_) == 0)
{
lean_object* v_snd_5262_; lean_object* v___x_5263_; lean_object* v___x_5265_; 
v_snd_5262_ = lean_ctor_get(v_a_5257_, 1);
lean_inc(v_snd_5262_);
lean_dec(v_a_5257_);
v___x_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5263_, 0, v_snd_5262_);
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 0, v___x_5263_);
v___x_5265_ = v___x_5259_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5263_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
else
{
lean_object* v_val_5267_; lean_object* v___x_5269_; 
lean_inc_ref(v_fst_5261_);
lean_dec(v_a_5257_);
v_val_5267_ = lean_ctor_get(v_fst_5261_, 0);
lean_inc(v_val_5267_);
lean_dec_ref_known(v_fst_5261_, 1);
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 0, v_val_5267_);
v___x_5269_ = v___x_5259_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5270_; 
v_reuseFailAlloc_5270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5270_, 0, v_val_5267_);
v___x_5269_ = v_reuseFailAlloc_5270_;
goto v_reusejp_5268_;
}
v_reusejp_5268_:
{
return v___x_5269_;
}
}
}
}
else
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5279_; 
v_a_5272_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5274_ = v___x_5256_;
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5256_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___x_5277_; 
if (v_isShared_5275_ == 0)
{
v___x_5277_ = v___x_5274_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v_a_5272_);
v___x_5277_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
return v___x_5277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5280_, lean_object* v_as_5281_, size_t v_sz_5282_, size_t v_i_5283_, lean_object* v_b_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_){
_start:
{
uint8_t v___x_5295_; 
v___x_5295_ = lean_usize_dec_lt(v_i_5283_, v_sz_5282_);
if (v___x_5295_ == 0)
{
lean_object* v___x_5296_; 
v___x_5296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5296_, 0, v_b_5284_);
return v___x_5296_;
}
else
{
lean_object* v_snd_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5331_; 
v_snd_5297_ = lean_ctor_get(v_b_5284_, 1);
v_isSharedCheck_5331_ = !lean_is_exclusive(v_b_5284_);
if (v_isSharedCheck_5331_ == 0)
{
lean_object* v_unused_5332_; 
v_unused_5332_ = lean_ctor_get(v_b_5284_, 0);
lean_dec(v_unused_5332_);
v___x_5299_ = v_b_5284_;
v_isShared_5300_ = v_isSharedCheck_5331_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_snd_5297_);
lean_dec(v_b_5284_);
v___x_5299_ = lean_box(0);
v_isShared_5300_ = v_isSharedCheck_5331_;
goto v_resetjp_5298_;
}
v_resetjp_5298_:
{
lean_object* v_a_5301_; lean_object* v___x_5302_; 
v_a_5301_ = lean_array_uget_borrowed(v_as_5281_, v_i_5283_);
lean_inc(v_snd_5297_);
v___x_5302_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5280_, v_a_5301_, v_snd_5297_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
if (lean_obj_tag(v___x_5302_) == 0)
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5322_; 
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5305_ = v___x_5302_;
v_isShared_5306_ = v_isSharedCheck_5322_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___x_5302_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5322_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
if (lean_obj_tag(v_a_5303_) == 0)
{
lean_object* v___x_5307_; lean_object* v___x_5309_; 
v___x_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5307_, 0, v_a_5303_);
if (v_isShared_5300_ == 0)
{
lean_ctor_set(v___x_5299_, 0, v___x_5307_);
v___x_5309_ = v___x_5299_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5313_; 
v_reuseFailAlloc_5313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5313_, 0, v___x_5307_);
lean_ctor_set(v_reuseFailAlloc_5313_, 1, v_snd_5297_);
v___x_5309_ = v_reuseFailAlloc_5313_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
lean_object* v___x_5311_; 
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 0, v___x_5309_);
v___x_5311_ = v___x_5305_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v___x_5309_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
else
{
lean_object* v_a_5314_; lean_object* v___x_5315_; lean_object* v___x_5317_; 
lean_del_object(v___x_5305_);
lean_dec(v_snd_5297_);
v_a_5314_ = lean_ctor_get(v_a_5303_, 0);
lean_inc(v_a_5314_);
lean_dec_ref_known(v_a_5303_, 1);
v___x_5315_ = lean_box(0);
if (v_isShared_5300_ == 0)
{
lean_ctor_set(v___x_5299_, 1, v_a_5314_);
lean_ctor_set(v___x_5299_, 0, v___x_5315_);
v___x_5317_ = v___x_5299_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v___x_5315_);
lean_ctor_set(v_reuseFailAlloc_5321_, 1, v_a_5314_);
v___x_5317_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
size_t v___x_5318_; size_t v___x_5319_; 
v___x_5318_ = ((size_t)1ULL);
v___x_5319_ = lean_usize_add(v_i_5283_, v___x_5318_);
v_i_5283_ = v___x_5319_;
v_b_5284_ = v___x_5317_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5330_; 
lean_del_object(v___x_5299_);
lean_dec(v_snd_5297_);
v_a_5323_ = lean_ctor_get(v___x_5302_, 0);
v_isSharedCheck_5330_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5330_ == 0)
{
v___x_5325_ = v___x_5302_;
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_a_5323_);
lean_dec(v___x_5302_);
v___x_5325_ = lean_box(0);
v_isShared_5326_ = v_isSharedCheck_5330_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v___x_5328_; 
if (v_isShared_5326_ == 0)
{
v___x_5328_ = v___x_5325_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v_a_5323_);
v___x_5328_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
return v___x_5328_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5333_, lean_object* v_as_5334_, lean_object* v_sz_5335_, lean_object* v_i_5336_, lean_object* v_b_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
size_t v_sz_boxed_5348_; size_t v_i_boxed_5349_; lean_object* v_res_5350_; 
v_sz_boxed_5348_ = lean_unbox_usize(v_sz_5335_);
lean_dec(v_sz_5335_);
v_i_boxed_5349_ = lean_unbox_usize(v_i_5336_);
lean_dec(v_i_5336_);
v_res_5350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5333_, v_as_5334_, v_sz_boxed_5348_, v_i_boxed_5349_, v_b_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec(v___y_5338_);
lean_dec_ref(v_as_5334_);
lean_dec_ref(v_init_5333_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5351_, lean_object* v_n_5352_, lean_object* v_b_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_){
_start:
{
lean_object* v_res_5364_; 
v_res_5364_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5351_, v_n_5352_, v_b_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
lean_dec(v___y_5360_);
lean_dec_ref(v___y_5359_);
lean_dec(v___y_5358_);
lean_dec_ref(v___y_5357_);
lean_dec(v___y_5356_);
lean_dec_ref(v___y_5355_);
lean_dec(v___y_5354_);
lean_dec_ref(v_n_5352_);
lean_dec_ref(v_init_5351_);
return v_res_5364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5365_, lean_object* v_init_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_root_5377_; lean_object* v_tail_5378_; lean_object* v___x_5379_; 
v_root_5377_ = lean_ctor_get(v_t_5365_, 0);
v_tail_5378_ = lean_ctor_get(v_t_5365_, 1);
lean_inc_ref(v_init_5366_);
v___x_5379_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5366_, v_root_5377_, v_init_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
lean_dec_ref(v_init_5366_);
if (lean_obj_tag(v___x_5379_) == 0)
{
lean_object* v_a_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5416_; 
v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5416_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5382_ = v___x_5379_;
v_isShared_5383_ = v_isSharedCheck_5416_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_a_5380_);
lean_dec(v___x_5379_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5416_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
if (lean_obj_tag(v_a_5380_) == 0)
{
lean_object* v_a_5384_; lean_object* v___x_5386_; 
v_a_5384_ = lean_ctor_get(v_a_5380_, 0);
lean_inc(v_a_5384_);
lean_dec_ref_known(v_a_5380_, 1);
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 0, v_a_5384_);
v___x_5386_ = v___x_5382_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_a_5384_);
v___x_5386_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
return v___x_5386_;
}
}
else
{
lean_object* v_a_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; size_t v_sz_5391_; size_t v___x_5392_; lean_object* v___x_5393_; 
lean_del_object(v___x_5382_);
v_a_5388_ = lean_ctor_get(v_a_5380_, 0);
lean_inc(v_a_5388_);
lean_dec_ref_known(v_a_5380_, 1);
v___x_5389_ = lean_box(0);
v___x_5390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5390_, 0, v___x_5389_);
lean_ctor_set(v___x_5390_, 1, v_a_5388_);
v_sz_5391_ = lean_array_size(v_tail_5378_);
v___x_5392_ = ((size_t)0ULL);
v___x_5393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5378_, v_sz_5391_, v___x_5392_, v___x_5390_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5407_; 
v_a_5394_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5396_ = v___x_5393_;
v_isShared_5397_ = v_isSharedCheck_5407_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5393_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5407_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v_fst_5398_; 
v_fst_5398_ = lean_ctor_get(v_a_5394_, 0);
if (lean_obj_tag(v_fst_5398_) == 0)
{
lean_object* v_snd_5399_; lean_object* v___x_5401_; 
v_snd_5399_ = lean_ctor_get(v_a_5394_, 1);
lean_inc(v_snd_5399_);
lean_dec(v_a_5394_);
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 0, v_snd_5399_);
v___x_5401_ = v___x_5396_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_snd_5399_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
else
{
lean_object* v_val_5403_; lean_object* v___x_5405_; 
lean_inc_ref(v_fst_5398_);
lean_dec(v_a_5394_);
v_val_5403_ = lean_ctor_get(v_fst_5398_, 0);
lean_inc(v_val_5403_);
lean_dec_ref_known(v_fst_5398_, 1);
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 0, v_val_5403_);
v___x_5405_ = v___x_5396_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_val_5403_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
}
else
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5415_; 
v_a_5408_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5410_ = v___x_5393_;
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5393_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5413_; 
if (v_isShared_5411_ == 0)
{
v___x_5413_ = v___x_5410_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
}
}
}
else
{
lean_object* v_a_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5424_; 
v_a_5417_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5424_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5424_ == 0)
{
v___x_5419_ = v___x_5379_;
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_a_5417_);
lean_dec(v___x_5379_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v___x_5422_; 
if (v_isShared_5420_ == 0)
{
v___x_5422_ = v___x_5419_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_a_5417_);
v___x_5422_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
return v___x_5422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5425_, lean_object* v_init_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5425_, v_init_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
lean_dec(v___y_5435_);
lean_dec_ref(v___y_5434_);
lean_dec(v___y_5433_);
lean_dec_ref(v___y_5432_);
lean_dec(v___y_5431_);
lean_dec_ref(v___y_5430_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v___y_5427_);
lean_dec_ref(v_t_5425_);
return v_res_5437_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; 
v___x_5438_ = lean_unsigned_to_nat(32u);
v___x_5439_ = lean_mk_empty_array_with_capacity(v___x_5438_);
v___x_5440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5440_, 0, v___x_5439_);
return v___x_5440_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v_result_5446_; 
v___x_5441_ = ((size_t)5ULL);
v___x_5442_ = lean_unsigned_to_nat(0u);
v___x_5443_ = lean_unsigned_to_nat(32u);
v___x_5444_ = lean_mk_empty_array_with_capacity(v___x_5443_);
v___x_5445_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5446_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5446_, 0, v___x_5445_);
lean_ctor_set(v_result_5446_, 1, v___x_5444_);
lean_ctor_set(v_result_5446_, 2, v___x_5442_);
lean_ctor_set(v_result_5446_, 3, v___x_5442_);
lean_ctor_set_usize(v_result_5446_, 4, v___x_5441_);
return v_result_5446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_){
_start:
{
lean_object* v_result_5458_; lean_object* v___x_5459_; 
v_result_5458_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5459_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5447_, v_result_5458_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_);
return v___x_5459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_){
_start:
{
lean_object* v_res_5471_; 
v_res_5471_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_);
lean_dec(v_a_5469_);
lean_dec_ref(v_a_5468_);
lean_dec(v_a_5467_);
lean_dec_ref(v_a_5466_);
lean_dec(v_a_5465_);
lean_dec_ref(v_a_5464_);
lean_dec(v_a_5463_);
lean_dec_ref(v_a_5462_);
lean_dec(v_a_5461_);
lean_dec_ref(v_thms_5460_);
return v_res_5471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5474_, lean_object* v_newThms_5475_, lean_object* v_gmt_5476_, lean_object* v_numInstances_5477_, lean_object* v_numDelayedInstances_5478_, lean_object* v_num_5479_, lean_object* v_preInstances_5480_, lean_object* v_nextThmIdx_5481_, lean_object* v_matchEqNames_5482_, lean_object* v_delayedThmInsts_5483_, lean_object* v_nextDeclIdx_5484_, lean_object* v_enodeMap_5485_, lean_object* v_exprs_5486_, lean_object* v_parents_5487_, lean_object* v_congrTable_5488_, lean_object* v_appMap_5489_, lean_object* v_indicesFound_5490_, lean_object* v_newFacts_5491_, uint8_t v_inconsistent_5492_, lean_object* v_nextIdx_5493_, lean_object* v_newRawFacts_5494_, lean_object* v_facts_5495_, lean_object* v_extThms_5496_, lean_object* v_inj_5497_, lean_object* v_split_5498_, lean_object* v_clean_5499_, lean_object* v_sstates_5500_, lean_object* v_mvarId_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_){
_start:
{
lean_object* v___x_5512_; 
v___x_5512_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5474_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_);
if (lean_obj_tag(v___x_5512_) == 0)
{
lean_object* v_a_5513_; lean_object* v___x_5514_; 
v_a_5513_ = lean_ctor_get(v___x_5512_, 0);
lean_inc(v_a_5513_);
lean_dec_ref_known(v___x_5512_, 1);
v___x_5514_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5475_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, v___y_5510_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_object* v_a_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5526_; 
v_a_5515_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5517_ = v___x_5514_;
v_isShared_5518_ = v_isSharedCheck_5526_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_a_5515_);
lean_dec(v___x_5514_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5526_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5524_; 
v___x_5519_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5520_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5520_, 0, v___x_5519_);
lean_ctor_set(v___x_5520_, 1, v_gmt_5476_);
lean_ctor_set(v___x_5520_, 2, v_a_5513_);
lean_ctor_set(v___x_5520_, 3, v_a_5515_);
lean_ctor_set(v___x_5520_, 4, v_numInstances_5477_);
lean_ctor_set(v___x_5520_, 5, v_numDelayedInstances_5478_);
lean_ctor_set(v___x_5520_, 6, v_num_5479_);
lean_ctor_set(v___x_5520_, 7, v_preInstances_5480_);
lean_ctor_set(v___x_5520_, 8, v_nextThmIdx_5481_);
lean_ctor_set(v___x_5520_, 9, v_matchEqNames_5482_);
lean_ctor_set(v___x_5520_, 10, v_delayedThmInsts_5483_);
v___x_5521_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_5521_, 0, v_nextDeclIdx_5484_);
lean_ctor_set(v___x_5521_, 1, v_enodeMap_5485_);
lean_ctor_set(v___x_5521_, 2, v_exprs_5486_);
lean_ctor_set(v___x_5521_, 3, v_parents_5487_);
lean_ctor_set(v___x_5521_, 4, v_congrTable_5488_);
lean_ctor_set(v___x_5521_, 5, v_appMap_5489_);
lean_ctor_set(v___x_5521_, 6, v_indicesFound_5490_);
lean_ctor_set(v___x_5521_, 7, v_newFacts_5491_);
lean_ctor_set(v___x_5521_, 8, v_nextIdx_5493_);
lean_ctor_set(v___x_5521_, 9, v_newRawFacts_5494_);
lean_ctor_set(v___x_5521_, 10, v_facts_5495_);
lean_ctor_set(v___x_5521_, 11, v_extThms_5496_);
lean_ctor_set(v___x_5521_, 12, v___x_5520_);
lean_ctor_set(v___x_5521_, 13, v_inj_5497_);
lean_ctor_set(v___x_5521_, 14, v_split_5498_);
lean_ctor_set(v___x_5521_, 15, v_clean_5499_);
lean_ctor_set(v___x_5521_, 16, v_sstates_5500_);
lean_ctor_set_uint8(v___x_5521_, sizeof(void*)*17, v_inconsistent_5492_);
v___x_5522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5522_, 0, v___x_5521_);
lean_ctor_set(v___x_5522_, 1, v_mvarId_5501_);
if (v_isShared_5518_ == 0)
{
lean_ctor_set(v___x_5517_, 0, v___x_5522_);
v___x_5524_ = v___x_5517_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v___x_5522_);
v___x_5524_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
return v___x_5524_;
}
}
}
else
{
lean_object* v_a_5527_; lean_object* v___x_5529_; uint8_t v_isShared_5530_; uint8_t v_isSharedCheck_5534_; 
lean_dec(v_a_5513_);
lean_dec(v_mvarId_5501_);
lean_dec_ref(v_sstates_5500_);
lean_dec_ref(v_clean_5499_);
lean_dec_ref(v_split_5498_);
lean_dec_ref(v_inj_5497_);
lean_dec_ref(v_extThms_5496_);
lean_dec_ref(v_facts_5495_);
lean_dec_ref(v_newRawFacts_5494_);
lean_dec(v_nextIdx_5493_);
lean_dec_ref(v_newFacts_5491_);
lean_dec_ref(v_indicesFound_5490_);
lean_dec_ref(v_appMap_5489_);
lean_dec_ref(v_congrTable_5488_);
lean_dec_ref(v_parents_5487_);
lean_dec_ref(v_exprs_5486_);
lean_dec_ref(v_enodeMap_5485_);
lean_dec(v_nextDeclIdx_5484_);
lean_dec_ref(v_delayedThmInsts_5483_);
lean_dec_ref(v_matchEqNames_5482_);
lean_dec(v_nextThmIdx_5481_);
lean_dec_ref(v_preInstances_5480_);
lean_dec(v_num_5479_);
lean_dec(v_numDelayedInstances_5478_);
lean_dec(v_numInstances_5477_);
lean_dec(v_gmt_5476_);
v_a_5527_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5534_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5534_ == 0)
{
v___x_5529_ = v___x_5514_;
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
else
{
lean_inc(v_a_5527_);
lean_dec(v___x_5514_);
v___x_5529_ = lean_box(0);
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
v_resetjp_5528_:
{
lean_object* v___x_5532_; 
if (v_isShared_5530_ == 0)
{
v___x_5532_ = v___x_5529_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_a_5527_);
v___x_5532_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
return v___x_5532_;
}
}
}
}
else
{
lean_object* v_a_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5542_; 
lean_dec(v_mvarId_5501_);
lean_dec_ref(v_sstates_5500_);
lean_dec_ref(v_clean_5499_);
lean_dec_ref(v_split_5498_);
lean_dec_ref(v_inj_5497_);
lean_dec_ref(v_extThms_5496_);
lean_dec_ref(v_facts_5495_);
lean_dec_ref(v_newRawFacts_5494_);
lean_dec(v_nextIdx_5493_);
lean_dec_ref(v_newFacts_5491_);
lean_dec_ref(v_indicesFound_5490_);
lean_dec_ref(v_appMap_5489_);
lean_dec_ref(v_congrTable_5488_);
lean_dec_ref(v_parents_5487_);
lean_dec_ref(v_exprs_5486_);
lean_dec_ref(v_enodeMap_5485_);
lean_dec(v_nextDeclIdx_5484_);
lean_dec_ref(v_delayedThmInsts_5483_);
lean_dec_ref(v_matchEqNames_5482_);
lean_dec(v_nextThmIdx_5481_);
lean_dec_ref(v_preInstances_5480_);
lean_dec(v_num_5479_);
lean_dec(v_numDelayedInstances_5478_);
lean_dec(v_numInstances_5477_);
lean_dec(v_gmt_5476_);
v_a_5535_ = lean_ctor_get(v___x_5512_, 0);
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5512_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5537_ = v___x_5512_;
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_a_5535_);
lean_dec(v___x_5512_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5540_; 
if (v_isShared_5538_ == 0)
{
v___x_5540_ = v___x_5537_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_a_5535_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
return v___x_5540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5543_ = _args[0];
lean_object* v_newThms_5544_ = _args[1];
lean_object* v_gmt_5545_ = _args[2];
lean_object* v_numInstances_5546_ = _args[3];
lean_object* v_numDelayedInstances_5547_ = _args[4];
lean_object* v_num_5548_ = _args[5];
lean_object* v_preInstances_5549_ = _args[6];
lean_object* v_nextThmIdx_5550_ = _args[7];
lean_object* v_matchEqNames_5551_ = _args[8];
lean_object* v_delayedThmInsts_5552_ = _args[9];
lean_object* v_nextDeclIdx_5553_ = _args[10];
lean_object* v_enodeMap_5554_ = _args[11];
lean_object* v_exprs_5555_ = _args[12];
lean_object* v_parents_5556_ = _args[13];
lean_object* v_congrTable_5557_ = _args[14];
lean_object* v_appMap_5558_ = _args[15];
lean_object* v_indicesFound_5559_ = _args[16];
lean_object* v_newFacts_5560_ = _args[17];
lean_object* v_inconsistent_5561_ = _args[18];
lean_object* v_nextIdx_5562_ = _args[19];
lean_object* v_newRawFacts_5563_ = _args[20];
lean_object* v_facts_5564_ = _args[21];
lean_object* v_extThms_5565_ = _args[22];
lean_object* v_inj_5566_ = _args[23];
lean_object* v_split_5567_ = _args[24];
lean_object* v_clean_5568_ = _args[25];
lean_object* v_sstates_5569_ = _args[26];
lean_object* v_mvarId_5570_ = _args[27];
lean_object* v___y_5571_ = _args[28];
lean_object* v___y_5572_ = _args[29];
lean_object* v___y_5573_ = _args[30];
lean_object* v___y_5574_ = _args[31];
lean_object* v___y_5575_ = _args[32];
lean_object* v___y_5576_ = _args[33];
lean_object* v___y_5577_ = _args[34];
lean_object* v___y_5578_ = _args[35];
lean_object* v___y_5579_ = _args[36];
lean_object* v___y_5580_ = _args[37];
_start:
{
uint8_t v_inconsistent_boxed_5581_; lean_object* v_res_5582_; 
v_inconsistent_boxed_5581_ = lean_unbox(v_inconsistent_5561_);
v_res_5582_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5543_, v_newThms_5544_, v_gmt_5545_, v_numInstances_5546_, v_numDelayedInstances_5547_, v_num_5548_, v_preInstances_5549_, v_nextThmIdx_5550_, v_matchEqNames_5551_, v_delayedThmInsts_5552_, v_nextDeclIdx_5553_, v_enodeMap_5554_, v_exprs_5555_, v_parents_5556_, v_congrTable_5557_, v_appMap_5558_, v_indicesFound_5559_, v_newFacts_5560_, v_inconsistent_boxed_5581_, v_nextIdx_5562_, v_newRawFacts_5563_, v_facts_5564_, v_extThms_5565_, v_inj_5566_, v_split_5567_, v_clean_5568_, v_sstates_5569_, v_mvarId_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_);
lean_dec(v___y_5579_);
lean_dec_ref(v___y_5578_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec(v___y_5575_);
lean_dec_ref(v___y_5574_);
lean_dec(v___y_5573_);
lean_dec_ref(v___y_5572_);
lean_dec(v___y_5571_);
lean_dec_ref(v_newThms_5544_);
lean_dec_ref(v_thms_5543_);
return v_res_5582_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5583_; 
v___x_5583_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_5583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5584_, size_t v_i_5585_, lean_object* v_bs_5586_){
_start:
{
uint8_t v___x_5587_; 
v___x_5587_ = lean_usize_dec_lt(v_i_5585_, v_sz_5584_);
if (v___x_5587_ == 0)
{
return v_bs_5586_;
}
else
{
lean_object* v_v_5588_; lean_object* v_casesTypes_5589_; lean_object* v_extThms_5590_; lean_object* v_funCC_5591_; lean_object* v_inj_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5606_; 
v_v_5588_ = lean_array_uget(v_bs_5586_, v_i_5585_);
v_casesTypes_5589_ = lean_ctor_get(v_v_5588_, 0);
v_extThms_5590_ = lean_ctor_get(v_v_5588_, 1);
v_funCC_5591_ = lean_ctor_get(v_v_5588_, 2);
v_inj_5592_ = lean_ctor_get(v_v_5588_, 4);
v_isSharedCheck_5606_ = !lean_is_exclusive(v_v_5588_);
if (v_isSharedCheck_5606_ == 0)
{
lean_object* v_unused_5607_; 
v_unused_5607_ = lean_ctor_get(v_v_5588_, 3);
lean_dec(v_unused_5607_);
v___x_5594_ = v_v_5588_;
v_isShared_5595_ = v_isSharedCheck_5606_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_inj_5592_);
lean_inc(v_funCC_5591_);
lean_inc(v_extThms_5590_);
lean_inc(v_casesTypes_5589_);
lean_dec(v_v_5588_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5606_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5596_; lean_object* v_bs_x27_5597_; lean_object* v___x_5598_; lean_object* v___x_5600_; 
v___x_5596_ = lean_unsigned_to_nat(0u);
v_bs_x27_5597_ = lean_array_uset(v_bs_5586_, v_i_5585_, v___x_5596_);
v___x_5598_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5595_ == 0)
{
lean_ctor_set(v___x_5594_, 3, v___x_5598_);
v___x_5600_ = v___x_5594_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_casesTypes_5589_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v_extThms_5590_);
lean_ctor_set(v_reuseFailAlloc_5605_, 2, v_funCC_5591_);
lean_ctor_set(v_reuseFailAlloc_5605_, 3, v___x_5598_);
lean_ctor_set(v_reuseFailAlloc_5605_, 4, v_inj_5592_);
v___x_5600_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
size_t v___x_5601_; size_t v___x_5602_; lean_object* v___x_5603_; 
v___x_5601_ = ((size_t)1ULL);
v___x_5602_ = lean_usize_add(v_i_5585_, v___x_5601_);
v___x_5603_ = lean_array_uset(v_bs_x27_5597_, v_i_5585_, v___x_5600_);
v_i_5585_ = v___x_5602_;
v_bs_5586_ = v___x_5603_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5608_, lean_object* v_i_5609_, lean_object* v_bs_5610_){
_start:
{
size_t v_sz_boxed_5611_; size_t v_i_boxed_5612_; lean_object* v_res_5613_; 
v_sz_boxed_5611_ = lean_unbox_usize(v_sz_5608_);
lean_dec(v_sz_5608_);
v_i_boxed_5612_ = lean_unbox_usize(v_i_5609_);
lean_dec(v_i_5609_);
v_res_5613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5611_, v_i_boxed_5612_, v_bs_5610_);
return v_res_5613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5614_, lean_object* v_ps_5615_, uint8_t v_only_5616_, lean_object* v_k_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_){
_start:
{
lean_object* v___y_5628_; lean_object* v___y_5629_; lean_object* v___y_5630_; lean_object* v___y_5631_; lean_object* v___y_5632_; lean_object* v___y_5633_; lean_object* v___y_5634_; lean_object* v___y_5635_; lean_object* v___y_5636_; uint8_t v___y_5649_; uint8_t v___y_5650_; lean_object* v_params_5651_; lean_object* v___y_5652_; lean_object* v___y_5653_; lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v___y_5657_; lean_object* v___y_5658_; lean_object* v___y_5659_; uint8_t v___y_5760_; 
if (v_only_5616_ == 0)
{
lean_object* v___x_5782_; lean_object* v___x_5783_; uint8_t v___x_5784_; 
v___x_5782_ = lean_array_get_size(v_ps_5615_);
v___x_5783_ = lean_unsigned_to_nat(0u);
v___x_5784_ = lean_nat_dec_eq(v___x_5782_, v___x_5783_);
if (v___x_5784_ == 0)
{
v___y_5760_ = v___x_5784_;
goto v___jp_5759_;
}
else
{
lean_object* v___x_5785_; 
lean_dec_ref(v_params_5614_);
lean_inc(v_a_5625_);
lean_inc_ref(v_a_5624_);
lean_inc(v_a_5623_);
lean_inc_ref(v_a_5622_);
lean_inc(v_a_5621_);
lean_inc_ref(v_a_5620_);
lean_inc(v_a_5619_);
lean_inc_ref(v_a_5618_);
v___x_5785_ = lean_apply_9(v_k_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_, lean_box(0));
return v___x_5785_;
}
}
else
{
uint8_t v___x_5786_; 
v___x_5786_ = 0;
v___y_5760_ = v___x_5786_;
goto v___jp_5759_;
}
v___jp_5627_:
{
lean_object* v___x_5637_; lean_object* v___x_5638_; 
v___x_5637_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5637_, 0, v___y_5628_);
v___x_5638_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5637_, v___y_5629_, v___y_5630_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_);
if (lean_obj_tag(v___x_5638_) == 0)
{
lean_object* v___x_5639_; 
lean_dec_ref_known(v___x_5638_, 1);
lean_inc(v___y_5636_);
lean_inc_ref(v___y_5635_);
lean_inc(v___y_5634_);
lean_inc_ref(v___y_5633_);
lean_inc(v___y_5632_);
lean_inc_ref(v___y_5631_);
lean_inc(v___y_5630_);
v___x_5639_ = lean_apply_9(v_k_5617_, v___y_5629_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, lean_box(0));
return v___x_5639_;
}
else
{
lean_object* v_a_5640_; lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5647_; 
lean_dec_ref(v___y_5629_);
lean_dec_ref(v_k_5617_);
v_a_5640_ = lean_ctor_get(v___x_5638_, 0);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5638_);
if (v_isSharedCheck_5647_ == 0)
{
v___x_5642_ = v___x_5638_;
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_a_5640_);
lean_dec(v___x_5638_);
v___x_5642_ = lean_box(0);
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
v_resetjp_5641_:
{
lean_object* v___x_5645_; 
if (v_isShared_5643_ == 0)
{
v___x_5645_ = v___x_5642_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_a_5640_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
}
v___jp_5648_:
{
lean_object* v___x_5660_; 
v___x_5660_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5651_, v_ps_5615_, v_only_5616_, v___y_5650_, v___y_5649_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
if (lean_obj_tag(v___x_5660_) == 0)
{
lean_object* v_a_5661_; lean_object* v_ctx_5662_; lean_object* v_anchorRefs_x3f_5663_; lean_object* v_toContext_5664_; lean_object* v_sctx_5665_; lean_object* v_methods_5666_; uint8_t v_sym_5667_; lean_object* v_simp_5668_; lean_object* v_simpMethods_5669_; lean_object* v_config_5670_; uint8_t v_cheapCases_5671_; uint8_t v_reportMVarIssue_5672_; lean_object* v_splitSource_5673_; lean_object* v_ematchDiagSource_5674_; lean_object* v_symPrios_5675_; lean_object* v_extensions_5676_; uint8_t v_debug_5677_; uint8_t v_ematchDiag_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; 
v_a_5661_ = lean_ctor_get(v___x_5660_, 0);
lean_inc_n(v_a_5661_, 2);
lean_dec_ref_known(v___x_5660_, 1);
v_ctx_5662_ = lean_ctor_get(v___y_5652_, 1);
v_anchorRefs_x3f_5663_ = lean_ctor_get(v_a_5661_, 8);
v_toContext_5664_ = lean_ctor_get(v___y_5652_, 0);
v_sctx_5665_ = lean_ctor_get(v___y_5652_, 2);
v_methods_5666_ = lean_ctor_get(v___y_5652_, 3);
v_sym_5667_ = lean_ctor_get_uint8(v___y_5652_, sizeof(void*)*5);
v_simp_5668_ = lean_ctor_get(v_ctx_5662_, 0);
v_simpMethods_5669_ = lean_ctor_get(v_ctx_5662_, 1);
v_config_5670_ = lean_ctor_get(v_ctx_5662_, 2);
v_cheapCases_5671_ = lean_ctor_get_uint8(v_ctx_5662_, sizeof(void*)*8);
v_reportMVarIssue_5672_ = lean_ctor_get_uint8(v_ctx_5662_, sizeof(void*)*8 + 1);
v_splitSource_5673_ = lean_ctor_get(v_ctx_5662_, 4);
v_ematchDiagSource_5674_ = lean_ctor_get(v_ctx_5662_, 5);
v_symPrios_5675_ = lean_ctor_get(v_ctx_5662_, 6);
v_extensions_5676_ = lean_ctor_get(v_ctx_5662_, 7);
v_debug_5677_ = lean_ctor_get_uint8(v_ctx_5662_, sizeof(void*)*8 + 2);
v_ematchDiag_5678_ = lean_ctor_get_uint8(v_ctx_5662_, sizeof(void*)*8 + 3);
lean_inc_ref(v_extensions_5676_);
lean_inc_ref(v_symPrios_5675_);
lean_inc(v_ematchDiagSource_5674_);
lean_inc(v_splitSource_5673_);
lean_inc(v_anchorRefs_x3f_5663_);
lean_inc_ref(v_config_5670_);
lean_inc_ref(v_simpMethods_5669_);
lean_inc_ref(v_simp_5668_);
v___x_5679_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_5679_, 0, v_simp_5668_);
lean_ctor_set(v___x_5679_, 1, v_simpMethods_5669_);
lean_ctor_set(v___x_5679_, 2, v_config_5670_);
lean_ctor_set(v___x_5679_, 3, v_anchorRefs_x3f_5663_);
lean_ctor_set(v___x_5679_, 4, v_splitSource_5673_);
lean_ctor_set(v___x_5679_, 5, v_ematchDiagSource_5674_);
lean_ctor_set(v___x_5679_, 6, v_symPrios_5675_);
lean_ctor_set(v___x_5679_, 7, v_extensions_5676_);
lean_ctor_set_uint8(v___x_5679_, sizeof(void*)*8, v_cheapCases_5671_);
lean_ctor_set_uint8(v___x_5679_, sizeof(void*)*8 + 1, v_reportMVarIssue_5672_);
lean_ctor_set_uint8(v___x_5679_, sizeof(void*)*8 + 2, v_debug_5677_);
lean_ctor_set_uint8(v___x_5679_, sizeof(void*)*8 + 3, v_ematchDiag_5678_);
lean_inc_ref(v_methods_5666_);
lean_inc_ref(v_sctx_5665_);
lean_inc_ref(v_toContext_5664_);
v___x_5680_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_5680_, 0, v_toContext_5664_);
lean_ctor_set(v___x_5680_, 1, v___x_5679_);
lean_ctor_set(v___x_5680_, 2, v_sctx_5665_);
lean_ctor_set(v___x_5680_, 3, v_methods_5666_);
lean_ctor_set(v___x_5680_, 4, v_a_5661_);
lean_ctor_set_uint8(v___x_5680_, sizeof(void*)*5, v_sym_5667_);
if (v_only_5616_ == 0)
{
v___y_5628_ = v_a_5661_;
v___y_5629_ = v___x_5680_;
v___y_5630_ = v___y_5653_;
v___y_5631_ = v___y_5654_;
v___y_5632_ = v___y_5655_;
v___y_5633_ = v___y_5656_;
v___y_5634_ = v___y_5657_;
v___y_5635_ = v___y_5658_;
v___y_5636_ = v___y_5659_;
goto v___jp_5627_;
}
else
{
lean_object* v___x_5681_; 
v___x_5681_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5653_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
if (lean_obj_tag(v___x_5681_) == 0)
{
lean_object* v_a_5682_; lean_object* v_toGoalState_5683_; lean_object* v_ematch_5684_; lean_object* v_mvarId_5685_; lean_object* v___x_5687_; uint8_t v_isShared_5688_; uint8_t v_isSharedCheck_5741_; 
v_a_5682_ = lean_ctor_get(v___x_5681_, 0);
lean_inc(v_a_5682_);
lean_dec_ref_known(v___x_5681_, 1);
v_toGoalState_5683_ = lean_ctor_get(v_a_5682_, 0);
lean_inc_ref(v_toGoalState_5683_);
v_ematch_5684_ = lean_ctor_get(v_toGoalState_5683_, 12);
lean_inc_ref(v_ematch_5684_);
v_mvarId_5685_ = lean_ctor_get(v_a_5682_, 1);
v_isSharedCheck_5741_ = !lean_is_exclusive(v_a_5682_);
if (v_isSharedCheck_5741_ == 0)
{
lean_object* v_unused_5742_; 
v_unused_5742_ = lean_ctor_get(v_a_5682_, 0);
lean_dec(v_unused_5742_);
v___x_5687_ = v_a_5682_;
v_isShared_5688_ = v_isSharedCheck_5741_;
goto v_resetjp_5686_;
}
else
{
lean_inc(v_mvarId_5685_);
lean_dec(v_a_5682_);
v___x_5687_ = lean_box(0);
v_isShared_5688_ = v_isSharedCheck_5741_;
goto v_resetjp_5686_;
}
v_resetjp_5686_:
{
lean_object* v_nextDeclIdx_5689_; lean_object* v_enodeMap_5690_; lean_object* v_exprs_5691_; lean_object* v_parents_5692_; lean_object* v_congrTable_5693_; lean_object* v_appMap_5694_; lean_object* v_indicesFound_5695_; lean_object* v_newFacts_5696_; uint8_t v_inconsistent_5697_; lean_object* v_nextIdx_5698_; lean_object* v_newRawFacts_5699_; lean_object* v_facts_5700_; lean_object* v_extThms_5701_; lean_object* v_inj_5702_; lean_object* v_split_5703_; lean_object* v_clean_5704_; lean_object* v_sstates_5705_; lean_object* v_gmt_5706_; lean_object* v_thms_5707_; lean_object* v_newThms_5708_; lean_object* v_numInstances_5709_; lean_object* v_numDelayedInstances_5710_; lean_object* v_num_5711_; lean_object* v_preInstances_5712_; lean_object* v_nextThmIdx_5713_; lean_object* v_matchEqNames_5714_; lean_object* v_delayedThmInsts_5715_; lean_object* v___x_5716_; lean_object* v___f_5717_; lean_object* v___x_5718_; 
v_nextDeclIdx_5689_ = lean_ctor_get(v_toGoalState_5683_, 0);
lean_inc(v_nextDeclIdx_5689_);
v_enodeMap_5690_ = lean_ctor_get(v_toGoalState_5683_, 1);
lean_inc_ref(v_enodeMap_5690_);
v_exprs_5691_ = lean_ctor_get(v_toGoalState_5683_, 2);
lean_inc_ref(v_exprs_5691_);
v_parents_5692_ = lean_ctor_get(v_toGoalState_5683_, 3);
lean_inc_ref(v_parents_5692_);
v_congrTable_5693_ = lean_ctor_get(v_toGoalState_5683_, 4);
lean_inc_ref(v_congrTable_5693_);
v_appMap_5694_ = lean_ctor_get(v_toGoalState_5683_, 5);
lean_inc_ref(v_appMap_5694_);
v_indicesFound_5695_ = lean_ctor_get(v_toGoalState_5683_, 6);
lean_inc_ref(v_indicesFound_5695_);
v_newFacts_5696_ = lean_ctor_get(v_toGoalState_5683_, 7);
lean_inc_ref(v_newFacts_5696_);
v_inconsistent_5697_ = lean_ctor_get_uint8(v_toGoalState_5683_, sizeof(void*)*17);
v_nextIdx_5698_ = lean_ctor_get(v_toGoalState_5683_, 8);
lean_inc(v_nextIdx_5698_);
v_newRawFacts_5699_ = lean_ctor_get(v_toGoalState_5683_, 9);
lean_inc_ref(v_newRawFacts_5699_);
v_facts_5700_ = lean_ctor_get(v_toGoalState_5683_, 10);
lean_inc_ref(v_facts_5700_);
v_extThms_5701_ = lean_ctor_get(v_toGoalState_5683_, 11);
lean_inc_ref(v_extThms_5701_);
v_inj_5702_ = lean_ctor_get(v_toGoalState_5683_, 13);
lean_inc_ref(v_inj_5702_);
v_split_5703_ = lean_ctor_get(v_toGoalState_5683_, 14);
lean_inc_ref(v_split_5703_);
v_clean_5704_ = lean_ctor_get(v_toGoalState_5683_, 15);
lean_inc_ref(v_clean_5704_);
v_sstates_5705_ = lean_ctor_get(v_toGoalState_5683_, 16);
lean_inc_ref(v_sstates_5705_);
lean_dec_ref(v_toGoalState_5683_);
v_gmt_5706_ = lean_ctor_get(v_ematch_5684_, 1);
lean_inc(v_gmt_5706_);
v_thms_5707_ = lean_ctor_get(v_ematch_5684_, 2);
lean_inc_ref(v_thms_5707_);
v_newThms_5708_ = lean_ctor_get(v_ematch_5684_, 3);
lean_inc_ref(v_newThms_5708_);
v_numInstances_5709_ = lean_ctor_get(v_ematch_5684_, 4);
lean_inc(v_numInstances_5709_);
v_numDelayedInstances_5710_ = lean_ctor_get(v_ematch_5684_, 5);
lean_inc(v_numDelayedInstances_5710_);
v_num_5711_ = lean_ctor_get(v_ematch_5684_, 6);
lean_inc(v_num_5711_);
v_preInstances_5712_ = lean_ctor_get(v_ematch_5684_, 7);
lean_inc_ref(v_preInstances_5712_);
v_nextThmIdx_5713_ = lean_ctor_get(v_ematch_5684_, 8);
lean_inc(v_nextThmIdx_5713_);
v_matchEqNames_5714_ = lean_ctor_get(v_ematch_5684_, 9);
lean_inc_ref(v_matchEqNames_5714_);
v_delayedThmInsts_5715_ = lean_ctor_get(v_ematch_5684_, 10);
lean_inc_ref(v_delayedThmInsts_5715_);
lean_dec_ref(v_ematch_5684_);
v___x_5716_ = lean_box(v_inconsistent_5697_);
v___f_5717_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 38, 28);
lean_closure_set(v___f_5717_, 0, v_thms_5707_);
lean_closure_set(v___f_5717_, 1, v_newThms_5708_);
lean_closure_set(v___f_5717_, 2, v_gmt_5706_);
lean_closure_set(v___f_5717_, 3, v_numInstances_5709_);
lean_closure_set(v___f_5717_, 4, v_numDelayedInstances_5710_);
lean_closure_set(v___f_5717_, 5, v_num_5711_);
lean_closure_set(v___f_5717_, 6, v_preInstances_5712_);
lean_closure_set(v___f_5717_, 7, v_nextThmIdx_5713_);
lean_closure_set(v___f_5717_, 8, v_matchEqNames_5714_);
lean_closure_set(v___f_5717_, 9, v_delayedThmInsts_5715_);
lean_closure_set(v___f_5717_, 10, v_nextDeclIdx_5689_);
lean_closure_set(v___f_5717_, 11, v_enodeMap_5690_);
lean_closure_set(v___f_5717_, 12, v_exprs_5691_);
lean_closure_set(v___f_5717_, 13, v_parents_5692_);
lean_closure_set(v___f_5717_, 14, v_congrTable_5693_);
lean_closure_set(v___f_5717_, 15, v_appMap_5694_);
lean_closure_set(v___f_5717_, 16, v_indicesFound_5695_);
lean_closure_set(v___f_5717_, 17, v_newFacts_5696_);
lean_closure_set(v___f_5717_, 18, v___x_5716_);
lean_closure_set(v___f_5717_, 19, v_nextIdx_5698_);
lean_closure_set(v___f_5717_, 20, v_newRawFacts_5699_);
lean_closure_set(v___f_5717_, 21, v_facts_5700_);
lean_closure_set(v___f_5717_, 22, v_extThms_5701_);
lean_closure_set(v___f_5717_, 23, v_inj_5702_);
lean_closure_set(v___f_5717_, 24, v_split_5703_);
lean_closure_set(v___f_5717_, 25, v_clean_5704_);
lean_closure_set(v___f_5717_, 26, v_sstates_5705_);
lean_closure_set(v___f_5717_, 27, v_mvarId_5685_);
v___x_5718_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5717_, v___x_5680_, v___y_5653_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
if (lean_obj_tag(v___x_5718_) == 0)
{
lean_object* v_a_5719_; lean_object* v___x_5720_; lean_object* v___x_5722_; 
v_a_5719_ = lean_ctor_get(v___x_5718_, 0);
lean_inc(v_a_5719_);
lean_dec_ref_known(v___x_5718_, 1);
v___x_5720_ = lean_box(0);
if (v_isShared_5688_ == 0)
{
lean_ctor_set_tag(v___x_5687_, 1);
lean_ctor_set(v___x_5687_, 1, v___x_5720_);
lean_ctor_set(v___x_5687_, 0, v_a_5719_);
v___x_5722_ = v___x_5687_;
goto v_reusejp_5721_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_a_5719_);
lean_ctor_set(v_reuseFailAlloc_5732_, 1, v___x_5720_);
v___x_5722_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5721_;
}
v_reusejp_5721_:
{
lean_object* v___x_5723_; 
v___x_5723_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5722_, v___y_5653_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
if (lean_obj_tag(v___x_5723_) == 0)
{
lean_dec_ref_known(v___x_5723_, 1);
v___y_5628_ = v_a_5661_;
v___y_5629_ = v___x_5680_;
v___y_5630_ = v___y_5653_;
v___y_5631_ = v___y_5654_;
v___y_5632_ = v___y_5655_;
v___y_5633_ = v___y_5656_;
v___y_5634_ = v___y_5657_;
v___y_5635_ = v___y_5658_;
v___y_5636_ = v___y_5659_;
goto v___jp_5627_;
}
else
{
lean_object* v_a_5724_; lean_object* v___x_5726_; uint8_t v_isShared_5727_; uint8_t v_isSharedCheck_5731_; 
lean_dec_ref_known(v___x_5680_, 5);
lean_dec(v_a_5661_);
lean_dec_ref(v_k_5617_);
v_a_5724_ = lean_ctor_get(v___x_5723_, 0);
v_isSharedCheck_5731_ = !lean_is_exclusive(v___x_5723_);
if (v_isSharedCheck_5731_ == 0)
{
v___x_5726_ = v___x_5723_;
v_isShared_5727_ = v_isSharedCheck_5731_;
goto v_resetjp_5725_;
}
else
{
lean_inc(v_a_5724_);
lean_dec(v___x_5723_);
v___x_5726_ = lean_box(0);
v_isShared_5727_ = v_isSharedCheck_5731_;
goto v_resetjp_5725_;
}
v_resetjp_5725_:
{
lean_object* v___x_5729_; 
if (v_isShared_5727_ == 0)
{
v___x_5729_ = v___x_5726_;
goto v_reusejp_5728_;
}
else
{
lean_object* v_reuseFailAlloc_5730_; 
v_reuseFailAlloc_5730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5730_, 0, v_a_5724_);
v___x_5729_ = v_reuseFailAlloc_5730_;
goto v_reusejp_5728_;
}
v_reusejp_5728_:
{
return v___x_5729_;
}
}
}
}
}
else
{
lean_object* v_a_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5740_; 
lean_del_object(v___x_5687_);
lean_dec_ref_known(v___x_5680_, 5);
lean_dec(v_a_5661_);
lean_dec_ref(v_k_5617_);
v_a_5733_ = lean_ctor_get(v___x_5718_, 0);
v_isSharedCheck_5740_ = !lean_is_exclusive(v___x_5718_);
if (v_isSharedCheck_5740_ == 0)
{
v___x_5735_ = v___x_5718_;
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_a_5733_);
lean_dec(v___x_5718_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5738_; 
if (v_isShared_5736_ == 0)
{
v___x_5738_ = v___x_5735_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v_a_5733_);
v___x_5738_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
return v___x_5738_;
}
}
}
}
}
else
{
lean_object* v_a_5743_; lean_object* v___x_5745_; uint8_t v_isShared_5746_; uint8_t v_isSharedCheck_5750_; 
lean_dec_ref_known(v___x_5680_, 5);
lean_dec(v_a_5661_);
lean_dec_ref(v_k_5617_);
v_a_5743_ = lean_ctor_get(v___x_5681_, 0);
v_isSharedCheck_5750_ = !lean_is_exclusive(v___x_5681_);
if (v_isSharedCheck_5750_ == 0)
{
v___x_5745_ = v___x_5681_;
v_isShared_5746_ = v_isSharedCheck_5750_;
goto v_resetjp_5744_;
}
else
{
lean_inc(v_a_5743_);
lean_dec(v___x_5681_);
v___x_5745_ = lean_box(0);
v_isShared_5746_ = v_isSharedCheck_5750_;
goto v_resetjp_5744_;
}
v_resetjp_5744_:
{
lean_object* v___x_5748_; 
if (v_isShared_5746_ == 0)
{
v___x_5748_ = v___x_5745_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_a_5743_);
v___x_5748_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
return v___x_5748_;
}
}
}
}
}
else
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5758_; 
lean_dec_ref(v_k_5617_);
v_a_5751_ = lean_ctor_get(v___x_5660_, 0);
v_isSharedCheck_5758_ = !lean_is_exclusive(v___x_5660_);
if (v_isSharedCheck_5758_ == 0)
{
v___x_5753_ = v___x_5660_;
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5660_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5756_; 
if (v_isShared_5754_ == 0)
{
v___x_5756_ = v___x_5753_;
goto v_reusejp_5755_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_a_5751_);
v___x_5756_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5755_;
}
v_reusejp_5755_:
{
return v___x_5756_;
}
}
}
}
v___jp_5759_:
{
uint8_t v___x_5761_; 
v___x_5761_ = 1;
if (v_only_5616_ == 0)
{
v___y_5649_ = v___x_5761_;
v___y_5650_ = v___y_5760_;
v_params_5651_ = v_params_5614_;
v___y_5652_ = v_a_5618_;
v___y_5653_ = v_a_5619_;
v___y_5654_ = v_a_5620_;
v___y_5655_ = v_a_5621_;
v___y_5656_ = v_a_5622_;
v___y_5657_ = v_a_5623_;
v___y_5658_ = v_a_5624_;
v___y_5659_ = v_a_5625_;
goto v___jp_5648_;
}
else
{
lean_object* v_config_5762_; lean_object* v_extensions_5763_; lean_object* v_extra_5764_; lean_object* v_extraInj_5765_; lean_object* v_extraFacts_5766_; lean_object* v_symPrios_5767_; lean_object* v_norm_5768_; lean_object* v_normProcs_5769_; lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5780_; 
v_config_5762_ = lean_ctor_get(v_params_5614_, 0);
v_extensions_5763_ = lean_ctor_get(v_params_5614_, 1);
v_extra_5764_ = lean_ctor_get(v_params_5614_, 2);
v_extraInj_5765_ = lean_ctor_get(v_params_5614_, 3);
v_extraFacts_5766_ = lean_ctor_get(v_params_5614_, 4);
v_symPrios_5767_ = lean_ctor_get(v_params_5614_, 5);
v_norm_5768_ = lean_ctor_get(v_params_5614_, 6);
v_normProcs_5769_ = lean_ctor_get(v_params_5614_, 7);
v_isSharedCheck_5780_ = !lean_is_exclusive(v_params_5614_);
if (v_isSharedCheck_5780_ == 0)
{
lean_object* v_unused_5781_; 
v_unused_5781_ = lean_ctor_get(v_params_5614_, 8);
lean_dec(v_unused_5781_);
v___x_5771_ = v_params_5614_;
v_isShared_5772_ = v_isSharedCheck_5780_;
goto v_resetjp_5770_;
}
else
{
lean_inc(v_normProcs_5769_);
lean_inc(v_norm_5768_);
lean_inc(v_symPrios_5767_);
lean_inc(v_extraFacts_5766_);
lean_inc(v_extraInj_5765_);
lean_inc(v_extra_5764_);
lean_inc(v_extensions_5763_);
lean_inc(v_config_5762_);
lean_dec(v_params_5614_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5780_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
size_t v_sz_5773_; size_t v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v_params_5778_; 
v_sz_5773_ = lean_array_size(v_extensions_5763_);
v___x_5774_ = ((size_t)0ULL);
v___x_5775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5773_, v___x_5774_, v_extensions_5763_);
v___x_5776_ = lean_box(0);
if (v_isShared_5772_ == 0)
{
lean_ctor_set(v___x_5771_, 8, v___x_5776_);
lean_ctor_set(v___x_5771_, 1, v___x_5775_);
v_params_5778_ = v___x_5771_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5779_; 
v_reuseFailAlloc_5779_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5779_, 0, v_config_5762_);
lean_ctor_set(v_reuseFailAlloc_5779_, 1, v___x_5775_);
lean_ctor_set(v_reuseFailAlloc_5779_, 2, v_extra_5764_);
lean_ctor_set(v_reuseFailAlloc_5779_, 3, v_extraInj_5765_);
lean_ctor_set(v_reuseFailAlloc_5779_, 4, v_extraFacts_5766_);
lean_ctor_set(v_reuseFailAlloc_5779_, 5, v_symPrios_5767_);
lean_ctor_set(v_reuseFailAlloc_5779_, 6, v_norm_5768_);
lean_ctor_set(v_reuseFailAlloc_5779_, 7, v_normProcs_5769_);
lean_ctor_set(v_reuseFailAlloc_5779_, 8, v___x_5776_);
v_params_5778_ = v_reuseFailAlloc_5779_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
v___y_5649_ = v___x_5761_;
v___y_5650_ = v___y_5760_;
v_params_5651_ = v_params_5778_;
v___y_5652_ = v_a_5618_;
v___y_5653_ = v_a_5619_;
v___y_5654_ = v_a_5620_;
v___y_5655_ = v_a_5621_;
v___y_5656_ = v_a_5622_;
v___y_5657_ = v_a_5623_;
v___y_5658_ = v_a_5624_;
v___y_5659_ = v_a_5625_;
goto v___jp_5648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_5787_, lean_object* v_ps_5788_, lean_object* v_only_5789_, lean_object* v_k_5790_, lean_object* v_a_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_){
_start:
{
uint8_t v_only_boxed_5800_; lean_object* v_res_5801_; 
v_only_boxed_5800_ = lean_unbox(v_only_5789_);
v_res_5801_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5787_, v_ps_5788_, v_only_boxed_5800_, v_k_5790_, v_a_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_, v_a_5796_, v_a_5797_, v_a_5798_);
lean_dec(v_a_5798_);
lean_dec_ref(v_a_5797_);
lean_dec(v_a_5796_);
lean_dec_ref(v_a_5795_);
lean_dec(v_a_5794_);
lean_dec_ref(v_a_5793_);
lean_dec(v_a_5792_);
lean_dec_ref(v_a_5791_);
lean_dec_ref(v_ps_5788_);
return v_res_5801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_5802_, lean_object* v_params_5803_, lean_object* v_ps_5804_, uint8_t v_only_5805_, lean_object* v_k_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_){
_start:
{
lean_object* v___x_5816_; 
v___x_5816_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5803_, v_ps_5804_, v_only_5805_, v_k_5806_, v_a_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_);
return v___x_5816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_5817_, lean_object* v_params_5818_, lean_object* v_ps_5819_, lean_object* v_only_5820_, lean_object* v_k_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_, lean_object* v_a_5826_, lean_object* v_a_5827_, lean_object* v_a_5828_, lean_object* v_a_5829_, lean_object* v_a_5830_){
_start:
{
uint8_t v_only_boxed_5831_; lean_object* v_res_5832_; 
v_only_boxed_5831_ = lean_unbox(v_only_5820_);
v_res_5832_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_5817_, v_params_5818_, v_ps_5819_, v_only_boxed_5831_, v_k_5821_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_);
lean_dec(v_a_5829_);
lean_dec_ref(v_a_5828_);
lean_dec(v_a_5827_);
lean_dec_ref(v_a_5826_);
lean_dec(v_a_5825_);
lean_dec_ref(v_a_5824_);
lean_dec(v_a_5823_);
lean_dec_ref(v_a_5822_);
lean_dec_ref(v_ps_5819_);
return v_res_5832_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Param(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
