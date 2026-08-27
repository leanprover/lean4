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
v_options_578_ = lean_ctor_get(v___y_570_, 2);
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
uint8_t v_suppressElabErrors_boxed_642_; uint8_t v___y_4434__boxed_643_; uint8_t v_res_644_; lean_object* v_r_645_; 
v_suppressElabErrors_boxed_642_ = lean_unbox(v_suppressElabErrors_639_);
v___y_4434__boxed_643_ = lean_unbox(v___y_640_);
v_res_644_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_642_, v___y_4434__boxed_643_, v_x_641_);
lean_dec(v_x_641_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_647_, lean_object* v_msgData_648_, uint8_t v_severity_649_, uint8_t v_isSilent_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
uint8_t v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; uint8_t v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_693_; uint8_t v___y_694_; lean_object* v___y_695_; uint8_t v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; uint8_t v___y_699_; lean_object* v___y_700_; lean_object* v___y_718_; uint8_t v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; uint8_t v___y_724_; lean_object* v___y_725_; lean_object* v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; uint8_t v___y_734_; uint8_t v___y_735_; uint8_t v___x_740_; lean_object* v___y_742_; uint8_t v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; uint8_t v___y_747_; uint8_t v___y_748_; uint8_t v___y_750_; uint8_t v___x_765_; 
v___x_740_ = 2;
v___x_765_ = l_Lean_instBEqMessageSeverity_beq(v_severity_649_, v___x_740_);
if (v___x_765_ == 0)
{
v___y_750_ = v___x_765_;
goto v___jp_749_;
}
else
{
uint8_t v___x_766_; 
lean_inc_ref(v_msgData_648_);
v___x_766_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_648_);
v___y_750_ = v___x_766_;
goto v___jp_749_;
}
v___jp_656_:
{
lean_object* v___x_666_; lean_object* v_currNamespace_667_; lean_object* v_openDecls_668_; lean_object* v_env_669_; lean_object* v_nextMacroScope_670_; lean_object* v_ngen_671_; lean_object* v_auxDeclNGen_672_; lean_object* v_traceState_673_; lean_object* v_cache_674_; lean_object* v_messages_675_; lean_object* v_infoState_676_; lean_object* v_snapshotTasks_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_691_; 
v___x_666_ = lean_st_ref_take(v___y_665_);
v_currNamespace_667_ = lean_ctor_get(v___y_664_, 6);
v_openDecls_668_ = lean_ctor_get(v___y_664_, 7);
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
lean_ctor_set(v___x_682_, 1, v___y_660_);
lean_inc_ref(v___y_662_);
lean_inc_ref(v___y_659_);
v___x_683_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_683_, 0, v___y_659_);
lean_ctor_set(v___x_683_, 1, v___y_661_);
lean_ctor_set(v___x_683_, 2, v___y_658_);
lean_ctor_set(v___x_683_, 3, v___y_662_);
lean_ctor_set(v___x_683_, 4, v___x_682_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*5, v___y_663_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*5 + 1, v___y_657_);
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
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_716_; 
v___x_701_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_648_);
v___x_702_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_701_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_716_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_716_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_716_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
lean_inc_ref_n(v___y_698_, 2);
v___x_707_ = l_Lean_FileMap_toPosition(v___y_698_, v___y_697_);
lean_dec(v___y_697_);
v___x_708_ = l_Lean_FileMap_toPosition(v___y_698_, v___y_700_);
lean_dec(v___y_700_);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
v___x_710_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_696_ == 0)
{
lean_del_object(v___x_705_);
lean_dec_ref(v___y_693_);
v___y_657_ = v___y_694_;
v___y_658_ = v___x_709_;
v___y_659_ = v___y_695_;
v___y_660_ = v_a_703_;
v___y_661_ = v___x_707_;
v___y_662_ = v___x_710_;
v___y_663_ = v___y_699_;
v___y_664_ = v___y_653_;
v___y_665_ = v___y_654_;
goto v___jp_656_;
}
else
{
uint8_t v___x_711_; 
lean_inc(v_a_703_);
v___x_711_ = l_Lean_MessageData_hasTag(v___y_693_, v_a_703_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_dec_ref_known(v___x_709_, 1);
lean_dec_ref(v___x_707_);
lean_dec(v_a_703_);
v___x_712_ = lean_box(0);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_712_);
v___x_714_ = v___x_705_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
else
{
lean_del_object(v___x_705_);
v___y_657_ = v___y_694_;
v___y_658_ = v___x_709_;
v___y_659_ = v___y_695_;
v___y_660_ = v_a_703_;
v___y_661_ = v___x_707_;
v___y_662_ = v___x_710_;
v___y_663_ = v___y_699_;
v___y_664_ = v___y_653_;
v___y_665_ = v___y_654_;
goto v___jp_656_;
}
}
}
}
v___jp_717_:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Syntax_getTailPos_x3f(v___y_722_, v___y_724_);
lean_dec(v___y_722_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_inc(v___y_725_);
v___y_693_ = v___y_718_;
v___y_694_ = v___y_719_;
v___y_695_ = v___y_720_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_725_;
v___y_698_ = v___y_723_;
v___y_699_ = v___y_724_;
v___y_700_ = v___y_725_;
goto v___jp_692_;
}
else
{
lean_object* v_val_727_; 
v_val_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_val_727_);
lean_dec_ref_known(v___x_726_, 1);
v___y_693_ = v___y_718_;
v___y_694_ = v___y_719_;
v___y_695_ = v___y_720_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_725_;
v___y_698_ = v___y_723_;
v___y_699_ = v___y_724_;
v___y_700_ = v_val_727_;
goto v___jp_692_;
}
}
v___jp_728_:
{
lean_object* v_ref_736_; lean_object* v___x_737_; 
v_ref_736_ = l_Lean_replaceRef(v_ref_647_, v___y_732_);
v___x_737_ = l_Lean_Syntax_getPos_x3f(v_ref_736_, v___y_734_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_738_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___y_718_ = v___y_729_;
v___y_719_ = v___y_735_;
v___y_720_ = v___y_730_;
v___y_721_ = v___y_731_;
v___y_722_ = v_ref_736_;
v___y_723_ = v___y_733_;
v___y_724_ = v___y_734_;
v___y_725_ = v___x_738_;
goto v___jp_717_;
}
else
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v___x_737_, 1);
v___y_718_ = v___y_729_;
v___y_719_ = v___y_735_;
v___y_720_ = v___y_730_;
v___y_721_ = v___y_731_;
v___y_722_ = v_ref_736_;
v___y_723_ = v___y_733_;
v___y_724_ = v___y_734_;
v___y_725_ = v_val_739_;
goto v___jp_717_;
}
}
v___jp_741_:
{
if (v___y_748_ == 0)
{
v___y_729_ = v___y_744_;
v___y_730_ = v___y_742_;
v___y_731_ = v___y_743_;
v___y_732_ = v___y_745_;
v___y_733_ = v___y_746_;
v___y_734_ = v___y_747_;
v___y_735_ = v_severity_649_;
goto v___jp_728_;
}
else
{
v___y_729_ = v___y_744_;
v___y_730_ = v___y_742_;
v___y_731_ = v___y_743_;
v___y_732_ = v___y_745_;
v___y_733_ = v___y_746_;
v___y_734_ = v___y_747_;
v___y_735_ = v___x_740_;
goto v___jp_728_;
}
}
v___jp_749_:
{
if (v___y_750_ == 0)
{
lean_object* v_fileName_751_; lean_object* v_fileMap_752_; lean_object* v_options_753_; lean_object* v_ref_754_; uint8_t v_suppressElabErrors_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___f_758_; uint8_t v___x_759_; uint8_t v___x_760_; 
v_fileName_751_ = lean_ctor_get(v___y_653_, 0);
v_fileMap_752_ = lean_ctor_get(v___y_653_, 1);
v_options_753_ = lean_ctor_get(v___y_653_, 2);
v_ref_754_ = lean_ctor_get(v___y_653_, 5);
v_suppressElabErrors_755_ = lean_ctor_get_uint8(v___y_653_, sizeof(void*)*14 + 1);
v___x_756_ = lean_box(v_suppressElabErrors_755_);
v___x_757_ = lean_box(v___y_750_);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_758_, 0, v___x_756_);
lean_closure_set(v___f_758_, 1, v___x_757_);
v___x_759_ = 1;
v___x_760_ = l_Lean_instBEqMessageSeverity_beq(v_severity_649_, v___x_759_);
if (v___x_760_ == 0)
{
v___y_742_ = v_fileName_751_;
v___y_743_ = v_suppressElabErrors_755_;
v___y_744_ = v___f_758_;
v___y_745_ = v_ref_754_;
v___y_746_ = v_fileMap_752_;
v___y_747_ = v___y_750_;
v___y_748_ = v___x_760_;
goto v___jp_741_;
}
else
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = l_Lean_warningAsError;
v___x_762_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_753_, v___x_761_);
v___y_742_ = v_fileName_751_;
v___y_743_ = v_suppressElabErrors_755_;
v___y_744_ = v___f_758_;
v___y_745_ = v_ref_754_;
v___y_746_ = v_fileMap_752_;
v___y_747_ = v___y_750_;
v___y_748_ = v___x_762_;
goto v___jp_741_;
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v_msgData_648_);
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_767_, lean_object* v_msgData_768_, lean_object* v_severity_769_, lean_object* v_isSilent_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
uint8_t v_severity_boxed_776_; uint8_t v_isSilent_boxed_777_; lean_object* v_res_778_; 
v_severity_boxed_776_ = lean_unbox(v_severity_769_);
v_isSilent_boxed_777_ = lean_unbox(v_isSilent_770_);
v_res_778_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_767_, v_msgData_768_, v_severity_boxed_776_, v_isSilent_boxed_777_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v_ref_767_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_779_, uint8_t v_severity_780_, uint8_t v_isSilent_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_ref_787_; lean_object* v___x_788_; 
v_ref_787_ = lean_ctor_get(v___y_784_, 5);
v___x_788_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_787_, v_msgData_779_, v_severity_780_, v_isSilent_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_789_, lean_object* v_severity_790_, lean_object* v_isSilent_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
uint8_t v_severity_boxed_797_; uint8_t v_isSilent_boxed_798_; lean_object* v_res_799_; 
v_severity_boxed_797_ = lean_unbox(v_severity_790_);
v_isSilent_boxed_798_ = lean_unbox(v_isSilent_791_);
v_res_799_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_789_, v_severity_boxed_797_, v_isSilent_boxed_798_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
uint8_t v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; 
v___x_806_ = 1;
v___x_807_ = 0;
v___x_808_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_800_, v___x_806_, v___x_807_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
return v_res_815_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_818_ = l_Lean_stringToMessageData(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
if (lean_obj_tag(v_a_819_) == 0)
{
lean_object* v___x_821_; 
v___x_821_ = l_List_reverse___redArg(v_a_820_);
return v___x_821_;
}
else
{
lean_object* v_head_822_; lean_object* v_tail_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_836_; 
v_head_822_ = lean_ctor_get(v_a_819_, 0);
v_tail_823_ = lean_ctor_get(v_a_819_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_a_819_);
if (v_isSharedCheck_836_ == 0)
{
v___x_825_ = v_a_819_;
v_isShared_826_ = v_isSharedCheck_836_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_tail_823_);
lean_inc(v_head_822_);
lean_dec(v_a_819_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_836_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint8_t v_minIndexable_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v_minIndexable_827_ = 0;
v___x_828_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_829_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_822_, v_minIndexable_827_);
lean_dec(v_head_822_);
v___x_830_ = l_Lean_stringToMessageData(v___x_829_);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_828_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v_a_820_);
lean_ctor_set(v___x_825_, 0, v___x_831_);
v___x_833_ = v___x_825_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_a_820_);
v___x_833_ = v_reuseFailAlloc_835_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
v_a_819_ = v_tail_823_;
v_a_820_ = v___x_833_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
if (lean_obj_tag(v_a_837_) == 0)
{
lean_object* v___x_839_; 
v___x_839_ = l_List_reverse___redArg(v_a_838_);
return v___x_839_;
}
else
{
lean_object* v_head_840_; lean_object* v_tail_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_849_; 
v_head_840_ = lean_ctor_get(v_a_837_, 0);
v_tail_841_ = lean_ctor_get(v_a_837_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_a_837_);
if (v_isSharedCheck_849_ == 0)
{
v___x_843_ = v_a_837_;
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_tail_841_);
lean_inc(v_head_840_);
lean_dec(v_a_837_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v_a_838_);
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_head_840_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_a_838_);
v___x_846_ = v_reuseFailAlloc_848_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
v_a_837_ = v_tail_841_;
v_a_838_ = v___x_846_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_858_ = l_Lean_stringToMessageData(v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_859_, lean_object* v_declName_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_kinds_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v_ks_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_inc(v_declName_860_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v_declName_860_);
v___x_892_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_859_, v___x_891_);
lean_dec_ref_known(v___x_891_, 1);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec(v_declName_860_);
v___x_893_ = lean_box(0);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; uint8_t v_minIndexable_897_; uint8_t v_gen_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; 
v_head_895_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_head_895_);
v_tail_896_ = lean_ctor_get(v___x_892_, 1);
lean_inc(v_tail_896_);
v_minIndexable_897_ = 0;
if (lean_obj_tag(v_tail_896_) == 0)
{
lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_918_; 
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; lean_object* v_unused_920_; 
v_unused_919_ = lean_ctor_get(v___x_892_, 1);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v___x_892_, 0);
lean_dec(v_unused_920_);
v___x_910_ = v___x_892_;
v_isShared_911_ = v_isSharedCheck_918_;
goto v_resetjp_909_;
}
else
{
lean_dec(v___x_892_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_918_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_912_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_913_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_895_, v_minIndexable_897_);
lean_dec(v_head_895_);
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
if (v_isShared_911_ == 0)
{
lean_ctor_set_tag(v___x_910_, 7);
lean_ctor_set(v___x_910_, 1, v___x_914_);
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
v_kinds_867_ = v___x_916_;
v___y_868_ = v_a_861_;
v___y_869_ = v_a_862_;
v___y_870_ = v_a_863_;
v___y_871_ = v_a_864_;
goto v___jp_866_;
}
}
}
else
{
lean_object* v_head_921_; 
v_head_921_ = lean_ctor_get(v_tail_896_, 0);
switch(lean_obj_tag(v_head_921_))
{
case 1:
{
lean_object* v_tail_922_; 
v_tail_922_ = lean_ctor_get(v_tail_896_, 1);
lean_inc(v_tail_922_);
lean_dec_ref_known(v_tail_896_, 2);
if (lean_obj_tag(v_tail_922_) == 0)
{
if (lean_obj_tag(v_head_895_) == 0)
{
uint8_t v_gen_923_; 
lean_dec_ref_known(v___x_892_, 2);
v_gen_923_ = lean_ctor_get_uint8(v_head_895_, 0);
lean_dec_ref_known(v_head_895_, 0);
v_gen_899_ = v_gen_923_;
v___y_900_ = v_a_861_;
v___y_901_ = v_a_862_;
v___y_902_ = v_a_863_;
v___y_903_ = v_a_864_;
goto v___jp_898_;
}
else
{
lean_dec(v_head_895_);
v_ks_882_ = v___x_892_;
v___y_883_ = v_a_861_;
v___y_884_ = v_a_862_;
v___y_885_ = v_a_863_;
v___y_886_ = v_a_864_;
goto v___jp_881_;
}
}
else
{
lean_dec(v_tail_922_);
lean_dec(v_head_895_);
v_ks_882_ = v___x_892_;
v___y_883_ = v_a_861_;
v___y_884_ = v_a_862_;
v___y_885_ = v_a_863_;
v___y_886_ = v_a_864_;
goto v___jp_881_;
}
}
case 0:
{
lean_object* v_tail_924_; 
v_tail_924_ = lean_ctor_get(v_tail_896_, 1);
lean_inc(v_tail_924_);
lean_dec_ref_known(v_tail_896_, 2);
if (lean_obj_tag(v_tail_924_) == 0)
{
if (lean_obj_tag(v_head_895_) == 1)
{
uint8_t v_gen_925_; 
lean_dec_ref_known(v___x_892_, 2);
v_gen_925_ = lean_ctor_get_uint8(v_head_895_, 0);
lean_dec_ref_known(v_head_895_, 0);
v_gen_899_ = v_gen_925_;
v___y_900_ = v_a_861_;
v___y_901_ = v_a_862_;
v___y_902_ = v_a_863_;
v___y_903_ = v_a_864_;
goto v___jp_898_;
}
else
{
lean_dec(v_head_895_);
v_ks_882_ = v___x_892_;
v___y_883_ = v_a_861_;
v___y_884_ = v_a_862_;
v___y_885_ = v_a_863_;
v___y_886_ = v_a_864_;
goto v___jp_881_;
}
}
else
{
lean_dec(v_tail_924_);
lean_dec(v_head_895_);
v_ks_882_ = v___x_892_;
v___y_883_ = v_a_861_;
v___y_884_ = v_a_862_;
v___y_885_ = v_a_863_;
v___y_886_ = v_a_864_;
goto v___jp_881_;
}
}
default: 
{
lean_dec_ref_known(v_tail_896_, 2);
lean_dec(v_head_895_);
v_ks_882_ = v___x_892_;
v___y_883_ = v_a_861_;
v___y_884_ = v_a_862_;
v___y_885_ = v_a_863_;
v___y_886_ = v_a_864_;
goto v___jp_881_;
}
}
}
v___jp_898_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_904_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_905_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_905_, 0, v_gen_899_);
v___x_906_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_905_, v_minIndexable_897_);
lean_dec_ref_known(v___x_905_, 0);
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_904_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v_kinds_867_ = v___x_908_;
v___y_868_ = v___y_900_;
v___y_869_ = v___y_901_;
v___y_870_ = v___y_902_;
v___y_871_ = v___y_903_;
goto v___jp_866_;
}
}
v___jp_866_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_872_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_873_ = l_Lean_MessageData_ofName(v_declName_860_);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v_kinds_867_);
v___x_878_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_879_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_880_;
}
v___jp_881_:
{
lean_object* v___x_887_; lean_object* v_ks_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = lean_box(0);
v_ks_888_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_882_, v___x_887_);
v___x_889_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_888_, v___x_887_);
v___x_890_ = l_Lean_MessageData_ofList(v___x_889_);
v_kinds_867_ = v___x_890_;
v___y_868_ = v___y_883_;
v___y_869_ = v___y_884_;
v___y_870_ = v___y_885_;
v___y_871_ = v___y_886_;
goto v___jp_866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_926_, lean_object* v_declName_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_926_, v_declName_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v_s_926_);
return v_res_933_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_934_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
lean_ctor_set(v___x_939_, 2, v___x_938_);
lean_ctor_set(v___x_939_, 3, v___x_938_);
lean_ctor_set(v___x_939_, 4, v___x_937_);
lean_ctor_set(v___x_939_, 5, v___x_937_);
lean_ctor_set(v___x_939_, 6, v___x_937_);
lean_ctor_set(v___x_939_, 7, v___x_937_);
lean_ctor_set(v___x_939_, 8, v___x_937_);
lean_ctor_set(v___x_939_, 9, v___x_937_);
lean_ctor_set(v___x_939_, 10, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_unsigned_to_nat(32u);
v___x_941_ = lean_mk_empty_array_with_capacity(v___x_940_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_943_ = ((size_t)5ULL);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_unsigned_to_nat(32u);
v___x_946_ = lean_mk_empty_array_with_capacity(v___x_945_);
v___x_947_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_948_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v___x_946_);
lean_ctor_set(v___x_948_, 2, v___x_944_);
lean_ctor_set(v___x_948_, 3, v___x_944_);
lean_ctor_set_usize(v___x_948_, 4, v___x_943_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_949_ = lean_box(1);
v___x_950_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_951_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v___x_950_);
lean_ctor_set(v___x_952_, 2, v___x_949_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_env_958_; lean_object* v_options_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_957_ = lean_st_ref_get(v___y_955_);
v_env_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_ref(v_env_958_);
lean_dec(v___x_957_);
v_options_959_ = lean_ctor_get(v___y_954_, 2);
v___x_960_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_961_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_959_);
v___x_962_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_962_, 0, v_env_958_);
lean_ctor_set(v___x_962_, 1, v___x_960_);
lean_ctor_set(v___x_962_, 2, v___x_961_);
lean_ctor_set(v___x_962_, 3, v_options_959_);
v___x_963_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v_msgData_953_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* v_msgData_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* v_msg_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_ref_974_; lean_object* v___x_975_; lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_984_; 
v_ref_974_ = lean_ctor_get(v___y_971_, 5);
v___x_975_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msg_970_, v___y_971_, v___y_972_);
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_984_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
lean_inc(v_ref_974_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v_ref_974_);
lean_ctor_set(v___x_980_, 1, v_a_976_);
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 1);
lean_ctor_set(v___x_978_, 0, v___x_980_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* v_msg_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
return v_res_989_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* v_s_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v_env_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1007_ = lean_st_ref_get(v_a_1005_);
v_env_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc_ref(v_env_1008_);
lean_dec(v___x_1007_);
v___x_1009_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
v___x_1010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(v_s_1003_);
v___x_1011_ = l_Lean_Parser_runParserCategory(v_env_1008_, v___x_1009_, v_s_1003_, v___x_1010_);
if (lean_obj_tag(v___x_1011_) == 1)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; 
lean_dec_ref(v_s_1003_);
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = l_Lean_Meta_Grind_getAttrKindCore(v_a_1012_, v_a_1004_, v_a_1005_);
return v___x_1013_;
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v___x_1011_);
v___x_1014_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
v___x_1015_ = l_Lean_stringToMessageData(v_s_1003_);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1016_, v_a_1004_, v_a_1005_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* v_s_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_1018_, v_a_1019_, v_a_1020_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* v_00_u03b1_1023_, lean_object* v_msg_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_1024_, v___y_1025_, v___y_1026_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(v_00_u03b1_1029_, v_msg_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* v_msg_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_ref_1041_; lean_object* v___x_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1051_; 
v_ref_1041_ = lean_ctor_get(v___y_1038_, 5);
v___x_1042_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
lean_inc(v_ref_1041_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_ref_1041_);
lean_ctor_set(v___x_1047_, 1, v_a_1043_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 1);
lean_ctor_set(v___x_1045_, 0, v___x_1047_);
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* v_msg_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1058_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t v_minIndexable_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
if (v_minIndexable_1062_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
v___x_1071_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1070_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* v_minIndexable_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
uint8_t v_minIndexable_boxed_1078_; lean_object* v_res_1079_; 
v_minIndexable_boxed_1078_ = lean_unbox(v_minIndexable_1072_);
v_res_1079_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_boxed_1078_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* v_00_u03b1_1080_, lean_object* v_msg_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* v_00_u03b1_1088_, lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(v_00_u03b1_1088_, v_msg_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1117_, lean_object* v_declHint_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; lean_object* v_env_1122_; uint8_t v___x_1123_; 
v___x_1121_ = lean_st_ref_get(v___y_1119_);
v_env_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_env_1122_);
lean_dec(v___x_1121_);
v___x_1123_ = l_Lean_Name_isAnonymous(v_declHint_1118_);
if (v___x_1123_ == 0)
{
uint8_t v_isExporting_1124_; 
v_isExporting_1124_ = lean_ctor_get_uint8(v_env_1122_, sizeof(void*)*8);
if (v_isExporting_1124_ == 0)
{
lean_object* v___x_1125_; 
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1118_);
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_msg_1117_);
return v___x_1125_;
}
else
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
lean_inc_ref(v_env_1122_);
v___x_1126_ = l_Lean_Environment_setExporting(v_env_1122_, v___x_1123_);
lean_inc(v_declHint_1118_);
lean_inc_ref(v___x_1126_);
v___x_1127_ = l_Lean_Environment_contains(v___x_1126_, v_declHint_1118_, v_isExporting_1124_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v___x_1126_);
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1118_);
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v_msg_1117_);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_c_1134_; lean_object* v___x_1135_; 
v___x_1129_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1130_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1131_ = l_Lean_Options_empty;
v___x_1132_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1126_);
lean_ctor_set(v___x_1132_, 1, v___x_1129_);
lean_ctor_set(v___x_1132_, 2, v___x_1130_);
lean_ctor_set(v___x_1132_, 3, v___x_1131_);
lean_inc(v_declHint_1118_);
v___x_1133_ = l_Lean_MessageData_ofConstName(v_declHint_1118_, v___x_1123_);
v_c_1134_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1134_, 0, v___x_1132_);
lean_ctor_set(v_c_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1122_, v_declHint_1118_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1118_);
v___x_1136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_c_1134_);
v___x_1138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_MessageData_note(v___x_1139_);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v_msg_1117_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
else
{
lean_object* v_val_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1178_; 
v_val_1143_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1145_ = v___x_1135_;
v_isShared_1146_ = v_isSharedCheck_1178_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_val_1143_);
lean_dec(v___x_1135_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1178_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_mod_1150_; uint8_t v___x_1151_; 
v___x_1147_ = lean_box(0);
v___x_1148_ = l_Lean_Environment_header(v_env_1122_);
lean_dec_ref(v_env_1122_);
v___x_1149_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1148_);
v_mod_1150_ = lean_array_get(v___x_1147_, v___x_1149_, v_val_1143_);
lean_dec(v_val_1143_);
lean_dec_ref(v___x_1149_);
v___x_1151_ = l_Lean_isPrivateName(v_declHint_1118_);
lean_dec(v_declHint_1118_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_c_1134_);
v___x_1154_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_MessageData_ofName(v_mod_1150_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_note(v___x_1159_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_msg_1117_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1161_);
v___x_1163_ = v___x_1145_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1165_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v_c_1134_);
v___x_1167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = l_Lean_MessageData_ofName(v_mod_1150_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_MessageData_note(v___x_1172_);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_msg_1117_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1174_);
v___x_1176_ = v___x_1145_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1179_; 
lean_dec_ref(v_env_1122_);
lean_dec(v_declHint_1118_);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_msg_1117_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1180_, lean_object* v_declHint_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1180_, v_declHint_1181_, v___y_1182_);
lean_dec(v___y_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1185_, lean_object* v_declHint_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1202_; 
v___x_1192_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1185_, v_declHint_1186_, v___y_1190_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = l_Lean_unknownIdentifierMessageTag;
v___x_1198_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v_a_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1203_, lean_object* v_declHint_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1203_, v_declHint_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_fileName_1218_; lean_object* v_fileMap_1219_; lean_object* v_options_1220_; lean_object* v_currRecDepth_1221_; lean_object* v_maxRecDepth_1222_; lean_object* v_ref_1223_; lean_object* v_currNamespace_1224_; lean_object* v_openDecls_1225_; lean_object* v_initHeartbeats_1226_; lean_object* v_maxHeartbeats_1227_; lean_object* v_quotContext_1228_; lean_object* v_currMacroScope_1229_; uint8_t v_diag_1230_; lean_object* v_cancelTk_x3f_1231_; uint8_t v_suppressElabErrors_1232_; lean_object* v_inheritedTraceOptions_1233_; lean_object* v_ref_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_fileName_1218_ = lean_ctor_get(v___y_1215_, 0);
v_fileMap_1219_ = lean_ctor_get(v___y_1215_, 1);
v_options_1220_ = lean_ctor_get(v___y_1215_, 2);
v_currRecDepth_1221_ = lean_ctor_get(v___y_1215_, 3);
v_maxRecDepth_1222_ = lean_ctor_get(v___y_1215_, 4);
v_ref_1223_ = lean_ctor_get(v___y_1215_, 5);
v_currNamespace_1224_ = lean_ctor_get(v___y_1215_, 6);
v_openDecls_1225_ = lean_ctor_get(v___y_1215_, 7);
v_initHeartbeats_1226_ = lean_ctor_get(v___y_1215_, 8);
v_maxHeartbeats_1227_ = lean_ctor_get(v___y_1215_, 9);
v_quotContext_1228_ = lean_ctor_get(v___y_1215_, 10);
v_currMacroScope_1229_ = lean_ctor_get(v___y_1215_, 11);
v_diag_1230_ = lean_ctor_get_uint8(v___y_1215_, sizeof(void*)*14);
v_cancelTk_x3f_1231_ = lean_ctor_get(v___y_1215_, 12);
v_suppressElabErrors_1232_ = lean_ctor_get_uint8(v___y_1215_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1233_ = lean_ctor_get(v___y_1215_, 13);
v_ref_1234_ = l_Lean_replaceRef(v_ref_1211_, v_ref_1223_);
lean_inc_ref(v_inheritedTraceOptions_1233_);
lean_inc(v_cancelTk_x3f_1231_);
lean_inc(v_currMacroScope_1229_);
lean_inc(v_quotContext_1228_);
lean_inc(v_maxHeartbeats_1227_);
lean_inc(v_initHeartbeats_1226_);
lean_inc(v_openDecls_1225_);
lean_inc(v_currNamespace_1224_);
lean_inc(v_maxRecDepth_1222_);
lean_inc(v_currRecDepth_1221_);
lean_inc_ref(v_options_1220_);
lean_inc_ref(v_fileMap_1219_);
lean_inc_ref(v_fileName_1218_);
v___x_1235_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1235_, 0, v_fileName_1218_);
lean_ctor_set(v___x_1235_, 1, v_fileMap_1219_);
lean_ctor_set(v___x_1235_, 2, v_options_1220_);
lean_ctor_set(v___x_1235_, 3, v_currRecDepth_1221_);
lean_ctor_set(v___x_1235_, 4, v_maxRecDepth_1222_);
lean_ctor_set(v___x_1235_, 5, v_ref_1234_);
lean_ctor_set(v___x_1235_, 6, v_currNamespace_1224_);
lean_ctor_set(v___x_1235_, 7, v_openDecls_1225_);
lean_ctor_set(v___x_1235_, 8, v_initHeartbeats_1226_);
lean_ctor_set(v___x_1235_, 9, v_maxHeartbeats_1227_);
lean_ctor_set(v___x_1235_, 10, v_quotContext_1228_);
lean_ctor_set(v___x_1235_, 11, v_currMacroScope_1229_);
lean_ctor_set(v___x_1235_, 12, v_cancelTk_x3f_1231_);
lean_ctor_set(v___x_1235_, 13, v_inheritedTraceOptions_1233_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*14, v_diag_1230_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*14 + 1, v_suppressElabErrors_1232_);
v___x_1236_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1212_, v___y_1213_, v___y_1214_, v___x_1235_, v___y_1216_);
lean_dec_ref_known(v___x_1235_, 14);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1237_, lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1237_, v_msg_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
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
lean_dec_ref(v___y_1261_);
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
lean_dec_ref(v___y_1286_);
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
v___x_1297_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1296_, v_constName_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
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
lean_dec_ref(v___y_1328_);
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
v___x_1338_ = l_Lean_getReducibilityStatusCore(v_env_1337_, v_declName_1333_);
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
lean_inc(v_declName_1392_);
v___x_1655_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1392_, v___x_1458_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; uint8_t v_kind_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
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
lean_dec_ref_known(v___x_1658_, 1);
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
return v___x_1688_;
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
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
v___x_1432_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1428_, v_origin_1430_, v_patterns_1429_, v_cnstrs_1431_);
if (v___x_1432_ == 0)
{
lean_dec(v_declName_1392_);
v___y_1403_ = v_thm_1423_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1428_, v_declName_1392_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_dec_ref_known(v___x_1433_, 1);
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
v___x_1454_ = l_Lean_PersistentArray_push___redArg(v___y_1446_, v___y_1450_);
v___x_1455_ = l_Lean_PersistentArray_push___redArg(v___x_1454_, v___y_1449_);
v___x_1456_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1456_, 0, v___y_1451_);
lean_ctor_set(v___x_1456_, 1, v___y_1444_);
lean_ctor_set(v___x_1456_, 2, v___x_1455_);
lean_ctor_set(v___x_1456_, 3, v___y_1443_);
lean_ctor_set(v___x_1456_, 4, v___y_1445_);
lean_ctor_set(v___x_1456_, 5, v___y_1448_);
lean_ctor_set(v___x_1456_, 6, v___y_1453_);
lean_ctor_set(v___x_1456_, 7, v___y_1452_);
lean_ctor_set(v___x_1456_, 8, v___y_1447_);
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
lean_dec_ref_known(v___x_1464_, 1);
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
lean_dec(v_declName_1392_);
v_val_1470_ = lean_ctor_get(v_a_1466_, 0);
lean_inc(v_val_1470_);
lean_dec_ref_known(v_a_1466_, 1);
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
v___x_1483_ = l_Lean_Array_toPArray_x27___redArg(v_val_1470_);
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
return v___x_1497_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
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
lean_inc_ref(v_symPrios_1541_);
lean_inc(v_declName_1392_);
v___x_1542_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1392_, v_kind_1393_, v_symPrios_1541_, v___x_1458_, v_minIndexable_1394_, v___y_1538_, v___y_1537_, v___y_1540_, v___y_1539_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v_thm_1423_ = v_a_1543_;
v___y_1424_ = v___y_1538_;
v___y_1425_ = v___y_1537_;
v___y_1426_ = v___y_1540_;
v___y_1427_ = v___y_1539_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
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
v___y_1537_ = v___y_1554_;
v___y_1538_ = v___y_1553_;
v___y_1539_ = v___y_1556_;
v___y_1540_ = v___y_1555_;
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
lean_inc_ref(v_symPrios_1560_);
lean_inc(v_declName_1392_);
v___x_1561_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1391_, v_declName_1392_, v_symPrios_1560_, v_minIndexable_1394_, v_suggest_1395_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
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
v___y_1537_ = v___y_1554_;
v___y_1538_ = v___y_1553_;
v___y_1539_ = v___y_1556_;
v___y_1540_ = v___y_1555_;
goto v___jp_1536_;
}
}
}
v___jp_1571_:
{
lean_object* v___x_1576_; 
v___x_1576_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1394_, v___y_1573_, v___y_1575_, v___y_1574_, v___y_1572_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_dec_ref_known(v___x_1576_, 1);
v___y_1553_ = v___y_1573_;
v___y_1554_ = v___y_1575_;
v___y_1555_ = v___y_1574_;
v___y_1556_ = v___y_1572_;
goto v___jp_1552_;
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
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
lean_dec_ref_known(v___x_1594_, 1);
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
lean_inc_ref(v_symPrios_1600_);
lean_inc(v_declName_1392_);
v___x_1606_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1392_, v___x_1605_, v_symPrios_1600_, v___x_1458_, v___x_1458_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1608_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1608_, 0, v_gen_1590_);
lean_inc_ref(v_symPrios_1600_);
lean_inc(v_declName_1392_);
v___x_1609_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1392_, v___x_1608_, v_symPrios_1600_, v___x_1458_, v___x_1458_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1609_) == 0)
{
if (v_warn_1396_ == 0)
{
lean_object* v_a_1610_; 
lean_dec(v_declName_1392_);
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___y_1443_ = v_extraInj_1598_;
v___y_1444_ = v_extensions_1596_;
v___y_1445_ = v_extraFacts_1599_;
v___y_1446_ = v_extra_1597_;
v___y_1447_ = v_anchorRefs_x3f_1603_;
v___y_1448_ = v_symPrios_1600_;
v___y_1449_ = v_a_1610_;
v___y_1450_ = v_a_1607_;
v___y_1451_ = v_config_1595_;
v___y_1452_ = v_normProcs_1602_;
v___y_1453_ = v_norm_1601_;
goto v___jp_1442_;
}
else
{
lean_object* v_a_1611_; lean_object* v_patterns_1612_; lean_object* v_origin_1613_; lean_object* v_cnstrs_1614_; uint8_t v___x_1615_; 
v_a_1611_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1609_, 1);
v_patterns_1612_ = lean_ctor_get(v_a_1607_, 3);
v_origin_1613_ = lean_ctor_get(v_a_1607_, 5);
v_cnstrs_1614_ = lean_ctor_get(v_a_1607_, 7);
v___x_1615_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1596_, v_origin_1613_, v_patterns_1612_, v_cnstrs_1614_);
if (v___x_1615_ == 0)
{
lean_dec(v_declName_1392_);
v___y_1443_ = v_extraInj_1598_;
v___y_1444_ = v_extensions_1596_;
v___y_1445_ = v_extraFacts_1599_;
v___y_1446_ = v_extra_1597_;
v___y_1447_ = v_anchorRefs_x3f_1603_;
v___y_1448_ = v_symPrios_1600_;
v___y_1449_ = v_a_1611_;
v___y_1450_ = v_a_1607_;
v___y_1451_ = v_config_1595_;
v___y_1452_ = v_normProcs_1602_;
v___y_1453_ = v_norm_1601_;
goto v___jp_1442_;
}
else
{
lean_object* v_patterns_1616_; lean_object* v_origin_1617_; lean_object* v_cnstrs_1618_; uint8_t v___x_1619_; 
v_patterns_1616_ = lean_ctor_get(v_a_1611_, 3);
v_origin_1617_ = lean_ctor_get(v_a_1611_, 5);
v_cnstrs_1618_ = lean_ctor_get(v_a_1611_, 7);
v___x_1619_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1596_, v_origin_1617_, v_patterns_1616_, v_cnstrs_1618_);
if (v___x_1619_ == 0)
{
lean_dec(v_declName_1392_);
v___y_1443_ = v_extraInj_1598_;
v___y_1444_ = v_extensions_1596_;
v___y_1445_ = v_extraFacts_1599_;
v___y_1446_ = v_extra_1597_;
v___y_1447_ = v_anchorRefs_x3f_1603_;
v___y_1448_ = v_symPrios_1600_;
v___y_1449_ = v_a_1611_;
v___y_1450_ = v_a_1607_;
v___y_1451_ = v_config_1595_;
v___y_1452_ = v_normProcs_1602_;
v___y_1453_ = v_norm_1601_;
goto v___jp_1442_;
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1596_, v_declName_1392_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref_known(v___x_1620_, 1);
v___y_1443_ = v_extraInj_1598_;
v___y_1444_ = v_extensions_1596_;
v___y_1445_ = v_extraFacts_1599_;
v___y_1446_ = v_extra_1597_;
v___y_1447_ = v_anchorRefs_x3f_1603_;
v___y_1448_ = v_symPrios_1600_;
v___y_1449_ = v_a_1611_;
v___y_1450_ = v_a_1607_;
v___y_1451_ = v_config_1595_;
v___y_1452_ = v_normProcs_1602_;
v___y_1453_ = v_norm_1601_;
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
v___y_1572_ = v___y_1589_;
v___y_1573_ = v___y_1586_;
v___y_1574_ = v___y_1588_;
v___y_1575_ = v___y_1587_;
goto v___jp_1571_;
}
case 1:
{
v___y_1572_ = v___y_1589_;
v___y_1573_ = v___y_1586_;
v___y_1574_ = v___y_1588_;
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
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
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
lean_dec_ref(v___y_1739_);
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
lean_dec_ref(v___y_1757_);
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
lean_dec_ref(v___y_1777_);
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
lean_dec_ref(v___y_1811_);
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
lean_dec_ref_known(v_anchorRefs_x3f_1830_, 1);
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
v_revert_1875_ = lean_ctor_get_uint8(v_config_1874_, sizeof(void*)*14 + 30);
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
v___x_1905_ = lean_st_ref_put(v___y_1886_, v___x_1904_);
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
v___x_1967_ = l_Lean_Elab_Term_elabTerm(v_term_1935_, v___x_1936_, v___x_1937_, v___x_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___x_1966_, v___y_1943_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = 1;
v___x_1970_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1969_, v___x_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___x_1966_, v___y_1943_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref_known(v___x_1970_, 1);
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
lean_dec_ref(v___x_1966_);
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
uint8_t v___x_12619__boxed_2040_; lean_object* v_res_2041_; 
v___x_12619__boxed_2040_ = lean_unbox(v___x_2032_);
v_res_2041_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v_p_2029_, v_term_2030_, v___x_2031_, v___x_12619__boxed_2040_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
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
v_val_2071_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v_a_2067_, 1);
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
return v___x_2076_;
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
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
uint8_t v___x_12793__boxed_2099_; uint8_t v_minIndexable_boxed_2100_; lean_object* v_res_2101_; 
v___x_12793__boxed_2099_ = lean_unbox(v___x_2090_);
v_minIndexable_boxed_2100_ = lean_unbox(v_minIndexable_2091_);
v_res_2101_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_params_2086_, v_p_2087_, v_fst_2088_, v_snd_2089_, v___x_12793__boxed_2099_, v_minIndexable_boxed_2100_, v_kind_2092_, v_idx_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
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
v___x_2184_ = l_Lean_Elab_getBetterRef(v_ref_2180_, v_macroStack_2183_);
lean_inc(v_macroStack_2183_);
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
lean_dec_ref(v___y_2196_);
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
lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2293_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v_kind_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v_fileName_2528_; lean_object* v_fileMap_2529_; lean_object* v_options_2530_; lean_object* v_currRecDepth_2531_; lean_object* v_maxRecDepth_2532_; lean_object* v_ref_2533_; lean_object* v_currNamespace_2534_; lean_object* v_openDecls_2535_; lean_object* v_initHeartbeats_2536_; lean_object* v_maxHeartbeats_2537_; lean_object* v_quotContext_2538_; lean_object* v_currMacroScope_2539_; uint8_t v_diag_2540_; lean_object* v_cancelTk_x3f_2541_; uint8_t v_suppressElabErrors_2542_; lean_object* v_inheritedTraceOptions_2543_; lean_object* v_ref_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
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
v_ref_2544_ = l_Lean_replaceRef(v_p_2219_, v_ref_2533_);
lean_inc_ref(v_inheritedTraceOptions_2543_);
lean_inc(v_cancelTk_x3f_2541_);
lean_inc(v_currMacroScope_2539_);
lean_inc(v_quotContext_2538_);
lean_inc(v_maxHeartbeats_2537_);
lean_inc(v_initHeartbeats_2536_);
lean_inc(v_openDecls_2535_);
lean_inc(v_currNamespace_2534_);
lean_inc(v_maxRecDepth_2532_);
lean_inc(v_currRecDepth_2531_);
lean_inc_ref(v_options_2530_);
lean_inc_ref(v_fileMap_2529_);
lean_inc_ref(v_fileName_2528_);
v___x_2545_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2545_, 0, v_fileName_2528_);
lean_ctor_set(v___x_2545_, 1, v_fileMap_2529_);
lean_ctor_set(v___x_2545_, 2, v_options_2530_);
lean_ctor_set(v___x_2545_, 3, v_currRecDepth_2531_);
lean_ctor_set(v___x_2545_, 4, v_maxRecDepth_2532_);
lean_ctor_set(v___x_2545_, 5, v_ref_2544_);
lean_ctor_set(v___x_2545_, 6, v_currNamespace_2534_);
lean_ctor_set(v___x_2545_, 7, v_openDecls_2535_);
lean_ctor_set(v___x_2545_, 8, v_initHeartbeats_2536_);
lean_ctor_set(v___x_2545_, 9, v_maxHeartbeats_2537_);
lean_ctor_set(v___x_2545_, 10, v_quotContext_2538_);
lean_ctor_set(v___x_2545_, 11, v_currMacroScope_2539_);
lean_ctor_set(v___x_2545_, 12, v_cancelTk_x3f_2541_);
lean_ctor_set(v___x_2545_, 13, v_inheritedTraceOptions_2543_);
lean_ctor_set_uint8(v___x_2545_, sizeof(void*)*14, v_diag_2540_);
lean_ctor_set_uint8(v___x_2545_, sizeof(void*)*14 + 1, v_suppressElabErrors_2542_);
v___x_2546_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2218_, v___x_2545_, v_a_2228_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_dec_ref_known(v___x_2546_, 1);
if (lean_obj_tag(v_mod_x3f_2220_) == 1)
{
lean_object* v_val_2547_; lean_object* v___x_2548_; 
v_val_2547_ = lean_ctor_get(v_mod_x3f_2220_, 0);
lean_inc(v_val_2547_);
v___x_2548_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2547_, v___x_2545_, v_a_2228_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
switch(lean_obj_tag(v_a_2549_))
{
case 0:
{
lean_object* v_k_2567_; 
v_k_2567_ = lean_ctor_get(v_a_2549_, 0);
lean_inc(v_k_2567_);
lean_dec_ref_known(v_a_2549_, 1);
if (lean_obj_tag(v_k_2567_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2220_, 1);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v___y_2551_ = v_a_2223_;
v___y_2552_ = v_a_2224_;
v___y_2553_ = v_a_2225_;
v___y_2554_ = v_a_2226_;
v___y_2555_ = v___x_2545_;
v___y_2556_ = v_a_2228_;
goto v___jp_2550_;
}
else
{
v_kind_2455_ = v_k_2567_;
v___y_2456_ = v_a_2223_;
v___y_2457_ = v_a_2224_;
v___y_2458_ = v_a_2225_;
v___y_2459_ = v_a_2226_;
v___y_2460_ = v___x_2545_;
v___y_2461_ = v_a_2228_;
goto v___jp_2454_;
}
}
case 1:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref_known(v_a_2549_, 0);
lean_dec_ref_known(v_mod_x3f_2220_, 1);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v___x_2568_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2569_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2568_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v___x_2545_, v_a_2228_);
lean_dec_ref_known(v___x_2545_, 14);
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
case 3:
{
v___y_2521_ = v_a_2223_;
v___y_2522_ = v_a_2224_;
v___y_2523_ = v_a_2225_;
v___y_2524_ = v_a_2226_;
v___y_2525_ = v___x_2545_;
v___y_2526_ = v_a_2228_;
goto v___jp_2520_;
}
case 5:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec_ref_known(v_a_2549_, 1);
lean_dec_ref_known(v_mod_x3f_2220_, 1);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v___x_2578_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2579_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2578_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v___x_2545_, v_a_2228_);
lean_dec_ref_known(v___x_2545_, 14);
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2579_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
case 8:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec_ref_known(v_a_2549_, 0);
lean_dec_ref_known(v_mod_x3f_2220_, 1);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v___x_2588_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2589_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2588_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v___x_2545_, v_a_2228_);
lean_dec_ref_known(v___x_2545_, 14);
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
default: 
{
lean_dec(v_a_2549_);
lean_dec_ref_known(v_mod_x3f_2220_, 1);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v___y_2551_ = v_a_2223_;
v___y_2552_ = v_a_2224_;
v___y_2553_ = v_a_2225_;
v___y_2554_ = v_a_2226_;
v___y_2555_ = v___x_2545_;
v___y_2556_ = v_a_2228_;
goto v___jp_2550_;
}
}
v___jp_2550_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v___x_2557_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2558_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2557_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec_ref(v___y_2555_);
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec_ref_known(v_mod_x3f_2220_, 1);
lean_dec_ref_known(v___x_2545_, 14);
lean_dec(v_term_2221_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v_a_2598_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2548_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2548_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
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
v___y_2525_ = v___x_2545_;
v___y_2526_ = v_a_2228_;
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref_known(v___x_2545_, 14);
lean_dec(v_term_2221_);
lean_dec(v_mod_x3f_2220_);
lean_dec(v_p_2219_);
lean_dec_ref(v_params_2218_);
v_a_2606_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2546_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2546_);
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
v___jp_2230_:
{
lean_object* v___x_2247_; 
lean_inc(v___y_2246_);
lean_inc(v___y_2244_);
lean_inc_ref(v___y_2243_);
v___x_2247_ = lean_apply_7(v___y_2234_, v___y_2242_, v___y_2238_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, lean_box(0));
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
v___x_2252_ = l_Lean_PersistentArray_push___redArg(v___y_2240_, v_a_2248_);
v___x_2253_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2253_, 0, v___y_2232_);
lean_ctor_set(v___x_2253_, 1, v___y_2236_);
lean_ctor_set(v___x_2253_, 2, v___x_2252_);
lean_ctor_set(v___x_2253_, 3, v___y_2239_);
lean_ctor_set(v___x_2253_, 4, v___y_2241_);
lean_ctor_set(v___x_2253_, 5, v___y_2237_);
lean_ctor_set(v___x_2253_, 6, v___y_2235_);
lean_ctor_set(v___x_2253_, 7, v___y_2231_);
lean_ctor_set(v___x_2253_, 8, v___y_2233_);
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
lean_dec_ref(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
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
v___x_2283_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2222_, v___y_2273_, v___y_2281_, v___y_2270_, v___y_2282_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_dec_ref_known(v___x_2283_, 1);
v___y_2231_ = v___y_2277_;
v___y_2232_ = v___y_2267_;
v___y_2233_ = v___y_2268_;
v___y_2234_ = v___y_2269_;
v___y_2235_ = v___y_2271_;
v___y_2236_ = v___y_2278_;
v___y_2237_ = v___y_2272_;
v___y_2238_ = v___y_2279_;
v___y_2239_ = v___y_2274_;
v___y_2240_ = v___y_2280_;
v___y_2241_ = v___y_2276_;
v___y_2242_ = v___y_2275_;
v___y_2243_ = v___y_2273_;
v___y_2244_ = v___y_2281_;
v___y_2245_ = v___y_2270_;
v___y_2246_ = v___y_2282_;
goto v___jp_2230_;
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
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
v___x_2322_ = lean_array_get_size(v___y_2315_);
lean_dec_ref(v___y_2315_);
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = lean_nat_dec_eq(v___x_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec_ref(v___y_2313_);
lean_dec_ref(v_params_2218_);
v___x_2325_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2326_ = l_Lean_indentExpr(v___y_2314_);
v___x_2327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2327_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec_ref(v___y_2320_);
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
lean_dec_ref(v___y_2320_);
lean_dec_ref(v___y_2314_);
v___y_2293_ = v___y_2313_;
goto v___jp_2292_;
}
}
v___jp_2337_:
{
uint8_t v___x_2349_; 
v___x_2349_ = l_Lean_Expr_isForall(v___y_2340_);
if (v___x_2349_ == 0)
{
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2338_);
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
lean_dec_ref_known(v_mod_x3f_2220_, 1);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___y_2339_);
lean_dec_ref(v_params_2218_);
v___x_2350_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2351_ = l_Lean_indentExpr(v___y_2340_);
v___x_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2352_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec_ref(v___y_2347_);
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
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v_mod_x3f_2220_);
v_extra_2362_ = lean_ctor_get(v_params_2218_, 2);
lean_inc_ref(v_extra_2362_);
if (lean_obj_tag(v___y_2341_) == 2)
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
v_gen_2375_ = lean_ctor_get_uint8(v___y_2341_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___y_2341_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2377_ = v___y_2341_;
v_isShared_2378_ = v_isSharedCheck_2424_;
goto v_resetjp_2376_;
}
else
{
lean_dec(v___y_2341_);
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
lean_dec_ref_known(v___x_2379_, 1);
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
lean_inc_ref(v___y_2338_);
lean_inc(v___y_2348_);
lean_inc_ref(v___y_2347_);
lean_inc(v___y_2346_);
lean_inc_ref(v___y_2345_);
lean_inc(v_size_2374_);
v___x_2382_ = lean_apply_7(v___y_2338_, v___x_2381_, v_size_2374_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, lean_box(0));
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2384_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2384_, 0, v_gen_2375_);
lean_inc(v___y_2348_);
lean_inc(v___y_2346_);
lean_inc_ref(v___y_2345_);
lean_inc(v_size_2374_);
v___x_2385_ = lean_apply_7(v___y_2338_, v___x_2384_, v_size_2374_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, lean_box(0));
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
lean_dec_ref(v___y_2347_);
lean_dec_ref(v___y_2338_);
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
lean_dec_ref(v___y_2347_);
lean_dec_ref(v___y_2338_);
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
switch(lean_obj_tag(v___y_2341_))
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
v___y_2267_ = v_config_2427_;
v___y_2268_ = v_anchorRefs_x3f_2434_;
v___y_2269_ = v___y_2338_;
v___y_2270_ = v___y_2347_;
v___y_2271_ = v_norm_2432_;
v___y_2272_ = v_symPrios_2431_;
v___y_2273_ = v___y_2345_;
v___y_2274_ = v_extraInj_2429_;
v___y_2275_ = v___y_2341_;
v___y_2276_ = v_extraFacts_2430_;
v___y_2277_ = v_normProcs_2433_;
v___y_2278_ = v_extensions_2428_;
v___y_2279_ = v_size_2435_;
v___y_2280_ = v_extra_2362_;
v___y_2281_ = v___y_2346_;
v___y_2282_ = v___y_2348_;
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
v___y_2267_ = v_config_2436_;
v___y_2268_ = v_anchorRefs_x3f_2443_;
v___y_2269_ = v___y_2338_;
v___y_2270_ = v___y_2347_;
v___y_2271_ = v_norm_2441_;
v___y_2272_ = v_symPrios_2440_;
v___y_2273_ = v___y_2345_;
v___y_2274_ = v_extraInj_2438_;
v___y_2275_ = v___y_2341_;
v___y_2276_ = v_extraFacts_2439_;
v___y_2277_ = v_normProcs_2442_;
v___y_2278_ = v_extensions_2437_;
v___y_2279_ = v_size_2444_;
v___y_2280_ = v_extra_2362_;
v___y_2281_ = v___y_2346_;
v___y_2282_ = v___y_2348_;
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
v___y_2231_ = v_normProcs_2451_;
v___y_2232_ = v_config_2445_;
v___y_2233_ = v_anchorRefs_x3f_2452_;
v___y_2234_ = v___y_2338_;
v___y_2235_ = v_norm_2450_;
v___y_2236_ = v_extensions_2446_;
v___y_2237_ = v_symPrios_2449_;
v___y_2238_ = v_size_2453_;
v___y_2239_ = v_extraInj_2447_;
v___y_2240_ = v_extra_2362_;
v___y_2241_ = v_extraFacts_2448_;
v___y_2242_ = v___y_2341_;
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
lean_dec_ref_known(v_a_2467_, 1);
v_fst_2472_ = lean_ctor_get(v_val_2471_, 0);
lean_inc(v_fst_2472_);
v_snd_2473_ = lean_ctor_get(v_val_2471_, 1);
lean_inc_n(v_snd_2473_, 2);
lean_dec(v_val_2471_);
lean_inc(v___y_2461_);
lean_inc_ref(v___y_2460_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
v___x_2474_ = lean_infer_type(v_snd_2473_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc_n(v_a_2475_, 2);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = l_Lean_Meta_isProp(v_a_2475_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___f_2480_; uint8_t v___x_2481_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
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
lean_dec_ref(v___y_2460_);
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
v___y_2338_ = v___f_2480_;
v___y_2339_ = v_snd_2473_;
v___y_2340_ = v_a_2475_;
v___y_2341_ = v_kind_2455_;
v___y_2342_ = v_fst_2472_;
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
lean_dec_ref(v___y_2460_);
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
lean_dec_ref(v___y_2460_);
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
lean_dec_ref(v___y_2460_);
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
lean_dec_ref(v___y_2460_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2614_, lean_object* v_p_2615_, lean_object* v_mod_x3f_2616_, lean_object* v_term_2617_, lean_object* v_minIndexable_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
uint8_t v_minIndexable_boxed_2626_; lean_object* v_res_2627_; 
v_minIndexable_boxed_2626_ = lean_unbox(v_minIndexable_2618_);
v_res_2627_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2614_, v_p_2615_, v_mod_x3f_2616_, v_term_2617_, v_minIndexable_boxed_2626_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object* v_00_u03b1_2628_, lean_object* v_msg_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v_00_u03b1_2638_, lean_object* v_msg_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v_00_u03b1_2638_, v_msg_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object* v_msgData_2648_, lean_object* v_macroStack_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2648_, v_macroStack_2649_, v___y_2654_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object* v_msgData_2658_, lean_object* v_macroStack_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(v_msgData_2658_, v_macroStack_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2668_, lean_object* v_val_2669_, lean_object* v___x_2670_, lean_object* v_____r_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; lean_object* v_ext_2680_; lean_object* v_toEnvExtension_2681_; lean_object* v_env_2682_; lean_object* v_config_2683_; lean_object* v_extensions_2684_; lean_object* v_extra_2685_; lean_object* v_extraInj_2686_; lean_object* v_extraFacts_2687_; lean_object* v_symPrios_2688_; lean_object* v_norm_2689_; lean_object* v_normProcs_2690_; lean_object* v_anchorRefs_x3f_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2703_; 
v___x_2679_ = lean_st_ref_get(v___y_2677_);
v_ext_2680_ = lean_ctor_get(v_val_2669_, 1);
v_toEnvExtension_2681_ = lean_ctor_get(v_ext_2680_, 0);
v_env_2682_ = lean_ctor_get(v___x_2679_, 0);
lean_inc_ref(v_env_2682_);
lean_dec(v___x_2679_);
v_config_2683_ = lean_ctor_get(v_params_2668_, 0);
v_extensions_2684_ = lean_ctor_get(v_params_2668_, 1);
v_extra_2685_ = lean_ctor_get(v_params_2668_, 2);
v_extraInj_2686_ = lean_ctor_get(v_params_2668_, 3);
v_extraFacts_2687_ = lean_ctor_get(v_params_2668_, 4);
v_symPrios_2688_ = lean_ctor_get(v_params_2668_, 5);
v_norm_2689_ = lean_ctor_get(v_params_2668_, 6);
v_normProcs_2690_ = lean_ctor_get(v_params_2668_, 7);
v_anchorRefs_x3f_2691_ = lean_ctor_get(v_params_2668_, 8);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_params_2668_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2693_ = v_params_2668_;
v_isShared_2694_ = v_isSharedCheck_2703_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_anchorRefs_x3f_2691_);
lean_inc(v_normProcs_2690_);
lean_inc(v_norm_2689_);
lean_inc(v_symPrios_2688_);
lean_inc(v_extraFacts_2687_);
lean_inc(v_extraInj_2686_);
lean_inc(v_extra_2685_);
lean_inc(v_extensions_2684_);
lean_inc(v_config_2683_);
lean_dec(v_params_2668_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2703_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v_asyncMode_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v_asyncMode_2695_ = lean_ctor_get(v_toEnvExtension_2681_, 2);
v___x_2696_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2670_, v_val_2669_, v_env_2682_, v_asyncMode_2695_);
v___x_2697_ = lean_array_push(v_extensions_2684_, v___x_2696_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v___x_2697_);
v___x_2699_ = v___x_2693_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_config_2683_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_extra_2685_);
lean_ctor_set(v_reuseFailAlloc_2702_, 3, v_extraInj_2686_);
lean_ctor_set(v_reuseFailAlloc_2702_, 4, v_extraFacts_2687_);
lean_ctor_set(v_reuseFailAlloc_2702_, 5, v_symPrios_2688_);
lean_ctor_set(v_reuseFailAlloc_2702_, 6, v_norm_2689_);
lean_ctor_set(v_reuseFailAlloc_2702_, 7, v_normProcs_2690_);
lean_ctor_set(v_reuseFailAlloc_2702_, 8, v_anchorRefs_x3f_2691_);
v___x_2699_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2704_, lean_object* v_val_2705_, lean_object* v___x_2706_, lean_object* v_____r_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2704_, v_val_2705_, v___x_2706_, v_____r_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v_val_2705_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2716_, lean_object* v_id_2717_, uint8_t v_minIndexable_2718_, lean_object* v_as_x27_2719_, lean_object* v_b_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
if (lean_obj_tag(v_as_x27_2719_) == 0)
{
lean_object* v___x_2726_; 
lean_dec(v_id_2717_);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_b_2720_);
return v___x_2726_;
}
else
{
lean_object* v_head_2727_; lean_object* v_tail_2728_; lean_object* v_fileName_2729_; lean_object* v_fileMap_2730_; lean_object* v_options_2731_; lean_object* v_currRecDepth_2732_; lean_object* v_maxRecDepth_2733_; lean_object* v_ref_2734_; lean_object* v_currNamespace_2735_; lean_object* v_openDecls_2736_; lean_object* v_initHeartbeats_2737_; lean_object* v_maxHeartbeats_2738_; lean_object* v_quotContext_2739_; lean_object* v_currMacroScope_2740_; uint8_t v_diag_2741_; lean_object* v_cancelTk_x3f_2742_; uint8_t v_suppressElabErrors_2743_; lean_object* v_inheritedTraceOptions_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; lean_object* v_ref_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v_head_2727_ = lean_ctor_get(v_as_x27_2719_, 0);
v_tail_2728_ = lean_ctor_get(v_as_x27_2719_, 1);
v_fileName_2729_ = lean_ctor_get(v___y_2723_, 0);
v_fileMap_2730_ = lean_ctor_get(v___y_2723_, 1);
v_options_2731_ = lean_ctor_get(v___y_2723_, 2);
v_currRecDepth_2732_ = lean_ctor_get(v___y_2723_, 3);
v_maxRecDepth_2733_ = lean_ctor_get(v___y_2723_, 4);
v_ref_2734_ = lean_ctor_get(v___y_2723_, 5);
v_currNamespace_2735_ = lean_ctor_get(v___y_2723_, 6);
v_openDecls_2736_ = lean_ctor_get(v___y_2723_, 7);
v_initHeartbeats_2737_ = lean_ctor_get(v___y_2723_, 8);
v_maxHeartbeats_2738_ = lean_ctor_get(v___y_2723_, 9);
v_quotContext_2739_ = lean_ctor_get(v___y_2723_, 10);
v_currMacroScope_2740_ = lean_ctor_get(v___y_2723_, 11);
v_diag_2741_ = lean_ctor_get_uint8(v___y_2723_, sizeof(void*)*14);
v_cancelTk_x3f_2742_ = lean_ctor_get(v___y_2723_, 12);
v_suppressElabErrors_2743_ = lean_ctor_get_uint8(v___y_2723_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2744_ = lean_ctor_get(v___y_2723_, 13);
v___x_2745_ = 0;
v___x_2746_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_2747_ = l_Lean_replaceRef(v_p_2716_, v_ref_2734_);
lean_inc_ref(v_inheritedTraceOptions_2744_);
lean_inc(v_cancelTk_x3f_2742_);
lean_inc(v_currMacroScope_2740_);
lean_inc(v_quotContext_2739_);
lean_inc(v_maxHeartbeats_2738_);
lean_inc(v_initHeartbeats_2737_);
lean_inc(v_openDecls_2736_);
lean_inc(v_currNamespace_2735_);
lean_inc(v_maxRecDepth_2733_);
lean_inc(v_currRecDepth_2732_);
lean_inc_ref(v_options_2731_);
lean_inc_ref(v_fileMap_2730_);
lean_inc_ref(v_fileName_2729_);
v___x_2748_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2748_, 0, v_fileName_2729_);
lean_ctor_set(v___x_2748_, 1, v_fileMap_2730_);
lean_ctor_set(v___x_2748_, 2, v_options_2731_);
lean_ctor_set(v___x_2748_, 3, v_currRecDepth_2732_);
lean_ctor_set(v___x_2748_, 4, v_maxRecDepth_2733_);
lean_ctor_set(v___x_2748_, 5, v_ref_2747_);
lean_ctor_set(v___x_2748_, 6, v_currNamespace_2735_);
lean_ctor_set(v___x_2748_, 7, v_openDecls_2736_);
lean_ctor_set(v___x_2748_, 8, v_initHeartbeats_2737_);
lean_ctor_set(v___x_2748_, 9, v_maxHeartbeats_2738_);
lean_ctor_set(v___x_2748_, 10, v_quotContext_2739_);
lean_ctor_set(v___x_2748_, 11, v_currMacroScope_2740_);
lean_ctor_set(v___x_2748_, 12, v_cancelTk_x3f_2742_);
lean_ctor_set(v___x_2748_, 13, v_inheritedTraceOptions_2744_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*14, v_diag_2741_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*14 + 1, v_suppressElabErrors_2743_);
lean_inc(v_head_2727_);
lean_inc(v_id_2717_);
v___x_2749_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2720_, v_id_2717_, v_head_2727_, v___x_2746_, v_minIndexable_2718_, v___x_2745_, v___x_2745_, v___y_2721_, v___y_2722_, v___x_2748_, v___y_2724_);
lean_dec_ref_known(v___x_2748_, 14);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v_as_x27_2719_ = v_tail_2728_;
v_b_2720_ = v_a_2750_;
goto _start;
}
else
{
lean_dec(v_id_2717_);
return v___x_2749_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2752_, lean_object* v_id_2753_, lean_object* v_minIndexable_2754_, lean_object* v_as_x27_2755_, lean_object* v_b_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v_minIndexable_boxed_2762_; lean_object* v_res_2763_; 
v_minIndexable_boxed_2762_ = lean_unbox(v_minIndexable_2754_);
v_res_2763_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2752_, v_id_2753_, v_minIndexable_boxed_2762_, v_as_x27_2755_, v_b_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v_as_x27_2755_);
lean_dec(v_p_2752_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
if (lean_obj_tag(v_a_2765_) == 0)
{
lean_object* v___x_2767_; 
v___x_2767_ = l_List_reverse___redArg(v_a_2766_);
return v___x_2767_;
}
else
{
lean_object* v_head_2768_; lean_object* v_tail_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2780_; 
v_head_2768_ = lean_ctor_get(v_a_2765_, 0);
v_tail_2769_ = lean_ctor_get(v_a_2765_, 1);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_a_2765_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2771_ = v_a_2765_;
v_isShared_2772_ = v_isSharedCheck_2780_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_tail_2769_);
lean_inc(v_head_2768_);
lean_dec(v_a_2765_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2780_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v_kind_2773_; uint8_t v___x_2774_; 
v_kind_2773_ = lean_ctor_get(v_head_2768_, 6);
v___x_2774_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2773_, v_k_2764_);
if (v___x_2774_ == 0)
{
lean_del_object(v___x_2771_);
lean_dec(v_head_2768_);
v_a_2765_ = v_tail_2769_;
goto _start;
}
else
{
lean_object* v___x_2777_; 
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 1, v_a_2766_);
v___x_2777_ = v___x_2771_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_head_2768_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_a_2766_);
v___x_2777_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
v_a_2765_ = v_tail_2769_;
v_a_2766_ = v___x_2777_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2781_, v_a_2782_, v_a_2783_);
lean_dec(v_k_2781_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_2785_, lean_object* v_msg_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_fileName_2794_; lean_object* v_fileMap_2795_; lean_object* v_options_2796_; lean_object* v_currRecDepth_2797_; lean_object* v_maxRecDepth_2798_; lean_object* v_ref_2799_; lean_object* v_currNamespace_2800_; lean_object* v_openDecls_2801_; lean_object* v_initHeartbeats_2802_; lean_object* v_maxHeartbeats_2803_; lean_object* v_quotContext_2804_; lean_object* v_currMacroScope_2805_; uint8_t v_diag_2806_; lean_object* v_cancelTk_x3f_2807_; uint8_t v_suppressElabErrors_2808_; lean_object* v_inheritedTraceOptions_2809_; lean_object* v_ref_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v_fileName_2794_ = lean_ctor_get(v___y_2791_, 0);
v_fileMap_2795_ = lean_ctor_get(v___y_2791_, 1);
v_options_2796_ = lean_ctor_get(v___y_2791_, 2);
v_currRecDepth_2797_ = lean_ctor_get(v___y_2791_, 3);
v_maxRecDepth_2798_ = lean_ctor_get(v___y_2791_, 4);
v_ref_2799_ = lean_ctor_get(v___y_2791_, 5);
v_currNamespace_2800_ = lean_ctor_get(v___y_2791_, 6);
v_openDecls_2801_ = lean_ctor_get(v___y_2791_, 7);
v_initHeartbeats_2802_ = lean_ctor_get(v___y_2791_, 8);
v_maxHeartbeats_2803_ = lean_ctor_get(v___y_2791_, 9);
v_quotContext_2804_ = lean_ctor_get(v___y_2791_, 10);
v_currMacroScope_2805_ = lean_ctor_get(v___y_2791_, 11);
v_diag_2806_ = lean_ctor_get_uint8(v___y_2791_, sizeof(void*)*14);
v_cancelTk_x3f_2807_ = lean_ctor_get(v___y_2791_, 12);
v_suppressElabErrors_2808_ = lean_ctor_get_uint8(v___y_2791_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2809_ = lean_ctor_get(v___y_2791_, 13);
v_ref_2810_ = l_Lean_replaceRef(v_ref_2785_, v_ref_2799_);
lean_inc_ref(v_inheritedTraceOptions_2809_);
lean_inc(v_cancelTk_x3f_2807_);
lean_inc(v_currMacroScope_2805_);
lean_inc(v_quotContext_2804_);
lean_inc(v_maxHeartbeats_2803_);
lean_inc(v_initHeartbeats_2802_);
lean_inc(v_openDecls_2801_);
lean_inc(v_currNamespace_2800_);
lean_inc(v_maxRecDepth_2798_);
lean_inc(v_currRecDepth_2797_);
lean_inc_ref(v_options_2796_);
lean_inc_ref(v_fileMap_2795_);
lean_inc_ref(v_fileName_2794_);
v___x_2811_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2811_, 0, v_fileName_2794_);
lean_ctor_set(v___x_2811_, 1, v_fileMap_2795_);
lean_ctor_set(v___x_2811_, 2, v_options_2796_);
lean_ctor_set(v___x_2811_, 3, v_currRecDepth_2797_);
lean_ctor_set(v___x_2811_, 4, v_maxRecDepth_2798_);
lean_ctor_set(v___x_2811_, 5, v_ref_2810_);
lean_ctor_set(v___x_2811_, 6, v_currNamespace_2800_);
lean_ctor_set(v___x_2811_, 7, v_openDecls_2801_);
lean_ctor_set(v___x_2811_, 8, v_initHeartbeats_2802_);
lean_ctor_set(v___x_2811_, 9, v_maxHeartbeats_2803_);
lean_ctor_set(v___x_2811_, 10, v_quotContext_2804_);
lean_ctor_set(v___x_2811_, 11, v_currMacroScope_2805_);
lean_ctor_set(v___x_2811_, 12, v_cancelTk_x3f_2807_);
lean_ctor_set(v___x_2811_, 13, v_inheritedTraceOptions_2809_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*14, v_diag_2806_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*14 + 1, v_suppressElabErrors_2808_);
v___x_2812_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___x_2811_, v___y_2792_);
lean_dec_ref_known(v___x_2811_, 14);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_2813_, lean_object* v_msg_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_2813_, v_msg_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v_ref_2813_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_2823_, lean_object* v_id_2824_, uint8_t v_minIndexable_2825_, lean_object* v_as_x27_2826_, lean_object* v_b_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
if (lean_obj_tag(v_as_x27_2826_) == 0)
{
lean_object* v___x_2833_; 
lean_dec(v_id_2824_);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_b_2827_);
return v___x_2833_;
}
else
{
lean_object* v_head_2834_; lean_object* v_tail_2835_; lean_object* v_fileName_2836_; lean_object* v_fileMap_2837_; lean_object* v_options_2838_; lean_object* v_currRecDepth_2839_; lean_object* v_maxRecDepth_2840_; lean_object* v_ref_2841_; lean_object* v_currNamespace_2842_; lean_object* v_openDecls_2843_; lean_object* v_initHeartbeats_2844_; lean_object* v_maxHeartbeats_2845_; lean_object* v_quotContext_2846_; lean_object* v_currMacroScope_2847_; uint8_t v_diag_2848_; lean_object* v_cancelTk_x3f_2849_; uint8_t v_suppressElabErrors_2850_; lean_object* v_inheritedTraceOptions_2851_; uint8_t v___x_2852_; uint8_t v___x_2853_; lean_object* v___x_2854_; lean_object* v_ref_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_head_2834_ = lean_ctor_get(v_as_x27_2826_, 0);
v_tail_2835_ = lean_ctor_get(v_as_x27_2826_, 1);
v_fileName_2836_ = lean_ctor_get(v___y_2830_, 0);
v_fileMap_2837_ = lean_ctor_get(v___y_2830_, 1);
v_options_2838_ = lean_ctor_get(v___y_2830_, 2);
v_currRecDepth_2839_ = lean_ctor_get(v___y_2830_, 3);
v_maxRecDepth_2840_ = lean_ctor_get(v___y_2830_, 4);
v_ref_2841_ = lean_ctor_get(v___y_2830_, 5);
v_currNamespace_2842_ = lean_ctor_get(v___y_2830_, 6);
v_openDecls_2843_ = lean_ctor_get(v___y_2830_, 7);
v_initHeartbeats_2844_ = lean_ctor_get(v___y_2830_, 8);
v_maxHeartbeats_2845_ = lean_ctor_get(v___y_2830_, 9);
v_quotContext_2846_ = lean_ctor_get(v___y_2830_, 10);
v_currMacroScope_2847_ = lean_ctor_get(v___y_2830_, 11);
v_diag_2848_ = lean_ctor_get_uint8(v___y_2830_, sizeof(void*)*14);
v_cancelTk_x3f_2849_ = lean_ctor_get(v___y_2830_, 12);
v_suppressElabErrors_2850_ = lean_ctor_get_uint8(v___y_2830_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2851_ = lean_ctor_get(v___y_2830_, 13);
v___x_2852_ = 0;
v___x_2853_ = 1;
v___x_2854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_2855_ = l_Lean_replaceRef(v_p_2823_, v_ref_2841_);
lean_inc_ref(v_inheritedTraceOptions_2851_);
lean_inc(v_cancelTk_x3f_2849_);
lean_inc(v_currMacroScope_2847_);
lean_inc(v_quotContext_2846_);
lean_inc(v_maxHeartbeats_2845_);
lean_inc(v_initHeartbeats_2844_);
lean_inc(v_openDecls_2843_);
lean_inc(v_currNamespace_2842_);
lean_inc(v_maxRecDepth_2840_);
lean_inc(v_currRecDepth_2839_);
lean_inc_ref(v_options_2838_);
lean_inc_ref(v_fileMap_2837_);
lean_inc_ref(v_fileName_2836_);
v___x_2856_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2856_, 0, v_fileName_2836_);
lean_ctor_set(v___x_2856_, 1, v_fileMap_2837_);
lean_ctor_set(v___x_2856_, 2, v_options_2838_);
lean_ctor_set(v___x_2856_, 3, v_currRecDepth_2839_);
lean_ctor_set(v___x_2856_, 4, v_maxRecDepth_2840_);
lean_ctor_set(v___x_2856_, 5, v_ref_2855_);
lean_ctor_set(v___x_2856_, 6, v_currNamespace_2842_);
lean_ctor_set(v___x_2856_, 7, v_openDecls_2843_);
lean_ctor_set(v___x_2856_, 8, v_initHeartbeats_2844_);
lean_ctor_set(v___x_2856_, 9, v_maxHeartbeats_2845_);
lean_ctor_set(v___x_2856_, 10, v_quotContext_2846_);
lean_ctor_set(v___x_2856_, 11, v_currMacroScope_2847_);
lean_ctor_set(v___x_2856_, 12, v_cancelTk_x3f_2849_);
lean_ctor_set(v___x_2856_, 13, v_inheritedTraceOptions_2851_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*14, v_diag_2848_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*14 + 1, v_suppressElabErrors_2850_);
lean_inc(v_head_2834_);
lean_inc(v_id_2824_);
v___x_2857_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2827_, v_id_2824_, v_head_2834_, v___x_2854_, v_minIndexable_2825_, v___x_2852_, v___x_2853_, v___y_2828_, v___y_2829_, v___x_2856_, v___y_2831_);
lean_dec_ref_known(v___x_2856_, 14);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v_as_x27_2826_ = v_tail_2835_;
v_b_2827_ = v_a_2858_;
goto _start;
}
else
{
lean_dec(v_id_2824_);
return v___x_2857_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_2860_, lean_object* v_id_2861_, lean_object* v_minIndexable_2862_, lean_object* v_as_x27_2863_, lean_object* v_b_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
uint8_t v_minIndexable_boxed_2870_; lean_object* v_res_2871_; 
v_minIndexable_boxed_2870_ = lean_unbox(v_minIndexable_2862_);
v_res_2871_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_2860_, v_id_2861_, v_minIndexable_boxed_2870_, v_as_x27_2863_, v_b_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v_as_x27_2863_);
lean_dec(v_p_2860_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_2872_){
_start:
{
if (lean_obj_tag(v_x_2872_) == 0)
{
lean_object* v___x_2873_; 
v___x_2873_ = lean_box(0);
return v___x_2873_;
}
else
{
lean_object* v_head_2874_; lean_object* v_tail_2875_; lean_object* v_fst_2876_; uint8_t v___x_2877_; 
v_head_2874_ = lean_ctor_get(v_x_2872_, 0);
v_tail_2875_ = lean_ctor_get(v_x_2872_, 1);
v_fst_2876_ = lean_ctor_get(v_head_2874_, 0);
v___x_2877_ = l_Lean_isPrivateName(v_fst_2876_);
if (v___x_2877_ == 0)
{
v_x_2872_ = v_tail_2875_;
goto _start;
}
else
{
lean_object* v___x_2879_; 
lean_inc(v_head_2874_);
v___x_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2879_, 0, v_head_2874_);
return v___x_2879_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_2880_);
lean_dec(v_x_2880_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_2882_, lean_object* v_msgData_2883_, uint8_t v_severity_2884_, uint8_t v_isSilent_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; uint8_t v___y_2895_; uint8_t v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; uint8_t v___y_2931_; uint8_t v___y_2932_; lean_object* v___y_2933_; uint8_t v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; uint8_t v___y_2957_; uint8_t v___y_2958_; uint8_t v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; uint8_t v___y_2967_; uint8_t v___y_2968_; lean_object* v___y_2969_; uint8_t v___y_2970_; uint8_t v___x_2975_; lean_object* v___y_2977_; lean_object* v___y_2978_; uint8_t v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; uint8_t v___y_2982_; uint8_t v___y_2983_; uint8_t v___y_2985_; uint8_t v___x_3000_; 
v___x_2975_ = 2;
v___x_3000_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2884_, v___x_2975_);
if (v___x_3000_ == 0)
{
v___y_2985_ = v___x_3000_;
goto v___jp_2984_;
}
else
{
uint8_t v___x_3001_; 
lean_inc_ref(v_msgData_2883_);
v___x_3001_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2883_);
v___y_2985_ = v___x_3001_;
goto v___jp_2984_;
}
v___jp_2891_:
{
lean_object* v___x_2901_; lean_object* v_currNamespace_2902_; lean_object* v_openDecls_2903_; lean_object* v_env_2904_; lean_object* v_nextMacroScope_2905_; lean_object* v_ngen_2906_; lean_object* v_auxDeclNGen_2907_; lean_object* v_traceState_2908_; lean_object* v_cache_2909_; lean_object* v_messages_2910_; lean_object* v_infoState_2911_; lean_object* v_snapshotTasks_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2926_; 
v___x_2901_ = lean_st_ref_take(v___y_2900_);
v_currNamespace_2902_ = lean_ctor_get(v___y_2899_, 6);
v_openDecls_2903_ = lean_ctor_get(v___y_2899_, 7);
v_env_2904_ = lean_ctor_get(v___x_2901_, 0);
v_nextMacroScope_2905_ = lean_ctor_get(v___x_2901_, 1);
v_ngen_2906_ = lean_ctor_get(v___x_2901_, 2);
v_auxDeclNGen_2907_ = lean_ctor_get(v___x_2901_, 3);
v_traceState_2908_ = lean_ctor_get(v___x_2901_, 4);
v_cache_2909_ = lean_ctor_get(v___x_2901_, 5);
v_messages_2910_ = lean_ctor_get(v___x_2901_, 6);
v_infoState_2911_ = lean_ctor_get(v___x_2901_, 7);
v_snapshotTasks_2912_ = lean_ctor_get(v___x_2901_, 8);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2914_ = v___x_2901_;
v_isShared_2915_ = v_isSharedCheck_2926_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_snapshotTasks_2912_);
lean_inc(v_infoState_2911_);
lean_inc(v_messages_2910_);
lean_inc(v_cache_2909_);
lean_inc(v_traceState_2908_);
lean_inc(v_auxDeclNGen_2907_);
lean_inc(v_ngen_2906_);
lean_inc(v_nextMacroScope_2905_);
lean_inc(v_env_2904_);
lean_dec(v___x_2901_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2926_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2921_; 
lean_inc(v_openDecls_2903_);
lean_inc(v_currNamespace_2902_);
v___x_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2916_, 0, v_currNamespace_2902_);
lean_ctor_set(v___x_2916_, 1, v_openDecls_2903_);
v___x_2917_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
lean_ctor_set(v___x_2917_, 1, v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc_ref(v___y_2892_);
v___x_2918_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2918_, 0, v___y_2892_);
lean_ctor_set(v___x_2918_, 1, v___y_2898_);
lean_ctor_set(v___x_2918_, 2, v___y_2897_);
lean_ctor_set(v___x_2918_, 3, v___y_2893_);
lean_ctor_set(v___x_2918_, 4, v___x_2917_);
lean_ctor_set_uint8(v___x_2918_, sizeof(void*)*5, v___y_2895_);
lean_ctor_set_uint8(v___x_2918_, sizeof(void*)*5 + 1, v___y_2896_);
lean_ctor_set_uint8(v___x_2918_, sizeof(void*)*5 + 2, v_isSilent_2885_);
v___x_2919_ = l_Lean_MessageLog_add(v___x_2918_, v_messages_2910_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 6, v___x_2919_);
v___x_2921_ = v___x_2914_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_env_2904_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_nextMacroScope_2905_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_ngen_2906_);
lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_auxDeclNGen_2907_);
lean_ctor_set(v_reuseFailAlloc_2925_, 4, v_traceState_2908_);
lean_ctor_set(v_reuseFailAlloc_2925_, 5, v_cache_2909_);
lean_ctor_set(v_reuseFailAlloc_2925_, 6, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2925_, 7, v_infoState_2911_);
lean_ctor_set(v_reuseFailAlloc_2925_, 8, v_snapshotTasks_2912_);
v___x_2921_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2922_ = lean_st_ref_put(v___y_2900_, v___x_2921_);
v___x_2923_ = lean_box(0);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
}
}
v___jp_2927_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2951_; 
v___x_2936_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2883_);
v___x_2937_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_2936_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2940_ = v___x_2937_;
v_isShared_2941_ = v_isSharedCheck_2951_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2951_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_inc_ref_n(v___y_2930_, 2);
v___x_2942_ = l_Lean_FileMap_toPosition(v___y_2930_, v___y_2933_);
lean_dec(v___y_2933_);
v___x_2943_ = l_Lean_FileMap_toPosition(v___y_2930_, v___y_2935_);
lean_dec(v___y_2935_);
v___x_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
v___x_2945_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_2931_ == 0)
{
lean_del_object(v___x_2940_);
lean_dec_ref(v___y_2928_);
v___y_2892_ = v___y_2929_;
v___y_2893_ = v___x_2945_;
v___y_2894_ = v_a_2938_;
v___y_2895_ = v___y_2932_;
v___y_2896_ = v___y_2934_;
v___y_2897_ = v___x_2944_;
v___y_2898_ = v___x_2942_;
v___y_2899_ = v___y_2888_;
v___y_2900_ = v___y_2889_;
goto v___jp_2891_;
}
else
{
uint8_t v___x_2946_; 
lean_inc(v_a_2938_);
v___x_2946_ = l_Lean_MessageData_hasTag(v___y_2928_, v_a_2938_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
lean_dec_ref_known(v___x_2944_, 1);
lean_dec_ref(v___x_2942_);
lean_dec(v_a_2938_);
v___x_2947_ = lean_box(0);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v___x_2947_);
v___x_2949_ = v___x_2940_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
else
{
lean_del_object(v___x_2940_);
v___y_2892_ = v___y_2929_;
v___y_2893_ = v___x_2945_;
v___y_2894_ = v_a_2938_;
v___y_2895_ = v___y_2932_;
v___y_2896_ = v___y_2934_;
v___y_2897_ = v___x_2944_;
v___y_2898_ = v___x_2942_;
v___y_2899_ = v___y_2888_;
v___y_2900_ = v___y_2889_;
goto v___jp_2891_;
}
}
}
}
v___jp_2952_:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_Syntax_getTailPos_x3f(v___y_2954_, v___y_2958_);
lean_dec(v___y_2954_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_inc(v___y_2960_);
v___y_2928_ = v___y_2953_;
v___y_2929_ = v___y_2955_;
v___y_2930_ = v___y_2956_;
v___y_2931_ = v___y_2957_;
v___y_2932_ = v___y_2958_;
v___y_2933_ = v___y_2960_;
v___y_2934_ = v___y_2959_;
v___y_2935_ = v___y_2960_;
goto v___jp_2927_;
}
else
{
lean_object* v_val_2962_; 
v_val_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_val_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v___y_2928_ = v___y_2953_;
v___y_2929_ = v___y_2955_;
v___y_2930_ = v___y_2956_;
v___y_2931_ = v___y_2957_;
v___y_2932_ = v___y_2958_;
v___y_2933_ = v___y_2960_;
v___y_2934_ = v___y_2959_;
v___y_2935_ = v_val_2962_;
goto v___jp_2927_;
}
}
v___jp_2963_:
{
lean_object* v_ref_2971_; lean_object* v___x_2972_; 
v_ref_2971_ = l_Lean_replaceRef(v_ref_2882_, v___y_2969_);
v___x_2972_ = l_Lean_Syntax_getPos_x3f(v_ref_2971_, v___y_2968_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_unsigned_to_nat(0u);
v___y_2953_ = v___y_2964_;
v___y_2954_ = v_ref_2971_;
v___y_2955_ = v___y_2965_;
v___y_2956_ = v___y_2966_;
v___y_2957_ = v___y_2967_;
v___y_2958_ = v___y_2968_;
v___y_2959_ = v___y_2970_;
v___y_2960_ = v___x_2973_;
goto v___jp_2952_;
}
else
{
lean_object* v_val_2974_; 
v_val_2974_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_val_2974_);
lean_dec_ref_known(v___x_2972_, 1);
v___y_2953_ = v___y_2964_;
v___y_2954_ = v_ref_2971_;
v___y_2955_ = v___y_2965_;
v___y_2956_ = v___y_2966_;
v___y_2957_ = v___y_2967_;
v___y_2958_ = v___y_2968_;
v___y_2959_ = v___y_2970_;
v___y_2960_ = v_val_2974_;
goto v___jp_2952_;
}
}
v___jp_2976_:
{
if (v___y_2983_ == 0)
{
v___y_2964_ = v___y_2980_;
v___y_2965_ = v___y_2977_;
v___y_2966_ = v___y_2978_;
v___y_2967_ = v___y_2979_;
v___y_2968_ = v___y_2982_;
v___y_2969_ = v___y_2981_;
v___y_2970_ = v_severity_2884_;
goto v___jp_2963_;
}
else
{
v___y_2964_ = v___y_2980_;
v___y_2965_ = v___y_2977_;
v___y_2966_ = v___y_2978_;
v___y_2967_ = v___y_2979_;
v___y_2968_ = v___y_2982_;
v___y_2969_ = v___y_2981_;
v___y_2970_ = v___x_2975_;
goto v___jp_2963_;
}
}
v___jp_2984_:
{
if (v___y_2985_ == 0)
{
lean_object* v_fileName_2986_; lean_object* v_fileMap_2987_; lean_object* v_options_2988_; lean_object* v_ref_2989_; uint8_t v_suppressElabErrors_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___f_2993_; uint8_t v___x_2994_; uint8_t v___x_2995_; 
v_fileName_2986_ = lean_ctor_get(v___y_2888_, 0);
v_fileMap_2987_ = lean_ctor_get(v___y_2888_, 1);
v_options_2988_ = lean_ctor_get(v___y_2888_, 2);
v_ref_2989_ = lean_ctor_get(v___y_2888_, 5);
v_suppressElabErrors_2990_ = lean_ctor_get_uint8(v___y_2888_, sizeof(void*)*14 + 1);
v___x_2991_ = lean_box(v_suppressElabErrors_2990_);
v___x_2992_ = lean_box(v___y_2985_);
v___f_2993_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2993_, 0, v___x_2991_);
lean_closure_set(v___f_2993_, 1, v___x_2992_);
v___x_2994_ = 1;
v___x_2995_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2884_, v___x_2994_);
if (v___x_2995_ == 0)
{
v___y_2977_ = v_fileName_2986_;
v___y_2978_ = v_fileMap_2987_;
v___y_2979_ = v_suppressElabErrors_2990_;
v___y_2980_ = v___f_2993_;
v___y_2981_ = v_ref_2989_;
v___y_2982_ = v___y_2985_;
v___y_2983_ = v___x_2995_;
goto v___jp_2976_;
}
else
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = l_Lean_warningAsError;
v___x_2997_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2988_, v___x_2996_);
v___y_2977_ = v_fileName_2986_;
v___y_2978_ = v_fileMap_2987_;
v___y_2979_ = v_suppressElabErrors_2990_;
v___y_2980_ = v___f_2993_;
v___y_2981_ = v_ref_2989_;
v___y_2982_ = v___y_2985_;
v___y_2983_ = v___x_2997_;
goto v___jp_2976_;
}
}
else
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_dec_ref(v_msgData_2883_);
v___x_2998_ = lean_box(0);
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
return v___x_2999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_3002_, lean_object* v_msgData_3003_, lean_object* v_severity_3004_, lean_object* v_isSilent_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
uint8_t v_severity_boxed_3011_; uint8_t v_isSilent_boxed_3012_; lean_object* v_res_3013_; 
v_severity_boxed_3011_ = lean_unbox(v_severity_3004_);
v_isSilent_boxed_3012_ = lean_unbox(v_isSilent_3005_);
v_res_3013_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3002_, v_msgData_3003_, v_severity_boxed_3011_, v_isSilent_boxed_3012_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v_ref_3002_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3014_, uint8_t v_severity_3015_, uint8_t v_isSilent_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_ref_3024_; lean_object* v___x_3025_; 
v_ref_3024_ = lean_ctor_get(v___y_3021_, 5);
v___x_3025_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3024_, v_msgData_3014_, v_severity_3015_, v_isSilent_3016_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3026_, lean_object* v_severity_3027_, lean_object* v_isSilent_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
uint8_t v_severity_boxed_3036_; uint8_t v_isSilent_boxed_3037_; lean_object* v_res_3038_; 
v_severity_boxed_3036_ = lean_unbox(v_severity_3027_);
v_isSilent_boxed_3037_ = lean_unbox(v_isSilent_3028_);
v_res_3038_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3026_, v_severity_boxed_3036_, v_isSilent_boxed_3037_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
uint8_t v___x_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = 1;
v___x_3048_ = 0;
v___x_3049_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3039_, v___x_3047_, v___x_3048_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_options_3062_; uint8_t v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v_options_3062_ = lean_ctor_get(v___y_3060_, 2);
v___x_3063_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_3062_, v_opt_3059_);
v___x_3064_ = lean_box(v___x_3063_);
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3066_, v___y_3067_);
lean_dec_ref(v___y_3067_);
lean_dec_ref(v_opt_3066_);
return v_res_3069_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3072_ = l_Lean_stringToMessageData(v___x_3071_);
return v___x_3072_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3075_ = l_Lean_stringToMessageData(v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; lean_object* v_env_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3107_; 
v___x_3084_ = lean_st_ref_get(v___y_3082_);
v_env_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc_ref(v_env_3085_);
lean_dec(v___x_3084_);
v___x_3086_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3087_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3086_, v___y_3081_);
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3090_ = v___x_3087_;
v_isShared_3091_ = v_isSharedCheck_3107_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3107_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
uint8_t v_isExporting_3097_; 
v_isExporting_3097_ = lean_ctor_get_uint8(v_env_3085_, sizeof(void*)*8);
lean_dec_ref(v_env_3085_);
if (v_isExporting_3097_ == 0)
{
lean_dec(v_a_3088_);
lean_dec(v_id_3076_);
goto v___jp_3092_;
}
else
{
uint8_t v___x_3098_; 
v___x_3098_ = l_Lean_isPrivateName(v_id_3076_);
if (v___x_3098_ == 0)
{
lean_dec(v_a_3088_);
lean_dec(v_id_3076_);
goto v___jp_3092_;
}
else
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_unbox(v_a_3088_);
lean_dec(v_a_3088_);
if (v___x_3099_ == 0)
{
lean_dec(v_id_3076_);
goto v___jp_3092_;
}
else
{
lean_object* v___x_3100_; uint8_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_del_object(v___x_3090_);
v___x_3100_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3101_ = 0;
v___x_3102_ = l_Lean_MessageData_ofConstName(v_id_3076_, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3100_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3103_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3105_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
return v___x_3106_;
}
}
}
v___jp_3092_:
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3093_ = lean_box(0);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3093_);
v___x_3095_ = v___x_3090_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3117_, uint8_t v_enableLog_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v___x_3126_; lean_object* v_env_3127_; lean_object* v_options_3128_; lean_object* v_currNamespace_3129_; lean_object* v_openDecls_3130_; lean_object* v___x_3131_; lean_object* v_env_3132_; lean_object* v_res_3133_; 
v___x_3126_ = lean_st_ref_get(v___y_3124_);
v_env_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc_ref(v_env_3127_);
lean_dec(v___x_3126_);
v_options_3128_ = lean_ctor_get(v___y_3123_, 2);
v_currNamespace_3129_ = lean_ctor_get(v___y_3123_, 6);
v_openDecls_3130_ = lean_ctor_get(v___y_3123_, 7);
v___x_3131_ = lean_st_ref_get(v___y_3124_);
v_env_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc_ref(v_env_3132_);
lean_dec(v___x_3131_);
lean_inc(v_openDecls_3130_);
lean_inc(v_currNamespace_3129_);
v_res_3133_ = l_Lean_ResolveName_resolveGlobalName(v_env_3127_, v_options_3128_, v_currNamespace_3129_, v_openDecls_3130_, v_id_3117_);
if (v_enableLog_3118_ == 0)
{
lean_object* v___x_3134_; 
lean_dec_ref(v_env_3132_);
v___x_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3134_, 0, v_res_3133_);
return v___x_3134_;
}
else
{
uint8_t v_isExporting_3135_; 
v_isExporting_3135_ = lean_ctor_get_uint8(v_env_3132_, sizeof(void*)*8);
lean_dec_ref(v_env_3132_);
if (v_isExporting_3135_ == 0)
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_res_3133_);
return v___x_3136_;
}
else
{
lean_object* v___x_3137_; 
v___x_3137_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3133_);
if (lean_obj_tag(v___x_3137_) == 1)
{
lean_object* v_val_3138_; lean_object* v_fst_3139_; lean_object* v___x_3140_; 
v_val_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_val_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v_fst_3139_ = lean_ctor_get(v_val_3138_, 0);
lean_inc(v_fst_3139_);
lean_dec(v_val_3138_);
v___x_3140_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3139_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v___x_3140_, 0);
lean_dec(v_unused_3148_);
v___x_3142_ = v___x_3140_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_dec(v___x_3140_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v_res_3133_);
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_res_3133_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec(v_res_3133_);
v_a_3149_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3140_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3140_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
else
{
lean_object* v___x_3157_; 
lean_dec(v___x_3137_);
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v_res_3133_);
return v___x_3157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3158_, lean_object* v_enableLog_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
uint8_t v_enableLog_boxed_3167_; lean_object* v_res_3168_; 
v_enableLog_boxed_3167_ = lean_unbox(v_enableLog_3159_);
v_res_3168_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3158_, v_enableLog_boxed_3167_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
if (lean_obj_tag(v_a_3169_) == 0)
{
lean_object* v___x_3171_; 
v___x_3171_ = l_List_reverse___redArg(v_a_3170_);
return v___x_3171_;
}
else
{
lean_object* v_head_3172_; lean_object* v_tail_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3184_; 
v_head_3172_ = lean_ctor_get(v_a_3169_, 0);
v_tail_3173_ = lean_ctor_get(v_a_3169_, 1);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_a_3169_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3175_ = v_a_3169_;
v_isShared_3176_ = v_isSharedCheck_3184_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_tail_3173_);
lean_inc(v_head_3172_);
lean_dec(v_a_3169_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3184_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v_snd_3177_; uint8_t v___x_3178_; 
v_snd_3177_ = lean_ctor_get(v_head_3172_, 1);
v___x_3178_ = l_List_isEmpty___redArg(v_snd_3177_);
if (v___x_3178_ == 0)
{
lean_del_object(v___x_3175_);
lean_dec(v_head_3172_);
v_a_3169_ = v_tail_3173_;
goto _start;
}
else
{
lean_object* v___x_3181_; 
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 1, v_a_3170_);
v___x_3181_ = v___x_3175_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_head_3172_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_a_3170_);
v___x_3181_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
v_a_3169_ = v_tail_3173_;
v_a_3170_ = v___x_3181_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3185_, lean_object* v_findLocalDecl_x3f_3186_, lean_object* v_n_3187_, lean_object* v_projs_3188_, uint8_t v_globalDeclFound_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___y_3198_; lean_object* v___y_3199_; uint8_t v_globalDeclFoundNext_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v_imported_3209_; lean_object* v_ctx_3210_; lean_object* v_scopes_3211_; lean_object* v_givenNameView_3212_; uint8_t v___y_3214_; 
v_imported_3209_ = lean_ctor_get(v_view_3185_, 1);
v_ctx_3210_ = lean_ctor_get(v_view_3185_, 2);
v_scopes_3211_ = lean_ctor_get(v_view_3185_, 3);
lean_inc(v_scopes_3211_);
lean_inc(v_ctx_3210_);
lean_inc(v_imported_3209_);
lean_inc(v_n_3187_);
v_givenNameView_3212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3212_, 0, v_n_3187_);
lean_ctor_set(v_givenNameView_3212_, 1, v_imported_3209_);
lean_ctor_set(v_givenNameView_3212_, 2, v_ctx_3210_);
lean_ctor_set(v_givenNameView_3212_, 3, v_scopes_3211_);
if (v_globalDeclFound_3189_ == 0)
{
v___y_3214_ = v_globalDeclFound_3189_;
goto v___jp_3213_;
}
else
{
uint8_t v___x_3249_; 
v___x_3249_ = l_List_isEmpty___redArg(v_projs_3188_);
if (v___x_3249_ == 0)
{
v___y_3214_ = v_globalDeclFound_3189_;
goto v___jp_3213_;
}
else
{
uint8_t v___x_3250_; 
v___x_3250_ = 0;
v___y_3214_ = v___x_3250_;
goto v___jp_3213_;
}
}
v___jp_3197_:
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___y_3199_);
lean_ctor_set(v___x_3207_, 1, v_projs_3188_);
v_n_3187_ = v___y_3198_;
v_projs_3188_ = v___x_3207_;
v_globalDeclFound_3189_ = v_globalDeclFoundNext_3200_;
v___y_3190_ = v___y_3201_;
v___y_3191_ = v___y_3202_;
v___y_3192_ = v___y_3203_;
v___y_3193_ = v___y_3204_;
v___y_3194_ = v___y_3205_;
v___y_3195_ = v___y_3206_;
goto _start;
}
v___jp_3213_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = lean_box(v___y_3214_);
lean_inc_ref(v_findLocalDecl_x3f_3186_);
lean_inc_ref(v_givenNameView_3212_);
v___x_3216_ = lean_apply_2(v_findLocalDecl_x3f_3186_, v_givenNameView_3212_, v___x_3215_);
if (lean_obj_tag(v___x_3216_) == 0)
{
if (lean_obj_tag(v_n_3187_) == 1)
{
if (v_globalDeclFound_3189_ == 0)
{
lean_object* v_pre_3217_; lean_object* v_str_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v_pre_3217_ = lean_ctor_get(v_n_3187_, 0);
lean_inc(v_pre_3217_);
v_str_3218_ = lean_ctor_get(v_n_3187_, 1);
lean_inc_ref(v_str_3218_);
lean_dec_ref_known(v_n_3187_, 2);
v___x_3219_ = l_Lean_MacroScopesView_review(v_givenNameView_3212_);
v___x_3220_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3219_, v_globalDeclFound_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3222_; lean_object* v_r_3223_; uint8_t v___x_3224_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v___x_3222_ = lean_box(0);
v_r_3223_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3221_, v___x_3222_);
v___x_3224_ = l_List_isEmpty___redArg(v_r_3223_);
lean_dec(v_r_3223_);
if (v___x_3224_ == 0)
{
uint8_t v_globalDeclFoundNext_3225_; 
v_globalDeclFoundNext_3225_ = 1;
v___y_3198_ = v_pre_3217_;
v___y_3199_ = v_str_3218_;
v_globalDeclFoundNext_3200_ = v_globalDeclFoundNext_3225_;
v___y_3201_ = v___y_3190_;
v___y_3202_ = v___y_3191_;
v___y_3203_ = v___y_3192_;
v___y_3204_ = v___y_3193_;
v___y_3205_ = v___y_3194_;
v___y_3206_ = v___y_3195_;
goto v___jp_3197_;
}
else
{
v___y_3198_ = v_pre_3217_;
v___y_3199_ = v_str_3218_;
v_globalDeclFoundNext_3200_ = v_globalDeclFound_3189_;
v___y_3201_ = v___y_3190_;
v___y_3202_ = v___y_3191_;
v___y_3203_ = v___y_3192_;
v___y_3204_ = v___y_3193_;
v___y_3205_ = v___y_3194_;
v___y_3206_ = v___y_3195_;
goto v___jp_3197_;
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref(v_str_3218_);
lean_dec(v_pre_3217_);
lean_dec(v_projs_3188_);
lean_dec_ref(v_findLocalDecl_x3f_3186_);
v_a_3226_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3220_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3220_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_pre_3234_; lean_object* v_str_3235_; 
lean_dec_ref_known(v_givenNameView_3212_, 4);
v_pre_3234_ = lean_ctor_get(v_n_3187_, 0);
lean_inc(v_pre_3234_);
v_str_3235_ = lean_ctor_get(v_n_3187_, 1);
lean_inc_ref(v_str_3235_);
lean_dec_ref_known(v_n_3187_, 2);
v___y_3198_ = v_pre_3234_;
v___y_3199_ = v_str_3235_;
v_globalDeclFoundNext_3200_ = v_globalDeclFound_3189_;
v___y_3201_ = v___y_3190_;
v___y_3202_ = v___y_3191_;
v___y_3203_ = v___y_3192_;
v___y_3204_ = v___y_3193_;
v___y_3205_ = v___y_3194_;
v___y_3206_ = v___y_3195_;
goto v___jp_3197_;
}
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_dec_ref_known(v_givenNameView_3212_, 4);
lean_dec(v_projs_3188_);
lean_dec(v_n_3187_);
lean_dec_ref(v_findLocalDecl_x3f_3186_);
v___x_3236_ = lean_box(0);
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
return v___x_3237_;
}
}
else
{
lean_object* v_val_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3248_; 
lean_dec_ref_known(v_givenNameView_3212_, 4);
lean_dec(v_n_3187_);
lean_dec_ref(v_findLocalDecl_x3f_3186_);
v_val_3238_ = lean_ctor_get(v___x_3216_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3240_ = v___x_3216_;
v_isShared_3241_ = v_isSharedCheck_3248_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_val_3238_);
lean_dec(v___x_3216_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3248_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3242_ = l_Lean_LocalDecl_toExpr(v_val_3238_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3242_);
lean_ctor_set(v___x_3243_, 1, v_projs_3188_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 0, v___x_3243_);
v___x_3245_ = v___x_3240_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
return v___x_3246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3251_, lean_object* v_findLocalDecl_x3f_3252_, lean_object* v_n_3253_, lean_object* v_projs_3254_, lean_object* v_globalDeclFound_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
uint8_t v_globalDeclFound_boxed_3263_; lean_object* v_res_3264_; 
v_globalDeclFound_boxed_3263_ = lean_unbox(v_globalDeclFound_3255_);
v_res_3264_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3251_, v_findLocalDecl_x3f_3252_, v_n_3253_, v_projs_3254_, v_globalDeclFound_boxed_3263_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec_ref(v_view_3251_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3265_, lean_object* v_givenName_3266_, lean_object* v_as_3267_, lean_object* v_i_3268_){
_start:
{
lean_object* v_zero_3269_; uint8_t v_isZero_3270_; 
v_zero_3269_ = lean_unsigned_to_nat(0u);
v_isZero_3270_ = lean_nat_dec_eq(v_i_3268_, v_zero_3269_);
if (v_isZero_3270_ == 1)
{
lean_object* v___x_3271_; 
lean_dec(v_i_3268_);
v___x_3271_ = lean_box(0);
return v___x_3271_;
}
else
{
lean_object* v_one_3272_; lean_object* v_n_3273_; lean_object* v___y_3275_; lean_object* v___x_3277_; 
v_one_3272_ = lean_unsigned_to_nat(1u);
v_n_3273_ = lean_nat_sub(v_i_3268_, v_one_3272_);
lean_dec(v_i_3268_);
v___x_3277_ = lean_array_fget_borrowed(v_as_3267_, v_n_3273_);
if (lean_obj_tag(v___x_3277_) == 0)
{
v___y_3275_ = v___x_3277_;
goto v___jp_3274_;
}
else
{
lean_object* v_val_3278_; uint8_t v___x_3279_; 
v_val_3278_ = lean_ctor_get(v___x_3277_, 0);
v___x_3279_ = l_Lean_LocalDecl_isAuxDecl(v_val_3278_);
if (v___x_3279_ == 0)
{
v___y_3275_ = v_localDecl_x3f_3265_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3280_; uint8_t v___x_3281_; 
v___x_3280_ = l_Lean_LocalDecl_userName(v_val_3278_);
v___x_3281_ = lean_name_eq(v___x_3280_, v_givenName_3266_);
lean_dec(v___x_3280_);
if (v___x_3281_ == 0)
{
v_i_3268_ = v_n_3273_;
goto _start;
}
else
{
v___y_3275_ = v___x_3277_;
goto v___jp_3274_;
}
}
}
v___jp_3274_:
{
if (lean_obj_tag(v___y_3275_) == 0)
{
v_i_3268_ = v_n_3273_;
goto _start;
}
else
{
lean_dec(v_n_3273_);
lean_inc_ref(v___y_3275_);
return v___y_3275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3283_, lean_object* v_givenName_3284_, lean_object* v_as_3285_, lean_object* v_i_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3283_, v_givenName_3284_, v_as_3285_, v_i_3286_);
lean_dec_ref(v_as_3285_);
lean_dec(v_givenName_3284_);
lean_dec(v_localDecl_x3f_3283_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3288_, lean_object* v_givenName_3289_, lean_object* v_as_3290_, lean_object* v_i_3291_){
_start:
{
lean_object* v_zero_3292_; uint8_t v_isZero_3293_; 
v_zero_3292_ = lean_unsigned_to_nat(0u);
v_isZero_3293_ = lean_nat_dec_eq(v_i_3291_, v_zero_3292_);
if (v_isZero_3293_ == 1)
{
lean_object* v___x_3294_; 
lean_dec(v_i_3291_);
v___x_3294_ = lean_box(0);
return v___x_3294_;
}
else
{
lean_object* v_one_3295_; lean_object* v_n_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_one_3295_ = lean_unsigned_to_nat(1u);
v_n_3296_ = lean_nat_sub(v_i_3291_, v_one_3295_);
lean_dec(v_i_3291_);
v___x_3297_ = lean_array_fget_borrowed(v_as_3290_, v_n_3296_);
v___x_3298_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3288_, v_givenName_3289_, v___x_3297_);
if (lean_obj_tag(v___x_3298_) == 0)
{
v_i_3291_ = v_n_3296_;
goto _start;
}
else
{
lean_dec(v_n_3296_);
return v___x_3298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3300_, lean_object* v_givenName_3301_, lean_object* v_x_3302_){
_start:
{
if (lean_obj_tag(v_x_3302_) == 0)
{
lean_object* v_cs_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v_cs_3303_ = lean_ctor_get(v_x_3302_, 0);
v___x_3304_ = lean_array_get_size(v_cs_3303_);
v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3300_, v_givenName_3301_, v_cs_3303_, v___x_3304_);
return v___x_3305_;
}
else
{
lean_object* v_vs_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_vs_3306_ = lean_ctor_get(v_x_3302_, 0);
v___x_3307_ = lean_array_get_size(v_vs_3306_);
v___x_3308_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3300_, v_givenName_3301_, v_vs_3306_, v___x_3307_);
return v___x_3308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3309_, lean_object* v_givenName_3310_, lean_object* v_x_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3309_, v_givenName_3310_, v_x_3311_);
lean_dec_ref(v_x_3311_);
lean_dec(v_givenName_3310_);
lean_dec(v_localDecl_x3f_3309_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3313_, lean_object* v_givenName_3314_, lean_object* v_as_3315_, lean_object* v_i_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3313_, v_givenName_3314_, v_as_3315_, v_i_3316_);
lean_dec_ref(v_as_3315_);
lean_dec(v_givenName_3314_);
lean_dec(v_localDecl_x3f_3313_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3318_, lean_object* v_givenName_3319_, lean_object* v_t_3320_){
_start:
{
lean_object* v_root_3321_; lean_object* v_tail_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v_root_3321_ = lean_ctor_get(v_t_3320_, 0);
v_tail_3322_ = lean_ctor_get(v_t_3320_, 1);
v___x_3323_ = lean_array_get_size(v_tail_3322_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3318_, v_givenName_3319_, v_tail_3322_, v___x_3323_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3318_, v_givenName_3319_, v_root_3321_);
return v___x_3325_;
}
else
{
return v___x_3324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3326_, lean_object* v_givenName_3327_, lean_object* v_t_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3326_, v_givenName_3327_, v_t_3328_);
lean_dec_ref(v_t_3328_);
lean_dec(v_givenName_3327_);
lean_dec(v_localDecl_x3f_3326_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3330_, lean_object* v_k_3331_){
_start:
{
if (lean_obj_tag(v_t_3330_) == 0)
{
lean_object* v_k_3332_; lean_object* v_v_3333_; lean_object* v_l_3334_; lean_object* v_r_3335_; uint8_t v___x_3336_; 
v_k_3332_ = lean_ctor_get(v_t_3330_, 1);
v_v_3333_ = lean_ctor_get(v_t_3330_, 2);
v_l_3334_ = lean_ctor_get(v_t_3330_, 3);
v_r_3335_ = lean_ctor_get(v_t_3330_, 4);
v___x_3336_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3331_, v_k_3332_);
switch(v___x_3336_)
{
case 0:
{
v_t_3330_ = v_l_3334_;
goto _start;
}
case 1:
{
lean_object* v___x_3338_; 
lean_inc(v_v_3333_);
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v_v_3333_);
return v___x_3338_;
}
default: 
{
v_t_3330_ = v_r_3335_;
goto _start;
}
}
}
else
{
lean_object* v___x_3340_; 
v___x_3340_ = lean_box(0);
return v___x_3340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3341_, lean_object* v_k_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3341_, v_k_3342_);
lean_dec(v_k_3342_);
lean_dec(v_t_3341_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3344_, lean_object* v_givenName_3345_){
_start:
{
lean_object* v___x_3346_; uint8_t v___x_3347_; 
v___x_3346_ = l_Lean_LocalDecl_userName(v_localDecl_3344_);
v___x_3347_ = lean_name_eq(v___x_3346_, v_givenName_3345_);
lean_dec(v___x_3346_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; 
lean_dec_ref(v_localDecl_3344_);
v___x_3348_ = lean_box(0);
return v___x_3348_;
}
else
{
lean_object* v___x_3349_; 
v___x_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_localDecl_3344_);
return v___x_3349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3350_, lean_object* v_givenName_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3350_, v_givenName_3351_);
lean_dec(v_givenName_3351_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3353_, uint8_t v_skipAuxDecl_3354_, lean_object* v_auxDeclToFullName_3355_, lean_object* v___x_3356_, lean_object* v_givenNameView_3357_, lean_object* v_as_3358_, lean_object* v_i_3359_){
_start:
{
lean_object* v_zero_3360_; uint8_t v_isZero_3361_; 
v_zero_3360_ = lean_unsigned_to_nat(0u);
v_isZero_3361_ = lean_nat_dec_eq(v_i_3359_, v_zero_3360_);
if (v_isZero_3361_ == 1)
{
lean_object* v___x_3362_; 
lean_dec(v_i_3359_);
lean_dec_ref(v_givenNameView_3357_);
lean_dec(v___x_3356_);
v___x_3362_ = lean_box(0);
return v___x_3362_;
}
else
{
lean_object* v_one_3363_; lean_object* v_n_3364_; lean_object* v___y_3366_; lean_object* v___x_3368_; 
v_one_3363_ = lean_unsigned_to_nat(1u);
v_n_3364_ = lean_nat_sub(v_i_3359_, v_one_3363_);
lean_dec(v_i_3359_);
v___x_3368_ = lean_array_fget_borrowed(v_as_3358_, v_n_3364_);
if (lean_obj_tag(v___x_3368_) == 0)
{
v___y_3366_ = v___x_3368_;
goto v___jp_3365_;
}
else
{
lean_object* v_val_3369_; uint8_t v___x_3370_; 
v_val_3369_ = lean_ctor_get(v___x_3368_, 0);
v___x_3370_ = l_Lean_LocalDecl_isAuxDecl(v_val_3369_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; 
lean_inc(v_val_3369_);
v___x_3371_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3369_, v_givenName_3353_);
v___y_3366_ = v___x_3371_;
goto v___jp_3365_;
}
else
{
if (v_skipAuxDecl_3354_ == 0)
{
if (v___x_3370_ == 0)
{
v_i_3359_ = v_n_3364_;
goto _start;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = l_Lean_LocalDecl_fvarId(v_val_3369_);
v___x_3374_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3355_, v___x_3373_);
lean_dec(v___x_3373_);
if (lean_obj_tag(v___x_3374_) == 1)
{
lean_object* v_val_3375_; lean_object* v_fullDeclView_3376_; lean_object* v___y_3378_; lean_object* v_name_3399_; lean_object* v___x_3400_; 
v_val_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v_fullDeclView_3376_ = l_Lean_extractMacroScopes(v_val_3375_);
v_name_3399_ = lean_ctor_get(v_fullDeclView_3376_, 0);
lean_inc_n(v_name_3399_, 2);
v___x_3400_ = l_Lean_privateToUserName_x3f(v_name_3399_);
if (lean_obj_tag(v___x_3400_) == 0)
{
v___y_3378_ = v_name_3399_;
goto v___jp_3377_;
}
else
{
lean_object* v_val_3401_; 
lean_dec(v_name_3399_);
v_val_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v___y_3378_ = v_val_3401_;
goto v___jp_3377_;
}
v___jp_3377_:
{
lean_object* v_imported_3379_; lean_object* v_ctx_3380_; lean_object* v_scopes_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3397_; 
v_imported_3379_ = lean_ctor_get(v_fullDeclView_3376_, 1);
v_ctx_3380_ = lean_ctor_get(v_fullDeclView_3376_, 2);
v_scopes_3381_ = lean_ctor_get(v_fullDeclView_3376_, 3);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_fullDeclView_3376_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; 
v_unused_3398_ = lean_ctor_get(v_fullDeclView_3376_, 0);
lean_dec(v_unused_3398_);
v___x_3383_ = v_fullDeclView_3376_;
v_isShared_3384_ = v_isSharedCheck_3397_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_scopes_3381_);
lean_inc(v_ctx_3380_);
lean_inc(v_imported_3379_);
lean_dec(v_fullDeclView_3376_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3397_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_fullDeclView_3386_; 
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___y_3378_);
v_fullDeclView_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___y_3378_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_imported_3379_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v_ctx_3380_);
lean_ctor_set(v_reuseFailAlloc_3396_, 3, v_scopes_3381_);
v_fullDeclView_3386_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
lean_object* v_fullDeclName_3387_; uint8_t v___x_3388_; 
lean_inc_ref(v_fullDeclView_3386_);
v_fullDeclName_3387_ = l_Lean_MacroScopesView_review(v_fullDeclView_3386_);
v___x_3388_ = l_Lean_Name_isPrefixOf(v___x_3356_, v_fullDeclName_3387_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; 
lean_dec_ref(v_fullDeclView_3386_);
lean_inc(v___x_3356_);
lean_inc_ref(v_givenNameView_3357_);
lean_inc(v_val_3369_);
v___x_3389_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3369_, v_givenNameView_3357_, v_fullDeclName_3387_, v___x_3356_);
lean_dec(v_fullDeclName_3387_);
v___y_3366_ = v___x_3389_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3390_; lean_object* v_localDeclNameView_3391_; uint8_t v___x_3392_; 
lean_dec(v_fullDeclName_3387_);
v___x_3390_ = l_Lean_LocalDecl_userName(v_val_3369_);
v_localDeclNameView_3391_ = l_Lean_extractMacroScopes(v___x_3390_);
v___x_3392_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3391_, v_givenNameView_3357_);
lean_dec_ref(v_localDeclNameView_3391_);
if (v___x_3392_ == 0)
{
lean_dec_ref(v_fullDeclView_3386_);
v_i_3359_ = v_n_3364_;
goto _start;
}
else
{
uint8_t v___x_3394_; 
v___x_3394_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3357_, v_fullDeclView_3386_);
lean_dec_ref(v_fullDeclView_3386_);
if (v___x_3394_ == 0)
{
v_i_3359_ = v_n_3364_;
goto _start;
}
else
{
lean_inc_ref(v___x_3368_);
v___y_3366_ = v___x_3368_;
goto v___jp_3365_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3402_; 
lean_dec(v___x_3374_);
lean_inc(v_val_3369_);
v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3369_, v_givenName_3353_);
v___y_3366_ = v___x_3402_;
goto v___jp_3365_;
}
}
}
else
{
v_i_3359_ = v_n_3364_;
goto _start;
}
}
}
v___jp_3365_:
{
if (lean_obj_tag(v___y_3366_) == 0)
{
v_i_3359_ = v_n_3364_;
goto _start;
}
else
{
lean_dec(v_n_3364_);
lean_dec_ref(v_givenNameView_3357_);
lean_dec(v___x_3356_);
return v___y_3366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3404_, lean_object* v_skipAuxDecl_3405_, lean_object* v_auxDeclToFullName_3406_, lean_object* v___x_3407_, lean_object* v_givenNameView_3408_, lean_object* v_as_3409_, lean_object* v_i_3410_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3411_; lean_object* v_res_3412_; 
v_skipAuxDecl_boxed_3411_ = lean_unbox(v_skipAuxDecl_3405_);
v_res_3412_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3404_, v_skipAuxDecl_boxed_3411_, v_auxDeclToFullName_3406_, v___x_3407_, v_givenNameView_3408_, v_as_3409_, v_i_3410_);
lean_dec_ref(v_as_3409_);
lean_dec(v_auxDeclToFullName_3406_);
lean_dec(v_givenName_3404_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3413_, uint8_t v_skipAuxDecl_3414_, lean_object* v_auxDeclToFullName_3415_, lean_object* v___x_3416_, lean_object* v_givenNameView_3417_, lean_object* v_as_3418_, lean_object* v_i_3419_){
_start:
{
lean_object* v_zero_3420_; uint8_t v_isZero_3421_; 
v_zero_3420_ = lean_unsigned_to_nat(0u);
v_isZero_3421_ = lean_nat_dec_eq(v_i_3419_, v_zero_3420_);
if (v_isZero_3421_ == 1)
{
lean_object* v___x_3422_; 
lean_dec(v_i_3419_);
lean_dec_ref(v_givenNameView_3417_);
lean_dec(v___x_3416_);
v___x_3422_ = lean_box(0);
return v___x_3422_;
}
else
{
lean_object* v_one_3423_; lean_object* v_n_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_one_3423_ = lean_unsigned_to_nat(1u);
v_n_3424_ = lean_nat_sub(v_i_3419_, v_one_3423_);
lean_dec(v_i_3419_);
v___x_3425_ = lean_array_fget_borrowed(v_as_3418_, v_n_3424_);
lean_inc_ref(v_givenNameView_3417_);
lean_inc(v___x_3416_);
v___x_3426_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3413_, v_skipAuxDecl_3414_, v_auxDeclToFullName_3415_, v___x_3416_, v_givenNameView_3417_, v___x_3425_);
if (lean_obj_tag(v___x_3426_) == 0)
{
v_i_3419_ = v_n_3424_;
goto _start;
}
else
{
lean_dec(v_n_3424_);
lean_dec_ref(v_givenNameView_3417_);
lean_dec(v___x_3416_);
return v___x_3426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3428_, uint8_t v_skipAuxDecl_3429_, lean_object* v_auxDeclToFullName_3430_, lean_object* v___x_3431_, lean_object* v_givenNameView_3432_, lean_object* v_x_3433_){
_start:
{
if (lean_obj_tag(v_x_3433_) == 0)
{
lean_object* v_cs_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v_cs_3434_ = lean_ctor_get(v_x_3433_, 0);
v___x_3435_ = lean_array_get_size(v_cs_3434_);
v___x_3436_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3428_, v_skipAuxDecl_3429_, v_auxDeclToFullName_3430_, v___x_3431_, v_givenNameView_3432_, v_cs_3434_, v___x_3435_);
return v___x_3436_;
}
else
{
lean_object* v_vs_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v_vs_3437_ = lean_ctor_get(v_x_3433_, 0);
v___x_3438_ = lean_array_get_size(v_vs_3437_);
v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3428_, v_skipAuxDecl_3429_, v_auxDeclToFullName_3430_, v___x_3431_, v_givenNameView_3432_, v_vs_3437_, v___x_3438_);
return v___x_3439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3440_, lean_object* v_skipAuxDecl_3441_, lean_object* v_auxDeclToFullName_3442_, lean_object* v___x_3443_, lean_object* v_givenNameView_3444_, lean_object* v_x_3445_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3446_; lean_object* v_res_3447_; 
v_skipAuxDecl_boxed_3446_ = lean_unbox(v_skipAuxDecl_3441_);
v_res_3447_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3440_, v_skipAuxDecl_boxed_3446_, v_auxDeclToFullName_3442_, v___x_3443_, v_givenNameView_3444_, v_x_3445_);
lean_dec_ref(v_x_3445_);
lean_dec(v_auxDeclToFullName_3442_);
lean_dec(v_givenName_3440_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3448_, lean_object* v_skipAuxDecl_3449_, lean_object* v_auxDeclToFullName_3450_, lean_object* v___x_3451_, lean_object* v_givenNameView_3452_, lean_object* v_as_3453_, lean_object* v_i_3454_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3455_; lean_object* v_res_3456_; 
v_skipAuxDecl_boxed_3455_ = lean_unbox(v_skipAuxDecl_3449_);
v_res_3456_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3448_, v_skipAuxDecl_boxed_3455_, v_auxDeclToFullName_3450_, v___x_3451_, v_givenNameView_3452_, v_as_3453_, v_i_3454_);
lean_dec_ref(v_as_3453_);
lean_dec(v_auxDeclToFullName_3450_);
lean_dec(v_givenName_3448_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3457_, uint8_t v_skipAuxDecl_3458_, lean_object* v_auxDeclToFullName_3459_, lean_object* v___x_3460_, lean_object* v_givenNameView_3461_, lean_object* v_t_3462_){
_start:
{
lean_object* v_root_3463_; lean_object* v_tail_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v_root_3463_ = lean_ctor_get(v_t_3462_, 0);
v_tail_3464_ = lean_ctor_get(v_t_3462_, 1);
v___x_3465_ = lean_array_get_size(v_tail_3464_);
lean_inc_ref(v_givenNameView_3461_);
lean_inc(v___x_3460_);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3457_, v_skipAuxDecl_3458_, v_auxDeclToFullName_3459_, v___x_3460_, v_givenNameView_3461_, v_tail_3464_, v___x_3465_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3467_; 
v___x_3467_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3457_, v_skipAuxDecl_3458_, v_auxDeclToFullName_3459_, v___x_3460_, v_givenNameView_3461_, v_root_3463_);
return v___x_3467_;
}
else
{
lean_dec_ref(v_givenNameView_3461_);
lean_dec(v___x_3460_);
return v___x_3466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3468_, lean_object* v_skipAuxDecl_3469_, lean_object* v_auxDeclToFullName_3470_, lean_object* v___x_3471_, lean_object* v_givenNameView_3472_, lean_object* v_t_3473_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3474_; lean_object* v_res_3475_; 
v_skipAuxDecl_boxed_3474_ = lean_unbox(v_skipAuxDecl_3469_);
v_res_3475_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3468_, v_skipAuxDecl_boxed_3474_, v_auxDeclToFullName_3470_, v___x_3471_, v_givenNameView_3472_, v_t_3473_);
lean_dec_ref(v_t_3473_);
lean_dec(v_auxDeclToFullName_3470_);
lean_dec(v_givenName_3468_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3476_, lean_object* v_currNamespace_3477_, lean_object* v_decls_3478_, lean_object* v_givenNameView_3479_, uint8_t v_skipAuxDecl_3480_){
_start:
{
lean_object* v_givenName_3481_; lean_object* v_localDecl_x3f_3482_; 
lean_inc_ref(v_givenNameView_3479_);
v_givenName_3481_ = l_Lean_MacroScopesView_review(v_givenNameView_3479_);
v_localDecl_x3f_3482_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3481_, v_skipAuxDecl_3480_, v_auxDeclToFullName_3476_, v_currNamespace_3477_, v_givenNameView_3479_, v_decls_3478_);
if (lean_obj_tag(v_localDecl_x3f_3482_) == 0)
{
if (v_skipAuxDecl_3480_ == 0)
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3482_, v_givenName_3481_, v_decls_3478_);
lean_dec(v_givenName_3481_);
return v___x_3483_;
}
else
{
lean_dec(v_givenName_3481_);
return v_localDecl_x3f_3482_;
}
}
else
{
lean_dec(v_givenName_3481_);
return v_localDecl_x3f_3482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3484_, lean_object* v_currNamespace_3485_, lean_object* v_decls_3486_, lean_object* v_givenNameView_3487_, lean_object* v_skipAuxDecl_3488_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3489_; lean_object* v_res_3490_; 
v_skipAuxDecl_boxed_3489_ = lean_unbox(v_skipAuxDecl_3488_);
v_res_3490_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3484_, v_currNamespace_3485_, v_decls_3486_, v_givenNameView_3487_, v_skipAuxDecl_boxed_3489_);
lean_dec_ref(v_decls_3486_);
lean_dec(v_auxDeclToFullName_3484_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v_lctx_3499_; lean_object* v_decls_3500_; lean_object* v_auxDeclToFullName_3501_; lean_object* v_currNamespace_3502_; lean_object* v_view_3503_; lean_object* v_name_3504_; lean_object* v_findLocalDecl_x3f_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; lean_object* v___x_3508_; 
v_lctx_3499_ = lean_ctor_get(v___y_3494_, 2);
v_decls_3500_ = lean_ctor_get(v_lctx_3499_, 1);
v_auxDeclToFullName_3501_ = lean_ctor_get(v_lctx_3499_, 2);
v_currNamespace_3502_ = lean_ctor_get(v___y_3496_, 6);
v_view_3503_ = l_Lean_extractMacroScopes(v_n_3491_);
v_name_3504_ = lean_ctor_get(v_view_3503_, 0);
lean_inc(v_name_3504_);
lean_inc_ref(v_decls_3500_);
lean_inc(v_currNamespace_3502_);
lean_inc(v_auxDeclToFullName_3501_);
v_findLocalDecl_x3f_3505_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3505_, 0, v_auxDeclToFullName_3501_);
lean_closure_set(v_findLocalDecl_x3f_3505_, 1, v_currNamespace_3502_);
lean_closure_set(v_findLocalDecl_x3f_3505_, 2, v_decls_3500_);
v___x_3506_ = lean_box(0);
v___x_3507_ = 0;
v___x_3508_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3503_, v_findLocalDecl_x3f_3505_, v_name_3504_, v___x_3506_, v___x_3507_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
lean_dec_ref(v_view_3503_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3518_, lean_object* v_b_3519_){
_start:
{
if (lean_obj_tag(v_as_x27_3518_) == 0)
{
lean_object* v___x_3521_; 
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v_b_3519_);
return v___x_3521_;
}
else
{
lean_object* v_head_3522_; lean_object* v_tail_3523_; lean_object* v_config_3524_; lean_object* v_extensions_3525_; lean_object* v_extra_3526_; lean_object* v_extraInj_3527_; lean_object* v_extraFacts_3528_; lean_object* v_symPrios_3529_; lean_object* v_norm_3530_; lean_object* v_normProcs_3531_; lean_object* v_anchorRefs_x3f_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3541_; 
v_head_3522_ = lean_ctor_get(v_as_x27_3518_, 0);
v_tail_3523_ = lean_ctor_get(v_as_x27_3518_, 1);
v_config_3524_ = lean_ctor_get(v_b_3519_, 0);
v_extensions_3525_ = lean_ctor_get(v_b_3519_, 1);
v_extra_3526_ = lean_ctor_get(v_b_3519_, 2);
v_extraInj_3527_ = lean_ctor_get(v_b_3519_, 3);
v_extraFacts_3528_ = lean_ctor_get(v_b_3519_, 4);
v_symPrios_3529_ = lean_ctor_get(v_b_3519_, 5);
v_norm_3530_ = lean_ctor_get(v_b_3519_, 6);
v_normProcs_3531_ = lean_ctor_get(v_b_3519_, 7);
v_anchorRefs_x3f_3532_ = lean_ctor_get(v_b_3519_, 8);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_b_3519_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3534_ = v_b_3519_;
v_isShared_3535_ = v_isSharedCheck_3541_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_anchorRefs_x3f_3532_);
lean_inc(v_normProcs_3531_);
lean_inc(v_norm_3530_);
lean_inc(v_symPrios_3529_);
lean_inc(v_extraFacts_3528_);
lean_inc(v_extraInj_3527_);
lean_inc(v_extra_3526_);
lean_inc(v_extensions_3525_);
lean_inc(v_config_3524_);
lean_dec(v_b_3519_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3541_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3536_; lean_object* v___x_3538_; 
lean_inc(v_head_3522_);
v___x_3536_ = l_Lean_PersistentArray_push___redArg(v_extra_3526_, v_head_3522_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 2, v___x_3536_);
v___x_3538_ = v___x_3534_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_config_3524_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_extensions_3525_);
lean_ctor_set(v_reuseFailAlloc_3540_, 2, v___x_3536_);
lean_ctor_set(v_reuseFailAlloc_3540_, 3, v_extraInj_3527_);
lean_ctor_set(v_reuseFailAlloc_3540_, 4, v_extraFacts_3528_);
lean_ctor_set(v_reuseFailAlloc_3540_, 5, v_symPrios_3529_);
lean_ctor_set(v_reuseFailAlloc_3540_, 6, v_norm_3530_);
lean_ctor_set(v_reuseFailAlloc_3540_, 7, v_normProcs_3531_);
lean_ctor_set(v_reuseFailAlloc_3540_, 8, v_anchorRefs_x3f_3532_);
v___x_3538_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
v_as_x27_3518_ = v_tail_3523_;
v_b_3519_ = v___x_3538_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3542_, lean_object* v_b_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3542_, v_b_3543_);
lean_dec(v_as_x27_3542_);
return v_res_3545_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3548_ = l_Lean_stringToMessageData(v___x_3547_);
return v___x_3548_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3551_ = l_Lean_stringToMessageData(v___x_3550_);
return v___x_3551_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3554_ = l_Lean_stringToMessageData(v___x_3553_);
return v___x_3554_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3557_ = l_Lean_stringToMessageData(v___x_3556_);
return v___x_3557_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3560_ = l_Lean_stringToMessageData(v___x_3559_);
return v___x_3560_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3563_ = l_Lean_stringToMessageData(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3566_ = l_Lean_stringToMessageData(v___x_3565_);
return v___x_3566_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3569_ = l_Lean_stringToMessageData(v___x_3568_);
return v___x_3569_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3572_ = l_Lean_stringToMessageData(v___x_3571_);
return v___x_3572_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3575_ = l_Lean_stringToMessageData(v___x_3574_);
return v___x_3575_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3578_ = l_Lean_stringToMessageData(v___x_3577_);
return v___x_3578_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3581_ = l_Lean_stringToMessageData(v___x_3580_);
return v___x_3581_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3584_ = l_Lean_stringToMessageData(v___x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3585_, lean_object* v_p_3586_, lean_object* v_mod_x3f_3587_, lean_object* v_id_3588_, uint8_t v_minIndexable_3589_, uint8_t v_only_3590_, uint8_t v_incremental_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v___y_3600_; uint8_t v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3712_; uint8_t v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v_a_3774_; lean_object* v___y_4019_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = lean_box(0);
lean_inc(v_id_3588_);
v___x_4031_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3588_, v___x_4030_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v_a_3774_ = v_a_4032_;
goto v___jp_3773_;
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4108_; 
v_a_4033_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4035_ = v___x_4031_;
v_isShared_4036_ = v_isSharedCheck_4108_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4031_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4108_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4037_; uint8_t v___y_4039_; uint8_t v___x_4106_; 
v___x_4037_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4106_ = l_Lean_Exception_isInterrupt(v_a_4033_);
if (v___x_4106_ == 0)
{
uint8_t v___x_4107_; 
lean_inc(v_a_4033_);
v___x_4107_ = l_Lean_Exception_isRuntime(v_a_4033_);
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
lean_del_object(v___x_4035_);
v___x_4040_ = l_Lean_TSyntax_getId(v_id_3588_);
lean_inc(v___x_4040_);
v___x_4041_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4040_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___x_4041_, 1);
if (lean_obj_tag(v_a_4042_) == 0)
{
lean_object* v___x_4043_; 
v___x_4043_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4040_, v_a_3596_, v_a_3597_);
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
lean_dec(v_a_4033_);
if (lean_obj_tag(v_mod_x3f_3587_) == 1)
{
lean_object* v_val_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec_ref_known(v_a_4044_, 1);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v_val_4048_ = lean_ctor_get(v_mod_x3f_3587_, 0);
lean_inc(v_val_4048_);
lean_dec_ref_known(v_mod_x3f_3587_, 1);
v___x_4049_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4050_ = l_Lean_MessageData_ofName(v___x_4040_);
v___x_4051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4049_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4051_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4048_, v___x_4053_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
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
lean_dec_ref_known(v_a_4044_, 1);
v___x_4064_ = lean_box(0);
lean_inc_ref(v_params_3585_);
v___x_4065_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3585_, v_val_4063_, v___x_4037_, v___x_4064_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
lean_dec(v_val_4063_);
v___y_4019_ = v___x_4065_;
goto v___jp_4018_;
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
lean_dec(v_a_4033_);
v___x_4068_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3585_, v_p_3586_, v_mod_x3f_3587_, v_id_3588_, v_minIndexable_3589_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
return v___x_4068_;
}
else
{
lean_object* v___x_4070_; 
lean_dec(v_id_3588_);
lean_dec(v_mod_x3f_3587_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set_tag(v___x_4046_, 1);
lean_ctor_set(v___x_4046_, 0, v_a_4033_);
v___x_4070_ = v___x_4046_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4033_);
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
lean_dec(v_a_4033_);
lean_dec(v_id_3588_);
lean_dec(v_mod_x3f_3587_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
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
lean_dec_ref_known(v_a_4042_, 1);
lean_dec(v___x_4040_);
lean_dec(v_a_4033_);
lean_dec(v_mod_x3f_3587_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v___x_4081_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3588_);
v___x_4082_ = l_Lean_MessageData_ofSyntax(v_id_3588_);
v___x_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_4085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4083_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
v___x_4086_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3588_, v___x_4085_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
lean_dec(v_id_3588_);
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
lean_dec(v_a_4033_);
lean_dec(v_id_3588_);
lean_dec(v_mod_x3f_3587_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
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
lean_dec(v_id_3588_);
lean_dec(v_mod_x3f_3587_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
if (v_isShared_4036_ == 0)
{
v___x_4104_ = v___x_4035_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4033_);
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
v___jp_3599_:
{
uint8_t v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = 0;
lean_inc(v___y_3600_);
v___x_3609_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3600_, v___x_3608_, v___y_3606_, v___y_3607_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
if (lean_obj_tag(v_a_3610_) == 1)
{
lean_object* v_val_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
lean_dec(v___y_3600_);
v_val_3611_ = lean_ctor_get(v_a_3610_, 0);
lean_inc_n(v_val_3611_, 2);
lean_dec_ref_known(v_a_3610_, 1);
v___x_3612_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3585_, v_val_3611_, v___x_3608_);
v___x_3613_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3611_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3624_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3616_ = v___x_3613_;
v_isShared_3617_ = v_isSharedCheck_3624_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3613_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3624_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
if (lean_obj_tag(v_a_3614_) == 1)
{
lean_object* v_val_3618_; lean_object* v_ctors_3619_; lean_object* v___x_3620_; 
lean_del_object(v___x_3616_);
v_val_3618_ = lean_ctor_get(v_a_3614_, 0);
lean_inc(v_val_3618_);
lean_dec_ref_known(v_a_3614_, 1);
v_ctors_3619_ = lean_ctor_get(v_val_3618_, 4);
lean_inc(v_ctors_3619_);
lean_dec(v_val_3618_);
v___x_3620_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3586_, v_id_3588_, v_minIndexable_3589_, v_ctors_3619_, v___x_3612_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec(v_ctors_3619_);
lean_dec(v_p_3586_);
return v___x_3620_;
}
else
{
lean_object* v___x_3622_; 
lean_dec(v_a_3614_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3612_);
v___x_3622_ = v___x_3616_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3612_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec_ref(v___x_3612_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
v_a_3625_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3613_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3613_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
else
{
lean_object* v_fileName_3633_; lean_object* v_fileMap_3634_; lean_object* v_options_3635_; lean_object* v_currRecDepth_3636_; lean_object* v_maxRecDepth_3637_; lean_object* v_ref_3638_; lean_object* v_currNamespace_3639_; lean_object* v_openDecls_3640_; lean_object* v_initHeartbeats_3641_; lean_object* v_maxHeartbeats_3642_; lean_object* v_quotContext_3643_; lean_object* v_currMacroScope_3644_; uint8_t v_diag_3645_; lean_object* v_cancelTk_x3f_3646_; uint8_t v_suppressElabErrors_3647_; lean_object* v_inheritedTraceOptions_3648_; lean_object* v___x_3649_; lean_object* v_ref_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
lean_dec(v_a_3610_);
v_fileName_3633_ = lean_ctor_get(v___y_3606_, 0);
v_fileMap_3634_ = lean_ctor_get(v___y_3606_, 1);
v_options_3635_ = lean_ctor_get(v___y_3606_, 2);
v_currRecDepth_3636_ = lean_ctor_get(v___y_3606_, 3);
v_maxRecDepth_3637_ = lean_ctor_get(v___y_3606_, 4);
v_ref_3638_ = lean_ctor_get(v___y_3606_, 5);
v_currNamespace_3639_ = lean_ctor_get(v___y_3606_, 6);
v_openDecls_3640_ = lean_ctor_get(v___y_3606_, 7);
v_initHeartbeats_3641_ = lean_ctor_get(v___y_3606_, 8);
v_maxHeartbeats_3642_ = lean_ctor_get(v___y_3606_, 9);
v_quotContext_3643_ = lean_ctor_get(v___y_3606_, 10);
v_currMacroScope_3644_ = lean_ctor_get(v___y_3606_, 11);
v_diag_3645_ = lean_ctor_get_uint8(v___y_3606_, sizeof(void*)*14);
v_cancelTk_x3f_3646_ = lean_ctor_get(v___y_3606_, 12);
v_suppressElabErrors_3647_ = lean_ctor_get_uint8(v___y_3606_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3648_ = lean_ctor_get(v___y_3606_, 13);
v___x_3649_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_3650_ = l_Lean_replaceRef(v_p_3586_, v_ref_3638_);
lean_dec(v_p_3586_);
lean_inc_ref(v_inheritedTraceOptions_3648_);
lean_inc(v_cancelTk_x3f_3646_);
lean_inc(v_currMacroScope_3644_);
lean_inc(v_quotContext_3643_);
lean_inc(v_maxHeartbeats_3642_);
lean_inc(v_initHeartbeats_3641_);
lean_inc(v_openDecls_3640_);
lean_inc(v_currNamespace_3639_);
lean_inc(v_maxRecDepth_3637_);
lean_inc(v_currRecDepth_3636_);
lean_inc_ref(v_options_3635_);
lean_inc_ref(v_fileMap_3634_);
lean_inc_ref(v_fileName_3633_);
v___x_3651_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3651_, 0, v_fileName_3633_);
lean_ctor_set(v___x_3651_, 1, v_fileMap_3634_);
lean_ctor_set(v___x_3651_, 2, v_options_3635_);
lean_ctor_set(v___x_3651_, 3, v_currRecDepth_3636_);
lean_ctor_set(v___x_3651_, 4, v_maxRecDepth_3637_);
lean_ctor_set(v___x_3651_, 5, v_ref_3650_);
lean_ctor_set(v___x_3651_, 6, v_currNamespace_3639_);
lean_ctor_set(v___x_3651_, 7, v_openDecls_3640_);
lean_ctor_set(v___x_3651_, 8, v_initHeartbeats_3641_);
lean_ctor_set(v___x_3651_, 9, v_maxHeartbeats_3642_);
lean_ctor_set(v___x_3651_, 10, v_quotContext_3643_);
lean_ctor_set(v___x_3651_, 11, v_currMacroScope_3644_);
lean_ctor_set(v___x_3651_, 12, v_cancelTk_x3f_3646_);
lean_ctor_set(v___x_3651_, 13, v_inheritedTraceOptions_3648_);
lean_ctor_set_uint8(v___x_3651_, sizeof(void*)*14, v_diag_3645_);
lean_ctor_set_uint8(v___x_3651_, sizeof(void*)*14 + 1, v_suppressElabErrors_3647_);
v___x_3652_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3585_, v_id_3588_, v___y_3600_, v___x_3649_, v_minIndexable_3589_, v___y_3601_, v___y_3601_, v___y_3604_, v___y_3605_, v___x_3651_, v___y_3607_);
lean_dec_ref_known(v___x_3651_, 14);
return v___x_3652_;
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_dec(v___y_3600_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v_a_3653_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3609_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3609_);
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
v___jp_3661_:
{
lean_object* v___x_3670_; 
v___x_3670_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3589_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_dec_ref_known(v___x_3670_, 1);
v___x_3671_ = l_Lean_Meta_Grind_grindExt;
v___x_3672_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3671_, v___y_3669_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3672_, 1);
lean_inc(v___y_3662_);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___y_3662_);
v___x_3675_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3673_, v___x_3674_);
lean_dec_ref_known(v___x_3674_, 1);
lean_dec(v_a_3673_);
v___x_3676_ = lean_box(0);
v___x_3677_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3663_, v___x_3675_, v___x_3676_);
lean_dec(v___y_3663_);
v___x_3678_ = l_List_isEmpty___redArg(v___x_3677_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3679_; 
lean_dec(v___y_3662_);
lean_dec(v_p_3586_);
v___x_3679_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3677_, v_params_3585_);
lean_dec(v___x_3677_);
return v___x_3679_;
}
else
{
lean_object* v___x_3680_; uint8_t v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec(v___x_3677_);
lean_dec_ref(v_params_3585_);
v___x_3680_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3681_ = 0;
v___x_3682_ = l_Lean_MessageData_ofConstName(v___y_3662_, v___x_3681_);
v___x_3683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3680_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3586_, v___x_3685_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
lean_dec(v_p_3586_);
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v_a_3695_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3672_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3672_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v_a_3703_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3670_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3670_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
v___jp_3711_:
{
lean_object* v___x_3718_; 
v___x_3718_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3589_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_fileName_3719_; lean_object* v_fileMap_3720_; lean_object* v_options_3721_; lean_object* v_currRecDepth_3722_; lean_object* v_maxRecDepth_3723_; lean_object* v_ref_3724_; lean_object* v_currNamespace_3725_; lean_object* v_openDecls_3726_; lean_object* v_initHeartbeats_3727_; lean_object* v_maxHeartbeats_3728_; lean_object* v_quotContext_3729_; lean_object* v_currMacroScope_3730_; uint8_t v_diag_3731_; lean_object* v_cancelTk_x3f_3732_; uint8_t v_suppressElabErrors_3733_; lean_object* v_inheritedTraceOptions_3734_; lean_object* v_ref_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_dec_ref_known(v___x_3718_, 1);
v_fileName_3719_ = lean_ctor_get(v___y_3716_, 0);
v_fileMap_3720_ = lean_ctor_get(v___y_3716_, 1);
v_options_3721_ = lean_ctor_get(v___y_3716_, 2);
v_currRecDepth_3722_ = lean_ctor_get(v___y_3716_, 3);
v_maxRecDepth_3723_ = lean_ctor_get(v___y_3716_, 4);
v_ref_3724_ = lean_ctor_get(v___y_3716_, 5);
v_currNamespace_3725_ = lean_ctor_get(v___y_3716_, 6);
v_openDecls_3726_ = lean_ctor_get(v___y_3716_, 7);
v_initHeartbeats_3727_ = lean_ctor_get(v___y_3716_, 8);
v_maxHeartbeats_3728_ = lean_ctor_get(v___y_3716_, 9);
v_quotContext_3729_ = lean_ctor_get(v___y_3716_, 10);
v_currMacroScope_3730_ = lean_ctor_get(v___y_3716_, 11);
v_diag_3731_ = lean_ctor_get_uint8(v___y_3716_, sizeof(void*)*14);
v_cancelTk_x3f_3732_ = lean_ctor_get(v___y_3716_, 12);
v_suppressElabErrors_3733_ = lean_ctor_get_uint8(v___y_3716_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3734_ = lean_ctor_get(v___y_3716_, 13);
v_ref_3735_ = l_Lean_replaceRef(v_p_3586_, v_ref_3724_);
lean_dec(v_p_3586_);
lean_inc_ref(v_inheritedTraceOptions_3734_);
lean_inc(v_cancelTk_x3f_3732_);
lean_inc(v_currMacroScope_3730_);
lean_inc(v_quotContext_3729_);
lean_inc(v_maxHeartbeats_3728_);
lean_inc(v_initHeartbeats_3727_);
lean_inc(v_openDecls_3726_);
lean_inc(v_currNamespace_3725_);
lean_inc(v_maxRecDepth_3723_);
lean_inc(v_currRecDepth_3722_);
lean_inc_ref(v_options_3721_);
lean_inc_ref(v_fileMap_3720_);
lean_inc_ref(v_fileName_3719_);
v___x_3736_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3736_, 0, v_fileName_3719_);
lean_ctor_set(v___x_3736_, 1, v_fileMap_3720_);
lean_ctor_set(v___x_3736_, 2, v_options_3721_);
lean_ctor_set(v___x_3736_, 3, v_currRecDepth_3722_);
lean_ctor_set(v___x_3736_, 4, v_maxRecDepth_3723_);
lean_ctor_set(v___x_3736_, 5, v_ref_3735_);
lean_ctor_set(v___x_3736_, 6, v_currNamespace_3725_);
lean_ctor_set(v___x_3736_, 7, v_openDecls_3726_);
lean_ctor_set(v___x_3736_, 8, v_initHeartbeats_3727_);
lean_ctor_set(v___x_3736_, 9, v_maxHeartbeats_3728_);
lean_ctor_set(v___x_3736_, 10, v_quotContext_3729_);
lean_ctor_set(v___x_3736_, 11, v_currMacroScope_3730_);
lean_ctor_set(v___x_3736_, 12, v_cancelTk_x3f_3732_);
lean_ctor_set(v___x_3736_, 13, v_inheritedTraceOptions_3734_);
lean_ctor_set_uint8(v___x_3736_, sizeof(void*)*14, v_diag_3731_);
lean_ctor_set_uint8(v___x_3736_, sizeof(void*)*14 + 1, v_suppressElabErrors_3733_);
lean_inc(v___y_3712_);
v___x_3737_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3712_, v___y_3713_, v___x_3736_, v___y_3717_);
lean_dec_ref_known(v___x_3736_, 14);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3745_; 
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3745_ == 0)
{
lean_object* v_unused_3746_; 
v_unused_3746_ = lean_ctor_get(v___x_3737_, 0);
lean_dec(v_unused_3746_);
v___x_3739_ = v___x_3737_;
v_isShared_3740_ = v_isSharedCheck_3745_;
goto v_resetjp_3738_;
}
else
{
lean_dec(v___x_3737_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3745_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3741_; lean_object* v___x_3743_; 
v___x_3741_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3585_, v___y_3712_, v___y_3713_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3741_);
v___x_3743_ = v___x_3739_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v___y_3712_);
lean_dec_ref(v_params_3585_);
v_a_3747_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3737_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3737_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec(v___y_3712_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v_a_3755_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3718_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3718_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
v___jp_3763_:
{
lean_object* v_ctors_3771_; lean_object* v___x_3772_; 
v_ctors_3771_ = lean_ctor_get(v___y_3764_, 4);
lean_inc(v_ctors_3771_);
lean_dec_ref(v___y_3764_);
v___x_3772_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3586_, v_id_3588_, v_minIndexable_3589_, v_ctors_3771_, v_params_3585_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v_ctors_3771_);
lean_dec(v_p_3586_);
return v___x_3772_;
}
v___jp_3773_:
{
uint8_t v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = 1;
lean_inc(v_a_3774_);
v___x_3776_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_3774_, v___x_3775_, v_a_3592_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_dec_ref_known(v___x_3776_, 1);
if (lean_obj_tag(v_mod_x3f_3587_) == 1)
{
lean_object* v_val_3777_; lean_object* v___x_3778_; 
v_val_3777_ = lean_ctor_get(v_mod_x3f_3587_, 0);
lean_inc(v_val_3777_);
lean_dec_ref_known(v_mod_x3f_3587_, 1);
v___x_3778_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3777_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_4001_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3781_ = v___x_3778_;
v_isShared_3782_ = v_isSharedCheck_4001_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3778_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_4001_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
switch(lean_obj_tag(v_a_3779_))
{
case 0:
{
lean_object* v_k_3783_; 
lean_del_object(v___x_3781_);
v_k_3783_ = lean_ctor_get(v_a_3779_, 0);
lean_inc(v_k_3783_);
lean_dec_ref_known(v_a_3779_, 1);
if (lean_obj_tag(v_k_3783_) == 9)
{
lean_dec(v_id_3588_);
if (v_only_3590_ == 0)
{
lean_object* v_fileName_3784_; lean_object* v_fileMap_3785_; lean_object* v_options_3786_; lean_object* v_currRecDepth_3787_; lean_object* v_maxRecDepth_3788_; lean_object* v_ref_3789_; lean_object* v_currNamespace_3790_; lean_object* v_openDecls_3791_; lean_object* v_initHeartbeats_3792_; lean_object* v_maxHeartbeats_3793_; lean_object* v_quotContext_3794_; lean_object* v_currMacroScope_3795_; uint8_t v_diag_3796_; lean_object* v_cancelTk_x3f_3797_; uint8_t v_suppressElabErrors_3798_; lean_object* v_inheritedTraceOptions_3799_; lean_object* v_ref_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v_fileName_3784_ = lean_ctor_get(v_a_3596_, 0);
v_fileMap_3785_ = lean_ctor_get(v_a_3596_, 1);
v_options_3786_ = lean_ctor_get(v_a_3596_, 2);
v_currRecDepth_3787_ = lean_ctor_get(v_a_3596_, 3);
v_maxRecDepth_3788_ = lean_ctor_get(v_a_3596_, 4);
v_ref_3789_ = lean_ctor_get(v_a_3596_, 5);
v_currNamespace_3790_ = lean_ctor_get(v_a_3596_, 6);
v_openDecls_3791_ = lean_ctor_get(v_a_3596_, 7);
v_initHeartbeats_3792_ = lean_ctor_get(v_a_3596_, 8);
v_maxHeartbeats_3793_ = lean_ctor_get(v_a_3596_, 9);
v_quotContext_3794_ = lean_ctor_get(v_a_3596_, 10);
v_currMacroScope_3795_ = lean_ctor_get(v_a_3596_, 11);
v_diag_3796_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*14);
v_cancelTk_x3f_3797_ = lean_ctor_get(v_a_3596_, 12);
v_suppressElabErrors_3798_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3799_ = lean_ctor_get(v_a_3596_, 13);
v_ref_3800_ = l_Lean_replaceRef(v_p_3586_, v_ref_3789_);
lean_inc_ref(v_inheritedTraceOptions_3799_);
lean_inc(v_cancelTk_x3f_3797_);
lean_inc(v_currMacroScope_3795_);
lean_inc(v_quotContext_3794_);
lean_inc(v_maxHeartbeats_3793_);
lean_inc(v_initHeartbeats_3792_);
lean_inc(v_openDecls_3791_);
lean_inc(v_currNamespace_3790_);
lean_inc(v_maxRecDepth_3788_);
lean_inc(v_currRecDepth_3787_);
lean_inc_ref(v_options_3786_);
lean_inc_ref(v_fileMap_3785_);
lean_inc_ref(v_fileName_3784_);
v___x_3801_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3801_, 0, v_fileName_3784_);
lean_ctor_set(v___x_3801_, 1, v_fileMap_3785_);
lean_ctor_set(v___x_3801_, 2, v_options_3786_);
lean_ctor_set(v___x_3801_, 3, v_currRecDepth_3787_);
lean_ctor_set(v___x_3801_, 4, v_maxRecDepth_3788_);
lean_ctor_set(v___x_3801_, 5, v_ref_3800_);
lean_ctor_set(v___x_3801_, 6, v_currNamespace_3790_);
lean_ctor_set(v___x_3801_, 7, v_openDecls_3791_);
lean_ctor_set(v___x_3801_, 8, v_initHeartbeats_3792_);
lean_ctor_set(v___x_3801_, 9, v_maxHeartbeats_3793_);
lean_ctor_set(v___x_3801_, 10, v_quotContext_3794_);
lean_ctor_set(v___x_3801_, 11, v_currMacroScope_3795_);
lean_ctor_set(v___x_3801_, 12, v_cancelTk_x3f_3797_);
lean_ctor_set(v___x_3801_, 13, v_inheritedTraceOptions_3799_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*14, v_diag_3796_);
lean_ctor_set_uint8(v___x_3801_, sizeof(void*)*14 + 1, v_suppressElabErrors_3798_);
v___x_3802_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3801_, v_a_3597_);
lean_dec_ref_known(v___x_3801_, 14);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_dec_ref_known(v___x_3802_, 1);
v___y_3662_ = v_a_3774_;
v___y_3663_ = v_k_3783_;
v___y_3664_ = v_a_3592_;
v___y_3665_ = v_a_3593_;
v___y_3666_ = v_a_3594_;
v___y_3667_ = v_a_3595_;
v___y_3668_ = v_a_3596_;
v___y_3669_ = v_a_3597_;
goto v___jp_3661_;
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec(v_a_3774_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
v___y_3662_ = v_a_3774_;
v___y_3663_ = v_k_3783_;
v___y_3664_ = v_a_3592_;
v___y_3665_ = v_a_3593_;
v___y_3666_ = v_a_3594_;
v___y_3667_ = v_a_3595_;
v___y_3668_ = v_a_3596_;
v___y_3669_ = v_a_3597_;
goto v___jp_3661_;
}
}
else
{
lean_object* v_fileName_3811_; lean_object* v_fileMap_3812_; lean_object* v_options_3813_; lean_object* v_currRecDepth_3814_; lean_object* v_maxRecDepth_3815_; lean_object* v_ref_3816_; lean_object* v_currNamespace_3817_; lean_object* v_openDecls_3818_; lean_object* v_initHeartbeats_3819_; lean_object* v_maxHeartbeats_3820_; lean_object* v_quotContext_3821_; lean_object* v_currMacroScope_3822_; uint8_t v_diag_3823_; lean_object* v_cancelTk_x3f_3824_; uint8_t v_suppressElabErrors_3825_; lean_object* v_inheritedTraceOptions_3826_; uint8_t v___x_3827_; lean_object* v_ref_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v_fileName_3811_ = lean_ctor_get(v_a_3596_, 0);
v_fileMap_3812_ = lean_ctor_get(v_a_3596_, 1);
v_options_3813_ = lean_ctor_get(v_a_3596_, 2);
v_currRecDepth_3814_ = lean_ctor_get(v_a_3596_, 3);
v_maxRecDepth_3815_ = lean_ctor_get(v_a_3596_, 4);
v_ref_3816_ = lean_ctor_get(v_a_3596_, 5);
v_currNamespace_3817_ = lean_ctor_get(v_a_3596_, 6);
v_openDecls_3818_ = lean_ctor_get(v_a_3596_, 7);
v_initHeartbeats_3819_ = lean_ctor_get(v_a_3596_, 8);
v_maxHeartbeats_3820_ = lean_ctor_get(v_a_3596_, 9);
v_quotContext_3821_ = lean_ctor_get(v_a_3596_, 10);
v_currMacroScope_3822_ = lean_ctor_get(v_a_3596_, 11);
v_diag_3823_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*14);
v_cancelTk_x3f_3824_ = lean_ctor_get(v_a_3596_, 12);
v_suppressElabErrors_3825_ = lean_ctor_get_uint8(v_a_3596_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3826_ = lean_ctor_get(v_a_3596_, 13);
v___x_3827_ = 0;
v_ref_3828_ = l_Lean_replaceRef(v_p_3586_, v_ref_3816_);
lean_dec(v_p_3586_);
lean_inc_ref(v_inheritedTraceOptions_3826_);
lean_inc(v_cancelTk_x3f_3824_);
lean_inc(v_currMacroScope_3822_);
lean_inc(v_quotContext_3821_);
lean_inc(v_maxHeartbeats_3820_);
lean_inc(v_initHeartbeats_3819_);
lean_inc(v_openDecls_3818_);
lean_inc(v_currNamespace_3817_);
lean_inc(v_maxRecDepth_3815_);
lean_inc(v_currRecDepth_3814_);
lean_inc_ref(v_options_3813_);
lean_inc_ref(v_fileMap_3812_);
lean_inc_ref(v_fileName_3811_);
v___x_3829_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3829_, 0, v_fileName_3811_);
lean_ctor_set(v___x_3829_, 1, v_fileMap_3812_);
lean_ctor_set(v___x_3829_, 2, v_options_3813_);
lean_ctor_set(v___x_3829_, 3, v_currRecDepth_3814_);
lean_ctor_set(v___x_3829_, 4, v_maxRecDepth_3815_);
lean_ctor_set(v___x_3829_, 5, v_ref_3828_);
lean_ctor_set(v___x_3829_, 6, v_currNamespace_3817_);
lean_ctor_set(v___x_3829_, 7, v_openDecls_3818_);
lean_ctor_set(v___x_3829_, 8, v_initHeartbeats_3819_);
lean_ctor_set(v___x_3829_, 9, v_maxHeartbeats_3820_);
lean_ctor_set(v___x_3829_, 10, v_quotContext_3821_);
lean_ctor_set(v___x_3829_, 11, v_currMacroScope_3822_);
lean_ctor_set(v___x_3829_, 12, v_cancelTk_x3f_3824_);
lean_ctor_set(v___x_3829_, 13, v_inheritedTraceOptions_3826_);
lean_ctor_set_uint8(v___x_3829_, sizeof(void*)*14, v_diag_3823_);
lean_ctor_set_uint8(v___x_3829_, sizeof(void*)*14 + 1, v_suppressElabErrors_3825_);
v___x_3830_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3585_, v_id_3588_, v_a_3774_, v_k_3783_, v_minIndexable_3589_, v___x_3827_, v___x_3775_, v_a_3594_, v_a_3595_, v___x_3829_, v_a_3597_);
lean_dec_ref_known(v___x_3829_, 14);
return v___x_3830_;
}
}
case 1:
{
lean_del_object(v___x_3781_);
lean_dec(v_id_3588_);
if (v_incremental_3591_ == 0)
{
uint8_t v_eager_3831_; 
v_eager_3831_ = lean_ctor_get_uint8(v_a_3779_, 0);
lean_dec_ref_known(v_a_3779_, 0);
v___y_3712_ = v_a_3774_;
v___y_3713_ = v_eager_3831_;
v___y_3714_ = v_a_3594_;
v___y_3715_ = v_a_3595_;
v___y_3716_ = v_a_3596_;
v___y_3717_ = v_a_3597_;
goto v___jp_3711_;
}
else
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec_ref_known(v_a_3779_, 0);
lean_dec(v_a_3774_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v___x_3832_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3833_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3832_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
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
}
case 2:
{
uint8_t v___x_3842_; lean_object* v___x_3843_; 
lean_del_object(v___x_3781_);
v___x_3842_ = 0;
lean_inc(v_a_3774_);
v___x_3843_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3774_, v___x_3842_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref_known(v___x_3843_, 1);
if (lean_obj_tag(v_a_3844_) == 1)
{
lean_dec(v_a_3774_);
if (v_incremental_3591_ == 0)
{
lean_object* v_val_3845_; 
v_val_3845_ = lean_ctor_get(v_a_3844_, 0);
lean_inc(v_val_3845_);
lean_dec_ref_known(v_a_3844_, 1);
v___y_3764_ = v_val_3845_;
v___y_3765_ = v_a_3592_;
v___y_3766_ = v_a_3593_;
v___y_3767_ = v_a_3594_;
v___y_3768_ = v_a_3595_;
v___y_3769_ = v_a_3596_;
v___y_3770_ = v_a_3597_;
goto v___jp_3763_;
}
else
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_dec_ref_known(v_a_3844_, 1);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v___x_3846_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3847_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3846_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3847_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3847_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec(v_a_3844_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v___x_3856_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_3857_ = l_Lean_MessageData_ofConstName(v_a_3774_, v___x_3842_);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_3860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3858_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3860_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3861_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec(v_a_3774_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v_a_3870_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3843_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3843_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
case 3:
{
lean_del_object(v___x_3781_);
v___y_3600_ = v_a_3774_;
v___y_3601_ = v___x_3775_;
v___y_3602_ = v_a_3592_;
v___y_3603_ = v_a_3593_;
v___y_3604_ = v_a_3594_;
v___y_3605_ = v_a_3595_;
v___y_3606_ = v_a_3596_;
v___y_3607_ = v_a_3597_;
goto v___jp_3599_;
}
case 4:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_del_object(v___x_3781_);
lean_dec(v_a_3774_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v___x_3878_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_3879_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3878_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3879_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3879_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
case 5:
{
lean_object* v_prio_3888_; lean_object* v___x_3889_; 
lean_del_object(v___x_3781_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
v_prio_3888_ = lean_ctor_get(v_a_3779_, 0);
lean_inc(v_prio_3888_);
lean_dec_ref_known(v_a_3779_, 1);
v___x_3889_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3589_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3913_; 
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; 
v_unused_3914_ = lean_ctor_get(v___x_3889_, 0);
lean_dec(v_unused_3914_);
v___x_3891_ = v___x_3889_;
v_isShared_3892_ = v_isSharedCheck_3913_;
goto v_resetjp_3890_;
}
else
{
lean_dec(v___x_3889_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3913_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v_config_3893_; lean_object* v_extensions_3894_; lean_object* v_extra_3895_; lean_object* v_extraInj_3896_; lean_object* v_extraFacts_3897_; lean_object* v_symPrios_3898_; lean_object* v_norm_3899_; lean_object* v_normProcs_3900_; lean_object* v_anchorRefs_x3f_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3912_; 
v_config_3893_ = lean_ctor_get(v_params_3585_, 0);
v_extensions_3894_ = lean_ctor_get(v_params_3585_, 1);
v_extra_3895_ = lean_ctor_get(v_params_3585_, 2);
v_extraInj_3896_ = lean_ctor_get(v_params_3585_, 3);
v_extraFacts_3897_ = lean_ctor_get(v_params_3585_, 4);
v_symPrios_3898_ = lean_ctor_get(v_params_3585_, 5);
v_norm_3899_ = lean_ctor_get(v_params_3585_, 6);
v_normProcs_3900_ = lean_ctor_get(v_params_3585_, 7);
v_anchorRefs_x3f_3901_ = lean_ctor_get(v_params_3585_, 8);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_params_3585_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3903_ = v_params_3585_;
v_isShared_3904_ = v_isSharedCheck_3912_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_anchorRefs_x3f_3901_);
lean_inc(v_normProcs_3900_);
lean_inc(v_norm_3899_);
lean_inc(v_symPrios_3898_);
lean_inc(v_extraFacts_3897_);
lean_inc(v_extraInj_3896_);
lean_inc(v_extra_3895_);
lean_inc(v_extensions_3894_);
lean_inc(v_config_3893_);
lean_dec(v_params_3585_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3912_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_3898_, v_a_3774_, v_prio_3888_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 5, v___x_3905_);
v___x_3907_ = v___x_3903_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_config_3893_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_extensions_3894_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_extra_3895_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_extraInj_3896_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_extraFacts_3897_);
lean_ctor_set(v_reuseFailAlloc_3911_, 5, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3911_, 6, v_norm_3899_);
lean_ctor_set(v_reuseFailAlloc_3911_, 7, v_normProcs_3900_);
lean_ctor_set(v_reuseFailAlloc_3911_, 8, v_anchorRefs_x3f_3901_);
v___x_3907_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3909_; 
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 0, v___x_3907_);
v___x_3909_ = v___x_3891_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v_prio_3888_);
lean_dec(v_a_3774_);
lean_dec_ref(v_params_3585_);
v_a_3915_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3889_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3889_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
case 6:
{
lean_object* v___x_3923_; 
lean_del_object(v___x_3781_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
v___x_3923_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3774_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3948_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3926_ = v___x_3923_;
v_isShared_3927_ = v_isSharedCheck_3948_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3923_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3948_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v_config_3928_; lean_object* v_extensions_3929_; lean_object* v_extra_3930_; lean_object* v_extraInj_3931_; lean_object* v_extraFacts_3932_; lean_object* v_symPrios_3933_; lean_object* v_norm_3934_; lean_object* v_normProcs_3935_; lean_object* v_anchorRefs_x3f_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3947_; 
v_config_3928_ = lean_ctor_get(v_params_3585_, 0);
v_extensions_3929_ = lean_ctor_get(v_params_3585_, 1);
v_extra_3930_ = lean_ctor_get(v_params_3585_, 2);
v_extraInj_3931_ = lean_ctor_get(v_params_3585_, 3);
v_extraFacts_3932_ = lean_ctor_get(v_params_3585_, 4);
v_symPrios_3933_ = lean_ctor_get(v_params_3585_, 5);
v_norm_3934_ = lean_ctor_get(v_params_3585_, 6);
v_normProcs_3935_ = lean_ctor_get(v_params_3585_, 7);
v_anchorRefs_x3f_3936_ = lean_ctor_get(v_params_3585_, 8);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_params_3585_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3938_ = v_params_3585_;
v_isShared_3939_ = v_isSharedCheck_3947_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_anchorRefs_x3f_3936_);
lean_inc(v_normProcs_3935_);
lean_inc(v_norm_3934_);
lean_inc(v_symPrios_3933_);
lean_inc(v_extraFacts_3932_);
lean_inc(v_extraInj_3931_);
lean_inc(v_extra_3930_);
lean_inc(v_extensions_3929_);
lean_inc(v_config_3928_);
lean_dec(v_params_3585_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3947_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3940_ = l_Lean_PersistentArray_push___redArg(v_extraInj_3931_, v_a_3924_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 3, v___x_3940_);
v___x_3942_ = v___x_3938_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_config_3928_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_extensions_3929_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_extra_3930_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v___x_3940_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v_extraFacts_3932_);
lean_ctor_set(v_reuseFailAlloc_3946_, 5, v_symPrios_3933_);
lean_ctor_set(v_reuseFailAlloc_3946_, 6, v_norm_3934_);
lean_ctor_set(v_reuseFailAlloc_3946_, 7, v_normProcs_3935_);
lean_ctor_set(v_reuseFailAlloc_3946_, 8, v_anchorRefs_x3f_3936_);
v___x_3942_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3944_; 
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v___x_3942_);
v___x_3944_ = v___x_3926_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec_ref(v_params_3585_);
v_a_3949_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3923_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3923_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
case 7:
{
lean_object* v___x_3957_; lean_object* v___x_3959_; 
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
v___x_3957_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3585_, v_a_3774_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v___x_3957_);
v___x_3959_ = v___x_3781_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3957_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
case 8:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec_ref_known(v_a_3779_, 0);
lean_del_object(v___x_3781_);
lean_dec(v_a_3774_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v___x_3961_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_3962_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3961_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3962_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3962_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
case 9:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_del_object(v___x_3781_);
lean_dec(v_a_3774_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v___x_3971_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_3972_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3971_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3972_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3972_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
case 10:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3990_; 
lean_del_object(v___x_3781_);
lean_dec(v_a_3774_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v___x_3981_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_3982_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3981_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3985_ = v___x_3982_;
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3982_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3988_; 
if (v_isShared_3986_ == 0)
{
v___x_3988_ = v___x_3985_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_a_3983_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
default: 
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_del_object(v___x_3781_);
lean_dec(v_a_3774_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v___x_3991_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_3992_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3991_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
v_a_3993_ = lean_ctor_get(v___x_3992_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3992_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3992_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3992_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec(v_a_3774_);
lean_dec(v_id_3588_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v_a_4002_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3778_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3778_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3587_);
v___y_3600_ = v_a_3774_;
v___y_3601_ = v___x_3775_;
v___y_3602_ = v_a_3592_;
v___y_3603_ = v_a_3593_;
v___y_3604_ = v_a_3594_;
v___y_3605_ = v_a_3595_;
v___y_3606_ = v_a_3596_;
v___y_3607_ = v_a_3597_;
goto v___jp_3599_;
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v_a_3774_);
lean_dec(v_id_3588_);
lean_dec(v_mod_x3f_3587_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v_a_4010_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3776_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3776_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
v___jp_4018_:
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4029_; 
v_a_4020_ = lean_ctor_get(v___y_4019_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___y_4019_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4022_ = v___y_4019_;
v_isShared_4023_ = v_isSharedCheck_4029_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___y_4019_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4029_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
if (lean_obj_tag(v_a_4020_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4026_; 
lean_dec(v_id_3588_);
lean_dec(v_mod_x3f_3587_);
lean_dec(v_p_3586_);
lean_dec_ref(v_params_3585_);
v_a_4024_ = lean_ctor_get(v_a_4020_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v_a_4020_, 1);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 0, v_a_4024_);
v___x_4026_ = v___x_4022_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4024_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
else
{
lean_object* v_a_4028_; 
lean_del_object(v___x_4022_);
v_a_4028_ = lean_ctor_get(v_a_4020_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v_a_4020_, 1);
v_a_3774_ = v_a_4028_;
goto v___jp_3773_;
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
lean_dec(v_a_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_a_4119_);
lean_dec_ref(v_a_4118_);
lean_dec(v_a_4117_);
lean_dec_ref(v_a_4116_);
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
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v_as_x27_4146_);
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
lean_dec(v_as_x27_4171_);
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
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
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
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v_as_x27_4223_);
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
lean_dec(v_localDecl_x3f_4268_);
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
lean_dec(v_localDecl_x3f_4299_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4305_, v___y_4310_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4323_, lean_object* v_msgData_4324_, uint8_t v_severity_4325_, uint8_t v_isSilent_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4323_, v_msgData_4324_, v_severity_4325_, v_isSilent_4326_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4335_, lean_object* v_msgData_4336_, lean_object* v_severity_4337_, lean_object* v_isSilent_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
uint8_t v_severity_boxed_4346_; uint8_t v_isSilent_boxed_4347_; lean_object* v_res_4348_; 
v_severity_boxed_4346_ = lean_unbox(v_severity_4337_);
v_isSilent_boxed_4347_ = lean_unbox(v_isSilent_4338_);
v_res_4348_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4335_, v_msgData_4336_, v_severity_boxed_4346_, v_isSilent_boxed_4347_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v_ref_4335_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4349_, uint8_t v___x_4350_, lean_object* v_b_4351_, lean_object* v_____r_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = lean_box(0);
v___x_4361_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4349_, v___x_4360_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4363_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc_n(v_a_4362_, 2);
lean_dec_ref_known(v___x_4361_, 1);
v___x_4363_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4362_, v___x_4350_, v___y_4353_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4363_) == 0)
{
uint8_t v___x_4364_; lean_object* v___x_4365_; 
lean_dec_ref_known(v___x_4363_, 1);
v___x_4364_ = 0;
lean_inc(v_a_4362_);
v___x_4365_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4362_, v___x_4364_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4425_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4368_ = v___x_4365_;
v_isShared_4369_ = v_isSharedCheck_4425_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4365_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4425_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
if (lean_obj_tag(v_a_4366_) == 1)
{
lean_object* v_val_4370_; lean_object* v___x_4371_; 
lean_del_object(v___x_4368_);
lean_dec(v_a_4362_);
v_val_4370_ = lean_ctor_get(v_a_4366_, 0);
lean_inc_n(v_val_4370_, 2);
lean_dec_ref_known(v_a_4366_, 1);
v___x_4371_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4370_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v___x_4372_; 
lean_dec_ref_known(v___x_4371_, 1);
v___x_4372_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4351_, v_val_4370_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4382_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4375_ = v___x_4372_;
v_isShared_4376_ = v_isSharedCheck_4382_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4372_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4382_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4380_; 
v___x_4377_ = lean_box(0);
v___x_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4377_);
lean_ctor_set(v___x_4378_, 1, v_a_4373_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 0, v___x_4378_);
v___x_4380_ = v___x_4375_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
v_a_4383_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4372_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4372_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_dec(v_val_4370_);
lean_dec_ref(v_b_4351_);
v_a_4391_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4371_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4371_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
else
{
uint8_t v___x_4399_; 
lean_dec(v_a_4366_);
lean_inc(v_a_4362_);
v___x_4399_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4351_, v_a_4362_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; 
lean_del_object(v___x_4368_);
v___x_4400_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4351_, v_a_4362_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4410_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4403_ = v___x_4400_;
v_isShared_4404_ = v_isSharedCheck_4410_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4400_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4410_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4408_; 
v___x_4405_ = lean_box(0);
v___x_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
lean_ctor_set(v___x_4406_, 1, v_a_4401_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v___x_4406_);
v___x_4408_ = v___x_4403_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
v_a_4411_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4400_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4400_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
else
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4419_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4351_, v_a_4362_);
v___x_4420_ = lean_box(0);
v___x_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
lean_ctor_set(v___x_4421_, 1, v___x_4419_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set(v___x_4368_, 0, v___x_4421_);
v___x_4423_ = v___x_4368_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_dec(v_a_4362_);
lean_dec_ref(v_b_4351_);
v_a_4426_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4365_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4365_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec(v_a_4362_);
lean_dec_ref(v_b_4351_);
v_a_4434_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4363_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4363_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_dec_ref(v_b_4351_);
v_a_4442_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4361_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4361_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4450_, lean_object* v___x_4451_, lean_object* v_b_4452_, lean_object* v_____r_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
uint8_t v___x_17487__boxed_4461_; lean_object* v_res_4462_; 
v___x_17487__boxed_4461_ = lean_unbox(v___x_4451_);
v_res_4462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4450_, v___x_17487__boxed_4461_, v_b_4452_, v_____r_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4466_, lean_object* v_b_4467_, lean_object* v_a_4468_, uint8_t v___x_4469_, uint8_t v_only_4470_, uint8_t v_incremental_4471_, lean_object* v_x_4472_, lean_object* v_mod_x3f_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; 
v___x_4481_ = lean_unsigned_to_nat(1u);
v___x_4482_ = l_Lean_Syntax_getArg(v___x_4466_, v___x_4481_);
if (v___x_4469_ == 0)
{
lean_object* v___x_4543_; uint8_t v___x_4544_; 
v___x_4543_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4482_);
v___x_4544_ = l_Lean_Syntax_isOfKind(v___x_4482_, v___x_4543_);
if (v___x_4544_ == 0)
{
lean_object* v___x_4545_; 
v___x_4545_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4467_, v_a_4468_, v_mod_x3f_4473_, v___x_4482_, v___x_4469_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4555_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4548_ = v___x_4545_;
v_isShared_4549_ = v_isSharedCheck_4555_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___x_4545_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4555_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4553_; 
v___x_4550_ = lean_box(0);
v___x_4551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4550_);
lean_ctor_set(v___x_4551_, 1, v_a_4546_);
if (v_isShared_4549_ == 0)
{
lean_ctor_set(v___x_4548_, 0, v___x_4551_);
v___x_4553_ = v___x_4548_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4551_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
v_a_4556_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4545_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4545_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
else
{
goto v___jp_4503_;
}
}
else
{
goto v___jp_4503_;
}
v___jp_4483_:
{
lean_object* v___x_4484_; 
v___x_4484_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4467_, v_a_4468_, v_mod_x3f_4473_, v___x_4482_, v___x_4469_, v_only_4470_, v_incremental_4471_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4494_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4487_ = v___x_4484_;
v_isShared_4488_ = v_isSharedCheck_4494_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4494_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4492_; 
v___x_4489_ = lean_box(0);
v___x_4490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4489_);
lean_ctor_set(v___x_4490_, 1, v_a_4485_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 0, v___x_4490_);
v___x_4492_ = v___x_4487_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
v_a_4495_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4484_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4484_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
v___jp_4503_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = l_Lean_TSyntax_getId(v___x_4482_);
v___x_4505_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4504_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_a_4506_);
lean_dec_ref_known(v___x_4505_, 1);
if (lean_obj_tag(v_a_4506_) == 1)
{
lean_object* v_val_4507_; lean_object* v_snd_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4533_; 
v_val_4507_ = lean_ctor_get(v_a_4506_, 0);
lean_inc(v_val_4507_);
lean_dec_ref_known(v_a_4506_, 1);
v_snd_4508_ = lean_ctor_get(v_val_4507_, 1);
v_isSharedCheck_4533_ = !lean_is_exclusive(v_val_4507_);
if (v_isSharedCheck_4533_ == 0)
{
lean_object* v_unused_4534_; 
v_unused_4534_ = lean_ctor_get(v_val_4507_, 0);
lean_dec(v_unused_4534_);
v___x_4510_ = v_val_4507_;
v_isShared_4511_ = v_isSharedCheck_4533_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_snd_4508_);
lean_dec(v_val_4507_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4533_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
if (lean_obj_tag(v_snd_4508_) == 1)
{
lean_object* v___x_4512_; 
lean_dec_ref_known(v_snd_4508_, 2);
v___x_4512_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4467_, v_a_4468_, v_mod_x3f_4473_, v___x_4482_, v___x_4469_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4512_) == 0)
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4524_; 
v_a_4513_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4515_ = v___x_4512_;
v_isShared_4516_ = v_isSharedCheck_4524_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4512_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4524_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4517_; lean_object* v___x_4519_; 
v___x_4517_ = lean_box(0);
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 1, v_a_4513_);
lean_ctor_set(v___x_4510_, 0, v___x_4517_);
v___x_4519_ = v___x_4510_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4517_);
lean_ctor_set(v_reuseFailAlloc_4523_, 1, v_a_4513_);
v___x_4519_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
lean_object* v___x_4521_; 
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 0, v___x_4519_);
v___x_4521_ = v___x_4515_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4519_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
else
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4532_; 
lean_del_object(v___x_4510_);
v_a_4525_ = lean_ctor_get(v___x_4512_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4512_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4527_ = v___x_4512_;
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4512_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4525_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
}
else
{
lean_del_object(v___x_4510_);
lean_dec(v_snd_4508_);
goto v___jp_4483_;
}
}
}
else
{
lean_dec(v_a_4506_);
goto v___jp_4483_;
}
}
else
{
lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4542_; 
lean_dec(v___x_4482_);
lean_dec(v_mod_x3f_4473_);
lean_dec(v_a_4468_);
lean_dec_ref(v_b_4467_);
v_a_4535_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4537_ = v___x_4505_;
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_dec(v___x_4505_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4542_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4538_ == 0)
{
v___x_4540_ = v___x_4537_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4564_, lean_object* v_b_4565_, lean_object* v_a_4566_, lean_object* v___x_4567_, lean_object* v_only_4568_, lean_object* v_incremental_4569_, lean_object* v_x_4570_, lean_object* v_mod_x3f_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v___x_17705__boxed_4579_; uint8_t v_only_boxed_4580_; uint8_t v_incremental_boxed_4581_; lean_object* v_res_4582_; 
v___x_17705__boxed_4579_ = lean_unbox(v___x_4567_);
v_only_boxed_4580_ = lean_unbox(v_only_4568_);
v_incremental_boxed_4581_ = lean_unbox(v_incremental_4569_);
v_res_4582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4564_, v_b_4565_, v_a_4566_, v___x_17705__boxed_4579_, v_only_boxed_4580_, v_incremental_boxed_4581_, v_x_4570_, v_mod_x3f_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___x_4564_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4583_, lean_object* v___x_4584_, lean_object* v_____r_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v___x_4593_; 
v___x_4593_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4583_, v___x_4584_, v___y_4590_, v___y_4591_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4603_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4596_ = v___x_4593_;
v_isShared_4597_ = v_isSharedCheck_4603_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___x_4593_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4603_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4601_; 
v___x_4598_ = lean_box(0);
v___x_4599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
lean_ctor_set(v___x_4599_, 1, v_a_4594_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 0, v___x_4599_);
v___x_4601_ = v___x_4596_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4599_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
v_a_4604_ = lean_ctor_get(v___x_4593_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4593_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4593_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4612_, lean_object* v___x_4613_, lean_object* v_____r_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
lean_object* v_res_4622_; 
v_res_4622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4612_, v___x_4613_, v_____r_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___x_4613_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4623_, lean_object* v_b_4624_, lean_object* v_a_4625_, uint8_t v___x_4626_, uint8_t v_only_4627_, uint8_t v_incremental_4628_, uint8_t v___x_4629_, lean_object* v_x_4630_, lean_object* v_mod_x3f_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = lean_unsigned_to_nat(2u);
v___x_4640_ = l_Lean_Syntax_getArg(v___x_4623_, v___x_4639_);
if (v___x_4629_ == 0)
{
lean_object* v___x_4701_; uint8_t v___x_4702_; 
v___x_4701_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4640_);
v___x_4702_ = l_Lean_Syntax_isOfKind(v___x_4640_, v___x_4701_);
if (v___x_4702_ == 0)
{
lean_object* v___x_4703_; 
v___x_4703_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4624_, v_a_4625_, v_mod_x3f_4631_, v___x_4640_, v___x_4626_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4713_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4706_ = v___x_4703_;
v_isShared_4707_ = v_isSharedCheck_4713_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4703_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4713_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4711_; 
v___x_4708_ = lean_box(0);
v___x_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
lean_ctor_set(v___x_4709_, 1, v_a_4704_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 0, v___x_4709_);
v___x_4711_ = v___x_4706_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v___x_4709_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
v_a_4714_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4716_ = v___x_4703_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_a_4714_);
lean_dec(v___x_4703_);
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
else
{
goto v___jp_4661_;
}
}
else
{
goto v___jp_4661_;
}
v___jp_4641_:
{
lean_object* v___x_4642_; 
v___x_4642_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4624_, v_a_4625_, v_mod_x3f_4631_, v___x_4640_, v___x_4626_, v_only_4627_, v_incremental_4628_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4652_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4645_ = v___x_4642_;
v_isShared_4646_ = v_isSharedCheck_4652_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_a_4643_);
lean_dec(v___x_4642_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4652_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4650_; 
v___x_4647_ = lean_box(0);
v___x_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
lean_ctor_set(v___x_4648_, 1, v_a_4643_);
if (v_isShared_4646_ == 0)
{
lean_ctor_set(v___x_4645_, 0, v___x_4648_);
v___x_4650_ = v___x_4645_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4648_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4660_; 
v_a_4653_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4655_ = v___x_4642_;
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4642_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4656_ == 0)
{
v___x_4658_ = v___x_4655_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4653_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
v___jp_4661_:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4662_ = l_Lean_TSyntax_getId(v___x_4640_);
v___x_4663_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4662_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; 
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
lean_inc(v_a_4664_);
lean_dec_ref_known(v___x_4663_, 1);
if (lean_obj_tag(v_a_4664_) == 1)
{
lean_object* v_val_4665_; lean_object* v_snd_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4691_; 
v_val_4665_ = lean_ctor_get(v_a_4664_, 0);
lean_inc(v_val_4665_);
lean_dec_ref_known(v_a_4664_, 1);
v_snd_4666_ = lean_ctor_get(v_val_4665_, 1);
v_isSharedCheck_4691_ = !lean_is_exclusive(v_val_4665_);
if (v_isSharedCheck_4691_ == 0)
{
lean_object* v_unused_4692_; 
v_unused_4692_ = lean_ctor_get(v_val_4665_, 0);
lean_dec(v_unused_4692_);
v___x_4668_ = v_val_4665_;
v_isShared_4669_ = v_isSharedCheck_4691_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_snd_4666_);
lean_dec(v_val_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4691_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
if (lean_obj_tag(v_snd_4666_) == 1)
{
lean_object* v___x_4670_; 
lean_dec_ref_known(v_snd_4666_, 2);
v___x_4670_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4624_, v_a_4625_, v_mod_x3f_4631_, v___x_4640_, v___x_4626_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4682_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4673_ = v___x_4670_;
v_isShared_4674_ = v_isSharedCheck_4682_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v___x_4670_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4682_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v___x_4677_; 
v___x_4675_ = lean_box(0);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 1, v_a_4671_);
lean_ctor_set(v___x_4668_, 0, v___x_4675_);
v___x_4677_ = v___x_4668_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v___x_4675_);
lean_ctor_set(v_reuseFailAlloc_4681_, 1, v_a_4671_);
v___x_4677_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
lean_object* v___x_4679_; 
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v___x_4677_);
v___x_4679_ = v___x_4673_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4677_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
lean_del_object(v___x_4668_);
v_a_4683_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4670_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4670_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
else
{
lean_del_object(v___x_4668_);
lean_dec(v_snd_4666_);
goto v___jp_4641_;
}
}
}
else
{
lean_dec(v_a_4664_);
goto v___jp_4641_;
}
}
else
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4700_; 
lean_dec(v___x_4640_);
lean_dec(v_mod_x3f_4631_);
lean_dec(v_a_4625_);
lean_dec_ref(v_b_4624_);
v_a_4693_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4695_ = v___x_4663_;
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4663_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4722_, lean_object* v_b_4723_, lean_object* v_a_4724_, lean_object* v___x_4725_, lean_object* v_only_4726_, lean_object* v_incremental_4727_, lean_object* v___x_4728_, lean_object* v_x_4729_, lean_object* v_mod_x3f_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
uint8_t v___x_17974__boxed_4738_; uint8_t v_only_boxed_4739_; uint8_t v_incremental_boxed_4740_; uint8_t v___x_17975__boxed_4741_; lean_object* v_res_4742_; 
v___x_17974__boxed_4738_ = lean_unbox(v___x_4725_);
v_only_boxed_4739_ = lean_unbox(v_only_4726_);
v_incremental_boxed_4740_ = lean_unbox(v_incremental_4727_);
v___x_17975__boxed_4741_ = lean_unbox(v___x_4728_);
v_res_4742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4722_, v_b_4723_, v_a_4724_, v___x_17974__boxed_4738_, v_only_boxed_4739_, v_incremental_boxed_4740_, v___x_17975__boxed_4741_, v_x_4729_, v_mod_x3f_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
lean_dec(v___x_4722_);
return v_res_4742_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4751_ = l_Lean_stringToMessageData(v___x_4750_);
return v___x_4751_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13(void){
_start:
{
lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12));
v___x_4778_ = l_Lean_stringToMessageData(v___x_4777_);
return v___x_4778_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4784_ = l_Lean_stringToMessageData(v___x_4783_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4785_, uint8_t v_only_4786_, uint8_t v_incremental_4787_, lean_object* v_as_4788_, size_t v_sz_4789_, size_t v_i_4790_, lean_object* v_b_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v_snd_4800_; lean_object* v___y_4805_; uint8_t v___y_4806_; lean_object* v_a_4810_; lean_object* v___y_4814_; uint8_t v___x_4818_; 
v___x_4818_ = lean_usize_dec_lt(v_i_4790_, v_sz_4789_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; 
v___x_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4819_, 0, v_b_4791_);
return v___x_4819_;
}
else
{
lean_object* v_a_4820_; lean_object* v___x_4821_; uint8_t v___x_4822_; 
v_a_4820_ = lean_array_uget_borrowed(v_as_4788_, v_i_4790_);
v___x_4821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4820_);
v___x_4822_ = l_Lean_Syntax_isOfKind(v_a_4820_, v___x_4821_);
if (v___x_4822_ == 0)
{
lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4823_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4820_);
v___x_4824_ = l_Lean_MessageData_ofSyntax(v_a_4820_);
v___x_4825_ = l_Lean_indentD(v___x_4824_);
v___x_4826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4823_);
lean_ctor_set(v___x_4826_, 1, v___x_4825_);
v___x_4827_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4826_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_dec_ref_known(v___x_4827_, 1);
v_snd_4800_ = v_b_4791_;
goto v___jp_4799_;
}
else
{
lean_object* v_a_4828_; 
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_a_4828_);
lean_dec_ref_known(v___x_4827_, 1);
v_a_4810_ = v_a_4828_;
goto v___jp_4809_;
}
}
else
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4829_ = lean_unsigned_to_nat(0u);
v___x_4830_ = l_Lean_Syntax_getArg(v_a_4820_, v___x_4829_);
v___x_4831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_4830_);
v___x_4832_ = l_Lean_Syntax_isOfKind(v___x_4830_, v___x_4831_);
if (v___x_4832_ == 0)
{
lean_object* v___x_4833_; uint8_t v___x_4834_; 
v___x_4833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_4830_);
v___x_4834_ = l_Lean_Syntax_isOfKind(v___x_4830_, v___x_4833_);
if (v___x_4834_ == 0)
{
lean_object* v___x_4835_; uint8_t v___x_4836_; 
v___x_4835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_4830_);
v___x_4836_ = l_Lean_Syntax_isOfKind(v___x_4830_, v___x_4835_);
if (v___x_4836_ == 0)
{
lean_object* v___x_4837_; uint8_t v___x_4838_; 
v___x_4837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_4830_);
v___x_4838_ = l_Lean_Syntax_isOfKind(v___x_4830_, v___x_4837_);
if (v___x_4838_ == 0)
{
lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_dec(v___x_4830_);
v___x_4839_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4820_);
v___x_4840_ = l_Lean_MessageData_ofSyntax(v_a_4820_);
v___x_4841_ = l_Lean_indentD(v___x_4840_);
v___x_4842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4839_);
lean_ctor_set(v___x_4842_, 1, v___x_4841_);
v___x_4843_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4842_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_dec_ref_known(v___x_4843_, 1);
v_snd_4800_ = v_b_4791_;
goto v___jp_4799_;
}
else
{
lean_object* v_a_4844_; 
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
lean_inc(v_a_4844_);
lean_dec_ref_known(v___x_4843_, 1);
v_a_4810_ = v_a_4844_;
goto v___jp_4809_;
}
}
else
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = lean_unsigned_to_nat(1u);
v___x_4846_ = l_Lean_Syntax_getArg(v___x_4830_, v___x_4845_);
lean_dec(v___x_4830_);
if (v___x_4836_ == 0)
{
lean_object* v___x_4855_; uint8_t v___x_4856_; 
v___x_4855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15));
lean_inc(v___x_4846_);
v___x_4856_ = l_Lean_Syntax_isOfKind(v___x_4846_, v___x_4855_);
if (v___x_4856_ == 0)
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
lean_dec(v___x_4846_);
v___x_4857_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4820_);
v___x_4858_ = l_Lean_MessageData_ofSyntax(v_a_4820_);
v___x_4859_ = l_Lean_indentD(v___x_4858_);
v___x_4860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4857_);
lean_ctor_set(v___x_4860_, 1, v___x_4859_);
v___x_4861_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4860_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_dec_ref_known(v___x_4861_, 1);
v_snd_4800_ = v_b_4791_;
goto v___jp_4799_;
}
else
{
lean_object* v_a_4862_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4862_);
lean_dec_ref_known(v___x_4861_, 1);
v_a_4810_ = v_a_4862_;
goto v___jp_4809_;
}
}
else
{
goto v___jp_4847_;
}
}
else
{
goto v___jp_4847_;
}
v___jp_4847_:
{
if (v_only_4786_ == 0)
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13);
v___x_4849_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_4846_, v___x_4848_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4851_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
lean_inc(v_a_4850_);
lean_dec_ref_known(v___x_4849_, 1);
lean_inc_ref(v_b_4791_);
v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4791_, v___x_4846_, v_a_4850_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___x_4846_);
v___y_4814_ = v___x_4851_;
goto v___jp_4813_;
}
else
{
lean_object* v_a_4852_; 
lean_dec(v___x_4846_);
v_a_4852_ = lean_ctor_get(v___x_4849_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4849_, 1);
v_a_4810_ = v_a_4852_;
goto v___jp_4809_;
}
}
else
{
lean_object* v___x_4853_; lean_object* v___x_4854_; 
v___x_4853_ = lean_box(0);
lean_inc_ref(v_b_4791_);
v___x_4854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4791_, v___x_4846_, v___x_4853_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___x_4846_);
v___y_4814_ = v___x_4854_;
goto v___jp_4813_;
}
}
}
}
else
{
lean_object* v___x_4863_; lean_object* v___x_4864_; uint8_t v___x_4865_; 
v___x_4863_ = lean_unsigned_to_nat(1u);
v___x_4864_ = l_Lean_Syntax_getArg(v___x_4830_, v___x_4863_);
v___x_4865_ = l_Lean_Syntax_isNone(v___x_4864_);
if (v___x_4865_ == 0)
{
uint8_t v___x_4866_; 
lean_inc(v___x_4864_);
v___x_4866_ = l_Lean_Syntax_matchesNull(v___x_4864_, v___x_4863_);
if (v___x_4866_ == 0)
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
lean_dec(v___x_4864_);
lean_dec(v___x_4830_);
v___x_4867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4820_);
v___x_4868_ = l_Lean_MessageData_ofSyntax(v_a_4820_);
v___x_4869_ = l_Lean_indentD(v___x_4868_);
v___x_4870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4867_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
v___x_4871_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4870_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_dec_ref_known(v___x_4871_, 1);
v_snd_4800_ = v_b_4791_;
goto v___jp_4799_;
}
else
{
lean_object* v_a_4872_; 
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
lean_inc(v_a_4872_);
lean_dec_ref_known(v___x_4871_, 1);
v_a_4810_ = v_a_4872_;
goto v___jp_4809_;
}
}
else
{
lean_object* v___x_4873_; 
v___x_4873_ = l_Lean_Syntax_getArg(v___x_4864_, v___x_4829_);
lean_dec(v___x_4864_);
if (v___x_4865_ == 0)
{
lean_object* v___x_4878_; uint8_t v___x_4879_; 
v___x_4878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4873_);
v___x_4879_ = l_Lean_Syntax_isOfKind(v___x_4873_, v___x_4878_);
if (v___x_4879_ == 0)
{
lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; 
lean_dec(v___x_4873_);
lean_dec(v___x_4830_);
v___x_4880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4820_);
v___x_4881_ = l_Lean_MessageData_ofSyntax(v_a_4820_);
v___x_4882_ = l_Lean_indentD(v___x_4881_);
v___x_4883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4880_);
lean_ctor_set(v___x_4883_, 1, v___x_4882_);
v___x_4884_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4883_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_dec_ref_known(v___x_4884_, 1);
v_snd_4800_ = v_b_4791_;
goto v___jp_4799_;
}
else
{
lean_object* v_a_4885_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
lean_inc(v_a_4885_);
lean_dec_ref_known(v___x_4884_, 1);
v_a_4810_ = v_a_4885_;
goto v___jp_4809_;
}
}
else
{
goto v___jp_4874_;
}
}
else
{
goto v___jp_4874_;
}
v___jp_4874_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4875_ = lean_box(0);
v___x_4876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4873_);
lean_inc(v_a_4820_);
lean_inc_ref(v_b_4791_);
v___x_4877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4830_, v_b_4791_, v_a_4820_, v___x_4822_, v_only_4786_, v_incremental_4787_, v___x_4834_, v___x_4875_, v___x_4876_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___x_4830_);
v___y_4814_ = v___x_4877_;
goto v___jp_4813_;
}
}
}
else
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
lean_dec(v___x_4864_);
v___x_4886_ = lean_box(0);
v___x_4887_ = lean_box(0);
lean_inc(v_a_4820_);
lean_inc_ref(v_b_4791_);
v___x_4888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4830_, v_b_4791_, v_a_4820_, v___x_4822_, v_only_4786_, v_incremental_4787_, v___x_4834_, v___x_4886_, v___x_4887_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___x_4830_);
v___y_4814_ = v___x_4888_;
goto v___jp_4813_;
}
}
}
else
{
lean_object* v___x_4889_; uint8_t v___x_4890_; 
v___x_4889_ = l_Lean_Syntax_getArg(v___x_4830_, v___x_4829_);
v___x_4890_ = l_Lean_Syntax_isNone(v___x_4889_);
if (v___x_4890_ == 0)
{
lean_object* v___x_4891_; uint8_t v___x_4892_; 
v___x_4891_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4889_);
v___x_4892_ = l_Lean_Syntax_matchesNull(v___x_4889_, v___x_4891_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
lean_dec(v___x_4889_);
lean_dec(v___x_4830_);
v___x_4893_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4820_);
v___x_4894_ = l_Lean_MessageData_ofSyntax(v_a_4820_);
v___x_4895_ = l_Lean_indentD(v___x_4894_);
v___x_4896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4893_);
lean_ctor_set(v___x_4896_, 1, v___x_4895_);
v___x_4897_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4896_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_dec_ref_known(v___x_4897_, 1);
v_snd_4800_ = v_b_4791_;
goto v___jp_4799_;
}
else
{
lean_object* v_a_4898_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4898_);
lean_dec_ref_known(v___x_4897_, 1);
v_a_4810_ = v_a_4898_;
goto v___jp_4809_;
}
}
else
{
lean_object* v___x_4899_; 
v___x_4899_ = l_Lean_Syntax_getArg(v___x_4889_, v___x_4829_);
lean_dec(v___x_4889_);
if (v___x_4890_ == 0)
{
lean_object* v___x_4904_; uint8_t v___x_4905_; 
v___x_4904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4899_);
v___x_4905_ = l_Lean_Syntax_isOfKind(v___x_4899_, v___x_4904_);
if (v___x_4905_ == 0)
{
lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
lean_dec(v___x_4899_);
lean_dec(v___x_4830_);
v___x_4906_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4820_);
v___x_4907_ = l_Lean_MessageData_ofSyntax(v_a_4820_);
v___x_4908_ = l_Lean_indentD(v___x_4907_);
v___x_4909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4909_, 0, v___x_4906_);
lean_ctor_set(v___x_4909_, 1, v___x_4908_);
v___x_4910_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4909_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_dec_ref_known(v___x_4910_, 1);
v_snd_4800_ = v_b_4791_;
goto v___jp_4799_;
}
else
{
lean_object* v_a_4911_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4910_, 1);
v_a_4810_ = v_a_4911_;
goto v___jp_4809_;
}
}
else
{
goto v___jp_4900_;
}
}
else
{
goto v___jp_4900_;
}
v___jp_4900_:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4901_ = lean_box(0);
v___x_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4899_);
lean_inc(v_a_4820_);
lean_inc_ref(v_b_4791_);
v___x_4903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4830_, v_b_4791_, v_a_4820_, v___x_4832_, v_only_4786_, v_incremental_4787_, v___x_4901_, v___x_4902_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___x_4830_);
v___y_4814_ = v___x_4903_;
goto v___jp_4813_;
}
}
}
else
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
lean_dec(v___x_4889_);
v___x_4912_ = lean_box(0);
v___x_4913_ = lean_box(0);
lean_inc(v_a_4820_);
lean_inc_ref(v_b_4791_);
v___x_4914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4830_, v_b_4791_, v_a_4820_, v___x_4832_, v_only_4786_, v_incremental_4787_, v___x_4912_, v___x_4913_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___x_4830_);
v___y_4814_ = v___x_4914_;
goto v___jp_4813_;
}
}
}
else
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; uint8_t v___x_4918_; 
v___x_4915_ = lean_unsigned_to_nat(1u);
v___x_4916_ = l_Lean_Syntax_getArg(v___x_4830_, v___x_4915_);
lean_dec(v___x_4830_);
v___x_4917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4916_);
v___x_4918_ = l_Lean_Syntax_isOfKind(v___x_4916_, v___x_4917_);
if (v___x_4918_ == 0)
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
lean_dec(v___x_4916_);
v___x_4919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4820_);
v___x_4920_ = l_Lean_MessageData_ofSyntax(v_a_4820_);
v___x_4921_ = l_Lean_indentD(v___x_4920_);
v___x_4922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4922_, 0, v___x_4919_);
lean_ctor_set(v___x_4922_, 1, v___x_4921_);
v___x_4923_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4922_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_dec_ref_known(v___x_4923_, 1);
v_snd_4800_ = v_b_4791_;
goto v___jp_4799_;
}
else
{
lean_object* v_a_4924_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
lean_inc(v_a_4924_);
lean_dec_ref_known(v___x_4923_, 1);
v_a_4810_ = v_a_4924_;
goto v___jp_4809_;
}
}
else
{
if (v_incremental_4787_ == 0)
{
lean_object* v___x_4925_; lean_object* v___x_4926_; 
v___x_4925_ = lean_box(0);
lean_inc_ref(v_b_4791_);
v___x_4926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4916_, v___x_4822_, v_b_4791_, v___x_4925_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
v___y_4814_ = v___x_4926_;
goto v___jp_4813_;
}
else
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_4928_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4820_, v___x_4927_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref_known(v___x_4928_, 1);
lean_inc_ref(v_b_4791_);
v___x_4930_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4916_, v___x_4822_, v_b_4791_, v_a_4929_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
v___y_4814_ = v___x_4930_;
goto v___jp_4813_;
}
else
{
lean_object* v_a_4931_; 
lean_dec(v___x_4916_);
v_a_4931_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___x_4928_, 1);
v_a_4810_ = v_a_4931_;
goto v___jp_4809_;
}
}
}
}
}
}
v___jp_4799_:
{
size_t v___x_4801_; size_t v___x_4802_; 
v___x_4801_ = ((size_t)1ULL);
v___x_4802_ = lean_usize_add(v_i_4790_, v___x_4801_);
v_i_4790_ = v___x_4802_;
v_b_4791_ = v_snd_4800_;
goto _start;
}
v___jp_4804_:
{
if (v___y_4806_ == 0)
{
if (v_lax_4785_ == 0)
{
lean_object* v___x_4807_; 
lean_dec_ref(v_b_4791_);
v___x_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4807_, 0, v___y_4805_);
return v___x_4807_;
}
else
{
lean_dec_ref(v___y_4805_);
v_snd_4800_ = v_b_4791_;
goto v___jp_4799_;
}
}
else
{
lean_object* v___x_4808_; 
lean_dec_ref(v_b_4791_);
v___x_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4808_, 0, v___y_4805_);
return v___x_4808_;
}
}
v___jp_4809_:
{
uint8_t v___x_4811_; 
v___x_4811_ = l_Lean_Exception_isInterrupt(v_a_4810_);
if (v___x_4811_ == 0)
{
uint8_t v___x_4812_; 
lean_inc_ref(v_a_4810_);
v___x_4812_ = l_Lean_Exception_isRuntime(v_a_4810_);
v___y_4805_ = v_a_4810_;
v___y_4806_ = v___x_4812_;
goto v___jp_4804_;
}
else
{
v___y_4805_ = v_a_4810_;
v___y_4806_ = v___x_4811_;
goto v___jp_4804_;
}
}
v___jp_4813_:
{
if (lean_obj_tag(v___y_4814_) == 0)
{
lean_object* v_a_4815_; lean_object* v_snd_4816_; 
lean_dec_ref(v_b_4791_);
v_a_4815_ = lean_ctor_get(v___y_4814_, 0);
lean_inc(v_a_4815_);
lean_dec_ref_known(v___y_4814_, 1);
v_snd_4816_ = lean_ctor_get(v_a_4815_, 1);
lean_inc(v_snd_4816_);
lean_dec(v_a_4815_);
v_snd_4800_ = v_snd_4816_;
goto v___jp_4799_;
}
else
{
lean_object* v_a_4817_; 
v_a_4817_ = lean_ctor_get(v___y_4814_, 0);
lean_inc(v_a_4817_);
lean_dec_ref_known(v___y_4814_, 1);
v_a_4810_ = v_a_4817_;
goto v___jp_4809_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_4932_, lean_object* v_only_4933_, lean_object* v_incremental_4934_, lean_object* v_as_4935_, lean_object* v_sz_4936_, lean_object* v_i_4937_, lean_object* v_b_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
uint8_t v_lax_boxed_4946_; uint8_t v_only_boxed_4947_; uint8_t v_incremental_boxed_4948_; size_t v_sz_boxed_4949_; size_t v_i_boxed_4950_; lean_object* v_res_4951_; 
v_lax_boxed_4946_ = lean_unbox(v_lax_4932_);
v_only_boxed_4947_ = lean_unbox(v_only_4933_);
v_incremental_boxed_4948_ = lean_unbox(v_incremental_4934_);
v_sz_boxed_4949_ = lean_unbox_usize(v_sz_4936_);
lean_dec(v_sz_4936_);
v_i_boxed_4950_ = lean_unbox_usize(v_i_4937_);
lean_dec(v_i_4937_);
v_res_4951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_4946_, v_only_boxed_4947_, v_incremental_boxed_4948_, v_as_4935_, v_sz_boxed_4949_, v_i_boxed_4950_, v_b_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
lean_dec(v___y_4940_);
lean_dec_ref(v___y_4939_);
lean_dec_ref(v_as_4935_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_4952_, lean_object* v_ps_4953_, uint8_t v_only_4954_, uint8_t v_lax_4955_, uint8_t v_incremental_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_){
_start:
{
size_t v_sz_4964_; size_t v___x_4965_; lean_object* v___x_4966_; 
v_sz_4964_ = lean_array_size(v_ps_4953_);
v___x_4965_ = ((size_t)0ULL);
v___x_4966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_4955_, v_only_4954_, v_incremental_4956_, v_ps_4953_, v_sz_4964_, v___x_4965_, v_params_4952_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_4967_, lean_object* v_ps_4968_, lean_object* v_only_4969_, lean_object* v_lax_4970_, lean_object* v_incremental_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_){
_start:
{
uint8_t v_only_boxed_4979_; uint8_t v_lax_boxed_4980_; uint8_t v_incremental_boxed_4981_; lean_object* v_res_4982_; 
v_only_boxed_4979_ = lean_unbox(v_only_4969_);
v_lax_boxed_4980_ = lean_unbox(v_lax_4970_);
v_incremental_boxed_4981_ = lean_unbox(v_incremental_4971_);
v_res_4982_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_4967_, v_ps_4968_, v_only_boxed_4979_, v_lax_boxed_4980_, v_incremental_boxed_4981_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec(v_a_4975_);
lean_dec_ref(v_a_4974_);
lean_dec(v_a_4973_);
lean_dec_ref(v_a_4972_);
lean_dec_ref(v_ps_4968_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_){
_start:
{
lean_object* v_origin_4994_; 
v_origin_4994_ = lean_ctor_get(v_thm_4983_, 5);
if (lean_obj_tag(v_origin_4994_) == 0)
{
lean_object* v_declName_4995_; lean_object* v___x_4996_; 
lean_inc_ref(v_origin_4994_);
lean_dec_ref(v_thm_4983_);
v_declName_4995_ = lean_ctor_get(v_origin_4994_, 0);
lean_inc(v_declName_4995_);
lean_dec_ref_known(v_origin_4994_, 1);
v___x_4996_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_4995_, v_a_4991_, v_a_4992_);
return v___x_4996_;
}
else
{
lean_object* v_proof_4997_; lean_object* v___x_4998_; 
v_proof_4997_ = lean_ctor_get(v_thm_4983_, 1);
lean_inc_ref(v_proof_4997_);
lean_dec_ref(v_thm_4983_);
v___x_4998_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_4997_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
return v___x_4998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
lean_dec(v_a_5006_);
lean_dec_ref(v_a_5005_);
lean_dec(v_a_5004_);
lean_dec_ref(v_a_5003_);
lean_dec(v_a_5002_);
lean_dec_ref(v_a_5001_);
lean_dec(v_a_5000_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_5011_, size_t v_sz_5012_, size_t v_i_5013_, lean_object* v_b_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
uint8_t v___x_5025_; 
v___x_5025_ = lean_usize_dec_lt(v_i_5013_, v_sz_5012_);
if (v___x_5025_ == 0)
{
lean_object* v___x_5026_; 
v___x_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5026_, 0, v_b_5014_);
return v___x_5026_;
}
else
{
lean_object* v_snd_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5053_; 
v_snd_5027_ = lean_ctor_get(v_b_5014_, 1);
v_isSharedCheck_5053_ = !lean_is_exclusive(v_b_5014_);
if (v_isSharedCheck_5053_ == 0)
{
lean_object* v_unused_5054_; 
v_unused_5054_ = lean_ctor_get(v_b_5014_, 0);
lean_dec(v_unused_5054_);
v___x_5029_ = v_b_5014_;
v_isShared_5030_ = v_isSharedCheck_5053_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_snd_5027_);
lean_dec(v_b_5014_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5053_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v_a_5031_; lean_object* v___x_5032_; 
v_a_5031_ = lean_array_uget_borrowed(v_as_5011_, v_i_5013_);
lean_inc(v_a_5031_);
v___x_5032_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5031_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_object* v_a_5033_; lean_object* v___x_5034_; lean_object* v_a_5036_; uint8_t v___x_5043_; 
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_a_5033_);
lean_dec_ref_known(v___x_5032_, 1);
v___x_5034_ = lean_box(0);
v___x_5043_ = lean_unbox(v_a_5033_);
lean_dec(v_a_5033_);
if (v___x_5043_ == 0)
{
v_a_5036_ = v_snd_5027_;
goto v___jp_5035_;
}
else
{
lean_object* v___x_5044_; 
lean_inc(v_a_5031_);
v___x_5044_ = l_Lean_PersistentArray_push___redArg(v_snd_5027_, v_a_5031_);
v_a_5036_ = v___x_5044_;
goto v___jp_5035_;
}
v___jp_5035_:
{
lean_object* v___x_5038_; 
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 1, v_a_5036_);
lean_ctor_set(v___x_5029_, 0, v___x_5034_);
v___x_5038_ = v___x_5029_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v___x_5034_);
lean_ctor_set(v_reuseFailAlloc_5042_, 1, v_a_5036_);
v___x_5038_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
size_t v___x_5039_; size_t v___x_5040_; 
v___x_5039_ = ((size_t)1ULL);
v___x_5040_ = lean_usize_add(v_i_5013_, v___x_5039_);
v_i_5013_ = v___x_5040_;
v_b_5014_ = v___x_5038_;
goto _start;
}
}
}
else
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
lean_del_object(v___x_5029_);
lean_dec(v_snd_5027_);
v_a_5045_ = lean_ctor_get(v___x_5032_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5032_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v___x_5032_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_5032_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5055_, lean_object* v_sz_5056_, lean_object* v_i_5057_, lean_object* v_b_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_){
_start:
{
size_t v_sz_boxed_5069_; size_t v_i_boxed_5070_; lean_object* v_res_5071_; 
v_sz_boxed_5069_ = lean_unbox_usize(v_sz_5056_);
lean_dec(v_sz_5056_);
v_i_boxed_5070_ = lean_unbox_usize(v_i_5057_);
lean_dec(v_i_5057_);
v_res_5071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5055_, v_sz_boxed_5069_, v_i_boxed_5070_, v_b_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v___y_5065_);
lean_dec_ref(v___y_5064_);
lean_dec(v___y_5063_);
lean_dec_ref(v___y_5062_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v_as_5055_);
return v_res_5071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5072_, size_t v_sz_5073_, size_t v_i_5074_, lean_object* v_b_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_){
_start:
{
uint8_t v___x_5086_; 
v___x_5086_ = lean_usize_dec_lt(v_i_5074_, v_sz_5073_);
if (v___x_5086_ == 0)
{
lean_object* v___x_5087_; 
v___x_5087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5087_, 0, v_b_5075_);
return v___x_5087_;
}
else
{
lean_object* v_snd_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5114_; 
v_snd_5088_ = lean_ctor_get(v_b_5075_, 1);
v_isSharedCheck_5114_ = !lean_is_exclusive(v_b_5075_);
if (v_isSharedCheck_5114_ == 0)
{
lean_object* v_unused_5115_; 
v_unused_5115_ = lean_ctor_get(v_b_5075_, 0);
lean_dec(v_unused_5115_);
v___x_5090_ = v_b_5075_;
v_isShared_5091_ = v_isSharedCheck_5114_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_snd_5088_);
lean_dec(v_b_5075_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5114_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v_a_5092_; lean_object* v___x_5093_; 
v_a_5092_ = lean_array_uget_borrowed(v_as_5072_, v_i_5074_);
lean_inc(v_a_5092_);
v___x_5093_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5092_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v_a_5094_; lean_object* v___x_5095_; lean_object* v_a_5097_; uint8_t v___x_5104_; 
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc(v_a_5094_);
lean_dec_ref_known(v___x_5093_, 1);
v___x_5095_ = lean_box(0);
v___x_5104_ = lean_unbox(v_a_5094_);
lean_dec(v_a_5094_);
if (v___x_5104_ == 0)
{
v_a_5097_ = v_snd_5088_;
goto v___jp_5096_;
}
else
{
lean_object* v___x_5105_; 
lean_inc(v_a_5092_);
v___x_5105_ = l_Lean_PersistentArray_push___redArg(v_snd_5088_, v_a_5092_);
v_a_5097_ = v___x_5105_;
goto v___jp_5096_;
}
v___jp_5096_:
{
lean_object* v___x_5099_; 
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 1, v_a_5097_);
lean_ctor_set(v___x_5090_, 0, v___x_5095_);
v___x_5099_ = v___x_5090_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5095_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_a_5097_);
v___x_5099_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
size_t v___x_5100_; size_t v___x_5101_; lean_object* v___x_5102_; 
v___x_5100_ = ((size_t)1ULL);
v___x_5101_ = lean_usize_add(v_i_5074_, v___x_5100_);
v___x_5102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5072_, v_sz_5073_, v___x_5101_, v___x_5099_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
return v___x_5102_;
}
}
}
else
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5113_; 
lean_del_object(v___x_5090_);
lean_dec(v_snd_5088_);
v_a_5106_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5108_ = v___x_5093_;
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5093_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5116_, lean_object* v_sz_5117_, lean_object* v_i_5118_, lean_object* v_b_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_){
_start:
{
size_t v_sz_boxed_5130_; size_t v_i_boxed_5131_; lean_object* v_res_5132_; 
v_sz_boxed_5130_ = lean_unbox_usize(v_sz_5117_);
lean_dec(v_sz_5117_);
v_i_boxed_5131_ = lean_unbox_usize(v_i_5118_);
lean_dec(v_i_5118_);
v_res_5132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5116_, v_sz_boxed_5130_, v_i_boxed_5131_, v_b_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v_as_5116_);
return v_res_5132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5133_, size_t v_sz_5134_, size_t v_i_5135_, lean_object* v_b_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_){
_start:
{
uint8_t v___x_5147_; 
v___x_5147_ = lean_usize_dec_lt(v_i_5135_, v_sz_5134_);
if (v___x_5147_ == 0)
{
lean_object* v___x_5148_; 
v___x_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5148_, 0, v_b_5136_);
return v___x_5148_;
}
else
{
lean_object* v_snd_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5175_; 
v_snd_5149_ = lean_ctor_get(v_b_5136_, 1);
v_isSharedCheck_5175_ = !lean_is_exclusive(v_b_5136_);
if (v_isSharedCheck_5175_ == 0)
{
lean_object* v_unused_5176_; 
v_unused_5176_ = lean_ctor_get(v_b_5136_, 0);
lean_dec(v_unused_5176_);
v___x_5151_ = v_b_5136_;
v_isShared_5152_ = v_isSharedCheck_5175_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_snd_5149_);
lean_dec(v_b_5136_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5175_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v_a_5153_; lean_object* v___x_5154_; 
v_a_5153_ = lean_array_uget_borrowed(v_as_5133_, v_i_5135_);
lean_inc(v_a_5153_);
v___x_5154_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5153_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_a_5155_; lean_object* v___x_5156_; lean_object* v_a_5158_; uint8_t v___x_5165_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_a_5155_);
lean_dec_ref_known(v___x_5154_, 1);
v___x_5156_ = lean_box(0);
v___x_5165_ = lean_unbox(v_a_5155_);
lean_dec(v_a_5155_);
if (v___x_5165_ == 0)
{
v_a_5158_ = v_snd_5149_;
goto v___jp_5157_;
}
else
{
lean_object* v___x_5166_; 
lean_inc(v_a_5153_);
v___x_5166_ = l_Lean_PersistentArray_push___redArg(v_snd_5149_, v_a_5153_);
v_a_5158_ = v___x_5166_;
goto v___jp_5157_;
}
v___jp_5157_:
{
lean_object* v___x_5160_; 
if (v_isShared_5152_ == 0)
{
lean_ctor_set(v___x_5151_, 1, v_a_5158_);
lean_ctor_set(v___x_5151_, 0, v___x_5156_);
v___x_5160_ = v___x_5151_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5164_; 
v_reuseFailAlloc_5164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5164_, 0, v___x_5156_);
lean_ctor_set(v_reuseFailAlloc_5164_, 1, v_a_5158_);
v___x_5160_ = v_reuseFailAlloc_5164_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
size_t v___x_5161_; size_t v___x_5162_; 
v___x_5161_ = ((size_t)1ULL);
v___x_5162_ = lean_usize_add(v_i_5135_, v___x_5161_);
v_i_5135_ = v___x_5162_;
v_b_5136_ = v___x_5160_;
goto _start;
}
}
}
else
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5174_; 
lean_del_object(v___x_5151_);
lean_dec(v_snd_5149_);
v_a_5167_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5169_ = v___x_5154_;
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___x_5154_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5172_; 
if (v_isShared_5170_ == 0)
{
v___x_5172_ = v___x_5169_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5167_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5177_, lean_object* v_sz_5178_, lean_object* v_i_5179_, lean_object* v_b_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
size_t v_sz_boxed_5191_; size_t v_i_boxed_5192_; lean_object* v_res_5193_; 
v_sz_boxed_5191_ = lean_unbox_usize(v_sz_5178_);
lean_dec(v_sz_5178_);
v_i_boxed_5192_ = lean_unbox_usize(v_i_5179_);
lean_dec(v_i_5179_);
v_res_5193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5177_, v_sz_boxed_5191_, v_i_boxed_5192_, v_b_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
lean_dec(v___y_5183_);
lean_dec_ref(v___y_5182_);
lean_dec(v___y_5181_);
lean_dec_ref(v_as_5177_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5194_, size_t v_sz_5195_, size_t v_i_5196_, lean_object* v_b_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_){
_start:
{
uint8_t v___x_5208_; 
v___x_5208_ = lean_usize_dec_lt(v_i_5196_, v_sz_5195_);
if (v___x_5208_ == 0)
{
lean_object* v___x_5209_; 
v___x_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5209_, 0, v_b_5197_);
return v___x_5209_;
}
else
{
lean_object* v_snd_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5236_; 
v_snd_5210_ = lean_ctor_get(v_b_5197_, 1);
v_isSharedCheck_5236_ = !lean_is_exclusive(v_b_5197_);
if (v_isSharedCheck_5236_ == 0)
{
lean_object* v_unused_5237_; 
v_unused_5237_ = lean_ctor_get(v_b_5197_, 0);
lean_dec(v_unused_5237_);
v___x_5212_ = v_b_5197_;
v_isShared_5213_ = v_isSharedCheck_5236_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_snd_5210_);
lean_dec(v_b_5197_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5236_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v_a_5214_; lean_object* v___x_5215_; 
v_a_5214_ = lean_array_uget_borrowed(v_as_5194_, v_i_5196_);
lean_inc(v_a_5214_);
v___x_5215_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5214_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_);
if (lean_obj_tag(v___x_5215_) == 0)
{
lean_object* v_a_5216_; lean_object* v___x_5217_; lean_object* v_a_5219_; uint8_t v___x_5226_; 
v_a_5216_ = lean_ctor_get(v___x_5215_, 0);
lean_inc(v_a_5216_);
lean_dec_ref_known(v___x_5215_, 1);
v___x_5217_ = lean_box(0);
v___x_5226_ = lean_unbox(v_a_5216_);
lean_dec(v_a_5216_);
if (v___x_5226_ == 0)
{
v_a_5219_ = v_snd_5210_;
goto v___jp_5218_;
}
else
{
lean_object* v___x_5227_; 
lean_inc(v_a_5214_);
v___x_5227_ = l_Lean_PersistentArray_push___redArg(v_snd_5210_, v_a_5214_);
v_a_5219_ = v___x_5227_;
goto v___jp_5218_;
}
v___jp_5218_:
{
lean_object* v___x_5221_; 
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 1, v_a_5219_);
lean_ctor_set(v___x_5212_, 0, v___x_5217_);
v___x_5221_ = v___x_5212_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v___x_5217_);
lean_ctor_set(v_reuseFailAlloc_5225_, 1, v_a_5219_);
v___x_5221_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
size_t v___x_5222_; size_t v___x_5223_; lean_object* v___x_5224_; 
v___x_5222_ = ((size_t)1ULL);
v___x_5223_ = lean_usize_add(v_i_5196_, v___x_5222_);
v___x_5224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5194_, v_sz_5195_, v___x_5223_, v___x_5221_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_);
return v___x_5224_;
}
}
}
else
{
lean_object* v_a_5228_; lean_object* v___x_5230_; uint8_t v_isShared_5231_; uint8_t v_isSharedCheck_5235_; 
lean_del_object(v___x_5212_);
lean_dec(v_snd_5210_);
v_a_5228_ = lean_ctor_get(v___x_5215_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5230_ = v___x_5215_;
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
else
{
lean_inc(v_a_5228_);
lean_dec(v___x_5215_);
v___x_5230_ = lean_box(0);
v_isShared_5231_ = v_isSharedCheck_5235_;
goto v_resetjp_5229_;
}
v_resetjp_5229_:
{
lean_object* v___x_5233_; 
if (v_isShared_5231_ == 0)
{
v___x_5233_ = v___x_5230_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_a_5228_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5238_, lean_object* v_sz_5239_, lean_object* v_i_5240_, lean_object* v_b_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
size_t v_sz_boxed_5252_; size_t v_i_boxed_5253_; lean_object* v_res_5254_; 
v_sz_boxed_5252_ = lean_unbox_usize(v_sz_5239_);
lean_dec(v_sz_5239_);
v_i_boxed_5253_ = lean_unbox_usize(v_i_5240_);
lean_dec(v_i_5240_);
v_res_5254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5238_, v_sz_boxed_5252_, v_i_boxed_5253_, v_b_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v___y_5246_);
lean_dec_ref(v___y_5245_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
lean_dec(v___y_5242_);
lean_dec_ref(v_as_5238_);
return v_res_5254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5255_, lean_object* v_n_5256_, lean_object* v_b_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
if (lean_obj_tag(v_n_5256_) == 0)
{
lean_object* v_cs_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; size_t v_sz_5271_; size_t v___x_5272_; lean_object* v___x_5273_; 
v_cs_5268_ = lean_ctor_get(v_n_5256_, 0);
v___x_5269_ = lean_box(0);
v___x_5270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5270_, 0, v___x_5269_);
lean_ctor_set(v___x_5270_, 1, v_b_5257_);
v_sz_5271_ = lean_array_size(v_cs_5268_);
v___x_5272_ = ((size_t)0ULL);
v___x_5273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5255_, v_cs_5268_, v_sz_5271_, v___x_5272_, v___x_5270_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5288_; 
v_a_5274_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5276_ = v___x_5273_;
v_isShared_5277_ = v_isSharedCheck_5288_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5273_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5288_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v_fst_5278_; 
v_fst_5278_ = lean_ctor_get(v_a_5274_, 0);
if (lean_obj_tag(v_fst_5278_) == 0)
{
lean_object* v_snd_5279_; lean_object* v___x_5280_; lean_object* v___x_5282_; 
v_snd_5279_ = lean_ctor_get(v_a_5274_, 1);
lean_inc(v_snd_5279_);
lean_dec(v_a_5274_);
v___x_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5280_, 0, v_snd_5279_);
if (v_isShared_5277_ == 0)
{
lean_ctor_set(v___x_5276_, 0, v___x_5280_);
v___x_5282_ = v___x_5276_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5280_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
else
{
lean_object* v_val_5284_; lean_object* v___x_5286_; 
lean_inc_ref(v_fst_5278_);
lean_dec(v_a_5274_);
v_val_5284_ = lean_ctor_get(v_fst_5278_, 0);
lean_inc(v_val_5284_);
lean_dec_ref_known(v_fst_5278_, 1);
if (v_isShared_5277_ == 0)
{
lean_ctor_set(v___x_5276_, 0, v_val_5284_);
v___x_5286_ = v___x_5276_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_val_5284_);
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
else
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5296_; 
v_a_5289_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5291_ = v___x_5273_;
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5273_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5294_; 
if (v_isShared_5292_ == 0)
{
v___x_5294_ = v___x_5291_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
}
}
}
}
else
{
lean_object* v_vs_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; size_t v_sz_5300_; size_t v___x_5301_; lean_object* v___x_5302_; 
v_vs_5297_ = lean_ctor_get(v_n_5256_, 0);
v___x_5298_ = lean_box(0);
v___x_5299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5299_, 0, v___x_5298_);
lean_ctor_set(v___x_5299_, 1, v_b_5257_);
v_sz_5300_ = lean_array_size(v_vs_5297_);
v___x_5301_ = ((size_t)0ULL);
v___x_5302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5297_, v_sz_5300_, v___x_5301_, v___x_5299_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
if (lean_obj_tag(v___x_5302_) == 0)
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5317_; 
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5305_ = v___x_5302_;
v_isShared_5306_ = v_isSharedCheck_5317_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___x_5302_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5317_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
lean_object* v_fst_5307_; 
v_fst_5307_ = lean_ctor_get(v_a_5303_, 0);
if (lean_obj_tag(v_fst_5307_) == 0)
{
lean_object* v_snd_5308_; lean_object* v___x_5309_; lean_object* v___x_5311_; 
v_snd_5308_ = lean_ctor_get(v_a_5303_, 1);
lean_inc(v_snd_5308_);
lean_dec(v_a_5303_);
v___x_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5309_, 0, v_snd_5308_);
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
else
{
lean_object* v_val_5313_; lean_object* v___x_5315_; 
lean_inc_ref(v_fst_5307_);
lean_dec(v_a_5303_);
v_val_5313_ = lean_ctor_get(v_fst_5307_, 0);
lean_inc(v_val_5313_);
lean_dec_ref_known(v_fst_5307_, 1);
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 0, v_val_5313_);
v___x_5315_ = v___x_5305_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_val_5313_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
}
}
else
{
lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5325_; 
v_a_5318_ = lean_ctor_get(v___x_5302_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5302_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5320_ = v___x_5302_;
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v___x_5302_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5326_, lean_object* v_as_5327_, size_t v_sz_5328_, size_t v_i_5329_, lean_object* v_b_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_){
_start:
{
uint8_t v___x_5341_; 
v___x_5341_ = lean_usize_dec_lt(v_i_5329_, v_sz_5328_);
if (v___x_5341_ == 0)
{
lean_object* v___x_5342_; 
v___x_5342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5342_, 0, v_b_5330_);
return v___x_5342_;
}
else
{
lean_object* v_snd_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5377_; 
v_snd_5343_ = lean_ctor_get(v_b_5330_, 1);
v_isSharedCheck_5377_ = !lean_is_exclusive(v_b_5330_);
if (v_isSharedCheck_5377_ == 0)
{
lean_object* v_unused_5378_; 
v_unused_5378_ = lean_ctor_get(v_b_5330_, 0);
lean_dec(v_unused_5378_);
v___x_5345_ = v_b_5330_;
v_isShared_5346_ = v_isSharedCheck_5377_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_snd_5343_);
lean_dec(v_b_5330_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5377_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v_a_5347_; lean_object* v___x_5348_; 
v_a_5347_ = lean_array_uget_borrowed(v_as_5327_, v_i_5329_);
lean_inc(v_snd_5343_);
v___x_5348_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5326_, v_a_5347_, v_snd_5343_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5368_; 
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5351_ = v___x_5348_;
v_isShared_5352_ = v_isSharedCheck_5368_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5348_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5368_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
if (lean_obj_tag(v_a_5349_) == 0)
{
lean_object* v___x_5353_; lean_object* v___x_5355_; 
v___x_5353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5353_, 0, v_a_5349_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 0, v___x_5353_);
v___x_5355_ = v___x_5345_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5353_);
lean_ctor_set(v_reuseFailAlloc_5359_, 1, v_snd_5343_);
v___x_5355_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
lean_object* v___x_5357_; 
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 0, v___x_5355_);
v___x_5357_ = v___x_5351_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v___x_5355_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5361_; lean_object* v___x_5363_; 
lean_del_object(v___x_5351_);
lean_dec(v_snd_5343_);
v_a_5360_ = lean_ctor_get(v_a_5349_, 0);
lean_inc(v_a_5360_);
lean_dec_ref_known(v_a_5349_, 1);
v___x_5361_ = lean_box(0);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 1, v_a_5360_);
lean_ctor_set(v___x_5345_, 0, v___x_5361_);
v___x_5363_ = v___x_5345_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v___x_5361_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v_a_5360_);
v___x_5363_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
size_t v___x_5364_; size_t v___x_5365_; 
v___x_5364_ = ((size_t)1ULL);
v___x_5365_ = lean_usize_add(v_i_5329_, v___x_5364_);
v_i_5329_ = v___x_5365_;
v_b_5330_ = v___x_5363_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5376_; 
lean_del_object(v___x_5345_);
lean_dec(v_snd_5343_);
v_a_5369_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5371_ = v___x_5348_;
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v___x_5348_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5374_; 
if (v_isShared_5372_ == 0)
{
v___x_5374_ = v___x_5371_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5379_, lean_object* v_as_5380_, lean_object* v_sz_5381_, lean_object* v_i_5382_, lean_object* v_b_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_){
_start:
{
size_t v_sz_boxed_5394_; size_t v_i_boxed_5395_; lean_object* v_res_5396_; 
v_sz_boxed_5394_ = lean_unbox_usize(v_sz_5381_);
lean_dec(v_sz_5381_);
v_i_boxed_5395_ = lean_unbox_usize(v_i_5382_);
lean_dec(v_i_5382_);
v_res_5396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5379_, v_as_5380_, v_sz_boxed_5394_, v_i_boxed_5395_, v_b_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
lean_dec(v___y_5390_);
lean_dec_ref(v___y_5389_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
lean_dec(v___y_5384_);
lean_dec_ref(v_as_5380_);
lean_dec_ref(v_init_5379_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5397_, lean_object* v_n_5398_, lean_object* v_b_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_){
_start:
{
lean_object* v_res_5410_; 
v_res_5410_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5397_, v_n_5398_, v_b_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_);
lean_dec(v___y_5408_);
lean_dec_ref(v___y_5407_);
lean_dec(v___y_5406_);
lean_dec_ref(v___y_5405_);
lean_dec(v___y_5404_);
lean_dec_ref(v___y_5403_);
lean_dec(v___y_5402_);
lean_dec_ref(v___y_5401_);
lean_dec(v___y_5400_);
lean_dec_ref(v_n_5398_);
lean_dec_ref(v_init_5397_);
return v_res_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5411_, lean_object* v_init_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
lean_object* v_root_5423_; lean_object* v_tail_5424_; lean_object* v___x_5425_; 
v_root_5423_ = lean_ctor_get(v_t_5411_, 0);
v_tail_5424_ = lean_ctor_get(v_t_5411_, 1);
lean_inc_ref(v_init_5412_);
v___x_5425_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5412_, v_root_5423_, v_init_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_);
lean_dec_ref(v_init_5412_);
if (lean_obj_tag(v___x_5425_) == 0)
{
lean_object* v_a_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5462_; 
v_a_5426_ = lean_ctor_get(v___x_5425_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5425_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5428_ = v___x_5425_;
v_isShared_5429_ = v_isSharedCheck_5462_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_a_5426_);
lean_dec(v___x_5425_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5462_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
if (lean_obj_tag(v_a_5426_) == 0)
{
lean_object* v_a_5430_; lean_object* v___x_5432_; 
v_a_5430_ = lean_ctor_get(v_a_5426_, 0);
lean_inc(v_a_5430_);
lean_dec_ref_known(v_a_5426_, 1);
if (v_isShared_5429_ == 0)
{
lean_ctor_set(v___x_5428_, 0, v_a_5430_);
v___x_5432_ = v___x_5428_;
goto v_reusejp_5431_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_a_5430_);
v___x_5432_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5431_;
}
v_reusejp_5431_:
{
return v___x_5432_;
}
}
else
{
lean_object* v_a_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; size_t v_sz_5437_; size_t v___x_5438_; lean_object* v___x_5439_; 
lean_del_object(v___x_5428_);
v_a_5434_ = lean_ctor_get(v_a_5426_, 0);
lean_inc(v_a_5434_);
lean_dec_ref_known(v_a_5426_, 1);
v___x_5435_ = lean_box(0);
v___x_5436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5436_, 0, v___x_5435_);
lean_ctor_set(v___x_5436_, 1, v_a_5434_);
v_sz_5437_ = lean_array_size(v_tail_5424_);
v___x_5438_ = ((size_t)0ULL);
v___x_5439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5424_, v_sz_5437_, v___x_5438_, v___x_5436_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v_a_5440_; lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5453_; 
v_a_5440_ = lean_ctor_get(v___x_5439_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5439_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5442_ = v___x_5439_;
v_isShared_5443_ = v_isSharedCheck_5453_;
goto v_resetjp_5441_;
}
else
{
lean_inc(v_a_5440_);
lean_dec(v___x_5439_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5453_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
lean_object* v_fst_5444_; 
v_fst_5444_ = lean_ctor_get(v_a_5440_, 0);
if (lean_obj_tag(v_fst_5444_) == 0)
{
lean_object* v_snd_5445_; lean_object* v___x_5447_; 
v_snd_5445_ = lean_ctor_get(v_a_5440_, 1);
lean_inc(v_snd_5445_);
lean_dec(v_a_5440_);
if (v_isShared_5443_ == 0)
{
lean_ctor_set(v___x_5442_, 0, v_snd_5445_);
v___x_5447_ = v___x_5442_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_snd_5445_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
else
{
lean_object* v_val_5449_; lean_object* v___x_5451_; 
lean_inc_ref(v_fst_5444_);
lean_dec(v_a_5440_);
v_val_5449_ = lean_ctor_get(v_fst_5444_, 0);
lean_inc(v_val_5449_);
lean_dec_ref_known(v_fst_5444_, 1);
if (v_isShared_5443_ == 0)
{
lean_ctor_set(v___x_5442_, 0, v_val_5449_);
v___x_5451_ = v___x_5442_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_val_5449_);
v___x_5451_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
return v___x_5451_;
}
}
}
}
else
{
lean_object* v_a_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5461_; 
v_a_5454_ = lean_ctor_get(v___x_5439_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5439_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5456_ = v___x_5439_;
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_a_5454_);
lean_dec(v___x_5439_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5461_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___x_5459_; 
if (v_isShared_5457_ == 0)
{
v___x_5459_ = v___x_5456_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5454_);
v___x_5459_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
return v___x_5459_;
}
}
}
}
}
}
else
{
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5470_; 
v_a_5463_ = lean_ctor_get(v___x_5425_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5425_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5465_ = v___x_5425_;
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5425_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5466_ == 0)
{
v___x_5468_ = v___x_5465_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5471_, lean_object* v_init_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_){
_start:
{
lean_object* v_res_5483_; 
v_res_5483_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5471_, v_init_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec(v___y_5475_);
lean_dec_ref(v___y_5474_);
lean_dec(v___y_5473_);
lean_dec_ref(v_t_5471_);
return v_res_5483_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; 
v___x_5484_ = lean_unsigned_to_nat(32u);
v___x_5485_ = lean_mk_empty_array_with_capacity(v___x_5484_);
v___x_5486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5486_, 0, v___x_5485_);
return v___x_5486_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v_result_5492_; 
v___x_5487_ = ((size_t)5ULL);
v___x_5488_ = lean_unsigned_to_nat(0u);
v___x_5489_ = lean_unsigned_to_nat(32u);
v___x_5490_ = lean_mk_empty_array_with_capacity(v___x_5489_);
v___x_5491_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5492_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5492_, 0, v___x_5491_);
lean_ctor_set(v_result_5492_, 1, v___x_5490_);
lean_ctor_set(v_result_5492_, 2, v___x_5488_);
lean_ctor_set(v_result_5492_, 3, v___x_5488_);
lean_ctor_set_usize(v_result_5492_, 4, v___x_5487_);
return v_result_5492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_, lean_object* v_a_5498_, lean_object* v_a_5499_, lean_object* v_a_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_){
_start:
{
lean_object* v_result_5504_; lean_object* v___x_5505_; 
v_result_5504_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5505_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5493_, v_result_5504_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_, v_a_5499_, v_a_5500_, v_a_5501_, v_a_5502_);
return v___x_5505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_){
_start:
{
lean_object* v_res_5517_; 
v_res_5517_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
lean_dec(v_a_5515_);
lean_dec_ref(v_a_5514_);
lean_dec(v_a_5513_);
lean_dec_ref(v_a_5512_);
lean_dec(v_a_5511_);
lean_dec_ref(v_a_5510_);
lean_dec(v_a_5509_);
lean_dec_ref(v_a_5508_);
lean_dec(v_a_5507_);
lean_dec_ref(v_thms_5506_);
return v_res_5517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5520_, lean_object* v_newThms_5521_, lean_object* v_gmt_5522_, lean_object* v_numInstances_5523_, lean_object* v_numDelayedInstances_5524_, lean_object* v_num_5525_, lean_object* v_preInstances_5526_, lean_object* v_nextThmIdx_5527_, lean_object* v_matchEqNames_5528_, lean_object* v_delayedThmInsts_5529_, lean_object* v_nextDeclIdx_5530_, lean_object* v_enodeMap_5531_, lean_object* v_exprs_5532_, lean_object* v_parents_5533_, lean_object* v_congrTable_5534_, lean_object* v_appMap_5535_, lean_object* v_indicesFound_5536_, lean_object* v_newFacts_5537_, uint8_t v_inconsistent_5538_, lean_object* v_nextIdx_5539_, lean_object* v_newRawFacts_5540_, lean_object* v_facts_5541_, lean_object* v_extThms_5542_, lean_object* v_inj_5543_, lean_object* v_split_5544_, lean_object* v_clean_5545_, lean_object* v_sstates_5546_, lean_object* v_mvarId_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_){
_start:
{
lean_object* v___x_5558_; 
v___x_5558_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5520_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_);
if (lean_obj_tag(v___x_5558_) == 0)
{
lean_object* v_a_5559_; lean_object* v___x_5560_; 
v_a_5559_ = lean_ctor_get(v___x_5558_, 0);
lean_inc(v_a_5559_);
lean_dec_ref_known(v___x_5558_, 1);
v___x_5560_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5521_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_);
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5572_; 
v_a_5561_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5563_ = v___x_5560_;
v_isShared_5564_ = v_isSharedCheck_5572_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_dec(v___x_5560_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5572_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5570_; 
v___x_5565_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5566_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5566_, 0, v___x_5565_);
lean_ctor_set(v___x_5566_, 1, v_gmt_5522_);
lean_ctor_set(v___x_5566_, 2, v_a_5559_);
lean_ctor_set(v___x_5566_, 3, v_a_5561_);
lean_ctor_set(v___x_5566_, 4, v_numInstances_5523_);
lean_ctor_set(v___x_5566_, 5, v_numDelayedInstances_5524_);
lean_ctor_set(v___x_5566_, 6, v_num_5525_);
lean_ctor_set(v___x_5566_, 7, v_preInstances_5526_);
lean_ctor_set(v___x_5566_, 8, v_nextThmIdx_5527_);
lean_ctor_set(v___x_5566_, 9, v_matchEqNames_5528_);
lean_ctor_set(v___x_5566_, 10, v_delayedThmInsts_5529_);
v___x_5567_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_5567_, 0, v_nextDeclIdx_5530_);
lean_ctor_set(v___x_5567_, 1, v_enodeMap_5531_);
lean_ctor_set(v___x_5567_, 2, v_exprs_5532_);
lean_ctor_set(v___x_5567_, 3, v_parents_5533_);
lean_ctor_set(v___x_5567_, 4, v_congrTable_5534_);
lean_ctor_set(v___x_5567_, 5, v_appMap_5535_);
lean_ctor_set(v___x_5567_, 6, v_indicesFound_5536_);
lean_ctor_set(v___x_5567_, 7, v_newFacts_5537_);
lean_ctor_set(v___x_5567_, 8, v_nextIdx_5539_);
lean_ctor_set(v___x_5567_, 9, v_newRawFacts_5540_);
lean_ctor_set(v___x_5567_, 10, v_facts_5541_);
lean_ctor_set(v___x_5567_, 11, v_extThms_5542_);
lean_ctor_set(v___x_5567_, 12, v___x_5566_);
lean_ctor_set(v___x_5567_, 13, v_inj_5543_);
lean_ctor_set(v___x_5567_, 14, v_split_5544_);
lean_ctor_set(v___x_5567_, 15, v_clean_5545_);
lean_ctor_set(v___x_5567_, 16, v_sstates_5546_);
lean_ctor_set_uint8(v___x_5567_, sizeof(void*)*17, v_inconsistent_5538_);
v___x_5568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5567_);
lean_ctor_set(v___x_5568_, 1, v_mvarId_5547_);
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 0, v___x_5568_);
v___x_5570_ = v___x_5563_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5568_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
else
{
lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5580_; 
lean_dec(v_a_5559_);
lean_dec(v_mvarId_5547_);
lean_dec_ref(v_sstates_5546_);
lean_dec_ref(v_clean_5545_);
lean_dec_ref(v_split_5544_);
lean_dec_ref(v_inj_5543_);
lean_dec_ref(v_extThms_5542_);
lean_dec_ref(v_facts_5541_);
lean_dec_ref(v_newRawFacts_5540_);
lean_dec(v_nextIdx_5539_);
lean_dec_ref(v_newFacts_5537_);
lean_dec_ref(v_indicesFound_5536_);
lean_dec_ref(v_appMap_5535_);
lean_dec_ref(v_congrTable_5534_);
lean_dec_ref(v_parents_5533_);
lean_dec_ref(v_exprs_5532_);
lean_dec_ref(v_enodeMap_5531_);
lean_dec(v_nextDeclIdx_5530_);
lean_dec_ref(v_delayedThmInsts_5529_);
lean_dec_ref(v_matchEqNames_5528_);
lean_dec(v_nextThmIdx_5527_);
lean_dec_ref(v_preInstances_5526_);
lean_dec(v_num_5525_);
lean_dec(v_numDelayedInstances_5524_);
lean_dec(v_numInstances_5523_);
lean_dec(v_gmt_5522_);
v_a_5573_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5575_ = v___x_5560_;
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5560_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5578_; 
if (v_isShared_5576_ == 0)
{
v___x_5578_ = v___x_5575_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
v___x_5578_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
return v___x_5578_;
}
}
}
}
else
{
lean_object* v_a_5581_; lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5588_; 
lean_dec(v_mvarId_5547_);
lean_dec_ref(v_sstates_5546_);
lean_dec_ref(v_clean_5545_);
lean_dec_ref(v_split_5544_);
lean_dec_ref(v_inj_5543_);
lean_dec_ref(v_extThms_5542_);
lean_dec_ref(v_facts_5541_);
lean_dec_ref(v_newRawFacts_5540_);
lean_dec(v_nextIdx_5539_);
lean_dec_ref(v_newFacts_5537_);
lean_dec_ref(v_indicesFound_5536_);
lean_dec_ref(v_appMap_5535_);
lean_dec_ref(v_congrTable_5534_);
lean_dec_ref(v_parents_5533_);
lean_dec_ref(v_exprs_5532_);
lean_dec_ref(v_enodeMap_5531_);
lean_dec(v_nextDeclIdx_5530_);
lean_dec_ref(v_delayedThmInsts_5529_);
lean_dec_ref(v_matchEqNames_5528_);
lean_dec(v_nextThmIdx_5527_);
lean_dec_ref(v_preInstances_5526_);
lean_dec(v_num_5525_);
lean_dec(v_numDelayedInstances_5524_);
lean_dec(v_numInstances_5523_);
lean_dec(v_gmt_5522_);
v_a_5581_ = lean_ctor_get(v___x_5558_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v___x_5558_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5583_ = v___x_5558_;
v_isShared_5584_ = v_isSharedCheck_5588_;
goto v_resetjp_5582_;
}
else
{
lean_inc(v_a_5581_);
lean_dec(v___x_5558_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5589_ = _args[0];
lean_object* v_newThms_5590_ = _args[1];
lean_object* v_gmt_5591_ = _args[2];
lean_object* v_numInstances_5592_ = _args[3];
lean_object* v_numDelayedInstances_5593_ = _args[4];
lean_object* v_num_5594_ = _args[5];
lean_object* v_preInstances_5595_ = _args[6];
lean_object* v_nextThmIdx_5596_ = _args[7];
lean_object* v_matchEqNames_5597_ = _args[8];
lean_object* v_delayedThmInsts_5598_ = _args[9];
lean_object* v_nextDeclIdx_5599_ = _args[10];
lean_object* v_enodeMap_5600_ = _args[11];
lean_object* v_exprs_5601_ = _args[12];
lean_object* v_parents_5602_ = _args[13];
lean_object* v_congrTable_5603_ = _args[14];
lean_object* v_appMap_5604_ = _args[15];
lean_object* v_indicesFound_5605_ = _args[16];
lean_object* v_newFacts_5606_ = _args[17];
lean_object* v_inconsistent_5607_ = _args[18];
lean_object* v_nextIdx_5608_ = _args[19];
lean_object* v_newRawFacts_5609_ = _args[20];
lean_object* v_facts_5610_ = _args[21];
lean_object* v_extThms_5611_ = _args[22];
lean_object* v_inj_5612_ = _args[23];
lean_object* v_split_5613_ = _args[24];
lean_object* v_clean_5614_ = _args[25];
lean_object* v_sstates_5615_ = _args[26];
lean_object* v_mvarId_5616_ = _args[27];
lean_object* v___y_5617_ = _args[28];
lean_object* v___y_5618_ = _args[29];
lean_object* v___y_5619_ = _args[30];
lean_object* v___y_5620_ = _args[31];
lean_object* v___y_5621_ = _args[32];
lean_object* v___y_5622_ = _args[33];
lean_object* v___y_5623_ = _args[34];
lean_object* v___y_5624_ = _args[35];
lean_object* v___y_5625_ = _args[36];
lean_object* v___y_5626_ = _args[37];
_start:
{
uint8_t v_inconsistent_boxed_5627_; lean_object* v_res_5628_; 
v_inconsistent_boxed_5627_ = lean_unbox(v_inconsistent_5607_);
v_res_5628_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5589_, v_newThms_5590_, v_gmt_5591_, v_numInstances_5592_, v_numDelayedInstances_5593_, v_num_5594_, v_preInstances_5595_, v_nextThmIdx_5596_, v_matchEqNames_5597_, v_delayedThmInsts_5598_, v_nextDeclIdx_5599_, v_enodeMap_5600_, v_exprs_5601_, v_parents_5602_, v_congrTable_5603_, v_appMap_5604_, v_indicesFound_5605_, v_newFacts_5606_, v_inconsistent_boxed_5627_, v_nextIdx_5608_, v_newRawFacts_5609_, v_facts_5610_, v_extThms_5611_, v_inj_5612_, v_split_5613_, v_clean_5614_, v_sstates_5615_, v_mvarId_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_);
lean_dec(v___y_5625_);
lean_dec_ref(v___y_5624_);
lean_dec(v___y_5623_);
lean_dec_ref(v___y_5622_);
lean_dec(v___y_5621_);
lean_dec_ref(v___y_5620_);
lean_dec(v___y_5619_);
lean_dec_ref(v___y_5618_);
lean_dec(v___y_5617_);
lean_dec_ref(v_newThms_5590_);
lean_dec_ref(v_thms_5589_);
return v_res_5628_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5629_; 
v___x_5629_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_5629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5630_, size_t v_i_5631_, lean_object* v_bs_5632_){
_start:
{
uint8_t v___x_5633_; 
v___x_5633_ = lean_usize_dec_lt(v_i_5631_, v_sz_5630_);
if (v___x_5633_ == 0)
{
return v_bs_5632_;
}
else
{
lean_object* v_v_5634_; lean_object* v_casesTypes_5635_; lean_object* v_extThms_5636_; lean_object* v_funCC_5637_; lean_object* v_inj_5638_; lean_object* v___x_5640_; uint8_t v_isShared_5641_; uint8_t v_isSharedCheck_5652_; 
v_v_5634_ = lean_array_uget(v_bs_5632_, v_i_5631_);
v_casesTypes_5635_ = lean_ctor_get(v_v_5634_, 0);
v_extThms_5636_ = lean_ctor_get(v_v_5634_, 1);
v_funCC_5637_ = lean_ctor_get(v_v_5634_, 2);
v_inj_5638_ = lean_ctor_get(v_v_5634_, 4);
v_isSharedCheck_5652_ = !lean_is_exclusive(v_v_5634_);
if (v_isSharedCheck_5652_ == 0)
{
lean_object* v_unused_5653_; 
v_unused_5653_ = lean_ctor_get(v_v_5634_, 3);
lean_dec(v_unused_5653_);
v___x_5640_ = v_v_5634_;
v_isShared_5641_ = v_isSharedCheck_5652_;
goto v_resetjp_5639_;
}
else
{
lean_inc(v_inj_5638_);
lean_inc(v_funCC_5637_);
lean_inc(v_extThms_5636_);
lean_inc(v_casesTypes_5635_);
lean_dec(v_v_5634_);
v___x_5640_ = lean_box(0);
v_isShared_5641_ = v_isSharedCheck_5652_;
goto v_resetjp_5639_;
}
v_resetjp_5639_:
{
lean_object* v___x_5642_; lean_object* v_bs_x27_5643_; lean_object* v___x_5644_; lean_object* v___x_5646_; 
v___x_5642_ = lean_unsigned_to_nat(0u);
v_bs_x27_5643_ = lean_array_uset(v_bs_5632_, v_i_5631_, v___x_5642_);
v___x_5644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 3, v___x_5644_);
v___x_5646_ = v___x_5640_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v_casesTypes_5635_);
lean_ctor_set(v_reuseFailAlloc_5651_, 1, v_extThms_5636_);
lean_ctor_set(v_reuseFailAlloc_5651_, 2, v_funCC_5637_);
lean_ctor_set(v_reuseFailAlloc_5651_, 3, v___x_5644_);
lean_ctor_set(v_reuseFailAlloc_5651_, 4, v_inj_5638_);
v___x_5646_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
size_t v___x_5647_; size_t v___x_5648_; lean_object* v___x_5649_; 
v___x_5647_ = ((size_t)1ULL);
v___x_5648_ = lean_usize_add(v_i_5631_, v___x_5647_);
v___x_5649_ = lean_array_uset(v_bs_x27_5643_, v_i_5631_, v___x_5646_);
v_i_5631_ = v___x_5648_;
v_bs_5632_ = v___x_5649_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5654_, lean_object* v_i_5655_, lean_object* v_bs_5656_){
_start:
{
size_t v_sz_boxed_5657_; size_t v_i_boxed_5658_; lean_object* v_res_5659_; 
v_sz_boxed_5657_ = lean_unbox_usize(v_sz_5654_);
lean_dec(v_sz_5654_);
v_i_boxed_5658_ = lean_unbox_usize(v_i_5655_);
lean_dec(v_i_5655_);
v_res_5659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5657_, v_i_boxed_5658_, v_bs_5656_);
return v_res_5659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5660_, lean_object* v_ps_5661_, uint8_t v_only_5662_, lean_object* v_k_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_){
_start:
{
lean_object* v___y_5674_; lean_object* v___y_5675_; lean_object* v___y_5676_; lean_object* v___y_5677_; lean_object* v___y_5678_; lean_object* v___y_5679_; lean_object* v___y_5680_; lean_object* v___y_5681_; lean_object* v___y_5682_; uint8_t v___y_5695_; uint8_t v___y_5696_; lean_object* v_params_5697_; lean_object* v___y_5698_; lean_object* v___y_5699_; lean_object* v___y_5700_; lean_object* v___y_5701_; lean_object* v___y_5702_; lean_object* v___y_5703_; lean_object* v___y_5704_; lean_object* v___y_5705_; uint8_t v___y_5806_; 
if (v_only_5662_ == 0)
{
lean_object* v___x_5828_; lean_object* v___x_5829_; uint8_t v___x_5830_; 
v___x_5828_ = lean_array_get_size(v_ps_5661_);
v___x_5829_ = lean_unsigned_to_nat(0u);
v___x_5830_ = lean_nat_dec_eq(v___x_5828_, v___x_5829_);
if (v___x_5830_ == 0)
{
v___y_5806_ = v___x_5830_;
goto v___jp_5805_;
}
else
{
lean_object* v___x_5831_; 
lean_dec_ref(v_params_5660_);
lean_inc(v_a_5671_);
lean_inc_ref(v_a_5670_);
lean_inc(v_a_5669_);
lean_inc_ref(v_a_5668_);
lean_inc(v_a_5667_);
lean_inc_ref(v_a_5666_);
lean_inc(v_a_5665_);
lean_inc_ref(v_a_5664_);
v___x_5831_ = lean_apply_9(v_k_5663_, v_a_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_, lean_box(0));
return v___x_5831_;
}
}
else
{
uint8_t v___x_5832_; 
v___x_5832_ = 0;
v___y_5806_ = v___x_5832_;
goto v___jp_5805_;
}
v___jp_5673_:
{
lean_object* v___x_5683_; lean_object* v___x_5684_; 
v___x_5683_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5683_, 0, v___y_5674_);
v___x_5684_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5683_, v___y_5675_, v___y_5676_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v___x_5685_; 
lean_dec_ref_known(v___x_5684_, 1);
lean_inc(v___y_5682_);
lean_inc_ref(v___y_5681_);
lean_inc(v___y_5680_);
lean_inc_ref(v___y_5679_);
lean_inc(v___y_5678_);
lean_inc_ref(v___y_5677_);
lean_inc(v___y_5676_);
v___x_5685_ = lean_apply_9(v_k_5663_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, lean_box(0));
return v___x_5685_;
}
else
{
lean_object* v_a_5686_; lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5693_; 
lean_dec_ref(v___y_5675_);
lean_dec_ref(v_k_5663_);
v_a_5686_ = lean_ctor_get(v___x_5684_, 0);
v_isSharedCheck_5693_ = !lean_is_exclusive(v___x_5684_);
if (v_isSharedCheck_5693_ == 0)
{
v___x_5688_ = v___x_5684_;
v_isShared_5689_ = v_isSharedCheck_5693_;
goto v_resetjp_5687_;
}
else
{
lean_inc(v_a_5686_);
lean_dec(v___x_5684_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5693_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v___x_5691_; 
if (v_isShared_5689_ == 0)
{
v___x_5691_ = v___x_5688_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_a_5686_);
v___x_5691_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
return v___x_5691_;
}
}
}
}
v___jp_5694_:
{
lean_object* v___x_5706_; 
v___x_5706_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5697_, v_ps_5661_, v_only_5662_, v___y_5696_, v___y_5695_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_);
if (lean_obj_tag(v___x_5706_) == 0)
{
lean_object* v_a_5707_; lean_object* v_ctx_5708_; lean_object* v_anchorRefs_x3f_5709_; lean_object* v_toContext_5710_; lean_object* v_sctx_5711_; lean_object* v_methods_5712_; uint8_t v_sym_5713_; lean_object* v_simp_5714_; lean_object* v_simpMethods_5715_; lean_object* v_config_5716_; uint8_t v_cheapCases_5717_; uint8_t v_reportMVarIssue_5718_; lean_object* v_splitSource_5719_; lean_object* v_ematchDiagSource_5720_; lean_object* v_symPrios_5721_; lean_object* v_extensions_5722_; uint8_t v_debug_5723_; uint8_t v_ematchDiag_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; 
v_a_5707_ = lean_ctor_get(v___x_5706_, 0);
lean_inc_n(v_a_5707_, 2);
lean_dec_ref_known(v___x_5706_, 1);
v_ctx_5708_ = lean_ctor_get(v___y_5698_, 1);
v_anchorRefs_x3f_5709_ = lean_ctor_get(v_a_5707_, 8);
v_toContext_5710_ = lean_ctor_get(v___y_5698_, 0);
v_sctx_5711_ = lean_ctor_get(v___y_5698_, 2);
v_methods_5712_ = lean_ctor_get(v___y_5698_, 3);
v_sym_5713_ = lean_ctor_get_uint8(v___y_5698_, sizeof(void*)*5);
v_simp_5714_ = lean_ctor_get(v_ctx_5708_, 0);
v_simpMethods_5715_ = lean_ctor_get(v_ctx_5708_, 1);
v_config_5716_ = lean_ctor_get(v_ctx_5708_, 2);
v_cheapCases_5717_ = lean_ctor_get_uint8(v_ctx_5708_, sizeof(void*)*8);
v_reportMVarIssue_5718_ = lean_ctor_get_uint8(v_ctx_5708_, sizeof(void*)*8 + 1);
v_splitSource_5719_ = lean_ctor_get(v_ctx_5708_, 4);
v_ematchDiagSource_5720_ = lean_ctor_get(v_ctx_5708_, 5);
v_symPrios_5721_ = lean_ctor_get(v_ctx_5708_, 6);
v_extensions_5722_ = lean_ctor_get(v_ctx_5708_, 7);
v_debug_5723_ = lean_ctor_get_uint8(v_ctx_5708_, sizeof(void*)*8 + 2);
v_ematchDiag_5724_ = lean_ctor_get_uint8(v_ctx_5708_, sizeof(void*)*8 + 3);
lean_inc_ref(v_extensions_5722_);
lean_inc_ref(v_symPrios_5721_);
lean_inc(v_ematchDiagSource_5720_);
lean_inc(v_splitSource_5719_);
lean_inc(v_anchorRefs_x3f_5709_);
lean_inc_ref(v_config_5716_);
lean_inc_ref(v_simpMethods_5715_);
lean_inc_ref(v_simp_5714_);
v___x_5725_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_5725_, 0, v_simp_5714_);
lean_ctor_set(v___x_5725_, 1, v_simpMethods_5715_);
lean_ctor_set(v___x_5725_, 2, v_config_5716_);
lean_ctor_set(v___x_5725_, 3, v_anchorRefs_x3f_5709_);
lean_ctor_set(v___x_5725_, 4, v_splitSource_5719_);
lean_ctor_set(v___x_5725_, 5, v_ematchDiagSource_5720_);
lean_ctor_set(v___x_5725_, 6, v_symPrios_5721_);
lean_ctor_set(v___x_5725_, 7, v_extensions_5722_);
lean_ctor_set_uint8(v___x_5725_, sizeof(void*)*8, v_cheapCases_5717_);
lean_ctor_set_uint8(v___x_5725_, sizeof(void*)*8 + 1, v_reportMVarIssue_5718_);
lean_ctor_set_uint8(v___x_5725_, sizeof(void*)*8 + 2, v_debug_5723_);
lean_ctor_set_uint8(v___x_5725_, sizeof(void*)*8 + 3, v_ematchDiag_5724_);
lean_inc_ref(v_methods_5712_);
lean_inc_ref(v_sctx_5711_);
lean_inc_ref(v_toContext_5710_);
v___x_5726_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_5726_, 0, v_toContext_5710_);
lean_ctor_set(v___x_5726_, 1, v___x_5725_);
lean_ctor_set(v___x_5726_, 2, v_sctx_5711_);
lean_ctor_set(v___x_5726_, 3, v_methods_5712_);
lean_ctor_set(v___x_5726_, 4, v_a_5707_);
lean_ctor_set_uint8(v___x_5726_, sizeof(void*)*5, v_sym_5713_);
if (v_only_5662_ == 0)
{
v___y_5674_ = v_a_5707_;
v___y_5675_ = v___x_5726_;
v___y_5676_ = v___y_5699_;
v___y_5677_ = v___y_5700_;
v___y_5678_ = v___y_5701_;
v___y_5679_ = v___y_5702_;
v___y_5680_ = v___y_5703_;
v___y_5681_ = v___y_5704_;
v___y_5682_ = v___y_5705_;
goto v___jp_5673_;
}
else
{
lean_object* v___x_5727_; 
v___x_5727_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5699_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_);
if (lean_obj_tag(v___x_5727_) == 0)
{
lean_object* v_a_5728_; lean_object* v_toGoalState_5729_; lean_object* v_ematch_5730_; lean_object* v_mvarId_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5787_; 
v_a_5728_ = lean_ctor_get(v___x_5727_, 0);
lean_inc(v_a_5728_);
lean_dec_ref_known(v___x_5727_, 1);
v_toGoalState_5729_ = lean_ctor_get(v_a_5728_, 0);
lean_inc_ref(v_toGoalState_5729_);
v_ematch_5730_ = lean_ctor_get(v_toGoalState_5729_, 12);
lean_inc_ref(v_ematch_5730_);
v_mvarId_5731_ = lean_ctor_get(v_a_5728_, 1);
v_isSharedCheck_5787_ = !lean_is_exclusive(v_a_5728_);
if (v_isSharedCheck_5787_ == 0)
{
lean_object* v_unused_5788_; 
v_unused_5788_ = lean_ctor_get(v_a_5728_, 0);
lean_dec(v_unused_5788_);
v___x_5733_ = v_a_5728_;
v_isShared_5734_ = v_isSharedCheck_5787_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_mvarId_5731_);
lean_dec(v_a_5728_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5787_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v_nextDeclIdx_5735_; lean_object* v_enodeMap_5736_; lean_object* v_exprs_5737_; lean_object* v_parents_5738_; lean_object* v_congrTable_5739_; lean_object* v_appMap_5740_; lean_object* v_indicesFound_5741_; lean_object* v_newFacts_5742_; uint8_t v_inconsistent_5743_; lean_object* v_nextIdx_5744_; lean_object* v_newRawFacts_5745_; lean_object* v_facts_5746_; lean_object* v_extThms_5747_; lean_object* v_inj_5748_; lean_object* v_split_5749_; lean_object* v_clean_5750_; lean_object* v_sstates_5751_; lean_object* v_gmt_5752_; lean_object* v_thms_5753_; lean_object* v_newThms_5754_; lean_object* v_numInstances_5755_; lean_object* v_numDelayedInstances_5756_; lean_object* v_num_5757_; lean_object* v_preInstances_5758_; lean_object* v_nextThmIdx_5759_; lean_object* v_matchEqNames_5760_; lean_object* v_delayedThmInsts_5761_; lean_object* v___x_5762_; lean_object* v___f_5763_; lean_object* v___x_5764_; 
v_nextDeclIdx_5735_ = lean_ctor_get(v_toGoalState_5729_, 0);
lean_inc(v_nextDeclIdx_5735_);
v_enodeMap_5736_ = lean_ctor_get(v_toGoalState_5729_, 1);
lean_inc_ref(v_enodeMap_5736_);
v_exprs_5737_ = lean_ctor_get(v_toGoalState_5729_, 2);
lean_inc_ref(v_exprs_5737_);
v_parents_5738_ = lean_ctor_get(v_toGoalState_5729_, 3);
lean_inc_ref(v_parents_5738_);
v_congrTable_5739_ = lean_ctor_get(v_toGoalState_5729_, 4);
lean_inc_ref(v_congrTable_5739_);
v_appMap_5740_ = lean_ctor_get(v_toGoalState_5729_, 5);
lean_inc_ref(v_appMap_5740_);
v_indicesFound_5741_ = lean_ctor_get(v_toGoalState_5729_, 6);
lean_inc_ref(v_indicesFound_5741_);
v_newFacts_5742_ = lean_ctor_get(v_toGoalState_5729_, 7);
lean_inc_ref(v_newFacts_5742_);
v_inconsistent_5743_ = lean_ctor_get_uint8(v_toGoalState_5729_, sizeof(void*)*17);
v_nextIdx_5744_ = lean_ctor_get(v_toGoalState_5729_, 8);
lean_inc(v_nextIdx_5744_);
v_newRawFacts_5745_ = lean_ctor_get(v_toGoalState_5729_, 9);
lean_inc_ref(v_newRawFacts_5745_);
v_facts_5746_ = lean_ctor_get(v_toGoalState_5729_, 10);
lean_inc_ref(v_facts_5746_);
v_extThms_5747_ = lean_ctor_get(v_toGoalState_5729_, 11);
lean_inc_ref(v_extThms_5747_);
v_inj_5748_ = lean_ctor_get(v_toGoalState_5729_, 13);
lean_inc_ref(v_inj_5748_);
v_split_5749_ = lean_ctor_get(v_toGoalState_5729_, 14);
lean_inc_ref(v_split_5749_);
v_clean_5750_ = lean_ctor_get(v_toGoalState_5729_, 15);
lean_inc_ref(v_clean_5750_);
v_sstates_5751_ = lean_ctor_get(v_toGoalState_5729_, 16);
lean_inc_ref(v_sstates_5751_);
lean_dec_ref(v_toGoalState_5729_);
v_gmt_5752_ = lean_ctor_get(v_ematch_5730_, 1);
lean_inc(v_gmt_5752_);
v_thms_5753_ = lean_ctor_get(v_ematch_5730_, 2);
lean_inc_ref(v_thms_5753_);
v_newThms_5754_ = lean_ctor_get(v_ematch_5730_, 3);
lean_inc_ref(v_newThms_5754_);
v_numInstances_5755_ = lean_ctor_get(v_ematch_5730_, 4);
lean_inc(v_numInstances_5755_);
v_numDelayedInstances_5756_ = lean_ctor_get(v_ematch_5730_, 5);
lean_inc(v_numDelayedInstances_5756_);
v_num_5757_ = lean_ctor_get(v_ematch_5730_, 6);
lean_inc(v_num_5757_);
v_preInstances_5758_ = lean_ctor_get(v_ematch_5730_, 7);
lean_inc_ref(v_preInstances_5758_);
v_nextThmIdx_5759_ = lean_ctor_get(v_ematch_5730_, 8);
lean_inc(v_nextThmIdx_5759_);
v_matchEqNames_5760_ = lean_ctor_get(v_ematch_5730_, 9);
lean_inc_ref(v_matchEqNames_5760_);
v_delayedThmInsts_5761_ = lean_ctor_get(v_ematch_5730_, 10);
lean_inc_ref(v_delayedThmInsts_5761_);
lean_dec_ref(v_ematch_5730_);
v___x_5762_ = lean_box(v_inconsistent_5743_);
v___f_5763_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 38, 28);
lean_closure_set(v___f_5763_, 0, v_thms_5753_);
lean_closure_set(v___f_5763_, 1, v_newThms_5754_);
lean_closure_set(v___f_5763_, 2, v_gmt_5752_);
lean_closure_set(v___f_5763_, 3, v_numInstances_5755_);
lean_closure_set(v___f_5763_, 4, v_numDelayedInstances_5756_);
lean_closure_set(v___f_5763_, 5, v_num_5757_);
lean_closure_set(v___f_5763_, 6, v_preInstances_5758_);
lean_closure_set(v___f_5763_, 7, v_nextThmIdx_5759_);
lean_closure_set(v___f_5763_, 8, v_matchEqNames_5760_);
lean_closure_set(v___f_5763_, 9, v_delayedThmInsts_5761_);
lean_closure_set(v___f_5763_, 10, v_nextDeclIdx_5735_);
lean_closure_set(v___f_5763_, 11, v_enodeMap_5736_);
lean_closure_set(v___f_5763_, 12, v_exprs_5737_);
lean_closure_set(v___f_5763_, 13, v_parents_5738_);
lean_closure_set(v___f_5763_, 14, v_congrTable_5739_);
lean_closure_set(v___f_5763_, 15, v_appMap_5740_);
lean_closure_set(v___f_5763_, 16, v_indicesFound_5741_);
lean_closure_set(v___f_5763_, 17, v_newFacts_5742_);
lean_closure_set(v___f_5763_, 18, v___x_5762_);
lean_closure_set(v___f_5763_, 19, v_nextIdx_5744_);
lean_closure_set(v___f_5763_, 20, v_newRawFacts_5745_);
lean_closure_set(v___f_5763_, 21, v_facts_5746_);
lean_closure_set(v___f_5763_, 22, v_extThms_5747_);
lean_closure_set(v___f_5763_, 23, v_inj_5748_);
lean_closure_set(v___f_5763_, 24, v_split_5749_);
lean_closure_set(v___f_5763_, 25, v_clean_5750_);
lean_closure_set(v___f_5763_, 26, v_sstates_5751_);
lean_closure_set(v___f_5763_, 27, v_mvarId_5731_);
v___x_5764_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5763_, v___x_5726_, v___y_5699_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_);
if (lean_obj_tag(v___x_5764_) == 0)
{
lean_object* v_a_5765_; lean_object* v___x_5766_; lean_object* v___x_5768_; 
v_a_5765_ = lean_ctor_get(v___x_5764_, 0);
lean_inc(v_a_5765_);
lean_dec_ref_known(v___x_5764_, 1);
v___x_5766_ = lean_box(0);
if (v_isShared_5734_ == 0)
{
lean_ctor_set_tag(v___x_5733_, 1);
lean_ctor_set(v___x_5733_, 1, v___x_5766_);
lean_ctor_set(v___x_5733_, 0, v_a_5765_);
v___x_5768_ = v___x_5733_;
goto v_reusejp_5767_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_a_5765_);
lean_ctor_set(v_reuseFailAlloc_5778_, 1, v___x_5766_);
v___x_5768_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5767_;
}
v_reusejp_5767_:
{
lean_object* v___x_5769_; 
v___x_5769_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5768_, v___y_5699_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_);
if (lean_obj_tag(v___x_5769_) == 0)
{
lean_dec_ref_known(v___x_5769_, 1);
v___y_5674_ = v_a_5707_;
v___y_5675_ = v___x_5726_;
v___y_5676_ = v___y_5699_;
v___y_5677_ = v___y_5700_;
v___y_5678_ = v___y_5701_;
v___y_5679_ = v___y_5702_;
v___y_5680_ = v___y_5703_;
v___y_5681_ = v___y_5704_;
v___y_5682_ = v___y_5705_;
goto v___jp_5673_;
}
else
{
lean_object* v_a_5770_; lean_object* v___x_5772_; uint8_t v_isShared_5773_; uint8_t v_isSharedCheck_5777_; 
lean_dec_ref_known(v___x_5726_, 5);
lean_dec(v_a_5707_);
lean_dec_ref(v_k_5663_);
v_a_5770_ = lean_ctor_get(v___x_5769_, 0);
v_isSharedCheck_5777_ = !lean_is_exclusive(v___x_5769_);
if (v_isSharedCheck_5777_ == 0)
{
v___x_5772_ = v___x_5769_;
v_isShared_5773_ = v_isSharedCheck_5777_;
goto v_resetjp_5771_;
}
else
{
lean_inc(v_a_5770_);
lean_dec(v___x_5769_);
v___x_5772_ = lean_box(0);
v_isShared_5773_ = v_isSharedCheck_5777_;
goto v_resetjp_5771_;
}
v_resetjp_5771_:
{
lean_object* v___x_5775_; 
if (v_isShared_5773_ == 0)
{
v___x_5775_ = v___x_5772_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v_a_5770_);
v___x_5775_ = v_reuseFailAlloc_5776_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
return v___x_5775_;
}
}
}
}
}
else
{
lean_object* v_a_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5786_; 
lean_del_object(v___x_5733_);
lean_dec_ref_known(v___x_5726_, 5);
lean_dec(v_a_5707_);
lean_dec_ref(v_k_5663_);
v_a_5779_ = lean_ctor_get(v___x_5764_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v___x_5764_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5781_ = v___x_5764_;
v_isShared_5782_ = v_isSharedCheck_5786_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_a_5779_);
lean_dec(v___x_5764_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5786_;
goto v_resetjp_5780_;
}
v_resetjp_5780_:
{
lean_object* v___x_5784_; 
if (v_isShared_5782_ == 0)
{
v___x_5784_ = v___x_5781_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v_a_5779_);
v___x_5784_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
return v___x_5784_;
}
}
}
}
}
else
{
lean_object* v_a_5789_; lean_object* v___x_5791_; uint8_t v_isShared_5792_; uint8_t v_isSharedCheck_5796_; 
lean_dec_ref_known(v___x_5726_, 5);
lean_dec(v_a_5707_);
lean_dec_ref(v_k_5663_);
v_a_5789_ = lean_ctor_get(v___x_5727_, 0);
v_isSharedCheck_5796_ = !lean_is_exclusive(v___x_5727_);
if (v_isSharedCheck_5796_ == 0)
{
v___x_5791_ = v___x_5727_;
v_isShared_5792_ = v_isSharedCheck_5796_;
goto v_resetjp_5790_;
}
else
{
lean_inc(v_a_5789_);
lean_dec(v___x_5727_);
v___x_5791_ = lean_box(0);
v_isShared_5792_ = v_isSharedCheck_5796_;
goto v_resetjp_5790_;
}
v_resetjp_5790_:
{
lean_object* v___x_5794_; 
if (v_isShared_5792_ == 0)
{
v___x_5794_ = v___x_5791_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_a_5789_);
v___x_5794_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
return v___x_5794_;
}
}
}
}
}
else
{
lean_object* v_a_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5804_; 
lean_dec_ref(v_k_5663_);
v_a_5797_ = lean_ctor_get(v___x_5706_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v___x_5706_);
if (v_isSharedCheck_5804_ == 0)
{
v___x_5799_ = v___x_5706_;
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_a_5797_);
lean_dec(v___x_5706_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v___x_5802_; 
if (v_isShared_5800_ == 0)
{
v___x_5802_ = v___x_5799_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_a_5797_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
}
v___jp_5805_:
{
uint8_t v___x_5807_; 
v___x_5807_ = 1;
if (v_only_5662_ == 0)
{
v___y_5695_ = v___x_5807_;
v___y_5696_ = v___y_5806_;
v_params_5697_ = v_params_5660_;
v___y_5698_ = v_a_5664_;
v___y_5699_ = v_a_5665_;
v___y_5700_ = v_a_5666_;
v___y_5701_ = v_a_5667_;
v___y_5702_ = v_a_5668_;
v___y_5703_ = v_a_5669_;
v___y_5704_ = v_a_5670_;
v___y_5705_ = v_a_5671_;
goto v___jp_5694_;
}
else
{
lean_object* v_config_5808_; lean_object* v_extensions_5809_; lean_object* v_extra_5810_; lean_object* v_extraInj_5811_; lean_object* v_extraFacts_5812_; lean_object* v_symPrios_5813_; lean_object* v_norm_5814_; lean_object* v_normProcs_5815_; lean_object* v___x_5817_; uint8_t v_isShared_5818_; uint8_t v_isSharedCheck_5826_; 
v_config_5808_ = lean_ctor_get(v_params_5660_, 0);
v_extensions_5809_ = lean_ctor_get(v_params_5660_, 1);
v_extra_5810_ = lean_ctor_get(v_params_5660_, 2);
v_extraInj_5811_ = lean_ctor_get(v_params_5660_, 3);
v_extraFacts_5812_ = lean_ctor_get(v_params_5660_, 4);
v_symPrios_5813_ = lean_ctor_get(v_params_5660_, 5);
v_norm_5814_ = lean_ctor_get(v_params_5660_, 6);
v_normProcs_5815_ = lean_ctor_get(v_params_5660_, 7);
v_isSharedCheck_5826_ = !lean_is_exclusive(v_params_5660_);
if (v_isSharedCheck_5826_ == 0)
{
lean_object* v_unused_5827_; 
v_unused_5827_ = lean_ctor_get(v_params_5660_, 8);
lean_dec(v_unused_5827_);
v___x_5817_ = v_params_5660_;
v_isShared_5818_ = v_isSharedCheck_5826_;
goto v_resetjp_5816_;
}
else
{
lean_inc(v_normProcs_5815_);
lean_inc(v_norm_5814_);
lean_inc(v_symPrios_5813_);
lean_inc(v_extraFacts_5812_);
lean_inc(v_extraInj_5811_);
lean_inc(v_extra_5810_);
lean_inc(v_extensions_5809_);
lean_inc(v_config_5808_);
lean_dec(v_params_5660_);
v___x_5817_ = lean_box(0);
v_isShared_5818_ = v_isSharedCheck_5826_;
goto v_resetjp_5816_;
}
v_resetjp_5816_:
{
size_t v_sz_5819_; size_t v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v_params_5824_; 
v_sz_5819_ = lean_array_size(v_extensions_5809_);
v___x_5820_ = ((size_t)0ULL);
v___x_5821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5819_, v___x_5820_, v_extensions_5809_);
v___x_5822_ = lean_box(0);
if (v_isShared_5818_ == 0)
{
lean_ctor_set(v___x_5817_, 8, v___x_5822_);
lean_ctor_set(v___x_5817_, 1, v___x_5821_);
v_params_5824_ = v___x_5817_;
goto v_reusejp_5823_;
}
else
{
lean_object* v_reuseFailAlloc_5825_; 
v_reuseFailAlloc_5825_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5825_, 0, v_config_5808_);
lean_ctor_set(v_reuseFailAlloc_5825_, 1, v___x_5821_);
lean_ctor_set(v_reuseFailAlloc_5825_, 2, v_extra_5810_);
lean_ctor_set(v_reuseFailAlloc_5825_, 3, v_extraInj_5811_);
lean_ctor_set(v_reuseFailAlloc_5825_, 4, v_extraFacts_5812_);
lean_ctor_set(v_reuseFailAlloc_5825_, 5, v_symPrios_5813_);
lean_ctor_set(v_reuseFailAlloc_5825_, 6, v_norm_5814_);
lean_ctor_set(v_reuseFailAlloc_5825_, 7, v_normProcs_5815_);
lean_ctor_set(v_reuseFailAlloc_5825_, 8, v___x_5822_);
v_params_5824_ = v_reuseFailAlloc_5825_;
goto v_reusejp_5823_;
}
v_reusejp_5823_:
{
v___y_5695_ = v___x_5807_;
v___y_5696_ = v___y_5806_;
v_params_5697_ = v_params_5824_;
v___y_5698_ = v_a_5664_;
v___y_5699_ = v_a_5665_;
v___y_5700_ = v_a_5666_;
v___y_5701_ = v_a_5667_;
v___y_5702_ = v_a_5668_;
v___y_5703_ = v_a_5669_;
v___y_5704_ = v_a_5670_;
v___y_5705_ = v_a_5671_;
goto v___jp_5694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_5833_, lean_object* v_ps_5834_, lean_object* v_only_5835_, lean_object* v_k_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_){
_start:
{
uint8_t v_only_boxed_5846_; lean_object* v_res_5847_; 
v_only_boxed_5846_ = lean_unbox(v_only_5835_);
v_res_5847_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5833_, v_ps_5834_, v_only_boxed_5846_, v_k_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_);
lean_dec(v_a_5844_);
lean_dec_ref(v_a_5843_);
lean_dec(v_a_5842_);
lean_dec_ref(v_a_5841_);
lean_dec(v_a_5840_);
lean_dec_ref(v_a_5839_);
lean_dec(v_a_5838_);
lean_dec_ref(v_a_5837_);
lean_dec_ref(v_ps_5834_);
return v_res_5847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_5848_, lean_object* v_params_5849_, lean_object* v_ps_5850_, uint8_t v_only_5851_, lean_object* v_k_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_){
_start:
{
lean_object* v___x_5862_; 
v___x_5862_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5849_, v_ps_5850_, v_only_5851_, v_k_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_);
return v___x_5862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_5863_, lean_object* v_params_5864_, lean_object* v_ps_5865_, lean_object* v_only_5866_, lean_object* v_k_5867_, lean_object* v_a_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_, lean_object* v_a_5873_, lean_object* v_a_5874_, lean_object* v_a_5875_, lean_object* v_a_5876_){
_start:
{
uint8_t v_only_boxed_5877_; lean_object* v_res_5878_; 
v_only_boxed_5877_ = lean_unbox(v_only_5866_);
v_res_5878_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_5863_, v_params_5864_, v_ps_5865_, v_only_boxed_5877_, v_k_5867_, v_a_5868_, v_a_5869_, v_a_5870_, v_a_5871_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_);
lean_dec(v_a_5875_);
lean_dec_ref(v_a_5874_);
lean_dec(v_a_5873_);
lean_dec_ref(v_a_5872_);
lean_dec(v_a_5871_);
lean_dec_ref(v_a_5870_);
lean_dec(v_a_5869_);
lean_dec_ref(v_a_5868_);
lean_dec_ref(v_ps_5865_);
return v_res_5878_;
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
