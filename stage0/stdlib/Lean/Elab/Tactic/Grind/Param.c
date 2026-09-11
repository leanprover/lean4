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
lean_object* v___x_573_; lean_object* v_env_574_; lean_object* v___x_575_; lean_object* v_toCold_576_; lean_object* v_mctx_577_; lean_object* v_lctx_578_; lean_object* v_options_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_573_ = lean_st_ref_get(v___y_571_);
v_env_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_env_574_);
lean_dec(v___x_573_);
v___x_575_ = lean_st_ref_get(v___y_569_);
v_toCold_576_ = lean_ctor_get(v___y_570_, 0);
v_mctx_577_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_mctx_577_);
lean_dec(v___x_575_);
v_lctx_578_ = lean_ctor_get(v___y_568_, 2);
v_options_579_ = lean_ctor_get(v_toCold_576_, 2);
lean_inc_ref(v_options_579_);
lean_inc_ref(v_lctx_578_);
v___x_580_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_580_, 0, v_env_574_);
lean_ctor_set(v___x_580_, 1, v_mctx_577_);
lean_ctor_set(v___x_580_, 2, v_lctx_578_);
lean_ctor_set(v___x_580_, 3, v_options_579_);
v___x_581_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_msgData_567_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_msgData_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msgData_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_589_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_590_, lean_object* v_opt_591_){
_start:
{
lean_object* v_name_592_; lean_object* v_defValue_593_; lean_object* v_map_594_; lean_object* v___x_595_; 
v_name_592_ = lean_ctor_get(v_opt_591_, 0);
v_defValue_593_ = lean_ctor_get(v_opt_591_, 1);
v_map_594_ = lean_ctor_get(v_opts_590_, 0);
v___x_595_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_594_, v_name_592_);
if (lean_obj_tag(v___x_595_) == 0)
{
uint8_t v___x_596_; 
v___x_596_ = lean_unbox(v_defValue_593_);
return v___x_596_;
}
else
{
lean_object* v_val_597_; 
v_val_597_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v___x_595_, 1);
if (lean_obj_tag(v_val_597_) == 1)
{
uint8_t v_v_598_; 
v_v_598_ = lean_ctor_get_uint8(v_val_597_, 0);
lean_dec_ref_known(v_val_597_, 0);
return v_v_598_;
}
else
{
uint8_t v___x_599_; 
lean_dec(v_val_597_);
v___x_599_ = lean_unbox(v_defValue_593_);
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_600_, lean_object* v_opt_601_){
_start:
{
uint8_t v_res_602_; lean_object* v_r_603_; 
v_res_602_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_opts_600_, v_opt_601_);
lean_dec_ref(v_opt_601_);
lean_dec_ref(v_opts_600_);
v_r_603_ = lean_box(v_res_602_);
return v_r_603_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_612_, uint8_t v___y_613_, lean_object* v_x_614_){
_start:
{
if (lean_obj_tag(v_x_614_) == 1)
{
lean_object* v_pre_615_; 
v_pre_615_ = lean_ctor_get(v_x_614_, 0);
switch(lean_obj_tag(v_pre_615_))
{
case 1:
{
lean_object* v_pre_616_; 
v_pre_616_ = lean_ctor_get(v_pre_615_, 0);
switch(lean_obj_tag(v_pre_616_))
{
case 0:
{
lean_object* v_str_617_; lean_object* v_str_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_str_617_ = lean_ctor_get(v_x_614_, 1);
v_str_618_ = lean_ctor_get(v_pre_615_, 1);
v___x_619_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_620_ = lean_string_dec_eq(v_str_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_622_ = lean_string_dec_eq(v_str_618_, v___x_621_);
if (v___x_622_ == 0)
{
return v___x_622_;
}
else
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_624_ = lean_string_dec_eq(v_str_617_, v___x_623_);
if (v___x_624_ == 0)
{
return v___x_624_;
}
else
{
return v_suppressElabErrors_612_;
}
}
}
else
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_626_ = lean_string_dec_eq(v_str_617_, v___x_625_);
if (v___x_626_ == 0)
{
return v___x_626_;
}
else
{
return v_suppressElabErrors_612_;
}
}
}
case 1:
{
lean_object* v_pre_627_; 
v_pre_627_ = lean_ctor_get(v_pre_616_, 0);
if (lean_obj_tag(v_pre_627_) == 0)
{
lean_object* v_str_628_; lean_object* v_str_629_; lean_object* v_str_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_str_628_ = lean_ctor_get(v_x_614_, 1);
v_str_629_ = lean_ctor_get(v_pre_615_, 1);
v_str_630_ = lean_ctor_get(v_pre_616_, 1);
v___x_631_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_632_ = lean_string_dec_eq(v_str_630_, v___x_631_);
if (v___x_632_ == 0)
{
return v___x_632_;
}
else
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_634_ = lean_string_dec_eq(v_str_629_, v___x_633_);
if (v___x_634_ == 0)
{
return v___x_634_;
}
else
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_636_ = lean_string_dec_eq(v_str_628_, v___x_635_);
if (v___x_636_ == 0)
{
return v___x_636_;
}
else
{
return v_suppressElabErrors_612_;
}
}
}
}
else
{
return v___y_613_;
}
}
default: 
{
return v___y_613_;
}
}
}
case 0:
{
lean_object* v_str_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_str_637_ = lean_ctor_get(v_x_614_, 1);
v___x_638_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_639_ = lean_string_dec_eq(v_str_637_, v___x_638_);
if (v___x_639_ == 0)
{
return v___x_639_;
}
else
{
return v_suppressElabErrors_612_;
}
}
default: 
{
return v___y_613_;
}
}
}
else
{
return v___y_613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_640_, lean_object* v___y_641_, lean_object* v_x_642_){
_start:
{
uint8_t v_suppressElabErrors_boxed_643_; uint8_t v___y_4484__boxed_644_; uint8_t v_res_645_; lean_object* v_r_646_; 
v_suppressElabErrors_boxed_643_ = lean_unbox(v_suppressElabErrors_640_);
v___y_4484__boxed_644_ = lean_unbox(v___y_641_);
v_res_645_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_643_, v___y_4484__boxed_644_, v_x_642_);
lean_dec(v_x_642_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_648_, lean_object* v_msgData_649_, uint8_t v_severity_650_, uint8_t v_isSilent_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___y_658_; uint8_t v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; uint8_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_695_; lean_object* v___y_696_; uint8_t v___y_697_; uint8_t v___y_698_; lean_object* v___y_699_; uint8_t v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_720_; lean_object* v___y_721_; uint8_t v___y_722_; lean_object* v___y_723_; uint8_t v___y_724_; lean_object* v___y_725_; uint8_t v___y_726_; lean_object* v___y_727_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; uint8_t v___y_734_; lean_object* v___y_735_; uint8_t v___y_736_; uint8_t v___y_737_; uint8_t v___x_742_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; uint8_t v___y_748_; uint8_t v___y_749_; uint8_t v___y_750_; uint8_t v___y_752_; uint8_t v___x_768_; 
v___x_742_ = 2;
v___x_768_ = l_Lean_instBEqMessageSeverity_beq(v_severity_650_, v___x_742_);
if (v___x_768_ == 0)
{
v___y_752_ = v___x_768_;
goto v___jp_751_;
}
else
{
uint8_t v___x_769_; 
lean_inc_ref(v_msgData_649_);
v___x_769_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_649_);
v___y_752_ = v___x_769_;
goto v___jp_751_;
}
v___jp_657_:
{
lean_object* v___x_667_; lean_object* v_toCold_668_; lean_object* v_currNamespace_669_; lean_object* v_openDecls_670_; lean_object* v_env_671_; lean_object* v_nextMacroScope_672_; lean_object* v_ngen_673_; lean_object* v_auxDeclNGen_674_; lean_object* v_traceState_675_; lean_object* v_cache_676_; lean_object* v_messages_677_; lean_object* v_infoState_678_; lean_object* v_snapshotTasks_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_693_; 
v___x_667_ = lean_st_ref_take(v___y_666_);
v_toCold_668_ = lean_ctor_get(v___y_665_, 0);
v_currNamespace_669_ = lean_ctor_get(v_toCold_668_, 4);
v_openDecls_670_ = lean_ctor_get(v_toCold_668_, 5);
v_env_671_ = lean_ctor_get(v___x_667_, 0);
v_nextMacroScope_672_ = lean_ctor_get(v___x_667_, 1);
v_ngen_673_ = lean_ctor_get(v___x_667_, 2);
v_auxDeclNGen_674_ = lean_ctor_get(v___x_667_, 3);
v_traceState_675_ = lean_ctor_get(v___x_667_, 4);
v_cache_676_ = lean_ctor_get(v___x_667_, 5);
v_messages_677_ = lean_ctor_get(v___x_667_, 6);
v_infoState_678_ = lean_ctor_get(v___x_667_, 7);
v_snapshotTasks_679_ = lean_ctor_get(v___x_667_, 8);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_693_ == 0)
{
v___x_681_ = v___x_667_;
v_isShared_682_ = v_isSharedCheck_693_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snapshotTasks_679_);
lean_inc(v_infoState_678_);
lean_inc(v_messages_677_);
lean_inc(v_cache_676_);
lean_inc(v_traceState_675_);
lean_inc(v_auxDeclNGen_674_);
lean_inc(v_ngen_673_);
lean_inc(v_nextMacroScope_672_);
lean_inc(v_env_671_);
lean_dec(v___x_667_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_693_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
lean_inc(v_openDecls_670_);
lean_inc(v_currNamespace_669_);
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v_currNamespace_669_);
lean_ctor_set(v___x_683_, 1, v_openDecls_670_);
v___x_684_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___y_664_);
lean_inc_ref(v___y_661_);
lean_inc_ref(v___y_658_);
v___x_685_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_685_, 0, v___y_658_);
lean_ctor_set(v___x_685_, 1, v___y_663_);
lean_ctor_set(v___x_685_, 2, v___y_660_);
lean_ctor_set(v___x_685_, 3, v___y_661_);
lean_ctor_set(v___x_685_, 4, v___x_684_);
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*5, v___y_662_);
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*5 + 1, v___y_659_);
lean_ctor_set_uint8(v___x_685_, sizeof(void*)*5 + 2, v_isSilent_651_);
v___x_686_ = l_Lean_MessageLog_add(v___x_685_, v_messages_677_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 6, v___x_686_);
v___x_688_ = v___x_681_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_env_671_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_nextMacroScope_672_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_ngen_673_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_auxDeclNGen_674_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_traceState_675_);
lean_ctor_set(v_reuseFailAlloc_692_, 5, v_cache_676_);
lean_ctor_set(v_reuseFailAlloc_692_, 6, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_692_, 7, v_infoState_678_);
lean_ctor_set(v_reuseFailAlloc_692_, 8, v_snapshotTasks_679_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_st_ref_put(v___y_666_, v___x_688_);
v___x_690_ = lean_box(0);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
}
v___jp_694_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_718_; 
v___x_703_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_649_);
v___x_704_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_703_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_718_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_718_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_718_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_inc_ref_n(v___y_699_, 2);
v___x_709_ = l_Lean_FileMap_toPosition(v___y_699_, v___y_701_);
lean_dec(v___y_701_);
v___x_710_ = l_Lean_FileMap_toPosition(v___y_699_, v___y_702_);
lean_dec(v___y_702_);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
v___x_712_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_700_ == 0)
{
lean_del_object(v___x_707_);
lean_dec_ref(v___y_695_);
v___y_658_ = v___y_696_;
v___y_659_ = v___y_697_;
v___y_660_ = v___x_711_;
v___y_661_ = v___x_712_;
v___y_662_ = v___y_698_;
v___y_663_ = v___x_709_;
v___y_664_ = v_a_705_;
v___y_665_ = v___y_654_;
v___y_666_ = v___y_655_;
goto v___jp_657_;
}
else
{
uint8_t v___x_713_; 
lean_inc(v_a_705_);
v___x_713_ = l_Lean_MessageData_hasTag(v___y_695_, v_a_705_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_716_; 
lean_dec_ref_known(v___x_711_, 1);
lean_dec_ref(v___x_709_);
lean_dec(v_a_705_);
v___x_714_ = lean_box(0);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_714_);
v___x_716_ = v___x_707_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
else
{
lean_del_object(v___x_707_);
v___y_658_ = v___y_696_;
v___y_659_ = v___y_697_;
v___y_660_ = v___x_711_;
v___y_661_ = v___x_712_;
v___y_662_ = v___y_698_;
v___y_663_ = v___x_709_;
v___y_664_ = v_a_705_;
v___y_665_ = v___y_654_;
v___y_666_ = v___y_655_;
goto v___jp_657_;
}
}
}
}
v___jp_719_:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Syntax_getTailPos_x3f(v___y_725_, v___y_724_);
lean_dec(v___y_725_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_inc(v___y_727_);
v___y_695_ = v___y_720_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_722_;
v___y_698_ = v___y_724_;
v___y_699_ = v___y_723_;
v___y_700_ = v___y_726_;
v___y_701_ = v___y_727_;
v___y_702_ = v___y_727_;
goto v___jp_694_;
}
else
{
lean_object* v_val_729_; 
v_val_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_val_729_);
lean_dec_ref_known(v___x_728_, 1);
v___y_695_ = v___y_720_;
v___y_696_ = v___y_721_;
v___y_697_ = v___y_722_;
v___y_698_ = v___y_724_;
v___y_699_ = v___y_723_;
v___y_700_ = v___y_726_;
v___y_701_ = v___y_727_;
v___y_702_ = v_val_729_;
goto v___jp_694_;
}
}
v___jp_730_:
{
lean_object* v_ref_738_; lean_object* v___x_739_; 
v_ref_738_ = l_Lean_replaceRef(v_ref_648_, v___y_733_);
v___x_739_ = l_Lean_Syntax_getPos_x3f(v_ref_738_, v___y_734_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v___x_740_; 
v___x_740_ = lean_unsigned_to_nat(0u);
v___y_720_ = v___y_731_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_737_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_734_;
v___y_725_ = v_ref_738_;
v___y_726_ = v___y_736_;
v___y_727_ = v___x_740_;
goto v___jp_719_;
}
else
{
lean_object* v_val_741_; 
v_val_741_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v___x_739_, 1);
v___y_720_ = v___y_731_;
v___y_721_ = v___y_732_;
v___y_722_ = v___y_737_;
v___y_723_ = v___y_735_;
v___y_724_ = v___y_734_;
v___y_725_ = v_ref_738_;
v___y_726_ = v___y_736_;
v___y_727_ = v_val_741_;
goto v___jp_719_;
}
}
v___jp_743_:
{
if (v___y_750_ == 0)
{
v___y_731_ = v___y_746_;
v___y_732_ = v___y_744_;
v___y_733_ = v___y_747_;
v___y_734_ = v___y_748_;
v___y_735_ = v___y_745_;
v___y_736_ = v___y_749_;
v___y_737_ = v_severity_650_;
goto v___jp_730_;
}
else
{
v___y_731_ = v___y_746_;
v___y_732_ = v___y_744_;
v___y_733_ = v___y_747_;
v___y_734_ = v___y_748_;
v___y_735_ = v___y_745_;
v___y_736_ = v___y_749_;
v___y_737_ = v___x_742_;
goto v___jp_730_;
}
}
v___jp_751_:
{
if (v___y_752_ == 0)
{
lean_object* v_toCold_753_; lean_object* v_ref_754_; uint8_t v_suppressElabErrors_755_; lean_object* v_fileName_756_; lean_object* v_fileMap_757_; lean_object* v_options_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___f_761_; uint8_t v___x_762_; uint8_t v___x_763_; 
v_toCold_753_ = lean_ctor_get(v___y_654_, 0);
v_ref_754_ = lean_ctor_get(v___y_654_, 2);
v_suppressElabErrors_755_ = lean_ctor_get_uint8(v___y_654_, sizeof(void*)*3 + 1);
v_fileName_756_ = lean_ctor_get(v_toCold_753_, 0);
v_fileMap_757_ = lean_ctor_get(v_toCold_753_, 1);
v_options_758_ = lean_ctor_get(v_toCold_753_, 2);
v___x_759_ = lean_box(v_suppressElabErrors_755_);
v___x_760_ = lean_box(v___y_752_);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_761_, 0, v___x_759_);
lean_closure_set(v___f_761_, 1, v___x_760_);
v___x_762_ = 1;
v___x_763_ = l_Lean_instBEqMessageSeverity_beq(v_severity_650_, v___x_762_);
if (v___x_763_ == 0)
{
v___y_744_ = v_fileName_756_;
v___y_745_ = v_fileMap_757_;
v___y_746_ = v___f_761_;
v___y_747_ = v_ref_754_;
v___y_748_ = v___y_752_;
v___y_749_ = v_suppressElabErrors_755_;
v___y_750_ = v___x_763_;
goto v___jp_743_;
}
else
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = l_Lean_warningAsError;
v___x_765_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_758_, v___x_764_);
v___y_744_ = v_fileName_756_;
v___y_745_ = v_fileMap_757_;
v___y_746_ = v___f_761_;
v___y_747_ = v_ref_754_;
v___y_748_ = v___y_752_;
v___y_749_ = v_suppressElabErrors_755_;
v___y_750_ = v___x_765_;
goto v___jp_743_;
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec_ref(v_msgData_649_);
v___x_766_ = lean_box(0);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_770_, lean_object* v_msgData_771_, lean_object* v_severity_772_, lean_object* v_isSilent_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
uint8_t v_severity_boxed_779_; uint8_t v_isSilent_boxed_780_; lean_object* v_res_781_; 
v_severity_boxed_779_ = lean_unbox(v_severity_772_);
v_isSilent_boxed_780_ = lean_unbox(v_isSilent_773_);
v_res_781_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_770_, v_msgData_771_, v_severity_boxed_779_, v_isSilent_boxed_780_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v_ref_770_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_782_, uint8_t v_severity_783_, uint8_t v_isSilent_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_ref_790_; lean_object* v___x_791_; 
v_ref_790_ = lean_ctor_get(v___y_787_, 2);
v___x_791_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_790_, v_msgData_782_, v_severity_783_, v_isSilent_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_792_, lean_object* v_severity_793_, lean_object* v_isSilent_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
uint8_t v_severity_boxed_800_; uint8_t v_isSilent_boxed_801_; lean_object* v_res_802_; 
v_severity_boxed_800_ = lean_unbox(v_severity_793_);
v_isSilent_boxed_801_ = lean_unbox(v_isSilent_794_);
v_res_802_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_792_, v_severity_boxed_800_, v_isSilent_boxed_801_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; 
v___x_809_ = 1;
v___x_810_ = 0;
v___x_811_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_803_, v___x_809_, v___x_810_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
return v_res_818_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_821_ = l_Lean_stringToMessageData(v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
if (lean_obj_tag(v_a_822_) == 0)
{
lean_object* v___x_824_; 
v___x_824_ = l_List_reverse___redArg(v_a_823_);
return v___x_824_;
}
else
{
lean_object* v_head_825_; lean_object* v_tail_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_839_; 
v_head_825_ = lean_ctor_get(v_a_822_, 0);
v_tail_826_ = lean_ctor_get(v_a_822_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_a_822_);
if (v_isSharedCheck_839_ == 0)
{
v___x_828_ = v_a_822_;
v_isShared_829_ = v_isSharedCheck_839_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_tail_826_);
lean_inc(v_head_825_);
lean_dec(v_a_822_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_839_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
uint8_t v_minIndexable_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v_minIndexable_830_ = 0;
v___x_831_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_832_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_825_, v_minIndexable_830_);
lean_dec(v_head_825_);
v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_831_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v_a_823_);
lean_ctor_set(v___x_828_, 0, v___x_834_);
v___x_836_ = v___x_828_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_a_823_);
v___x_836_ = v_reuseFailAlloc_838_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
v_a_822_ = v_tail_826_;
v_a_823_ = v___x_836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
if (lean_obj_tag(v_a_840_) == 0)
{
lean_object* v___x_842_; 
v___x_842_ = l_List_reverse___redArg(v_a_841_);
return v___x_842_;
}
else
{
lean_object* v_head_843_; lean_object* v_tail_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_852_; 
v_head_843_ = lean_ctor_get(v_a_840_, 0);
v_tail_844_ = lean_ctor_get(v_a_840_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_a_840_);
if (v_isSharedCheck_852_ == 0)
{
v___x_846_ = v_a_840_;
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_tail_844_);
lean_inc(v_head_843_);
lean_dec(v_a_840_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v_a_841_);
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_head_843_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_a_841_);
v___x_849_ = v_reuseFailAlloc_851_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
v_a_840_ = v_tail_844_;
v_a_841_ = v___x_849_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_858_ = l_Lean_stringToMessageData(v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_862_, lean_object* v_declName_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_kinds_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v_ks_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_inc(v_declName_863_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v_declName_863_);
v___x_895_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_862_, v___x_894_);
lean_dec_ref_known(v___x_894_, 1);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec(v_declName_863_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
else
{
lean_object* v_head_898_; lean_object* v_tail_899_; uint8_t v_minIndexable_900_; uint8_t v_gen_902_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; 
v_head_898_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_head_898_);
v_tail_899_ = lean_ctor_get(v___x_895_, 1);
lean_inc(v_tail_899_);
v_minIndexable_900_ = 0;
if (lean_obj_tag(v_tail_899_) == 0)
{
lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_921_; 
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; lean_object* v_unused_923_; 
v_unused_922_ = lean_ctor_get(v___x_895_, 1);
lean_dec(v_unused_922_);
v_unused_923_ = lean_ctor_get(v___x_895_, 0);
lean_dec(v_unused_923_);
v___x_913_ = v___x_895_;
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
else
{
lean_dec(v___x_895_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_915_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_916_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_898_, v_minIndexable_900_);
lean_dec(v_head_898_);
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 7);
lean_ctor_set(v___x_913_, 1, v___x_917_);
lean_ctor_set(v___x_913_, 0, v___x_915_);
v___x_919_ = v___x_913_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
v_kinds_870_ = v___x_919_;
v___y_871_ = v_a_864_;
v___y_872_ = v_a_865_;
v___y_873_ = v_a_866_;
v___y_874_ = v_a_867_;
goto v___jp_869_;
}
}
}
else
{
lean_object* v_head_924_; 
v_head_924_ = lean_ctor_get(v_tail_899_, 0);
switch(lean_obj_tag(v_head_924_))
{
case 1:
{
lean_object* v_tail_925_; 
v_tail_925_ = lean_ctor_get(v_tail_899_, 1);
lean_inc(v_tail_925_);
lean_dec_ref_known(v_tail_899_, 2);
if (lean_obj_tag(v_tail_925_) == 0)
{
if (lean_obj_tag(v_head_898_) == 0)
{
uint8_t v_gen_926_; 
lean_dec_ref_known(v___x_895_, 2);
v_gen_926_ = lean_ctor_get_uint8(v_head_898_, 0);
lean_dec_ref_known(v_head_898_, 0);
v_gen_902_ = v_gen_926_;
v___y_903_ = v_a_864_;
v___y_904_ = v_a_865_;
v___y_905_ = v_a_866_;
v___y_906_ = v_a_867_;
goto v___jp_901_;
}
else
{
lean_dec(v_head_898_);
v_ks_885_ = v___x_895_;
v___y_886_ = v_a_864_;
v___y_887_ = v_a_865_;
v___y_888_ = v_a_866_;
v___y_889_ = v_a_867_;
goto v___jp_884_;
}
}
else
{
lean_dec(v_tail_925_);
lean_dec(v_head_898_);
v_ks_885_ = v___x_895_;
v___y_886_ = v_a_864_;
v___y_887_ = v_a_865_;
v___y_888_ = v_a_866_;
v___y_889_ = v_a_867_;
goto v___jp_884_;
}
}
case 0:
{
lean_object* v_tail_927_; 
v_tail_927_ = lean_ctor_get(v_tail_899_, 1);
lean_inc(v_tail_927_);
lean_dec_ref_known(v_tail_899_, 2);
if (lean_obj_tag(v_tail_927_) == 0)
{
if (lean_obj_tag(v_head_898_) == 1)
{
uint8_t v_gen_928_; 
lean_dec_ref_known(v___x_895_, 2);
v_gen_928_ = lean_ctor_get_uint8(v_head_898_, 0);
lean_dec_ref_known(v_head_898_, 0);
v_gen_902_ = v_gen_928_;
v___y_903_ = v_a_864_;
v___y_904_ = v_a_865_;
v___y_905_ = v_a_866_;
v___y_906_ = v_a_867_;
goto v___jp_901_;
}
else
{
lean_dec(v_head_898_);
v_ks_885_ = v___x_895_;
v___y_886_ = v_a_864_;
v___y_887_ = v_a_865_;
v___y_888_ = v_a_866_;
v___y_889_ = v_a_867_;
goto v___jp_884_;
}
}
else
{
lean_dec(v_tail_927_);
lean_dec(v_head_898_);
v_ks_885_ = v___x_895_;
v___y_886_ = v_a_864_;
v___y_887_ = v_a_865_;
v___y_888_ = v_a_866_;
v___y_889_ = v_a_867_;
goto v___jp_884_;
}
}
default: 
{
lean_dec_ref_known(v_tail_899_, 2);
lean_dec(v_head_898_);
v_ks_885_ = v___x_895_;
v___y_886_ = v_a_864_;
v___y_887_ = v_a_865_;
v___y_888_ = v_a_866_;
v___y_889_ = v_a_867_;
goto v___jp_884_;
}
}
}
v___jp_901_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_907_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_908_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_908_, 0, v_gen_902_);
v___x_909_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_908_, v_minIndexable_900_);
lean_dec_ref_known(v___x_908_, 0);
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_907_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v_kinds_870_ = v___x_911_;
v___y_871_ = v___y_903_;
v___y_872_ = v___y_904_;
v___y_873_ = v___y_905_;
v___y_874_ = v___y_906_;
goto v___jp_869_;
}
}
v___jp_869_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_875_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_876_ = l_Lean_MessageData_ofName(v_declName_863_);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v_kinds_870_);
v___x_881_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_882_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
return v___x_883_;
}
v___jp_884_:
{
lean_object* v___x_890_; lean_object* v_ks_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_890_ = lean_box(0);
v_ks_891_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_885_, v___x_890_);
v___x_892_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_891_, v___x_890_);
v___x_893_ = l_Lean_MessageData_ofList(v___x_892_);
v_kinds_870_ = v___x_893_;
v___y_871_ = v___y_886_;
v___y_872_ = v___y_887_;
v___y_873_ = v___y_888_;
v___y_874_ = v___y_889_;
goto v___jp_869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_929_, lean_object* v_declName_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_929_, v_declName_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
lean_dec_ref(v_s_929_);
return v_res_936_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_937_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
lean_ctor_set(v___x_942_, 2, v___x_941_);
lean_ctor_set(v___x_942_, 3, v___x_941_);
lean_ctor_set(v___x_942_, 4, v___x_940_);
lean_ctor_set(v___x_942_, 5, v___x_940_);
lean_ctor_set(v___x_942_, 6, v___x_940_);
lean_ctor_set(v___x_942_, 7, v___x_940_);
lean_ctor_set(v___x_942_, 8, v___x_940_);
lean_ctor_set(v___x_942_, 9, v___x_940_);
lean_ctor_set(v___x_942_, 10, v___x_940_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_unsigned_to_nat(32u);
v___x_944_ = lean_mk_empty_array_with_capacity(v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_946_ = ((size_t)5ULL);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_unsigned_to_nat(32u);
v___x_949_ = lean_mk_empty_array_with_capacity(v___x_948_);
v___x_950_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_951_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_949_);
lean_ctor_set(v___x_951_, 2, v___x_947_);
lean_ctor_set(v___x_951_, 3, v___x_947_);
lean_ctor_set_usize(v___x_951_, 4, v___x_946_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_952_ = lean_box(1);
v___x_953_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_954_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
lean_ctor_set(v___x_955_, 2, v___x_952_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; lean_object* v_toCold_961_; lean_object* v_env_962_; lean_object* v_options_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_960_ = lean_st_ref_get(v___y_958_);
v_toCold_961_ = lean_ctor_get(v___y_957_, 0);
v_env_962_ = lean_ctor_get(v___x_960_, 0);
lean_inc_ref(v_env_962_);
lean_dec(v___x_960_);
v_options_963_ = lean_ctor_get(v_toCold_961_, 2);
v___x_964_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_965_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_963_);
v___x_966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_966_, 0, v_env_962_);
lean_ctor_set(v___x_966_, 1, v___x_964_);
lean_ctor_set(v___x_966_, 2, v___x_965_);
lean_ctor_set(v___x_966_, 3, v_options_963_);
v___x_967_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v_msgData_956_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* v_msgData_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_ref_978_; lean_object* v___x_979_; lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_988_; 
v_ref_978_ = lean_ctor_get(v___y_975_, 2);
v___x_979_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msg_974_, v___y_975_, v___y_976_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_988_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
lean_inc(v_ref_978_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_ref_978_);
lean_ctor_set(v___x_984_, 1, v_a_980_);
if (v_isShared_983_ == 0)
{
lean_ctor_set_tag(v___x_982_, 1);
lean_ctor_set(v___x_982_, 0, v___x_984_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* v_msg_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_993_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
v___x_1006_ = l_Lean_stringToMessageData(v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* v_s_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v_env_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1011_ = lean_st_ref_get(v_a_1009_);
v_env_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_ref(v_env_1012_);
lean_dec(v___x_1011_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
v___x_1014_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(v_s_1007_);
v___x_1015_ = l_Lean_Parser_runParserCategory(v_env_1012_, v___x_1013_, v_s_1007_, v___x_1014_);
if (lean_obj_tag(v___x_1015_) == 1)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v_s_1007_);
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = l_Lean_Meta_Grind_getAttrKindCore(v_a_1016_, v_a_1008_, v_a_1009_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec_ref(v___x_1015_);
v___x_1018_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
v___x_1019_ = l_Lean_stringToMessageData(v_s_1007_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1020_, v_a_1008_, v_a_1009_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* v_s_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* v_00_u03b1_1027_, lean_object* v_msg_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_1028_, v___y_1029_, v___y_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(v_00_u03b1_1033_, v_msg_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* v_msg_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_ref_1045_; lean_object* v___x_1046_; lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1055_; 
v_ref_1045_ = lean_ctor_get(v___y_1042_, 2);
v___x_1046_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1053_; 
lean_inc(v_ref_1045_);
v___x_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_ref_1045_);
lean_ctor_set(v___x_1051_, 1, v_a_1047_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 1);
lean_ctor_set(v___x_1049_, 0, v___x_1051_);
v___x_1053_ = v___x_1049_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1062_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t v_minIndexable_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
if (v_minIndexable_1066_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
v___x_1075_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1074_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* v_minIndexable_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
uint8_t v_minIndexable_boxed_1082_; lean_object* v_res_1083_; 
v_minIndexable_boxed_1082_ = lean_unbox(v_minIndexable_1076_);
v_res_1083_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_boxed_1082_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* v_00_u03b1_1084_, lean_object* v_msg_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(v_00_u03b1_1092_, v_msg_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1108_ = l_Lean_stringToMessageData(v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1114_ = l_Lean_stringToMessageData(v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1117_ = l_Lean_stringToMessageData(v___x_1116_);
return v___x_1117_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1120_ = l_Lean_stringToMessageData(v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1121_, lean_object* v_declHint_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; lean_object* v_env_1126_; uint8_t v___x_1127_; 
v___x_1125_ = lean_st_ref_get(v___y_1123_);
v_env_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_env_1126_);
lean_dec(v___x_1125_);
v___x_1127_ = l_Lean_Name_isAnonymous(v_declHint_1122_);
if (v___x_1127_ == 0)
{
uint8_t v_isExporting_1128_; 
v_isExporting_1128_ = lean_ctor_get_uint8(v_env_1126_, sizeof(void*)*8);
if (v_isExporting_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref(v_env_1126_);
lean_dec(v_declHint_1122_);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_msg_1121_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
lean_inc_ref(v_env_1126_);
v___x_1130_ = l_Lean_Environment_setExporting(v_env_1126_, v___x_1127_);
lean_inc(v_declHint_1122_);
lean_inc_ref(v___x_1130_);
v___x_1131_ = l_Lean_Environment_contains(v___x_1130_, v_declHint_1122_, v_isExporting_1128_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref(v___x_1130_);
lean_dec_ref(v_env_1126_);
lean_dec(v_declHint_1122_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_msg_1121_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v_c_1138_; lean_object* v___x_1139_; 
v___x_1133_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1134_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1135_ = l_Lean_Options_empty;
v___x_1136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1130_);
lean_ctor_set(v___x_1136_, 1, v___x_1133_);
lean_ctor_set(v___x_1136_, 2, v___x_1134_);
lean_ctor_set(v___x_1136_, 3, v___x_1135_);
lean_inc(v_declHint_1122_);
v___x_1137_ = l_Lean_MessageData_ofConstName(v_declHint_1122_, v___x_1127_);
v_c_1138_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1138_, 0, v___x_1136_);
lean_ctor_set(v_c_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1126_, v_declHint_1122_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_env_1126_);
lean_dec(v_declHint_1122_);
v___x_1140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v_c_1138_);
v___x_1142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = l_Lean_MessageData_note(v___x_1143_);
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_msg_1121_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1182_; 
v_val_1147_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1149_ = v___x_1139_;
v_isShared_1150_ = v_isSharedCheck_1182_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_val_1147_);
lean_dec(v___x_1139_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1182_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_mod_1154_; uint8_t v___x_1155_; 
v___x_1151_ = lean_box(0);
v___x_1152_ = l_Lean_Environment_header(v_env_1126_);
lean_dec_ref(v_env_1126_);
v___x_1153_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1152_);
v_mod_1154_ = lean_array_get(v___x_1151_, v___x_1153_, v_val_1147_);
lean_dec(v_val_1147_);
lean_dec_ref(v___x_1153_);
v___x_1155_ = l_Lean_isPrivateName(v_declHint_1122_);
lean_dec(v_declHint_1122_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1156_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v_c_1138_);
v___x_1158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_ofName(v_mod_1154_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_MessageData_note(v___x_1163_);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_msg_1121_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1165_);
v___x_1167_ = v___x_1149_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
else
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1169_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v_c_1138_);
v___x_1171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_MessageData_ofName(v_mod_1154_);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = l_Lean_MessageData_note(v___x_1176_);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v_msg_1121_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1178_);
v___x_1180_ = v___x_1149_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1183_; 
lean_dec_ref(v_env_1126_);
lean_dec(v_declHint_1122_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_msg_1121_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1184_, lean_object* v_declHint_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1184_, v_declHint_1185_, v___y_1186_);
lean_dec(v___y_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1189_, lean_object* v_declHint_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1206_; 
v___x_1196_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1189_, v_declHint_1190_, v___y_1194_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1206_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1206_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1201_ = l_Lean_unknownIdentifierMessageTag;
v___x_1202_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v_a_1197_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1202_);
v___x_1204_ = v___x_1199_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1207_, lean_object* v_declHint_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1207_, v_declHint_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1215_, lean_object* v_msg_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_toCold_1222_; lean_object* v_currRecDepth_1223_; lean_object* v_ref_1224_; uint8_t v_diag_1225_; uint8_t v_suppressElabErrors_1226_; lean_object* v_ref_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_toCold_1222_ = lean_ctor_get(v___y_1219_, 0);
v_currRecDepth_1223_ = lean_ctor_get(v___y_1219_, 1);
v_ref_1224_ = lean_ctor_get(v___y_1219_, 2);
v_diag_1225_ = lean_ctor_get_uint8(v___y_1219_, sizeof(void*)*3);
v_suppressElabErrors_1226_ = lean_ctor_get_uint8(v___y_1219_, sizeof(void*)*3 + 1);
v_ref_1227_ = l_Lean_replaceRef(v_ref_1215_, v_ref_1224_);
lean_inc(v_currRecDepth_1223_);
lean_inc_ref(v_toCold_1222_);
v___x_1228_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1228_, 0, v_toCold_1222_);
lean_ctor_set(v___x_1228_, 1, v_currRecDepth_1223_);
lean_ctor_set(v___x_1228_, 2, v_ref_1227_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*3, v_diag_1225_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*3 + 1, v_suppressElabErrors_1226_);
v___x_1229_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1216_, v___y_1217_, v___y_1218_, v___x_1228_, v___y_1220_);
lean_dec_ref_known(v___x_1228_, 3);
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
v_ref_1289_ = lean_ctor_get(v___y_1286_, 2);
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
lean_object* v___y_1396_; lean_object* v_thm_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; uint8_t v___x_1451_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___x_1649_; 
v___x_1451_ = 0;
lean_inc(v_declName_1385_);
v___x_1649_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1385_, v___x_1451_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; uint8_t v_kind_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v_kind_1651_ = lean_ctor_get_uint8(v_a_1650_, sizeof(void*)*3);
lean_dec(v_a_1650_);
switch(v_kind_1651_)
{
case 1:
{
v___y_1580_ = v_a_1390_;
v___y_1581_ = v_a_1391_;
v___y_1582_ = v_a_1392_;
v___y_1583_ = v_a_1393_;
goto v___jp_1579_;
}
case 2:
{
v___y_1580_ = v_a_1390_;
v___y_1581_ = v_a_1391_;
v___y_1582_ = v_a_1392_;
v___y_1583_ = v_a_1393_;
goto v___jp_1579_;
}
case 6:
{
v___y_1580_ = v_a_1390_;
v___y_1581_ = v_a_1391_;
v___y_1582_ = v_a_1392_;
v___y_1583_ = v_a_1393_;
goto v___jp_1579_;
}
case 0:
{
lean_object* v___x_1652_; 
lean_dec(v_id_1384_);
lean_inc(v_declName_1385_);
v___x_1652_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1385_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; uint8_t v___x_1654_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v___x_1654_ = lean_unbox(v_a_1653_);
lean_dec(v_a_1653_);
if (v___x_1654_ == 0)
{
v___y_1509_ = v_a_1390_;
v___y_1510_ = v_a_1391_;
v___y_1511_ = v_a_1392_;
v___y_1512_ = v_a_1393_;
goto v___jp_1508_;
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_kind_1386_);
lean_dec_ref(v_params_1383_);
v___x_1655_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1656_ = l_Lean_MessageData_ofConstName(v_declName_1385_, v___x_1451_);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1659_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v_kind_1386_);
lean_dec(v_declName_1385_);
lean_dec_ref(v_params_1383_);
v_a_1669_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1652_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1652_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
default: 
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec(v_kind_1386_);
lean_dec(v_id_1384_);
lean_dec_ref(v_params_1383_);
v___x_1677_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1678_ = l_Lean_MessageData_ofConstName(v_declName_1385_, v___x_1451_);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1681_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
return v___x_1682_;
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec(v_kind_1386_);
lean_dec(v_declName_1385_);
lean_dec(v_id_1384_);
lean_dec_ref(v_params_1383_);
v_a_1683_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1649_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1649_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
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
v___x_1447_ = l_Lean_PersistentArray_push___redArg(v___y_1443_, v___y_1442_);
v___x_1448_ = l_Lean_PersistentArray_push___redArg(v___x_1447_, v___y_1441_);
v___x_1449_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1449_, 0, v___y_1438_);
lean_ctor_set(v___x_1449_, 1, v___y_1436_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
lean_ctor_set(v___x_1449_, 3, v___y_1440_);
lean_ctor_set(v___x_1449_, 4, v___y_1437_);
lean_ctor_set(v___x_1449_, 5, v___y_1445_);
lean_ctor_set(v___x_1449_, 6, v___y_1446_);
lean_ctor_set(v___x_1449_, 7, v___y_1439_);
lean_ctor_set(v___x_1449_, 8, v___y_1444_);
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
lean_object* v_toCold_1550_; lean_object* v_options_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_toCold_1550_ = lean_ctor_get(v___y_1548_, 0);
v_options_1551_ = lean_ctor_get(v_toCold_1550_, 2);
v___x_1552_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1553_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v_symPrios_1554_; lean_object* v___x_1555_; 
lean_dec(v_kind_1386_);
v_symPrios_1554_ = lean_ctor_get(v_params_1383_, 5);
lean_inc_ref(v_symPrios_1554_);
lean_inc(v_declName_1385_);
v___x_1555_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1384_, v_declName_1385_, v_symPrios_1554_, v_minIndexable_1387_, v_suggest_1388_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v_thm_1416_ = v_a_1556_;
v___y_1417_ = v___y_1546_;
v___y_1418_ = v___y_1547_;
v___y_1419_ = v___y_1548_;
v___y_1420_ = v___y_1549_;
goto v___jp_1415_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_declName_1385_);
lean_dec_ref(v_params_1383_);
v_a_1557_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1555_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1555_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
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
v___jp_1565_:
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1387_, v___y_1567_, v___y_1569_, v___y_1568_, v___y_1566_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_dec_ref_known(v___x_1570_, 1);
v___y_1546_ = v___y_1567_;
v___y_1547_ = v___y_1569_;
v___y_1548_ = v___y_1568_;
v___y_1549_ = v___y_1566_;
goto v___jp_1545_;
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_kind_1386_);
lean_dec(v_declName_1385_);
lean_dec(v_id_1384_);
lean_dec_ref(v_params_1383_);
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
v___jp_1579_:
{
if (lean_obj_tag(v_kind_1386_) == 2)
{
uint8_t v_gen_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_id_1384_);
v_gen_1584_ = lean_ctor_get_uint8(v_kind_1386_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_kind_1386_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1586_ = v_kind_1386_;
v_isShared_1587_ = v_isSharedCheck_1648_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v_kind_1386_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1648_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1387_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_config_1589_; lean_object* v_extensions_1590_; lean_object* v_extra_1591_; lean_object* v_extraInj_1592_; lean_object* v_extraFacts_1593_; lean_object* v_symPrios_1594_; lean_object* v_norm_1595_; lean_object* v_normProcs_1596_; lean_object* v_anchorRefs_x3f_1597_; lean_object* v___x_1599_; 
lean_dec_ref_known(v___x_1588_, 1);
v_config_1589_ = lean_ctor_get(v_params_1383_, 0);
lean_inc_ref(v_config_1589_);
v_extensions_1590_ = lean_ctor_get(v_params_1383_, 1);
lean_inc_ref(v_extensions_1590_);
v_extra_1591_ = lean_ctor_get(v_params_1383_, 2);
lean_inc_ref(v_extra_1591_);
v_extraInj_1592_ = lean_ctor_get(v_params_1383_, 3);
lean_inc_ref(v_extraInj_1592_);
v_extraFacts_1593_ = lean_ctor_get(v_params_1383_, 4);
lean_inc_ref(v_extraFacts_1593_);
v_symPrios_1594_ = lean_ctor_get(v_params_1383_, 5);
lean_inc_ref(v_symPrios_1594_);
v_norm_1595_ = lean_ctor_get(v_params_1383_, 6);
lean_inc_ref(v_norm_1595_);
v_normProcs_1596_ = lean_ctor_get(v_params_1383_, 7);
lean_inc_ref(v_normProcs_1596_);
v_anchorRefs_x3f_1597_ = lean_ctor_get(v_params_1383_, 8);
lean_inc(v_anchorRefs_x3f_1597_);
lean_dec_ref(v_params_1383_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set_tag(v___x_1586_, 0);
v___x_1599_ = v___x_1586_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1639_, 0, v_gen_1584_);
v___x_1599_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
lean_inc_ref(v_symPrios_1594_);
lean_inc(v_declName_1385_);
v___x_1600_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1385_, v___x_1599_, v_symPrios_1594_, v___x_1451_, v___x_1451_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1602_, 0, v_gen_1584_);
lean_inc_ref(v_symPrios_1594_);
lean_inc(v_declName_1385_);
v___x_1603_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1385_, v___x_1602_, v_symPrios_1594_, v___x_1451_, v___x_1451_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1603_) == 0)
{
if (v_warn_1389_ == 0)
{
lean_object* v_a_1604_; 
lean_dec(v_declName_1385_);
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v___y_1436_ = v_extensions_1590_;
v___y_1437_ = v_extraFacts_1593_;
v___y_1438_ = v_config_1589_;
v___y_1439_ = v_normProcs_1596_;
v___y_1440_ = v_extraInj_1592_;
v___y_1441_ = v_a_1604_;
v___y_1442_ = v_a_1601_;
v___y_1443_ = v_extra_1591_;
v___y_1444_ = v_anchorRefs_x3f_1597_;
v___y_1445_ = v_symPrios_1594_;
v___y_1446_ = v_norm_1595_;
goto v___jp_1435_;
}
else
{
lean_object* v_a_1605_; lean_object* v_patterns_1606_; lean_object* v_origin_1607_; lean_object* v_cnstrs_1608_; uint8_t v___x_1609_; 
v_a_1605_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1603_, 1);
v_patterns_1606_ = lean_ctor_get(v_a_1601_, 3);
v_origin_1607_ = lean_ctor_get(v_a_1601_, 5);
v_cnstrs_1608_ = lean_ctor_get(v_a_1601_, 7);
v___x_1609_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1590_, v_origin_1607_, v_patterns_1606_, v_cnstrs_1608_);
if (v___x_1609_ == 0)
{
lean_dec(v_declName_1385_);
v___y_1436_ = v_extensions_1590_;
v___y_1437_ = v_extraFacts_1593_;
v___y_1438_ = v_config_1589_;
v___y_1439_ = v_normProcs_1596_;
v___y_1440_ = v_extraInj_1592_;
v___y_1441_ = v_a_1605_;
v___y_1442_ = v_a_1601_;
v___y_1443_ = v_extra_1591_;
v___y_1444_ = v_anchorRefs_x3f_1597_;
v___y_1445_ = v_symPrios_1594_;
v___y_1446_ = v_norm_1595_;
goto v___jp_1435_;
}
else
{
lean_object* v_patterns_1610_; lean_object* v_origin_1611_; lean_object* v_cnstrs_1612_; uint8_t v___x_1613_; 
v_patterns_1610_ = lean_ctor_get(v_a_1605_, 3);
v_origin_1611_ = lean_ctor_get(v_a_1605_, 5);
v_cnstrs_1612_ = lean_ctor_get(v_a_1605_, 7);
v___x_1613_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1590_, v_origin_1611_, v_patterns_1610_, v_cnstrs_1612_);
if (v___x_1613_ == 0)
{
lean_dec(v_declName_1385_);
v___y_1436_ = v_extensions_1590_;
v___y_1437_ = v_extraFacts_1593_;
v___y_1438_ = v_config_1589_;
v___y_1439_ = v_normProcs_1596_;
v___y_1440_ = v_extraInj_1592_;
v___y_1441_ = v_a_1605_;
v___y_1442_ = v_a_1601_;
v___y_1443_ = v_extra_1591_;
v___y_1444_ = v_anchorRefs_x3f_1597_;
v___y_1445_ = v_symPrios_1594_;
v___y_1446_ = v_norm_1595_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1590_, v_declName_1385_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_dec_ref_known(v___x_1614_, 1);
v___y_1436_ = v_extensions_1590_;
v___y_1437_ = v_extraFacts_1593_;
v___y_1438_ = v_config_1589_;
v___y_1439_ = v_normProcs_1596_;
v___y_1440_ = v_extraInj_1592_;
v___y_1441_ = v_a_1605_;
v___y_1442_ = v_a_1601_;
v___y_1443_ = v_extra_1591_;
v___y_1444_ = v_anchorRefs_x3f_1597_;
v___y_1445_ = v_symPrios_1594_;
v___y_1446_ = v_norm_1595_;
goto v___jp_1435_;
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec(v_a_1605_);
lean_dec(v_a_1601_);
lean_dec(v_anchorRefs_x3f_1597_);
lean_dec_ref(v_normProcs_1596_);
lean_dec_ref(v_norm_1595_);
lean_dec_ref(v_symPrios_1594_);
lean_dec_ref(v_extraFacts_1593_);
lean_dec_ref(v_extraInj_1592_);
lean_dec_ref(v_extra_1591_);
lean_dec_ref(v_extensions_1590_);
lean_dec_ref(v_config_1589_);
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
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
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_a_1601_);
lean_dec(v_anchorRefs_x3f_1597_);
lean_dec_ref(v_normProcs_1596_);
lean_dec_ref(v_norm_1595_);
lean_dec_ref(v_symPrios_1594_);
lean_dec_ref(v_extraFacts_1593_);
lean_dec_ref(v_extraInj_1592_);
lean_dec_ref(v_extra_1591_);
lean_dec_ref(v_extensions_1590_);
lean_dec_ref(v_config_1589_);
lean_dec(v_declName_1385_);
v_a_1623_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1603_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1603_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_anchorRefs_x3f_1597_);
lean_dec_ref(v_normProcs_1596_);
lean_dec_ref(v_norm_1595_);
lean_dec_ref(v_symPrios_1594_);
lean_dec_ref(v_extraFacts_1593_);
lean_dec_ref(v_extraInj_1592_);
lean_dec_ref(v_extra_1591_);
lean_dec_ref(v_extensions_1590_);
lean_dec_ref(v_config_1589_);
lean_dec(v_declName_1385_);
v_a_1631_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1600_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1600_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_del_object(v___x_1586_);
lean_dec(v_declName_1385_);
lean_dec_ref(v_params_1383_);
v_a_1640_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1588_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1588_);
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
}
else
{
switch(lean_obj_tag(v_kind_1386_))
{
case 0:
{
v___y_1566_ = v___y_1583_;
v___y_1567_ = v___y_1580_;
v___y_1568_ = v___y_1582_;
v___y_1569_ = v___y_1581_;
goto v___jp_1565_;
}
case 1:
{
v___y_1566_ = v___y_1583_;
v___y_1567_ = v___y_1580_;
v___y_1568_ = v___y_1582_;
v___y_1569_ = v___y_1581_;
goto v___jp_1565_;
}
default: 
{
v___y_1546_ = v___y_1580_;
v___y_1547_ = v___y_1581_;
v___y_1548_ = v___y_1582_;
v___y_1549_ = v___y_1583_;
goto v___jp_1545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1691_, lean_object* v_id_1692_, lean_object* v_declName_1693_, lean_object* v_kind_1694_, lean_object* v_minIndexable_1695_, lean_object* v_suggest_1696_, lean_object* v_warn_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
uint8_t v_minIndexable_boxed_1703_; uint8_t v_suggest_boxed_1704_; uint8_t v_warn_boxed_1705_; lean_object* v_res_1706_; 
v_minIndexable_boxed_1703_ = lean_unbox(v_minIndexable_1695_);
v_suggest_boxed_1704_ = lean_unbox(v_suggest_1696_);
v_warn_boxed_1705_ = lean_unbox(v_warn_1697_);
v_res_1706_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1691_, v_id_1692_, v_declName_1693_, v_kind_1694_, v_minIndexable_boxed_1703_, v_suggest_boxed_1704_, v_warn_boxed_1705_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1707_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1721_, lean_object* v_constName_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_constName_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1729_, v_constName_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1737_, lean_object* v_ref_1738_, lean_object* v_constName_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1738_, v_constName_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_ref_1747_, lean_object* v_constName_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1746_, v_ref_1747_, v_constName_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v_ref_1747_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1755_, lean_object* v_ref_1756_, lean_object* v_msg_1757_, lean_object* v_declHint_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1756_, v_msg_1757_, v_declHint_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1765_, lean_object* v_ref_1766_, lean_object* v_msg_1767_, lean_object* v_declHint_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1765_, v_ref_1766_, v_msg_1767_, v_declHint_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v_ref_1766_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1775_, lean_object* v_declHint_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1775_, v_declHint_1776_, v___y_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1783_, lean_object* v_declHint_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1783_, v_declHint_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1791_, lean_object* v_ref_1792_, lean_object* v_msg_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1792_, v_msg_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1800_, lean_object* v_ref_1801_, lean_object* v_msg_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1800_, v_ref_1801_, v_msg_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v_ref_1801_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1811_, lean_object* v_val_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_config_1816_; lean_object* v_extensions_1817_; lean_object* v_extra_1818_; lean_object* v_extraInj_1819_; lean_object* v_extraFacts_1820_; lean_object* v_symPrios_1821_; lean_object* v_norm_1822_; lean_object* v_normProcs_1823_; lean_object* v_anchorRefs_x3f_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1854_; 
v_config_1816_ = lean_ctor_get(v_params_1811_, 0);
v_extensions_1817_ = lean_ctor_get(v_params_1811_, 1);
v_extra_1818_ = lean_ctor_get(v_params_1811_, 2);
v_extraInj_1819_ = lean_ctor_get(v_params_1811_, 3);
v_extraFacts_1820_ = lean_ctor_get(v_params_1811_, 4);
v_symPrios_1821_ = lean_ctor_get(v_params_1811_, 5);
v_norm_1822_ = lean_ctor_get(v_params_1811_, 6);
v_normProcs_1823_ = lean_ctor_get(v_params_1811_, 7);
v_anchorRefs_x3f_1824_ = lean_ctor_get(v_params_1811_, 8);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_params_1811_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1826_ = v_params_1811_;
v_isShared_1827_ = v_isSharedCheck_1854_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_anchorRefs_x3f_1824_);
lean_inc(v_normProcs_1823_);
lean_inc(v_norm_1822_);
lean_inc(v_symPrios_1821_);
lean_inc(v_extraFacts_1820_);
lean_inc(v_extraInj_1819_);
lean_inc(v_extra_1818_);
lean_inc(v_extensions_1817_);
lean_inc(v_config_1816_);
lean_dec(v_params_1811_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1854_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___y_1829_; 
if (lean_obj_tag(v_anchorRefs_x3f_1824_) == 0)
{
lean_object* v___x_1852_; 
v___x_1852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1829_ = v___x_1852_;
goto v___jp_1828_;
}
else
{
lean_object* v_val_1853_; 
v_val_1853_ = lean_ctor_get(v_anchorRefs_x3f_1824_, 0);
lean_inc(v_val_1853_);
lean_dec_ref_known(v_anchorRefs_x3f_1824_, 1);
v___y_1829_ = v_val_1853_;
goto v___jp_1828_;
}
v___jp_1828_:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1812_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1843_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1843_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1843_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1835_ = lean_array_push(v___y_1829_, v_a_1831_);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 8, v___x_1836_);
v___x_1838_ = v___x_1826_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_config_1816_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_extensions_1817_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_extra_1818_);
lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_extraInj_1819_);
lean_ctor_set(v_reuseFailAlloc_1842_, 4, v_extraFacts_1820_);
lean_ctor_set(v_reuseFailAlloc_1842_, 5, v_symPrios_1821_);
lean_ctor_set(v_reuseFailAlloc_1842_, 6, v_norm_1822_);
lean_ctor_set(v_reuseFailAlloc_1842_, 7, v_normProcs_1823_);
lean_ctor_set(v_reuseFailAlloc_1842_, 8, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1840_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1838_);
v___x_1840_ = v___x_1833_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v___y_1829_);
lean_del_object(v___x_1826_);
lean_dec_ref(v_normProcs_1823_);
lean_dec_ref(v_norm_1822_);
lean_dec_ref(v_symPrios_1821_);
lean_dec_ref(v_extraFacts_1820_);
lean_dec_ref(v_extraInj_1819_);
lean_dec_ref(v_extra_1818_);
lean_dec_ref(v_extensions_1817_);
lean_dec_ref(v_config_1816_);
v_a_1844_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1830_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1830_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1855_, lean_object* v_val_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1855_, v_val_1856_, v_a_1857_, v_a_1858_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_val_1856_);
return v_res_1860_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1863_ = l_Lean_stringToMessageData(v___x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_config_1868_; uint8_t v_revert_1869_; 
v_config_1868_ = lean_ctor_get(v_params_1864_, 0);
v_revert_1869_ = lean_ctor_get_uint8(v_config_1868_, sizeof(void*)*14 + 30);
if (v_revert_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_box(0);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_1873_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1872_, v_a_1865_, v_a_1866_);
return v___x_1873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_1874_, v_a_1875_, v_a_1876_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec_ref(v_params_1874_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_1879_, lean_object* v___y_1880_){
_start:
{
uint8_t v___x_1882_; 
v___x_1882_ = l_Lean_Expr_hasMVar(v_e_1879_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v_e_1879_);
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; lean_object* v_mctx_1885_; lean_object* v___x_1886_; lean_object* v_fst_1887_; lean_object* v_snd_1888_; lean_object* v___x_1889_; lean_object* v_cache_1890_; lean_object* v_zetaDeltaFVarIds_1891_; lean_object* v_postponed_1892_; lean_object* v_diag_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1902_; 
v___x_1884_ = lean_st_ref_get(v___y_1880_);
v_mctx_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc_ref(v_mctx_1885_);
lean_dec(v___x_1884_);
v___x_1886_ = l_Lean_instantiateMVarsCore(v_mctx_1885_, v_e_1879_);
v_fst_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_fst_1887_);
v_snd_1888_ = lean_ctor_get(v___x_1886_, 1);
lean_inc(v_snd_1888_);
lean_dec_ref(v___x_1886_);
v___x_1889_ = lean_st_ref_take(v___y_1880_);
v_cache_1890_ = lean_ctor_get(v___x_1889_, 1);
v_zetaDeltaFVarIds_1891_ = lean_ctor_get(v___x_1889_, 2);
v_postponed_1892_ = lean_ctor_get(v___x_1889_, 3);
v_diag_1893_ = lean_ctor_get(v___x_1889_, 4);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1889_, 0);
lean_dec(v_unused_1903_);
v___x_1895_ = v___x_1889_;
v_isShared_1896_ = v_isSharedCheck_1902_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_diag_1893_);
lean_inc(v_postponed_1892_);
lean_inc(v_zetaDeltaFVarIds_1891_);
lean_inc(v_cache_1890_);
lean_dec(v___x_1889_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1902_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v_snd_1888_);
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_snd_1888_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_cache_1890_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_zetaDeltaFVarIds_1891_);
lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_postponed_1892_);
lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_diag_1893_);
v___x_1898_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_st_ref_put(v___y_1880_, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v_fst_1887_);
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1904_, v___y_1905_);
lean_dec(v___y_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1908_, v___y_1912_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(lean_object* v_p_1928_, lean_object* v_term_1929_, lean_object* v___x_1930_, uint8_t v___x_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_toCold_1939_; lean_object* v_currRecDepth_1940_; lean_object* v_ref_1941_; uint8_t v_diag_1942_; uint8_t v_suppressElabErrors_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_2011_; 
v_toCold_1939_ = lean_ctor_get(v___y_1936_, 0);
v_currRecDepth_1940_ = lean_ctor_get(v___y_1936_, 1);
v_ref_1941_ = lean_ctor_get(v___y_1936_, 2);
v_diag_1942_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*3);
v_suppressElabErrors_1943_ = lean_ctor_get_uint8(v___y_1936_, sizeof(void*)*3 + 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___y_1936_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1945_ = v___y_1936_;
v_isShared_1946_ = v_isSharedCheck_2011_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_ref_1941_);
lean_inc(v_currRecDepth_1940_);
lean_inc(v_toCold_1939_);
lean_dec(v___y_1936_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_2011_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_ref_1947_; lean_object* v___x_1949_; 
v_ref_1947_ = l_Lean_replaceRef(v_p_1928_, v_ref_1941_);
lean_dec(v_ref_1941_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 2, v_ref_1947_);
v___x_1949_ = v___x_1945_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_toCold_1939_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_currRecDepth_1940_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_ref_1947_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*3, v_diag_1942_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*3 + 1, v_suppressElabErrors_1943_);
v___x_1949_ = v_reuseFailAlloc_2010_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_Elab_Term_elabTerm(v_term_1929_, v___x_1930_, v___x_1931_, v___x_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___x_1949_, v___y_1937_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; uint8_t v___x_1952_; lean_object* v___x_1953_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = 1;
v___x_1953_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1952_, v___x_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___x_1949_, v___y_1937_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v___x_1954_; lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref_known(v___x_1953_, 1);
v___x_1954_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_1951_, v___y_1935_);
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1993_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1993_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
uint8_t v___x_1959_; 
v___x_1959_ = l_Lean_Expr_hasSyntheticSorry(v_a_1955_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1960_ = l_Lean_Expr_eta(v_a_1955_);
v___x_1961_ = l_Lean_Expr_hasMVar(v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
lean_dec_ref(v___x_1949_);
v___x_1962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0));
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v___x_1960_);
v___x_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1964_);
v___x_1966_ = v___x_1957_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
else
{
lean_object* v___x_1968_; 
lean_del_object(v___x_1957_);
v___x_1968_ = l_Lean_Meta_abstractMVars(v___x_1960_, v___x_1931_, v___y_1934_, v___y_1935_, v___x_1949_, v___y_1937_);
lean_dec_ref(v___x_1949_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1980_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_paramNames_1973_; lean_object* v_expr_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v_paramNames_1973_ = lean_ctor_get(v_a_1969_, 0);
lean_inc_ref(v_paramNames_1973_);
v_expr_1974_ = lean_ctor_get(v_a_1969_, 2);
lean_inc_ref(v_expr_1974_);
lean_dec(v_a_1969_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v_paramNames_1973_);
lean_ctor_set(v___x_1975_, 1, v_expr_1974_);
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1976_);
v___x_1978_ = v___x_1971_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1968_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1968_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_dec(v_a_1955_);
lean_dec_ref(v___x_1949_);
v___x_1989_ = lean_box(0);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1989_);
v___x_1991_ = v___x_1957_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v_a_1951_);
lean_dec_ref(v___x_1949_);
v_a_1994_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1953_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1953_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v___x_1949_);
v_a_2002_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1950_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1950_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v_p_2012_, lean_object* v_term_2013_, lean_object* v___x_2014_, lean_object* v___x_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
uint8_t v___x_12103__boxed_2023_; lean_object* v_res_2024_; 
v___x_12103__boxed_2023_ = lean_unbox(v___x_2015_);
v_res_2024_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v_p_2012_, v_term_2013_, v___x_2014_, v___x_12103__boxed_2023_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v_p_2012_);
return v_res_2024_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2));
v___x_2030_ = l_Lean_stringToMessageData(v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_params_2031_, lean_object* v_p_2032_, lean_object* v_fst_2033_, lean_object* v_snd_2034_, uint8_t v___x_2035_, uint8_t v_minIndexable_2036_, lean_object* v_kind_2037_, lean_object* v_idx_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_symPrios_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; 
v_symPrios_2044_ = lean_ctor_get(v_params_2031_, 5);
lean_inc_ref(v_symPrios_2044_);
lean_dec_ref(v_params_2031_);
v___x_2045_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1));
v___x_2046_ = lean_name_append_index_after(v___x_2045_, v_idx_2038_);
v___x_2047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set(v___x_2047_, 1, v_p_2032_);
v___x_2048_ = 0;
v___x_2049_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2047_, v_fst_2033_, v_snd_2034_, v_kind_2037_, v_symPrios_2044_, v___x_2035_, v___x_2048_, v_minIndexable_2036_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2060_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2060_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2060_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
if (lean_obj_tag(v_a_2050_) == 1)
{
lean_object* v_val_2054_; lean_object* v___x_2056_; 
v_val_2054_ = lean_ctor_get(v_a_2050_, 0);
lean_inc(v_val_2054_);
lean_dec_ref_known(v_a_2050_, 1);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v_val_2054_);
v___x_2056_ = v___x_2052_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_val_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_del_object(v___x_2052_);
lean_dec(v_a_2050_);
v___x_2058_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3);
v___x_2059_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2058_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
return v___x_2059_;
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_a_2061_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2049_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2049_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_params_2069_, lean_object* v_p_2070_, lean_object* v_fst_2071_, lean_object* v_snd_2072_, lean_object* v___x_2073_, lean_object* v_minIndexable_2074_, lean_object* v_kind_2075_, lean_object* v_idx_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
uint8_t v___x_12277__boxed_2082_; uint8_t v_minIndexable_boxed_2083_; lean_object* v_res_2084_; 
v___x_12277__boxed_2082_ = lean_unbox(v___x_2073_);
v_minIndexable_boxed_2083_ = lean_unbox(v_minIndexable_2074_);
v_res_2084_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_params_2069_, v_p_2070_, v_fst_2071_, v_snd_2072_, v___x_12277__boxed_2082_, v_minIndexable_boxed_2083_, v_kind_2075_, v_idx_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2084_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_box(1);
v___x_2086_ = l_Lean_MessageData_ofFormat(v___x_2085_);
return v___x_2086_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2));
v___x_2091_ = l_Lean_MessageData_ofFormat(v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object* v_x_2092_, lean_object* v_x_2093_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
return v_x_2092_;
}
else
{
lean_object* v_head_2094_; lean_object* v_tail_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2117_; 
v_head_2094_ = lean_ctor_get(v_x_2093_, 0);
v_tail_2095_ = lean_ctor_get(v_x_2093_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2097_ = v_x_2093_;
v_isShared_2098_ = v_isSharedCheck_2117_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_tail_2095_);
lean_inc(v_head_2094_);
lean_dec(v_x_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2117_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_before_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2115_; 
v_before_2099_ = lean_ctor_get(v_head_2094_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_head_2094_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v_head_2094_, 1);
lean_dec(v_unused_2116_);
v___x_2101_ = v_head_2094_;
v_isShared_2102_ = v_isSharedCheck_2115_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_before_2099_);
lean_dec(v_head_2094_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2115_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 7);
lean_ctor_set(v___x_2101_, 1, v___x_2103_);
lean_ctor_set(v___x_2101_, 0, v_x_2092_);
v___x_2105_ = v___x_2101_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_x_2092_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3);
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 7);
lean_ctor_set(v___x_2097_, 1, v___x_2106_);
lean_ctor_set(v___x_2097_, 0, v___x_2105_);
v___x_2108_ = v___x_2097_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = l_Lean_MessageData_ofSyntax(v_before_2099_);
v___x_2110_ = l_Lean_indentD(v___x_2109_);
v___x_2111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2108_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v_x_2092_ = v___x_2111_;
v_x_2093_ = v_tail_2095_;
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
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1));
v___x_2122_ = l_Lean_MessageData_ofFormat(v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object* v_msgData_2123_, lean_object* v_macroStack_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_toCold_2127_; lean_object* v_options_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
v_toCold_2127_ = lean_ctor_get(v___y_2125_, 0);
v_options_2128_ = lean_ctor_get(v_toCold_2127_, 2);
v___x_2129_ = l_Lean_Elab_pp_macroStack;
v___x_2130_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2128_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; 
lean_dec(v_macroStack_2124_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_msgData_2123_);
return v___x_2131_;
}
else
{
if (lean_obj_tag(v_macroStack_2124_) == 0)
{
lean_object* v___x_2132_; 
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_msgData_2123_);
return v___x_2132_;
}
else
{
lean_object* v_head_2133_; lean_object* v_after_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2149_; 
v_head_2133_ = lean_ctor_get(v_macroStack_2124_, 0);
lean_inc(v_head_2133_);
v_after_2134_ = lean_ctor_get(v_head_2133_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_head_2133_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; 
v_unused_2150_ = lean_ctor_get(v_head_2133_, 0);
lean_dec(v_unused_2150_);
v___x_2136_ = v_head_2133_;
v_isShared_2137_ = v_isSharedCheck_2149_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_after_2134_);
lean_dec(v_head_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2149_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 7);
lean_ctor_set(v___x_2136_, 1, v___x_2138_);
lean_ctor_set(v___x_2136_, 0, v_msgData_2123_);
v___x_2140_ = v___x_2136_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_msgData_2123_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v_msgData_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2141_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2);
v___x_2142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = l_Lean_MessageData_ofSyntax(v_after_2134_);
v___x_2144_ = l_Lean_indentD(v___x_2143_);
v_msgData_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2145_, 0, v___x_2142_);
lean_ctor_set(v_msgData_2145_, 1, v___x_2144_);
v___x_2146_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(v_msgData_2145_, v_macroStack_2124_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2151_, lean_object* v_macroStack_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2151_, v_macroStack_2152_, v___y_2153_);
lean_dec_ref(v___y_2153_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_ref_2164_; lean_object* v___x_2165_; lean_object* v_a_2166_; lean_object* v_macroStack_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2178_; 
v_ref_2164_ = lean_ctor_get(v___y_2161_, 2);
v___x_2165_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2156_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref(v___x_2165_);
v_macroStack_2167_ = lean_ctor_get(v___y_2157_, 1);
v___x_2168_ = l_Lean_Elab_getBetterRef(v_ref_2164_, v_macroStack_2167_);
lean_inc(v_macroStack_2167_);
v___x_2169_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_a_2166_, v_macroStack_2167_, v___y_2161_);
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2178_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2178_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2168_);
lean_ctor_set(v___x_2174_, 1, v_a_2170_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 1);
lean_ctor_set(v___x_2172_, 0, v___x_2174_);
v___x_2176_ = v___x_2172_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v_msg_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2187_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2190_ = l_Lean_stringToMessageData(v___x_2189_);
return v___x_2190_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2193_ = l_Lean_stringToMessageData(v___x_2192_);
return v___x_2193_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2196_ = l_Lean_stringToMessageData(v___x_2195_);
return v___x_2196_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2202_, lean_object* v_p_2203_, lean_object* v_mod_x3f_2204_, lean_object* v_term_2205_, uint8_t v_minIndexable_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2277_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v_kind_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v_toCold_2512_; lean_object* v_currRecDepth_2513_; lean_object* v_ref_2514_; uint8_t v_diag_2515_; uint8_t v_suppressElabErrors_2516_; lean_object* v_ref_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_toCold_2512_ = lean_ctor_get(v_a_2211_, 0);
v_currRecDepth_2513_ = lean_ctor_get(v_a_2211_, 1);
v_ref_2514_ = lean_ctor_get(v_a_2211_, 2);
v_diag_2515_ = lean_ctor_get_uint8(v_a_2211_, sizeof(void*)*3);
v_suppressElabErrors_2516_ = lean_ctor_get_uint8(v_a_2211_, sizeof(void*)*3 + 1);
v_ref_2517_ = l_Lean_replaceRef(v_p_2203_, v_ref_2514_);
lean_inc(v_currRecDepth_2513_);
lean_inc_ref(v_toCold_2512_);
v___x_2518_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2518_, 0, v_toCold_2512_);
lean_ctor_set(v___x_2518_, 1, v_currRecDepth_2513_);
lean_ctor_set(v___x_2518_, 2, v_ref_2517_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3, v_diag_2515_);
lean_ctor_set_uint8(v___x_2518_, sizeof(void*)*3 + 1, v_suppressElabErrors_2516_);
v___x_2519_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2202_, v___x_2518_, v_a_2212_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_dec_ref_known(v___x_2519_, 1);
if (lean_obj_tag(v_mod_x3f_2204_) == 1)
{
lean_object* v_val_2520_; lean_object* v___x_2521_; 
v_val_2520_ = lean_ctor_get(v_mod_x3f_2204_, 0);
lean_inc(v_val_2520_);
v___x_2521_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2520_, v___x_2518_, v_a_2212_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2521_, 1);
switch(lean_obj_tag(v_a_2522_))
{
case 0:
{
lean_object* v_k_2540_; 
v_k_2540_ = lean_ctor_get(v_a_2522_, 0);
lean_inc(v_k_2540_);
lean_dec_ref_known(v_a_2522_, 1);
if (lean_obj_tag(v_k_2540_) == 9)
{
lean_dec_ref_known(v_mod_x3f_2204_, 1);
lean_dec(v_term_2205_);
lean_dec(v_p_2203_);
lean_dec_ref(v_params_2202_);
v___y_2524_ = v_a_2207_;
v___y_2525_ = v_a_2208_;
v___y_2526_ = v_a_2209_;
v___y_2527_ = v_a_2210_;
v___y_2528_ = v___x_2518_;
v___y_2529_ = v_a_2212_;
goto v___jp_2523_;
}
else
{
v_kind_2439_ = v_k_2540_;
v___y_2440_ = v_a_2207_;
v___y_2441_ = v_a_2208_;
v___y_2442_ = v_a_2209_;
v___y_2443_ = v_a_2210_;
v___y_2444_ = v___x_2518_;
v___y_2445_ = v_a_2212_;
goto v___jp_2438_;
}
}
case 1:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref_known(v_a_2522_, 0);
lean_dec_ref_known(v_mod_x3f_2204_, 1);
lean_dec(v_term_2205_);
lean_dec(v_p_2203_);
lean_dec_ref(v_params_2202_);
v___x_2541_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2542_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2541_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v___x_2518_, v_a_2212_);
lean_dec_ref_known(v___x_2518_, 3);
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2542_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2542_);
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
case 3:
{
v___y_2505_ = v_a_2207_;
v___y_2506_ = v_a_2208_;
v___y_2507_ = v_a_2209_;
v___y_2508_ = v_a_2210_;
v___y_2509_ = v___x_2518_;
v___y_2510_ = v_a_2212_;
goto v___jp_2504_;
}
case 5:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref_known(v_a_2522_, 1);
lean_dec_ref_known(v_mod_x3f_2204_, 1);
lean_dec(v_term_2205_);
lean_dec(v_p_2203_);
lean_dec_ref(v_params_2202_);
v___x_2551_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2552_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2551_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v___x_2518_, v_a_2212_);
lean_dec_ref_known(v___x_2518_, 3);
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
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
case 8:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref_known(v_a_2522_, 0);
lean_dec_ref_known(v_mod_x3f_2204_, 1);
lean_dec(v_term_2205_);
lean_dec(v_p_2203_);
lean_dec_ref(v_params_2202_);
v___x_2561_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2562_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2561_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v___x_2518_, v_a_2212_);
lean_dec_ref_known(v___x_2518_, 3);
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
default: 
{
lean_dec(v_a_2522_);
lean_dec_ref_known(v_mod_x3f_2204_, 1);
lean_dec(v_term_2205_);
lean_dec(v_p_2203_);
lean_dec_ref(v_params_2202_);
v___y_2524_ = v_a_2207_;
v___y_2525_ = v_a_2208_;
v___y_2526_ = v_a_2209_;
v___y_2527_ = v_a_2210_;
v___y_2528_ = v___x_2518_;
v___y_2529_ = v_a_2212_;
goto v___jp_2523_;
}
}
v___jp_2523_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v___x_2530_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2531_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2530_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec_ref(v___y_2528_);
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec_ref_known(v_mod_x3f_2204_, 1);
lean_dec_ref_known(v___x_2518_, 3);
lean_dec(v_term_2205_);
lean_dec(v_p_2203_);
lean_dec_ref(v_params_2202_);
v_a_2571_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2521_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2521_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
v___y_2505_ = v_a_2207_;
v___y_2506_ = v_a_2208_;
v___y_2507_ = v_a_2209_;
v___y_2508_ = v_a_2210_;
v___y_2509_ = v___x_2518_;
v___y_2510_ = v_a_2212_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec_ref_known(v___x_2518_, 3);
lean_dec(v_term_2205_);
lean_dec(v_mod_x3f_2204_);
lean_dec(v_p_2203_);
lean_dec_ref(v_params_2202_);
v_a_2579_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2519_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2519_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
v___jp_2214_:
{
lean_object* v___x_2231_; 
lean_inc(v___y_2230_);
lean_inc(v___y_2228_);
lean_inc_ref(v___y_2227_);
v___x_2231_ = lean_apply_7(v___y_2226_, v___y_2219_, v___y_2220_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, lean_box(0));
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2241_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2241_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2241_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2236_ = l_Lean_PersistentArray_push___redArg(v___y_2224_, v_a_2232_);
v___x_2237_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2237_, 0, v___y_2222_);
lean_ctor_set(v___x_2237_, 1, v___y_2218_);
lean_ctor_set(v___x_2237_, 2, v___x_2236_);
lean_ctor_set(v___x_2237_, 3, v___y_2216_);
lean_ctor_set(v___x_2237_, 4, v___y_2221_);
lean_ctor_set(v___x_2237_, 5, v___y_2223_);
lean_ctor_set(v___x_2237_, 6, v___y_2217_);
lean_ctor_set(v___x_2237_, 7, v___y_2215_);
lean_ctor_set(v___x_2237_, 8, v___y_2225_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2237_);
v___x_2239_ = v___x_2234_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec_ref(v___y_2215_);
v_a_2242_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2231_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2231_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
v___jp_2250_:
{
lean_object* v___x_2267_; 
v___x_2267_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2206_, v___y_2262_, v___y_2259_, v___y_2254_, v___y_2264_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_dec_ref_known(v___x_2267_, 1);
v___y_2215_ = v___y_2251_;
v___y_2216_ = v___y_2260_;
v___y_2217_ = v___y_2261_;
v___y_2218_ = v___y_2252_;
v___y_2219_ = v___y_2253_;
v___y_2220_ = v___y_2263_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2256_;
v___y_2223_ = v___y_2257_;
v___y_2224_ = v___y_2265_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2266_;
v___y_2227_ = v___y_2262_;
v___y_2228_ = v___y_2259_;
v___y_2229_ = v___y_2254_;
v___y_2230_ = v___y_2264_;
goto v___jp_2214_;
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec_ref(v___y_2251_);
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
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_2276_:
{
lean_object* v_config_2278_; lean_object* v_extensions_2279_; lean_object* v_extra_2280_; lean_object* v_extraInj_2281_; lean_object* v_extraFacts_2282_; lean_object* v_symPrios_2283_; lean_object* v_norm_2284_; lean_object* v_normProcs_2285_; lean_object* v_anchorRefs_x3f_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2295_; 
v_config_2278_ = lean_ctor_get(v_params_2202_, 0);
v_extensions_2279_ = lean_ctor_get(v_params_2202_, 1);
v_extra_2280_ = lean_ctor_get(v_params_2202_, 2);
v_extraInj_2281_ = lean_ctor_get(v_params_2202_, 3);
v_extraFacts_2282_ = lean_ctor_get(v_params_2202_, 4);
v_symPrios_2283_ = lean_ctor_get(v_params_2202_, 5);
v_norm_2284_ = lean_ctor_get(v_params_2202_, 6);
v_normProcs_2285_ = lean_ctor_get(v_params_2202_, 7);
v_anchorRefs_x3f_2286_ = lean_ctor_get(v_params_2202_, 8);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_params_2202_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2288_ = v_params_2202_;
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_anchorRefs_x3f_2286_);
lean_inc(v_normProcs_2285_);
lean_inc(v_norm_2284_);
lean_inc(v_symPrios_2283_);
lean_inc(v_extraFacts_2282_);
lean_inc(v_extraInj_2281_);
lean_inc(v_extra_2280_);
lean_inc(v_extensions_2279_);
lean_inc(v_config_2278_);
lean_dec(v_params_2202_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2290_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2282_, v___y_2277_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 4, v___x_2290_);
v___x_2292_ = v___x_2288_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_config_2278_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_extensions_2279_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v_extra_2280_);
lean_ctor_set(v_reuseFailAlloc_2294_, 3, v_extraInj_2281_);
lean_ctor_set(v_reuseFailAlloc_2294_, 4, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2294_, 5, v_symPrios_2283_);
lean_ctor_set(v_reuseFailAlloc_2294_, 6, v_norm_2284_);
lean_ctor_set(v_reuseFailAlloc_2294_, 7, v_normProcs_2285_);
lean_ctor_set(v_reuseFailAlloc_2294_, 8, v_anchorRefs_x3f_2286_);
v___x_2292_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
}
}
v___jp_2296_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2306_ = lean_array_get_size(v___y_2299_);
lean_dec_ref(v___y_2299_);
v___x_2307_ = lean_unsigned_to_nat(0u);
v___x_2308_ = lean_nat_dec_eq(v___x_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v___y_2297_);
lean_dec_ref(v_params_2202_);
v___x_2309_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2310_ = l_Lean_indentExpr(v___y_2298_);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2311_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec_ref(v___y_2304_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
lean_dec_ref(v___y_2304_);
lean_dec_ref(v___y_2298_);
v___y_2277_ = v___y_2297_;
goto v___jp_2276_;
}
}
v___jp_2321_:
{
uint8_t v___x_2333_; 
v___x_2333_ = l_Lean_Expr_isForall(v___y_2324_);
if (v___x_2333_ == 0)
{
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2323_);
if (lean_obj_tag(v_mod_x3f_2204_) == 0)
{
v___y_2297_ = v___y_2322_;
v___y_2298_ = v___y_2324_;
v___y_2299_ = v___y_2325_;
v___y_2300_ = v___y_2327_;
v___y_2301_ = v___y_2328_;
v___y_2302_ = v___y_2329_;
v___y_2303_ = v___y_2330_;
v___y_2304_ = v___y_2331_;
v___y_2305_ = v___y_2332_;
goto v___jp_2296_;
}
else
{
lean_dec_ref_known(v_mod_x3f_2204_, 1);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v___y_2325_);
lean_dec_ref(v___y_2322_);
lean_dec_ref(v_params_2202_);
v___x_2334_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2335_ = l_Lean_indentExpr(v___y_2324_);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2336_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec_ref(v___y_2331_);
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
else
{
v___y_2297_ = v___y_2322_;
v___y_2298_ = v___y_2324_;
v___y_2299_ = v___y_2325_;
v___y_2300_ = v___y_2327_;
v___y_2301_ = v___y_2328_;
v___y_2302_ = v___y_2329_;
v___y_2303_ = v___y_2330_;
v___y_2304_ = v___y_2331_;
v___y_2305_ = v___y_2332_;
goto v___jp_2296_;
}
}
}
else
{
lean_object* v_extra_2346_; 
lean_dec_ref(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec_ref(v___y_2322_);
lean_dec(v_mod_x3f_2204_);
v_extra_2346_ = lean_ctor_get(v_params_2202_, 2);
lean_inc_ref(v_extra_2346_);
if (lean_obj_tag(v___y_2323_) == 2)
{
lean_object* v_config_2347_; lean_object* v_extensions_2348_; lean_object* v_extraInj_2349_; lean_object* v_extraFacts_2350_; lean_object* v_symPrios_2351_; lean_object* v_norm_2352_; lean_object* v_normProcs_2353_; lean_object* v_anchorRefs_x3f_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2409_; 
v_config_2347_ = lean_ctor_get(v_params_2202_, 0);
v_extensions_2348_ = lean_ctor_get(v_params_2202_, 1);
v_extraInj_2349_ = lean_ctor_get(v_params_2202_, 3);
v_extraFacts_2350_ = lean_ctor_get(v_params_2202_, 4);
v_symPrios_2351_ = lean_ctor_get(v_params_2202_, 5);
v_norm_2352_ = lean_ctor_get(v_params_2202_, 6);
v_normProcs_2353_ = lean_ctor_get(v_params_2202_, 7);
v_anchorRefs_x3f_2354_ = lean_ctor_get(v_params_2202_, 8);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_params_2202_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v_params_2202_, 2);
lean_dec(v_unused_2410_);
v___x_2356_ = v_params_2202_;
v_isShared_2357_ = v_isSharedCheck_2409_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_anchorRefs_x3f_2354_);
lean_inc(v_normProcs_2353_);
lean_inc(v_norm_2352_);
lean_inc(v_symPrios_2351_);
lean_inc(v_extraFacts_2350_);
lean_inc(v_extraInj_2349_);
lean_inc(v_extensions_2348_);
lean_inc(v_config_2347_);
lean_dec(v_params_2202_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2409_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_size_2358_; uint8_t v_gen_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2408_; 
v_size_2358_ = lean_ctor_get(v_extra_2346_, 2);
v_gen_2359_ = lean_ctor_get_uint8(v___y_2323_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___y_2323_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2361_ = v___y_2323_;
v_isShared_2362_ = v_isSharedCheck_2408_;
goto v_resetjp_2360_;
}
else
{
lean_dec(v___y_2323_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2408_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; 
v___x_2363_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2206_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v___x_2365_; 
lean_dec_ref_known(v___x_2363_, 1);
if (v_isShared_2362_ == 0)
{
lean_ctor_set_tag(v___x_2361_, 0);
v___x_2365_ = v___x_2361_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2399_, 0, v_gen_2359_);
v___x_2365_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; 
lean_inc_ref(v___y_2326_);
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
lean_inc(v_size_2358_);
v___x_2366_ = lean_apply_7(v___y_2326_, v___x_2365_, v_size_2358_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, lean_box(0));
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2368_, 0, v_gen_2359_);
lean_inc(v___y_2332_);
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
lean_inc(v_size_2358_);
v___x_2369_ = lean_apply_7(v___y_2326_, v___x_2368_, v_size_2358_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, lean_box(0));
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2382_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2382_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2382_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2374_ = l_Lean_PersistentArray_push___redArg(v_extra_2346_, v_a_2367_);
v___x_2375_ = l_Lean_PersistentArray_push___redArg(v___x_2374_, v_a_2370_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 2, v___x_2375_);
v___x_2377_ = v___x_2356_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_config_2347_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_extensions_2348_);
lean_ctor_set(v_reuseFailAlloc_2381_, 2, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2381_, 3, v_extraInj_2349_);
lean_ctor_set(v_reuseFailAlloc_2381_, 4, v_extraFacts_2350_);
lean_ctor_set(v_reuseFailAlloc_2381_, 5, v_symPrios_2351_);
lean_ctor_set(v_reuseFailAlloc_2381_, 6, v_norm_2352_);
lean_ctor_set(v_reuseFailAlloc_2381_, 7, v_normProcs_2353_);
lean_ctor_set(v_reuseFailAlloc_2381_, 8, v_anchorRefs_x3f_2354_);
v___x_2377_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2379_; 
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2377_);
v___x_2379_ = v___x_2372_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec(v_a_2367_);
lean_del_object(v___x_2356_);
lean_dec(v_anchorRefs_x3f_2354_);
lean_dec_ref(v_normProcs_2353_);
lean_dec_ref(v_norm_2352_);
lean_dec_ref(v_symPrios_2351_);
lean_dec_ref(v_extraFacts_2350_);
lean_dec_ref(v_extraInj_2349_);
lean_dec_ref(v_extensions_2348_);
lean_dec_ref(v_config_2347_);
lean_dec_ref(v_extra_2346_);
v_a_2383_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2369_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2369_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_del_object(v___x_2356_);
lean_dec(v_anchorRefs_x3f_2354_);
lean_dec_ref(v_normProcs_2353_);
lean_dec_ref(v_norm_2352_);
lean_dec_ref(v_symPrios_2351_);
lean_dec_ref(v_extraFacts_2350_);
lean_dec_ref(v_extraInj_2349_);
lean_dec_ref(v_extensions_2348_);
lean_dec_ref(v_config_2347_);
lean_dec_ref(v_extra_2346_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v___y_2326_);
v_a_2391_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2366_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2366_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_del_object(v___x_2361_);
lean_del_object(v___x_2356_);
lean_dec(v_anchorRefs_x3f_2354_);
lean_dec_ref(v_normProcs_2353_);
lean_dec_ref(v_norm_2352_);
lean_dec_ref(v_symPrios_2351_);
lean_dec_ref(v_extraFacts_2350_);
lean_dec_ref(v_extraInj_2349_);
lean_dec_ref(v_extensions_2348_);
lean_dec_ref(v_config_2347_);
lean_dec_ref(v_extra_2346_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v___y_2326_);
v_a_2400_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2363_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2363_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
else
{
switch(lean_obj_tag(v___y_2323_))
{
case 0:
{
lean_object* v_config_2411_; lean_object* v_extensions_2412_; lean_object* v_extraInj_2413_; lean_object* v_extraFacts_2414_; lean_object* v_symPrios_2415_; lean_object* v_norm_2416_; lean_object* v_normProcs_2417_; lean_object* v_anchorRefs_x3f_2418_; lean_object* v_size_2419_; 
v_config_2411_ = lean_ctor_get(v_params_2202_, 0);
lean_inc_ref(v_config_2411_);
v_extensions_2412_ = lean_ctor_get(v_params_2202_, 1);
lean_inc_ref(v_extensions_2412_);
v_extraInj_2413_ = lean_ctor_get(v_params_2202_, 3);
lean_inc_ref(v_extraInj_2413_);
v_extraFacts_2414_ = lean_ctor_get(v_params_2202_, 4);
lean_inc_ref(v_extraFacts_2414_);
v_symPrios_2415_ = lean_ctor_get(v_params_2202_, 5);
lean_inc_ref(v_symPrios_2415_);
v_norm_2416_ = lean_ctor_get(v_params_2202_, 6);
lean_inc_ref(v_norm_2416_);
v_normProcs_2417_ = lean_ctor_get(v_params_2202_, 7);
lean_inc_ref(v_normProcs_2417_);
v_anchorRefs_x3f_2418_ = lean_ctor_get(v_params_2202_, 8);
lean_inc(v_anchorRefs_x3f_2418_);
lean_dec_ref(v_params_2202_);
v_size_2419_ = lean_ctor_get(v_extra_2346_, 2);
lean_inc(v_size_2419_);
v___y_2251_ = v_normProcs_2417_;
v___y_2252_ = v_extensions_2412_;
v___y_2253_ = v___y_2323_;
v___y_2254_ = v___y_2331_;
v___y_2255_ = v_extraFacts_2414_;
v___y_2256_ = v_config_2411_;
v___y_2257_ = v_symPrios_2415_;
v___y_2258_ = v_anchorRefs_x3f_2418_;
v___y_2259_ = v___y_2330_;
v___y_2260_ = v_extraInj_2413_;
v___y_2261_ = v_norm_2416_;
v___y_2262_ = v___y_2329_;
v___y_2263_ = v_size_2419_;
v___y_2264_ = v___y_2332_;
v___y_2265_ = v_extra_2346_;
v___y_2266_ = v___y_2326_;
goto v___jp_2250_;
}
case 1:
{
lean_object* v_config_2420_; lean_object* v_extensions_2421_; lean_object* v_extraInj_2422_; lean_object* v_extraFacts_2423_; lean_object* v_symPrios_2424_; lean_object* v_norm_2425_; lean_object* v_normProcs_2426_; lean_object* v_anchorRefs_x3f_2427_; lean_object* v_size_2428_; 
v_config_2420_ = lean_ctor_get(v_params_2202_, 0);
lean_inc_ref(v_config_2420_);
v_extensions_2421_ = lean_ctor_get(v_params_2202_, 1);
lean_inc_ref(v_extensions_2421_);
v_extraInj_2422_ = lean_ctor_get(v_params_2202_, 3);
lean_inc_ref(v_extraInj_2422_);
v_extraFacts_2423_ = lean_ctor_get(v_params_2202_, 4);
lean_inc_ref(v_extraFacts_2423_);
v_symPrios_2424_ = lean_ctor_get(v_params_2202_, 5);
lean_inc_ref(v_symPrios_2424_);
v_norm_2425_ = lean_ctor_get(v_params_2202_, 6);
lean_inc_ref(v_norm_2425_);
v_normProcs_2426_ = lean_ctor_get(v_params_2202_, 7);
lean_inc_ref(v_normProcs_2426_);
v_anchorRefs_x3f_2427_ = lean_ctor_get(v_params_2202_, 8);
lean_inc(v_anchorRefs_x3f_2427_);
lean_dec_ref(v_params_2202_);
v_size_2428_ = lean_ctor_get(v_extra_2346_, 2);
lean_inc(v_size_2428_);
v___y_2251_ = v_normProcs_2426_;
v___y_2252_ = v_extensions_2421_;
v___y_2253_ = v___y_2323_;
v___y_2254_ = v___y_2331_;
v___y_2255_ = v_extraFacts_2423_;
v___y_2256_ = v_config_2420_;
v___y_2257_ = v_symPrios_2424_;
v___y_2258_ = v_anchorRefs_x3f_2427_;
v___y_2259_ = v___y_2330_;
v___y_2260_ = v_extraInj_2422_;
v___y_2261_ = v_norm_2425_;
v___y_2262_ = v___y_2329_;
v___y_2263_ = v_size_2428_;
v___y_2264_ = v___y_2332_;
v___y_2265_ = v_extra_2346_;
v___y_2266_ = v___y_2326_;
goto v___jp_2250_;
}
default: 
{
lean_object* v_config_2429_; lean_object* v_extensions_2430_; lean_object* v_extraInj_2431_; lean_object* v_extraFacts_2432_; lean_object* v_symPrios_2433_; lean_object* v_norm_2434_; lean_object* v_normProcs_2435_; lean_object* v_anchorRefs_x3f_2436_; lean_object* v_size_2437_; 
v_config_2429_ = lean_ctor_get(v_params_2202_, 0);
lean_inc_ref(v_config_2429_);
v_extensions_2430_ = lean_ctor_get(v_params_2202_, 1);
lean_inc_ref(v_extensions_2430_);
v_extraInj_2431_ = lean_ctor_get(v_params_2202_, 3);
lean_inc_ref(v_extraInj_2431_);
v_extraFacts_2432_ = lean_ctor_get(v_params_2202_, 4);
lean_inc_ref(v_extraFacts_2432_);
v_symPrios_2433_ = lean_ctor_get(v_params_2202_, 5);
lean_inc_ref(v_symPrios_2433_);
v_norm_2434_ = lean_ctor_get(v_params_2202_, 6);
lean_inc_ref(v_norm_2434_);
v_normProcs_2435_ = lean_ctor_get(v_params_2202_, 7);
lean_inc_ref(v_normProcs_2435_);
v_anchorRefs_x3f_2436_ = lean_ctor_get(v_params_2202_, 8);
lean_inc(v_anchorRefs_x3f_2436_);
lean_dec_ref(v_params_2202_);
v_size_2437_ = lean_ctor_get(v_extra_2346_, 2);
lean_inc(v_size_2437_);
v___y_2215_ = v_normProcs_2435_;
v___y_2216_ = v_extraInj_2431_;
v___y_2217_ = v_norm_2434_;
v___y_2218_ = v_extensions_2430_;
v___y_2219_ = v___y_2323_;
v___y_2220_ = v_size_2437_;
v___y_2221_ = v_extraFacts_2432_;
v___y_2222_ = v_config_2429_;
v___y_2223_ = v_symPrios_2433_;
v___y_2224_ = v_extra_2346_;
v___y_2225_ = v_anchorRefs_x3f_2436_;
v___y_2226_ = v___y_2326_;
v___y_2227_ = v___y_2329_;
v___y_2228_ = v___y_2330_;
v___y_2229_ = v___y_2331_;
v___y_2230_ = v___y_2332_;
goto v___jp_2214_;
}
}
}
}
}
v___jp_2438_:
{
lean_object* v___x_2446_; uint8_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___f_2449_; lean_object* v___x_2450_; 
v___x_2446_ = lean_box(0);
v___x_2447_ = 1;
v___x_2448_ = lean_box(v___x_2447_);
lean_inc(v_p_2203_);
v___f_2449_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2449_, 0, v_p_2203_);
lean_closure_set(v___f_2449_, 1, v_term_2205_);
lean_closure_set(v___f_2449_, 2, v___x_2446_);
lean_closure_set(v___f_2449_, 3, v___x_2448_);
v___x_2450_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2449_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2495_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2495_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2495_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
if (lean_obj_tag(v_a_2451_) == 1)
{
lean_object* v_val_2455_; lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2458_; 
lean_del_object(v___x_2453_);
v_val_2455_ = lean_ctor_get(v_a_2451_, 0);
lean_inc(v_val_2455_);
lean_dec_ref_known(v_a_2451_, 1);
v_fst_2456_ = lean_ctor_get(v_val_2455_, 0);
lean_inc(v_fst_2456_);
v_snd_2457_ = lean_ctor_get(v_val_2455_, 1);
lean_inc_n(v_snd_2457_, 2);
lean_dec(v_val_2455_);
lean_inc(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
v___x_2458_ = lean_infer_type(v_snd_2457_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2460_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc_n(v_a_2459_, 2);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2460_ = l_Lean_Meta_isProp(v_a_2459_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___f_2464_; uint8_t v___x_2465_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2460_, 1);
v___x_2462_ = lean_box(v___x_2447_);
v___x_2463_ = lean_box(v_minIndexable_2206_);
lean_inc(v_snd_2457_);
lean_inc(v_fst_2456_);
lean_inc_ref(v_params_2202_);
v___f_2464_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2464_, 0, v_params_2202_);
lean_closure_set(v___f_2464_, 1, v_p_2203_);
lean_closure_set(v___f_2464_, 2, v_fst_2456_);
lean_closure_set(v___f_2464_, 3, v_snd_2457_);
lean_closure_set(v___f_2464_, 4, v___x_2462_);
lean_closure_set(v___f_2464_, 5, v___x_2463_);
v___x_2465_ = lean_unbox(v_a_2461_);
lean_dec(v_a_2461_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec_ref(v___f_2464_);
lean_dec(v_a_2459_);
lean_dec(v_snd_2457_);
lean_dec(v_fst_2456_);
lean_dec(v_kind_2439_);
lean_dec(v_mod_x3f_2204_);
lean_dec_ref(v_params_2202_);
v___x_2466_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2467_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2466_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec_ref(v___y_2444_);
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
v___y_2322_ = v_snd_2457_;
v___y_2323_ = v_kind_2439_;
v___y_2324_ = v_a_2459_;
v___y_2325_ = v_fst_2456_;
v___y_2326_ = v___f_2464_;
v___y_2327_ = v___y_2440_;
v___y_2328_ = v___y_2441_;
v___y_2329_ = v___y_2442_;
v___y_2330_ = v___y_2443_;
v___y_2331_ = v___y_2444_;
v___y_2332_ = v___y_2445_;
goto v___jp_2321_;
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec(v_a_2459_);
lean_dec(v_snd_2457_);
lean_dec(v_fst_2456_);
lean_dec_ref(v___y_2444_);
lean_dec(v_kind_2439_);
lean_dec(v_mod_x3f_2204_);
lean_dec(v_p_2203_);
lean_dec_ref(v_params_2202_);
v_a_2476_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2460_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2460_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v_snd_2457_);
lean_dec(v_fst_2456_);
lean_dec_ref(v___y_2444_);
lean_dec(v_kind_2439_);
lean_dec(v_mod_x3f_2204_);
lean_dec(v_p_2203_);
lean_dec_ref(v_params_2202_);
v_a_2484_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2458_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2458_);
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
}
else
{
lean_object* v___x_2493_; 
lean_dec(v_a_2451_);
lean_dec_ref(v___y_2444_);
lean_dec(v_kind_2439_);
lean_dec(v_mod_x3f_2204_);
lean_dec(v_p_2203_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v_params_2202_);
v___x_2493_ = v___x_2453_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_params_2202_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec_ref(v___y_2444_);
lean_dec(v_kind_2439_);
lean_dec(v_mod_x3f_2204_);
lean_dec(v_p_2203_);
lean_dec_ref(v_params_2202_);
v_a_2496_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2450_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2450_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
v___jp_2504_:
{
lean_object* v___x_2511_; 
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_kind_2439_ = v___x_2511_;
v___y_2440_ = v___y_2505_;
v___y_2441_ = v___y_2506_;
v___y_2442_ = v___y_2507_;
v___y_2443_ = v___y_2508_;
v___y_2444_ = v___y_2509_;
v___y_2445_ = v___y_2510_;
goto v___jp_2438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2587_, lean_object* v_p_2588_, lean_object* v_mod_x3f_2589_, lean_object* v_term_2590_, lean_object* v_minIndexable_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_){
_start:
{
uint8_t v_minIndexable_boxed_2599_; lean_object* v_res_2600_; 
v_minIndexable_boxed_2599_ = lean_unbox(v_minIndexable_2591_);
v_res_2600_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2587_, v_p_2588_, v_mod_x3f_2589_, v_term_2590_, v_minIndexable_boxed_2599_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec_ref(v_a_2592_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object* v_00_u03b1_2601_, lean_object* v_msg_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v_00_u03b1_2611_, lean_object* v_msg_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v_00_u03b1_2611_, v_msg_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object* v_msgData_2621_, lean_object* v_macroStack_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2621_, v_macroStack_2622_, v___y_2627_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object* v_msgData_2631_, lean_object* v_macroStack_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(v_msgData_2631_, v_macroStack_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2641_, lean_object* v_val_2642_, lean_object* v___x_2643_, lean_object* v_____r_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v___x_2652_; lean_object* v_ext_2653_; lean_object* v_toEnvExtension_2654_; lean_object* v_env_2655_; lean_object* v_config_2656_; lean_object* v_extensions_2657_; lean_object* v_extra_2658_; lean_object* v_extraInj_2659_; lean_object* v_extraFacts_2660_; lean_object* v_symPrios_2661_; lean_object* v_norm_2662_; lean_object* v_normProcs_2663_; lean_object* v_anchorRefs_x3f_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2676_; 
v___x_2652_ = lean_st_ref_get(v___y_2650_);
v_ext_2653_ = lean_ctor_get(v_val_2642_, 1);
v_toEnvExtension_2654_ = lean_ctor_get(v_ext_2653_, 0);
v_env_2655_ = lean_ctor_get(v___x_2652_, 0);
lean_inc_ref(v_env_2655_);
lean_dec(v___x_2652_);
v_config_2656_ = lean_ctor_get(v_params_2641_, 0);
v_extensions_2657_ = lean_ctor_get(v_params_2641_, 1);
v_extra_2658_ = lean_ctor_get(v_params_2641_, 2);
v_extraInj_2659_ = lean_ctor_get(v_params_2641_, 3);
v_extraFacts_2660_ = lean_ctor_get(v_params_2641_, 4);
v_symPrios_2661_ = lean_ctor_get(v_params_2641_, 5);
v_norm_2662_ = lean_ctor_get(v_params_2641_, 6);
v_normProcs_2663_ = lean_ctor_get(v_params_2641_, 7);
v_anchorRefs_x3f_2664_ = lean_ctor_get(v_params_2641_, 8);
v_isSharedCheck_2676_ = !lean_is_exclusive(v_params_2641_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2666_ = v_params_2641_;
v_isShared_2667_ = v_isSharedCheck_2676_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_anchorRefs_x3f_2664_);
lean_inc(v_normProcs_2663_);
lean_inc(v_norm_2662_);
lean_inc(v_symPrios_2661_);
lean_inc(v_extraFacts_2660_);
lean_inc(v_extraInj_2659_);
lean_inc(v_extra_2658_);
lean_inc(v_extensions_2657_);
lean_inc(v_config_2656_);
lean_dec(v_params_2641_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2676_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_asyncMode_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v_asyncMode_2668_ = lean_ctor_get(v_toEnvExtension_2654_, 2);
v___x_2669_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2643_, v_val_2642_, v_env_2655_, v_asyncMode_2668_);
v___x_2670_ = lean_array_push(v_extensions_2657_, v___x_2669_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2670_);
v___x_2672_ = v___x_2666_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_config_2656_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2675_, 2, v_extra_2658_);
lean_ctor_set(v_reuseFailAlloc_2675_, 3, v_extraInj_2659_);
lean_ctor_set(v_reuseFailAlloc_2675_, 4, v_extraFacts_2660_);
lean_ctor_set(v_reuseFailAlloc_2675_, 5, v_symPrios_2661_);
lean_ctor_set(v_reuseFailAlloc_2675_, 6, v_norm_2662_);
lean_ctor_set(v_reuseFailAlloc_2675_, 7, v_normProcs_2663_);
lean_ctor_set(v_reuseFailAlloc_2675_, 8, v_anchorRefs_x3f_2664_);
v___x_2672_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
return v___x_2674_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2677_, lean_object* v_val_2678_, lean_object* v___x_2679_, lean_object* v_____r_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2677_, v_val_2678_, v___x_2679_, v_____r_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec_ref(v___x_2679_);
lean_dec_ref(v_val_2678_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2689_, lean_object* v_id_2690_, uint8_t v_minIndexable_2691_, lean_object* v_as_x27_2692_, lean_object* v_b_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
if (lean_obj_tag(v_as_x27_2692_) == 0)
{
lean_object* v___x_2699_; 
lean_dec(v_id_2690_);
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v_b_2693_);
return v___x_2699_;
}
else
{
lean_object* v_head_2700_; lean_object* v_tail_2701_; lean_object* v_toCold_2702_; lean_object* v_currRecDepth_2703_; lean_object* v_ref_2704_; uint8_t v_diag_2705_; uint8_t v_suppressElabErrors_2706_; uint8_t v___x_2707_; lean_object* v___x_2708_; lean_object* v_ref_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_head_2700_ = lean_ctor_get(v_as_x27_2692_, 0);
v_tail_2701_ = lean_ctor_get(v_as_x27_2692_, 1);
v_toCold_2702_ = lean_ctor_get(v___y_2696_, 0);
v_currRecDepth_2703_ = lean_ctor_get(v___y_2696_, 1);
v_ref_2704_ = lean_ctor_get(v___y_2696_, 2);
v_diag_2705_ = lean_ctor_get_uint8(v___y_2696_, sizeof(void*)*3);
v_suppressElabErrors_2706_ = lean_ctor_get_uint8(v___y_2696_, sizeof(void*)*3 + 1);
v___x_2707_ = 0;
v___x_2708_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_2709_ = l_Lean_replaceRef(v_p_2689_, v_ref_2704_);
lean_inc(v_currRecDepth_2703_);
lean_inc_ref(v_toCold_2702_);
v___x_2710_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2710_, 0, v_toCold_2702_);
lean_ctor_set(v___x_2710_, 1, v_currRecDepth_2703_);
lean_ctor_set(v___x_2710_, 2, v_ref_2709_);
lean_ctor_set_uint8(v___x_2710_, sizeof(void*)*3, v_diag_2705_);
lean_ctor_set_uint8(v___x_2710_, sizeof(void*)*3 + 1, v_suppressElabErrors_2706_);
lean_inc(v_head_2700_);
lean_inc(v_id_2690_);
v___x_2711_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2693_, v_id_2690_, v_head_2700_, v___x_2708_, v_minIndexable_2691_, v___x_2707_, v___x_2707_, v___y_2694_, v___y_2695_, v___x_2710_, v___y_2697_);
lean_dec_ref_known(v___x_2710_, 3);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v_as_x27_2692_ = v_tail_2701_;
v_b_2693_ = v_a_2712_;
goto _start;
}
else
{
lean_dec(v_id_2690_);
return v___x_2711_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2714_, lean_object* v_id_2715_, lean_object* v_minIndexable_2716_, lean_object* v_as_x27_2717_, lean_object* v_b_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
uint8_t v_minIndexable_boxed_2724_; lean_object* v_res_2725_; 
v_minIndexable_boxed_2724_ = lean_unbox(v_minIndexable_2716_);
v_res_2725_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2714_, v_id_2715_, v_minIndexable_boxed_2724_, v_as_x27_2717_, v_b_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v_as_x27_2717_);
lean_dec(v_p_2714_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
if (lean_obj_tag(v_a_2727_) == 0)
{
lean_object* v___x_2729_; 
v___x_2729_ = l_List_reverse___redArg(v_a_2728_);
return v___x_2729_;
}
else
{
lean_object* v_head_2730_; lean_object* v_tail_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2742_; 
v_head_2730_ = lean_ctor_get(v_a_2727_, 0);
v_tail_2731_ = lean_ctor_get(v_a_2727_, 1);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_a_2727_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2733_ = v_a_2727_;
v_isShared_2734_ = v_isSharedCheck_2742_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_tail_2731_);
lean_inc(v_head_2730_);
lean_dec(v_a_2727_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2742_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_kind_2735_; uint8_t v___x_2736_; 
v_kind_2735_ = lean_ctor_get(v_head_2730_, 6);
v___x_2736_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2735_, v_k_2726_);
if (v___x_2736_ == 0)
{
lean_del_object(v___x_2733_);
lean_dec(v_head_2730_);
v_a_2727_ = v_tail_2731_;
goto _start;
}
else
{
lean_object* v___x_2739_; 
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v_a_2728_);
v___x_2739_ = v___x_2733_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_head_2730_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_a_2728_);
v___x_2739_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
v_a_2727_ = v_tail_2731_;
v_a_2728_ = v___x_2739_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2743_, v_a_2744_, v_a_2745_);
lean_dec(v_k_2743_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_2747_, lean_object* v_msg_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_toCold_2756_; lean_object* v_currRecDepth_2757_; lean_object* v_ref_2758_; uint8_t v_diag_2759_; uint8_t v_suppressElabErrors_2760_; lean_object* v_ref_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_toCold_2756_ = lean_ctor_get(v___y_2753_, 0);
v_currRecDepth_2757_ = lean_ctor_get(v___y_2753_, 1);
v_ref_2758_ = lean_ctor_get(v___y_2753_, 2);
v_diag_2759_ = lean_ctor_get_uint8(v___y_2753_, sizeof(void*)*3);
v_suppressElabErrors_2760_ = lean_ctor_get_uint8(v___y_2753_, sizeof(void*)*3 + 1);
v_ref_2761_ = l_Lean_replaceRef(v_ref_2747_, v_ref_2758_);
lean_inc(v_currRecDepth_2757_);
lean_inc_ref(v_toCold_2756_);
v___x_2762_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2762_, 0, v_toCold_2756_);
lean_ctor_set(v___x_2762_, 1, v_currRecDepth_2757_);
lean_ctor_set(v___x_2762_, 2, v_ref_2761_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*3, v_diag_2759_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*3 + 1, v_suppressElabErrors_2760_);
v___x_2763_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___x_2762_, v___y_2754_);
lean_dec_ref_known(v___x_2762_, 3);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_2764_, lean_object* v_msg_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_2764_, v_msg_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v_ref_2764_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_2774_, lean_object* v_id_2775_, uint8_t v_minIndexable_2776_, lean_object* v_as_x27_2777_, lean_object* v_b_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
if (lean_obj_tag(v_as_x27_2777_) == 0)
{
lean_object* v___x_2784_; 
lean_dec(v_id_2775_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_b_2778_);
return v___x_2784_;
}
else
{
lean_object* v_head_2785_; lean_object* v_tail_2786_; lean_object* v_toCold_2787_; lean_object* v_currRecDepth_2788_; lean_object* v_ref_2789_; uint8_t v_diag_2790_; uint8_t v_suppressElabErrors_2791_; uint8_t v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v_ref_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_head_2785_ = lean_ctor_get(v_as_x27_2777_, 0);
v_tail_2786_ = lean_ctor_get(v_as_x27_2777_, 1);
v_toCold_2787_ = lean_ctor_get(v___y_2781_, 0);
v_currRecDepth_2788_ = lean_ctor_get(v___y_2781_, 1);
v_ref_2789_ = lean_ctor_get(v___y_2781_, 2);
v_diag_2790_ = lean_ctor_get_uint8(v___y_2781_, sizeof(void*)*3);
v_suppressElabErrors_2791_ = lean_ctor_get_uint8(v___y_2781_, sizeof(void*)*3 + 1);
v___x_2792_ = 0;
v___x_2793_ = 1;
v___x_2794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_2795_ = l_Lean_replaceRef(v_p_2774_, v_ref_2789_);
lean_inc(v_currRecDepth_2788_);
lean_inc_ref(v_toCold_2787_);
v___x_2796_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2796_, 0, v_toCold_2787_);
lean_ctor_set(v___x_2796_, 1, v_currRecDepth_2788_);
lean_ctor_set(v___x_2796_, 2, v_ref_2795_);
lean_ctor_set_uint8(v___x_2796_, sizeof(void*)*3, v_diag_2790_);
lean_ctor_set_uint8(v___x_2796_, sizeof(void*)*3 + 1, v_suppressElabErrors_2791_);
lean_inc(v_head_2785_);
lean_inc(v_id_2775_);
v___x_2797_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2778_, v_id_2775_, v_head_2785_, v___x_2794_, v_minIndexable_2776_, v___x_2792_, v___x_2793_, v___y_2779_, v___y_2780_, v___x_2796_, v___y_2782_);
lean_dec_ref_known(v___x_2796_, 3);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v_as_x27_2777_ = v_tail_2786_;
v_b_2778_ = v_a_2798_;
goto _start;
}
else
{
lean_dec(v_id_2775_);
return v___x_2797_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_2800_, lean_object* v_id_2801_, lean_object* v_minIndexable_2802_, lean_object* v_as_x27_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
uint8_t v_minIndexable_boxed_2810_; lean_object* v_res_2811_; 
v_minIndexable_boxed_2810_ = lean_unbox(v_minIndexable_2802_);
v_res_2811_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_2800_, v_id_2801_, v_minIndexable_boxed_2810_, v_as_x27_2803_, v_b_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v_as_x27_2803_);
lean_dec(v_p_2800_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_2812_){
_start:
{
if (lean_obj_tag(v_x_2812_) == 0)
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_box(0);
return v___x_2813_;
}
else
{
lean_object* v_head_2814_; lean_object* v_tail_2815_; lean_object* v_fst_2816_; uint8_t v___x_2817_; 
v_head_2814_ = lean_ctor_get(v_x_2812_, 0);
v_tail_2815_ = lean_ctor_get(v_x_2812_, 1);
v_fst_2816_ = lean_ctor_get(v_head_2814_, 0);
v___x_2817_ = l_Lean_isPrivateName(v_fst_2816_);
if (v___x_2817_ == 0)
{
v_x_2812_ = v_tail_2815_;
goto _start;
}
else
{
lean_object* v___x_2819_; 
lean_inc(v_head_2814_);
v___x_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_head_2814_);
return v___x_2819_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_2820_);
lean_dec(v_x_2820_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_2822_, lean_object* v_msgData_2823_, uint8_t v_severity_2824_, uint8_t v_isSilent_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; uint8_t v___y_2837_; uint8_t v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; uint8_t v___y_2872_; uint8_t v___y_2873_; uint8_t v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; uint8_t v___y_2897_; uint8_t v___y_2898_; lean_object* v___y_2899_; uint8_t v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2905_; lean_object* v___y_2906_; uint8_t v___y_2907_; lean_object* v___y_2908_; uint8_t v___y_2909_; lean_object* v___y_2910_; uint8_t v___y_2911_; uint8_t v___x_2916_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; uint8_t v___y_2921_; lean_object* v___y_2922_; uint8_t v___y_2923_; uint8_t v___y_2924_; uint8_t v___y_2926_; uint8_t v___x_2942_; 
v___x_2916_ = 2;
v___x_2942_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2824_, v___x_2916_);
if (v___x_2942_ == 0)
{
v___y_2926_ = v___x_2942_;
goto v___jp_2925_;
}
else
{
uint8_t v___x_2943_; 
lean_inc_ref(v_msgData_2823_);
v___x_2943_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2823_);
v___y_2926_ = v___x_2943_;
goto v___jp_2925_;
}
v___jp_2831_:
{
lean_object* v___x_2841_; lean_object* v_toCold_2842_; lean_object* v_currNamespace_2843_; lean_object* v_openDecls_2844_; lean_object* v_env_2845_; lean_object* v_nextMacroScope_2846_; lean_object* v_ngen_2847_; lean_object* v_auxDeclNGen_2848_; lean_object* v_traceState_2849_; lean_object* v_cache_2850_; lean_object* v_messages_2851_; lean_object* v_infoState_2852_; lean_object* v_snapshotTasks_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2867_; 
v___x_2841_ = lean_st_ref_take(v___y_2840_);
v_toCold_2842_ = lean_ctor_get(v___y_2839_, 0);
v_currNamespace_2843_ = lean_ctor_get(v_toCold_2842_, 4);
v_openDecls_2844_ = lean_ctor_get(v_toCold_2842_, 5);
v_env_2845_ = lean_ctor_get(v___x_2841_, 0);
v_nextMacroScope_2846_ = lean_ctor_get(v___x_2841_, 1);
v_ngen_2847_ = lean_ctor_get(v___x_2841_, 2);
v_auxDeclNGen_2848_ = lean_ctor_get(v___x_2841_, 3);
v_traceState_2849_ = lean_ctor_get(v___x_2841_, 4);
v_cache_2850_ = lean_ctor_get(v___x_2841_, 5);
v_messages_2851_ = lean_ctor_get(v___x_2841_, 6);
v_infoState_2852_ = lean_ctor_get(v___x_2841_, 7);
v_snapshotTasks_2853_ = lean_ctor_get(v___x_2841_, 8);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2855_ = v___x_2841_;
v_isShared_2856_ = v_isSharedCheck_2867_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_snapshotTasks_2853_);
lean_inc(v_infoState_2852_);
lean_inc(v_messages_2851_);
lean_inc(v_cache_2850_);
lean_inc(v_traceState_2849_);
lean_inc(v_auxDeclNGen_2848_);
lean_inc(v_ngen_2847_);
lean_inc(v_nextMacroScope_2846_);
lean_inc(v_env_2845_);
lean_dec(v___x_2841_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2867_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
lean_inc(v_openDecls_2844_);
lean_inc(v_currNamespace_2843_);
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v_currNamespace_2843_);
lean_ctor_set(v___x_2857_, 1, v_openDecls_2844_);
v___x_2858_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
lean_ctor_set(v___x_2858_, 1, v___y_2835_);
lean_inc_ref(v___y_2836_);
lean_inc_ref(v___y_2834_);
v___x_2859_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2859_, 0, v___y_2834_);
lean_ctor_set(v___x_2859_, 1, v___y_2833_);
lean_ctor_set(v___x_2859_, 2, v___y_2832_);
lean_ctor_set(v___x_2859_, 3, v___y_2836_);
lean_ctor_set(v___x_2859_, 4, v___x_2858_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*5, v___y_2838_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*5 + 1, v___y_2837_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*5 + 2, v_isSilent_2825_);
v___x_2860_ = l_Lean_MessageLog_add(v___x_2859_, v_messages_2851_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 6, v___x_2860_);
v___x_2862_ = v___x_2855_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_env_2845_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_nextMacroScope_2846_);
lean_ctor_set(v_reuseFailAlloc_2866_, 2, v_ngen_2847_);
lean_ctor_set(v_reuseFailAlloc_2866_, 3, v_auxDeclNGen_2848_);
lean_ctor_set(v_reuseFailAlloc_2866_, 4, v_traceState_2849_);
lean_ctor_set(v_reuseFailAlloc_2866_, 5, v_cache_2850_);
lean_ctor_set(v_reuseFailAlloc_2866_, 6, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2866_, 7, v_infoState_2852_);
lean_ctor_set(v_reuseFailAlloc_2866_, 8, v_snapshotTasks_2853_);
v___x_2862_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2863_ = lean_st_ref_put(v___y_2840_, v___x_2862_);
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
return v___x_2865_;
}
}
}
v___jp_2868_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2892_; 
v___x_2877_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2823_);
v___x_2878_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_2877_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2892_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2892_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_inc_ref_n(v___y_2875_, 2);
v___x_2883_ = l_Lean_FileMap_toPosition(v___y_2875_, v___y_2870_);
lean_dec(v___y_2870_);
v___x_2884_ = l_Lean_FileMap_toPosition(v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
v___x_2886_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_2872_ == 0)
{
lean_del_object(v___x_2881_);
lean_dec_ref(v___y_2869_);
v___y_2832_ = v___x_2885_;
v___y_2833_ = v___x_2883_;
v___y_2834_ = v___y_2871_;
v___y_2835_ = v_a_2879_;
v___y_2836_ = v___x_2886_;
v___y_2837_ = v___y_2873_;
v___y_2838_ = v___y_2874_;
v___y_2839_ = v___y_2828_;
v___y_2840_ = v___y_2829_;
goto v___jp_2831_;
}
else
{
uint8_t v___x_2887_; 
lean_inc(v_a_2879_);
v___x_2887_ = l_Lean_MessageData_hasTag(v___y_2869_, v_a_2879_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2890_; 
lean_dec_ref_known(v___x_2885_, 1);
lean_dec_ref(v___x_2883_);
lean_dec(v_a_2879_);
v___x_2888_ = lean_box(0);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2888_);
v___x_2890_ = v___x_2881_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
else
{
lean_del_object(v___x_2881_);
v___y_2832_ = v___x_2885_;
v___y_2833_ = v___x_2883_;
v___y_2834_ = v___y_2871_;
v___y_2835_ = v_a_2879_;
v___y_2836_ = v___x_2886_;
v___y_2837_ = v___y_2873_;
v___y_2838_ = v___y_2874_;
v___y_2839_ = v___y_2828_;
v___y_2840_ = v___y_2829_;
goto v___jp_2831_;
}
}
}
}
v___jp_2893_:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_Syntax_getTailPos_x3f(v___y_2895_, v___y_2900_);
lean_dec(v___y_2895_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_inc(v___y_2901_);
v___y_2869_ = v___y_2894_;
v___y_2870_ = v___y_2901_;
v___y_2871_ = v___y_2896_;
v___y_2872_ = v___y_2898_;
v___y_2873_ = v___y_2897_;
v___y_2874_ = v___y_2900_;
v___y_2875_ = v___y_2899_;
v___y_2876_ = v___y_2901_;
goto v___jp_2868_;
}
else
{
lean_object* v_val_2903_; 
v_val_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_val_2903_);
lean_dec_ref_known(v___x_2902_, 1);
v___y_2869_ = v___y_2894_;
v___y_2870_ = v___y_2901_;
v___y_2871_ = v___y_2896_;
v___y_2872_ = v___y_2898_;
v___y_2873_ = v___y_2897_;
v___y_2874_ = v___y_2900_;
v___y_2875_ = v___y_2899_;
v___y_2876_ = v_val_2903_;
goto v___jp_2868_;
}
}
v___jp_2904_:
{
lean_object* v_ref_2912_; lean_object* v___x_2913_; 
v_ref_2912_ = l_Lean_replaceRef(v_ref_2822_, v___y_2908_);
v___x_2913_ = l_Lean_Syntax_getPos_x3f(v_ref_2912_, v___y_2909_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2914_; 
v___x_2914_ = lean_unsigned_to_nat(0u);
v___y_2894_ = v___y_2905_;
v___y_2895_ = v_ref_2912_;
v___y_2896_ = v___y_2906_;
v___y_2897_ = v___y_2911_;
v___y_2898_ = v___y_2907_;
v___y_2899_ = v___y_2910_;
v___y_2900_ = v___y_2909_;
v___y_2901_ = v___x_2914_;
goto v___jp_2893_;
}
else
{
lean_object* v_val_2915_; 
v_val_2915_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_val_2915_);
lean_dec_ref_known(v___x_2913_, 1);
v___y_2894_ = v___y_2905_;
v___y_2895_ = v_ref_2912_;
v___y_2896_ = v___y_2906_;
v___y_2897_ = v___y_2911_;
v___y_2898_ = v___y_2907_;
v___y_2899_ = v___y_2910_;
v___y_2900_ = v___y_2909_;
v___y_2901_ = v_val_2915_;
goto v___jp_2893_;
}
}
v___jp_2917_:
{
if (v___y_2924_ == 0)
{
v___y_2905_ = v___y_2918_;
v___y_2906_ = v___y_2919_;
v___y_2907_ = v___y_2921_;
v___y_2908_ = v___y_2922_;
v___y_2909_ = v___y_2923_;
v___y_2910_ = v___y_2920_;
v___y_2911_ = v_severity_2824_;
goto v___jp_2904_;
}
else
{
v___y_2905_ = v___y_2918_;
v___y_2906_ = v___y_2919_;
v___y_2907_ = v___y_2921_;
v___y_2908_ = v___y_2922_;
v___y_2909_ = v___y_2923_;
v___y_2910_ = v___y_2920_;
v___y_2911_ = v___x_2916_;
goto v___jp_2904_;
}
}
v___jp_2925_:
{
if (v___y_2926_ == 0)
{
lean_object* v_toCold_2927_; lean_object* v_ref_2928_; uint8_t v_suppressElabErrors_2929_; lean_object* v_fileName_2930_; lean_object* v_fileMap_2931_; lean_object* v_options_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___f_2935_; uint8_t v___x_2936_; uint8_t v___x_2937_; 
v_toCold_2927_ = lean_ctor_get(v___y_2828_, 0);
v_ref_2928_ = lean_ctor_get(v___y_2828_, 2);
v_suppressElabErrors_2929_ = lean_ctor_get_uint8(v___y_2828_, sizeof(void*)*3 + 1);
v_fileName_2930_ = lean_ctor_get(v_toCold_2927_, 0);
v_fileMap_2931_ = lean_ctor_get(v_toCold_2927_, 1);
v_options_2932_ = lean_ctor_get(v_toCold_2927_, 2);
v___x_2933_ = lean_box(v_suppressElabErrors_2929_);
v___x_2934_ = lean_box(v___y_2926_);
v___f_2935_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2935_, 0, v___x_2933_);
lean_closure_set(v___f_2935_, 1, v___x_2934_);
v___x_2936_ = 1;
v___x_2937_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2824_, v___x_2936_);
if (v___x_2937_ == 0)
{
v___y_2918_ = v___f_2935_;
v___y_2919_ = v_fileName_2930_;
v___y_2920_ = v_fileMap_2931_;
v___y_2921_ = v_suppressElabErrors_2929_;
v___y_2922_ = v_ref_2928_;
v___y_2923_ = v___y_2926_;
v___y_2924_ = v___x_2937_;
goto v___jp_2917_;
}
else
{
lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2938_ = l_Lean_warningAsError;
v___x_2939_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2932_, v___x_2938_);
v___y_2918_ = v___f_2935_;
v___y_2919_ = v_fileName_2930_;
v___y_2920_ = v_fileMap_2931_;
v___y_2921_ = v_suppressElabErrors_2929_;
v___y_2922_ = v_ref_2928_;
v___y_2923_ = v___y_2926_;
v___y_2924_ = v___x_2939_;
goto v___jp_2917_;
}
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec_ref(v_msgData_2823_);
v___x_2940_ = lean_box(0);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_2944_, lean_object* v_msgData_2945_, lean_object* v_severity_2946_, lean_object* v_isSilent_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
uint8_t v_severity_boxed_2953_; uint8_t v_isSilent_boxed_2954_; lean_object* v_res_2955_; 
v_severity_boxed_2953_ = lean_unbox(v_severity_2946_);
v_isSilent_boxed_2954_ = lean_unbox(v_isSilent_2947_);
v_res_2955_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_2944_, v_msgData_2945_, v_severity_boxed_2953_, v_isSilent_boxed_2954_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v_ref_2944_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_2956_, uint8_t v_severity_2957_, uint8_t v_isSilent_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_ref_2966_; lean_object* v___x_2967_; 
v_ref_2966_ = lean_ctor_get(v___y_2963_, 2);
v___x_2967_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_2966_, v_msgData_2956_, v_severity_2957_, v_isSilent_2958_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_2968_, lean_object* v_severity_2969_, lean_object* v_isSilent_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
uint8_t v_severity_boxed_2978_; uint8_t v_isSilent_boxed_2979_; lean_object* v_res_2980_; 
v_severity_boxed_2978_ = lean_unbox(v_severity_2969_);
v_isSilent_boxed_2979_ = lean_unbox(v_isSilent_2970_);
v_res_2980_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_2968_, v_severity_boxed_2978_, v_isSilent_boxed_2979_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
uint8_t v___x_2989_; uint8_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = 1;
v___x_2990_ = 0;
v___x_2991_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_2981_, v___x_2989_, v___x_2990_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_toCold_3004_; lean_object* v_options_3005_; uint8_t v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_toCold_3004_ = lean_ctor_get(v___y_3002_, 0);
v_options_3005_ = lean_ctor_get(v_toCold_3004_, 2);
v___x_3006_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_3005_, v_opt_3001_);
v___x_3007_ = lean_box(v___x_3006_);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3009_, v___y_3010_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v_opt_3009_);
return v_res_3012_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3015_ = l_Lean_stringToMessageData(v___x_3014_);
return v___x_3015_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3018_ = l_Lean_stringToMessageData(v___x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___x_3027_; lean_object* v_env_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3050_; 
v___x_3027_ = lean_st_ref_get(v___y_3025_);
v_env_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc_ref(v_env_3028_);
lean_dec(v___x_3027_);
v___x_3029_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3030_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3029_, v___y_3024_);
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3050_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3050_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
uint8_t v_isExporting_3040_; 
v_isExporting_3040_ = lean_ctor_get_uint8(v_env_3028_, sizeof(void*)*8);
lean_dec_ref(v_env_3028_);
if (v_isExporting_3040_ == 0)
{
lean_dec(v_a_3031_);
lean_dec(v_id_3019_);
goto v___jp_3035_;
}
else
{
uint8_t v___x_3041_; 
v___x_3041_ = l_Lean_isPrivateName(v_id_3019_);
if (v___x_3041_ == 0)
{
lean_dec(v_a_3031_);
lean_dec(v_id_3019_);
goto v___jp_3035_;
}
else
{
uint8_t v___x_3042_; 
v___x_3042_ = lean_unbox(v_a_3031_);
lean_dec(v_a_3031_);
if (v___x_3042_ == 0)
{
lean_dec(v_id_3019_);
goto v___jp_3035_;
}
else
{
lean_object* v___x_3043_; uint8_t v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_del_object(v___x_3033_);
v___x_3043_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3044_ = 0;
v___x_3045_ = l_Lean_MessageData_ofConstName(v_id_3019_, v___x_3044_);
v___x_3046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3043_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3048_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
return v___x_3049_;
}
}
}
v___jp_3035_:
{
lean_object* v___x_3036_; lean_object* v___x_3038_; 
v___x_3036_ = lean_box(0);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3036_);
v___x_3038_ = v___x_3033_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3036_);
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
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3060_, uint8_t v_enableLog_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v___x_3069_; lean_object* v_toCold_3070_; lean_object* v_env_3071_; lean_object* v_options_3072_; lean_object* v_currNamespace_3073_; lean_object* v_openDecls_3074_; lean_object* v___x_3075_; lean_object* v_env_3076_; lean_object* v_res_3077_; 
v___x_3069_ = lean_st_ref_get(v___y_3067_);
v_toCold_3070_ = lean_ctor_get(v___y_3066_, 0);
v_env_3071_ = lean_ctor_get(v___x_3069_, 0);
lean_inc_ref(v_env_3071_);
lean_dec(v___x_3069_);
v_options_3072_ = lean_ctor_get(v_toCold_3070_, 2);
v_currNamespace_3073_ = lean_ctor_get(v_toCold_3070_, 4);
v_openDecls_3074_ = lean_ctor_get(v_toCold_3070_, 5);
v___x_3075_ = lean_st_ref_get(v___y_3067_);
v_env_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc_ref(v_env_3076_);
lean_dec(v___x_3075_);
lean_inc(v_openDecls_3074_);
lean_inc(v_currNamespace_3073_);
v_res_3077_ = l_Lean_ResolveName_resolveGlobalName(v_env_3071_, v_options_3072_, v_currNamespace_3073_, v_openDecls_3074_, v_id_3060_);
if (v_enableLog_3061_ == 0)
{
lean_object* v___x_3078_; 
lean_dec_ref(v_env_3076_);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v_res_3077_);
return v___x_3078_;
}
else
{
uint8_t v_isExporting_3079_; 
v_isExporting_3079_ = lean_ctor_get_uint8(v_env_3076_, sizeof(void*)*8);
lean_dec_ref(v_env_3076_);
if (v_isExporting_3079_ == 0)
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3080_, 0, v_res_3077_);
return v___x_3080_;
}
else
{
lean_object* v___x_3081_; 
v___x_3081_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3077_);
if (lean_obj_tag(v___x_3081_) == 1)
{
lean_object* v_val_3082_; lean_object* v_fst_3083_; lean_object* v___x_3084_; 
v_val_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_val_3082_);
lean_dec_ref_known(v___x_3081_, 1);
v_fst_3083_ = lean_ctor_get(v_val_3082_, 0);
lean_inc(v_fst_3083_);
lean_dec(v_val_3082_);
v___x_3084_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3083_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v___x_3084_, 0);
lean_dec(v_unused_3092_);
v___x_3086_ = v___x_3084_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_dec(v___x_3084_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v_res_3077_);
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_res_3077_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec(v_res_3077_);
v_a_3093_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3084_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3084_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
else
{
lean_object* v___x_3101_; 
lean_dec(v___x_3081_);
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v_res_3077_);
return v___x_3101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3102_, lean_object* v_enableLog_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
uint8_t v_enableLog_boxed_3111_; lean_object* v_res_3112_; 
v_enableLog_boxed_3111_ = lean_unbox(v_enableLog_3103_);
v_res_3112_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3102_, v_enableLog_boxed_3111_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3113_, lean_object* v_a_3114_){
_start:
{
if (lean_obj_tag(v_a_3113_) == 0)
{
lean_object* v___x_3115_; 
v___x_3115_ = l_List_reverse___redArg(v_a_3114_);
return v___x_3115_;
}
else
{
lean_object* v_head_3116_; lean_object* v_tail_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3128_; 
v_head_3116_ = lean_ctor_get(v_a_3113_, 0);
v_tail_3117_ = lean_ctor_get(v_a_3113_, 1);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_a_3113_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3119_ = v_a_3113_;
v_isShared_3120_ = v_isSharedCheck_3128_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_tail_3117_);
lean_inc(v_head_3116_);
lean_dec(v_a_3113_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3128_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v_snd_3121_; uint8_t v___x_3122_; 
v_snd_3121_ = lean_ctor_get(v_head_3116_, 1);
v___x_3122_ = l_List_isEmpty___redArg(v_snd_3121_);
if (v___x_3122_ == 0)
{
lean_del_object(v___x_3119_);
lean_dec(v_head_3116_);
v_a_3113_ = v_tail_3117_;
goto _start;
}
else
{
lean_object* v___x_3125_; 
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 1, v_a_3114_);
v___x_3125_ = v___x_3119_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_head_3116_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_a_3114_);
v___x_3125_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
v_a_3113_ = v_tail_3117_;
v_a_3114_ = v___x_3125_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3129_, lean_object* v_findLocalDecl_x3f_3130_, lean_object* v_n_3131_, lean_object* v_projs_3132_, uint8_t v_globalDeclFound_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___y_3142_; lean_object* v___y_3143_; uint8_t v_globalDeclFoundNext_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v_imported_3153_; lean_object* v_ctx_3154_; lean_object* v_scopes_3155_; lean_object* v_givenNameView_3156_; uint8_t v___y_3158_; 
v_imported_3153_ = lean_ctor_get(v_view_3129_, 1);
v_ctx_3154_ = lean_ctor_get(v_view_3129_, 2);
v_scopes_3155_ = lean_ctor_get(v_view_3129_, 3);
lean_inc(v_scopes_3155_);
lean_inc(v_ctx_3154_);
lean_inc(v_imported_3153_);
lean_inc(v_n_3131_);
v_givenNameView_3156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3156_, 0, v_n_3131_);
lean_ctor_set(v_givenNameView_3156_, 1, v_imported_3153_);
lean_ctor_set(v_givenNameView_3156_, 2, v_ctx_3154_);
lean_ctor_set(v_givenNameView_3156_, 3, v_scopes_3155_);
if (v_globalDeclFound_3133_ == 0)
{
v___y_3158_ = v_globalDeclFound_3133_;
goto v___jp_3157_;
}
else
{
uint8_t v___x_3193_; 
v___x_3193_ = l_List_isEmpty___redArg(v_projs_3132_);
if (v___x_3193_ == 0)
{
v___y_3158_ = v_globalDeclFound_3133_;
goto v___jp_3157_;
}
else
{
uint8_t v___x_3194_; 
v___x_3194_ = 0;
v___y_3158_ = v___x_3194_;
goto v___jp_3157_;
}
}
v___jp_3141_:
{
lean_object* v___x_3151_; 
v___x_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___y_3143_);
lean_ctor_set(v___x_3151_, 1, v_projs_3132_);
v_n_3131_ = v___y_3142_;
v_projs_3132_ = v___x_3151_;
v_globalDeclFound_3133_ = v_globalDeclFoundNext_3144_;
v___y_3134_ = v___y_3145_;
v___y_3135_ = v___y_3146_;
v___y_3136_ = v___y_3147_;
v___y_3137_ = v___y_3148_;
v___y_3138_ = v___y_3149_;
v___y_3139_ = v___y_3150_;
goto _start;
}
v___jp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_box(v___y_3158_);
lean_inc_ref(v_findLocalDecl_x3f_3130_);
lean_inc_ref(v_givenNameView_3156_);
v___x_3160_ = lean_apply_2(v_findLocalDecl_x3f_3130_, v_givenNameView_3156_, v___x_3159_);
if (lean_obj_tag(v___x_3160_) == 0)
{
if (lean_obj_tag(v_n_3131_) == 1)
{
if (v_globalDeclFound_3133_ == 0)
{
lean_object* v_pre_3161_; lean_object* v_str_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_pre_3161_ = lean_ctor_get(v_n_3131_, 0);
lean_inc(v_pre_3161_);
v_str_3162_ = lean_ctor_get(v_n_3131_, 1);
lean_inc_ref(v_str_3162_);
lean_dec_ref_known(v_n_3131_, 2);
v___x_3163_ = l_Lean_MacroScopesView_review(v_givenNameView_3156_);
v___x_3164_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3163_, v_globalDeclFound_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; lean_object* v_r_3167_; uint8_t v___x_3168_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v___x_3166_ = lean_box(0);
v_r_3167_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3165_, v___x_3166_);
v___x_3168_ = l_List_isEmpty___redArg(v_r_3167_);
lean_dec(v_r_3167_);
if (v___x_3168_ == 0)
{
uint8_t v_globalDeclFoundNext_3169_; 
v_globalDeclFoundNext_3169_ = 1;
v___y_3142_ = v_pre_3161_;
v___y_3143_ = v_str_3162_;
v_globalDeclFoundNext_3144_ = v_globalDeclFoundNext_3169_;
v___y_3145_ = v___y_3134_;
v___y_3146_ = v___y_3135_;
v___y_3147_ = v___y_3136_;
v___y_3148_ = v___y_3137_;
v___y_3149_ = v___y_3138_;
v___y_3150_ = v___y_3139_;
goto v___jp_3141_;
}
else
{
v___y_3142_ = v_pre_3161_;
v___y_3143_ = v_str_3162_;
v_globalDeclFoundNext_3144_ = v_globalDeclFound_3133_;
v___y_3145_ = v___y_3134_;
v___y_3146_ = v___y_3135_;
v___y_3147_ = v___y_3136_;
v___y_3148_ = v___y_3137_;
v___y_3149_ = v___y_3138_;
v___y_3150_ = v___y_3139_;
goto v___jp_3141_;
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec_ref(v_str_3162_);
lean_dec(v_pre_3161_);
lean_dec(v_projs_3132_);
lean_dec_ref(v_findLocalDecl_x3f_3130_);
v_a_3170_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3164_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3164_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
lean_object* v_pre_3178_; lean_object* v_str_3179_; 
lean_dec_ref_known(v_givenNameView_3156_, 4);
v_pre_3178_ = lean_ctor_get(v_n_3131_, 0);
lean_inc(v_pre_3178_);
v_str_3179_ = lean_ctor_get(v_n_3131_, 1);
lean_inc_ref(v_str_3179_);
lean_dec_ref_known(v_n_3131_, 2);
v___y_3142_ = v_pre_3178_;
v___y_3143_ = v_str_3179_;
v_globalDeclFoundNext_3144_ = v_globalDeclFound_3133_;
v___y_3145_ = v___y_3134_;
v___y_3146_ = v___y_3135_;
v___y_3147_ = v___y_3136_;
v___y_3148_ = v___y_3137_;
v___y_3149_ = v___y_3138_;
v___y_3150_ = v___y_3139_;
goto v___jp_3141_;
}
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_dec_ref_known(v_givenNameView_3156_, 4);
lean_dec(v_projs_3132_);
lean_dec(v_n_3131_);
lean_dec_ref(v_findLocalDecl_x3f_3130_);
v___x_3180_ = lean_box(0);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
return v___x_3181_;
}
}
else
{
lean_object* v_val_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3192_; 
lean_dec_ref_known(v_givenNameView_3156_, 4);
lean_dec(v_n_3131_);
lean_dec_ref(v_findLocalDecl_x3f_3130_);
v_val_3182_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3184_ = v___x_3160_;
v_isShared_3185_ = v_isSharedCheck_3192_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_val_3182_);
lean_dec(v___x_3160_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3192_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
v___x_3186_ = l_Lean_LocalDecl_toExpr(v_val_3182_);
v___x_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v_projs_3132_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v___x_3187_);
v___x_3189_ = v___x_3184_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
return v___x_3190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3195_, lean_object* v_findLocalDecl_x3f_3196_, lean_object* v_n_3197_, lean_object* v_projs_3198_, lean_object* v_globalDeclFound_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
uint8_t v_globalDeclFound_boxed_3207_; lean_object* v_res_3208_; 
v_globalDeclFound_boxed_3207_ = lean_unbox(v_globalDeclFound_3199_);
v_res_3208_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3195_, v_findLocalDecl_x3f_3196_, v_n_3197_, v_projs_3198_, v_globalDeclFound_boxed_3207_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec_ref(v_view_3195_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3209_, lean_object* v_givenName_3210_, lean_object* v_as_3211_, lean_object* v_i_3212_){
_start:
{
lean_object* v_zero_3213_; uint8_t v_isZero_3214_; 
v_zero_3213_ = lean_unsigned_to_nat(0u);
v_isZero_3214_ = lean_nat_dec_eq(v_i_3212_, v_zero_3213_);
if (v_isZero_3214_ == 1)
{
lean_object* v___x_3215_; 
lean_dec(v_i_3212_);
v___x_3215_ = lean_box(0);
return v___x_3215_;
}
else
{
lean_object* v_one_3216_; lean_object* v_n_3217_; lean_object* v___y_3219_; lean_object* v___x_3221_; 
v_one_3216_ = lean_unsigned_to_nat(1u);
v_n_3217_ = lean_nat_sub(v_i_3212_, v_one_3216_);
lean_dec(v_i_3212_);
v___x_3221_ = lean_array_fget_borrowed(v_as_3211_, v_n_3217_);
if (lean_obj_tag(v___x_3221_) == 0)
{
v___y_3219_ = v___x_3221_;
goto v___jp_3218_;
}
else
{
lean_object* v_val_3222_; uint8_t v___x_3223_; 
v_val_3222_ = lean_ctor_get(v___x_3221_, 0);
v___x_3223_ = l_Lean_LocalDecl_isAuxDecl(v_val_3222_);
if (v___x_3223_ == 0)
{
v___y_3219_ = v_localDecl_x3f_3209_;
goto v___jp_3218_;
}
else
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = l_Lean_LocalDecl_userName(v_val_3222_);
v___x_3225_ = lean_name_eq(v___x_3224_, v_givenName_3210_);
lean_dec(v___x_3224_);
if (v___x_3225_ == 0)
{
v_i_3212_ = v_n_3217_;
goto _start;
}
else
{
v___y_3219_ = v___x_3221_;
goto v___jp_3218_;
}
}
}
v___jp_3218_:
{
if (lean_obj_tag(v___y_3219_) == 0)
{
v_i_3212_ = v_n_3217_;
goto _start;
}
else
{
lean_dec(v_n_3217_);
lean_inc_ref(v___y_3219_);
return v___y_3219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3227_, lean_object* v_givenName_3228_, lean_object* v_as_3229_, lean_object* v_i_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3227_, v_givenName_3228_, v_as_3229_, v_i_3230_);
lean_dec_ref(v_as_3229_);
lean_dec(v_givenName_3228_);
lean_dec(v_localDecl_x3f_3227_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3232_, lean_object* v_givenName_3233_, lean_object* v_as_3234_, lean_object* v_i_3235_){
_start:
{
lean_object* v_zero_3236_; uint8_t v_isZero_3237_; 
v_zero_3236_ = lean_unsigned_to_nat(0u);
v_isZero_3237_ = lean_nat_dec_eq(v_i_3235_, v_zero_3236_);
if (v_isZero_3237_ == 1)
{
lean_object* v___x_3238_; 
lean_dec(v_i_3235_);
v___x_3238_ = lean_box(0);
return v___x_3238_;
}
else
{
lean_object* v_one_3239_; lean_object* v_n_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_one_3239_ = lean_unsigned_to_nat(1u);
v_n_3240_ = lean_nat_sub(v_i_3235_, v_one_3239_);
lean_dec(v_i_3235_);
v___x_3241_ = lean_array_fget_borrowed(v_as_3234_, v_n_3240_);
v___x_3242_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3232_, v_givenName_3233_, v___x_3241_);
if (lean_obj_tag(v___x_3242_) == 0)
{
v_i_3235_ = v_n_3240_;
goto _start;
}
else
{
lean_dec(v_n_3240_);
return v___x_3242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3244_, lean_object* v_givenName_3245_, lean_object* v_x_3246_){
_start:
{
if (lean_obj_tag(v_x_3246_) == 0)
{
lean_object* v_cs_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v_cs_3247_ = lean_ctor_get(v_x_3246_, 0);
v___x_3248_ = lean_array_get_size(v_cs_3247_);
v___x_3249_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3244_, v_givenName_3245_, v_cs_3247_, v___x_3248_);
return v___x_3249_;
}
else
{
lean_object* v_vs_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v_vs_3250_ = lean_ctor_get(v_x_3246_, 0);
v___x_3251_ = lean_array_get_size(v_vs_3250_);
v___x_3252_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3244_, v_givenName_3245_, v_vs_3250_, v___x_3251_);
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3253_, lean_object* v_givenName_3254_, lean_object* v_x_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3253_, v_givenName_3254_, v_x_3255_);
lean_dec_ref(v_x_3255_);
lean_dec(v_givenName_3254_);
lean_dec(v_localDecl_x3f_3253_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3257_, lean_object* v_givenName_3258_, lean_object* v_as_3259_, lean_object* v_i_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3257_, v_givenName_3258_, v_as_3259_, v_i_3260_);
lean_dec_ref(v_as_3259_);
lean_dec(v_givenName_3258_);
lean_dec(v_localDecl_x3f_3257_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3262_, lean_object* v_givenName_3263_, lean_object* v_t_3264_){
_start:
{
lean_object* v_root_3265_; lean_object* v_tail_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_root_3265_ = lean_ctor_get(v_t_3264_, 0);
v_tail_3266_ = lean_ctor_get(v_t_3264_, 1);
v___x_3267_ = lean_array_get_size(v_tail_3266_);
v___x_3268_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3262_, v_givenName_3263_, v_tail_3266_, v___x_3267_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3262_, v_givenName_3263_, v_root_3265_);
return v___x_3269_;
}
else
{
return v___x_3268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3270_, lean_object* v_givenName_3271_, lean_object* v_t_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3270_, v_givenName_3271_, v_t_3272_);
lean_dec_ref(v_t_3272_);
lean_dec(v_givenName_3271_);
lean_dec(v_localDecl_x3f_3270_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3274_, lean_object* v_k_3275_){
_start:
{
if (lean_obj_tag(v_t_3274_) == 0)
{
lean_object* v_k_3276_; lean_object* v_v_3277_; lean_object* v_l_3278_; lean_object* v_r_3279_; uint8_t v___x_3280_; 
v_k_3276_ = lean_ctor_get(v_t_3274_, 1);
v_v_3277_ = lean_ctor_get(v_t_3274_, 2);
v_l_3278_ = lean_ctor_get(v_t_3274_, 3);
v_r_3279_ = lean_ctor_get(v_t_3274_, 4);
v___x_3280_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3275_, v_k_3276_);
switch(v___x_3280_)
{
case 0:
{
v_t_3274_ = v_l_3278_;
goto _start;
}
case 1:
{
lean_object* v___x_3282_; 
lean_inc(v_v_3277_);
v___x_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_v_3277_);
return v___x_3282_;
}
default: 
{
v_t_3274_ = v_r_3279_;
goto _start;
}
}
}
else
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_box(0);
return v___x_3284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3285_, lean_object* v_k_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3285_, v_k_3286_);
lean_dec(v_k_3286_);
lean_dec(v_t_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3288_, lean_object* v_givenName_3289_){
_start:
{
lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3290_ = l_Lean_LocalDecl_userName(v_localDecl_3288_);
v___x_3291_ = lean_name_eq(v___x_3290_, v_givenName_3289_);
lean_dec(v___x_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; 
lean_dec_ref(v_localDecl_3288_);
v___x_3292_ = lean_box(0);
return v___x_3292_;
}
else
{
lean_object* v___x_3293_; 
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v_localDecl_3288_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3294_, lean_object* v_givenName_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3294_, v_givenName_3295_);
lean_dec(v_givenName_3295_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3297_, uint8_t v_skipAuxDecl_3298_, lean_object* v_auxDeclToFullName_3299_, lean_object* v___x_3300_, lean_object* v_givenNameView_3301_, lean_object* v_as_3302_, lean_object* v_i_3303_){
_start:
{
lean_object* v_zero_3304_; uint8_t v_isZero_3305_; 
v_zero_3304_ = lean_unsigned_to_nat(0u);
v_isZero_3305_ = lean_nat_dec_eq(v_i_3303_, v_zero_3304_);
if (v_isZero_3305_ == 1)
{
lean_object* v___x_3306_; 
lean_dec(v_i_3303_);
lean_dec_ref(v_givenNameView_3301_);
lean_dec(v___x_3300_);
v___x_3306_ = lean_box(0);
return v___x_3306_;
}
else
{
lean_object* v_one_3307_; lean_object* v_n_3308_; lean_object* v___y_3310_; lean_object* v___x_3312_; 
v_one_3307_ = lean_unsigned_to_nat(1u);
v_n_3308_ = lean_nat_sub(v_i_3303_, v_one_3307_);
lean_dec(v_i_3303_);
v___x_3312_ = lean_array_fget_borrowed(v_as_3302_, v_n_3308_);
if (lean_obj_tag(v___x_3312_) == 0)
{
v___y_3310_ = v___x_3312_;
goto v___jp_3309_;
}
else
{
lean_object* v_val_3313_; uint8_t v___x_3314_; 
v_val_3313_ = lean_ctor_get(v___x_3312_, 0);
v___x_3314_ = l_Lean_LocalDecl_isAuxDecl(v_val_3313_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; 
lean_inc(v_val_3313_);
v___x_3315_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3313_, v_givenName_3297_);
v___y_3310_ = v___x_3315_;
goto v___jp_3309_;
}
else
{
if (v_skipAuxDecl_3298_ == 0)
{
if (v___x_3314_ == 0)
{
v_i_3303_ = v_n_3308_;
goto _start;
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3317_ = l_Lean_LocalDecl_fvarId(v_val_3313_);
v___x_3318_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3299_, v___x_3317_);
lean_dec(v___x_3317_);
if (lean_obj_tag(v___x_3318_) == 1)
{
lean_object* v_val_3319_; lean_object* v_fullDeclView_3320_; lean_object* v___y_3322_; lean_object* v_name_3343_; lean_object* v___x_3344_; 
v_val_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_val_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v_fullDeclView_3320_ = l_Lean_extractMacroScopes(v_val_3319_);
v_name_3343_ = lean_ctor_get(v_fullDeclView_3320_, 0);
lean_inc_n(v_name_3343_, 2);
v___x_3344_ = l_Lean_privateToUserName_x3f(v_name_3343_);
if (lean_obj_tag(v___x_3344_) == 0)
{
v___y_3322_ = v_name_3343_;
goto v___jp_3321_;
}
else
{
lean_object* v_val_3345_; 
lean_dec(v_name_3343_);
v_val_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_val_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v___y_3322_ = v_val_3345_;
goto v___jp_3321_;
}
v___jp_3321_:
{
lean_object* v_imported_3323_; lean_object* v_ctx_3324_; lean_object* v_scopes_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3341_; 
v_imported_3323_ = lean_ctor_get(v_fullDeclView_3320_, 1);
v_ctx_3324_ = lean_ctor_get(v_fullDeclView_3320_, 2);
v_scopes_3325_ = lean_ctor_get(v_fullDeclView_3320_, 3);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_fullDeclView_3320_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; 
v_unused_3342_ = lean_ctor_get(v_fullDeclView_3320_, 0);
lean_dec(v_unused_3342_);
v___x_3327_ = v_fullDeclView_3320_;
v_isShared_3328_ = v_isSharedCheck_3341_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_scopes_3325_);
lean_inc(v_ctx_3324_);
lean_inc(v_imported_3323_);
lean_dec(v_fullDeclView_3320_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3341_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_fullDeclView_3330_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v___y_3322_);
v_fullDeclView_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___y_3322_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_imported_3323_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_ctx_3324_);
lean_ctor_set(v_reuseFailAlloc_3340_, 3, v_scopes_3325_);
v_fullDeclView_3330_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v_fullDeclName_3331_; uint8_t v___x_3332_; 
lean_inc_ref(v_fullDeclView_3330_);
v_fullDeclName_3331_ = l_Lean_MacroScopesView_review(v_fullDeclView_3330_);
v___x_3332_ = l_Lean_Name_isPrefixOf(v___x_3300_, v_fullDeclName_3331_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; 
lean_dec_ref(v_fullDeclView_3330_);
lean_inc(v___x_3300_);
lean_inc_ref(v_givenNameView_3301_);
lean_inc(v_val_3313_);
v___x_3333_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3313_, v_givenNameView_3301_, v_fullDeclName_3331_, v___x_3300_);
lean_dec(v_fullDeclName_3331_);
v___y_3310_ = v___x_3333_;
goto v___jp_3309_;
}
else
{
lean_object* v___x_3334_; lean_object* v_localDeclNameView_3335_; uint8_t v___x_3336_; 
lean_dec(v_fullDeclName_3331_);
v___x_3334_ = l_Lean_LocalDecl_userName(v_val_3313_);
v_localDeclNameView_3335_ = l_Lean_extractMacroScopes(v___x_3334_);
v___x_3336_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3335_, v_givenNameView_3301_);
lean_dec_ref(v_localDeclNameView_3335_);
if (v___x_3336_ == 0)
{
lean_dec_ref(v_fullDeclView_3330_);
v_i_3303_ = v_n_3308_;
goto _start;
}
else
{
uint8_t v___x_3338_; 
v___x_3338_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3301_, v_fullDeclView_3330_);
lean_dec_ref(v_fullDeclView_3330_);
if (v___x_3338_ == 0)
{
v_i_3303_ = v_n_3308_;
goto _start;
}
else
{
lean_inc_ref(v___x_3312_);
v___y_3310_ = v___x_3312_;
goto v___jp_3309_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3346_; 
lean_dec(v___x_3318_);
lean_inc(v_val_3313_);
v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3313_, v_givenName_3297_);
v___y_3310_ = v___x_3346_;
goto v___jp_3309_;
}
}
}
else
{
v_i_3303_ = v_n_3308_;
goto _start;
}
}
}
v___jp_3309_:
{
if (lean_obj_tag(v___y_3310_) == 0)
{
v_i_3303_ = v_n_3308_;
goto _start;
}
else
{
lean_dec(v_n_3308_);
lean_dec_ref(v_givenNameView_3301_);
lean_dec(v___x_3300_);
return v___y_3310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3348_, lean_object* v_skipAuxDecl_3349_, lean_object* v_auxDeclToFullName_3350_, lean_object* v___x_3351_, lean_object* v_givenNameView_3352_, lean_object* v_as_3353_, lean_object* v_i_3354_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3355_; lean_object* v_res_3356_; 
v_skipAuxDecl_boxed_3355_ = lean_unbox(v_skipAuxDecl_3349_);
v_res_3356_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3348_, v_skipAuxDecl_boxed_3355_, v_auxDeclToFullName_3350_, v___x_3351_, v_givenNameView_3352_, v_as_3353_, v_i_3354_);
lean_dec_ref(v_as_3353_);
lean_dec(v_auxDeclToFullName_3350_);
lean_dec(v_givenName_3348_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3357_, uint8_t v_skipAuxDecl_3358_, lean_object* v_auxDeclToFullName_3359_, lean_object* v___x_3360_, lean_object* v_givenNameView_3361_, lean_object* v_as_3362_, lean_object* v_i_3363_){
_start:
{
lean_object* v_zero_3364_; uint8_t v_isZero_3365_; 
v_zero_3364_ = lean_unsigned_to_nat(0u);
v_isZero_3365_ = lean_nat_dec_eq(v_i_3363_, v_zero_3364_);
if (v_isZero_3365_ == 1)
{
lean_object* v___x_3366_; 
lean_dec(v_i_3363_);
lean_dec_ref(v_givenNameView_3361_);
lean_dec(v___x_3360_);
v___x_3366_ = lean_box(0);
return v___x_3366_;
}
else
{
lean_object* v_one_3367_; lean_object* v_n_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v_one_3367_ = lean_unsigned_to_nat(1u);
v_n_3368_ = lean_nat_sub(v_i_3363_, v_one_3367_);
lean_dec(v_i_3363_);
v___x_3369_ = lean_array_fget_borrowed(v_as_3362_, v_n_3368_);
lean_inc_ref(v_givenNameView_3361_);
lean_inc(v___x_3360_);
v___x_3370_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3357_, v_skipAuxDecl_3358_, v_auxDeclToFullName_3359_, v___x_3360_, v_givenNameView_3361_, v___x_3369_);
if (lean_obj_tag(v___x_3370_) == 0)
{
v_i_3363_ = v_n_3368_;
goto _start;
}
else
{
lean_dec(v_n_3368_);
lean_dec_ref(v_givenNameView_3361_);
lean_dec(v___x_3360_);
return v___x_3370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3372_, uint8_t v_skipAuxDecl_3373_, lean_object* v_auxDeclToFullName_3374_, lean_object* v___x_3375_, lean_object* v_givenNameView_3376_, lean_object* v_x_3377_){
_start:
{
if (lean_obj_tag(v_x_3377_) == 0)
{
lean_object* v_cs_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_cs_3378_ = lean_ctor_get(v_x_3377_, 0);
v___x_3379_ = lean_array_get_size(v_cs_3378_);
v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3372_, v_skipAuxDecl_3373_, v_auxDeclToFullName_3374_, v___x_3375_, v_givenNameView_3376_, v_cs_3378_, v___x_3379_);
return v___x_3380_;
}
else
{
lean_object* v_vs_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v_vs_3381_ = lean_ctor_get(v_x_3377_, 0);
v___x_3382_ = lean_array_get_size(v_vs_3381_);
v___x_3383_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3372_, v_skipAuxDecl_3373_, v_auxDeclToFullName_3374_, v___x_3375_, v_givenNameView_3376_, v_vs_3381_, v___x_3382_);
return v___x_3383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3384_, lean_object* v_skipAuxDecl_3385_, lean_object* v_auxDeclToFullName_3386_, lean_object* v___x_3387_, lean_object* v_givenNameView_3388_, lean_object* v_x_3389_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3390_; lean_object* v_res_3391_; 
v_skipAuxDecl_boxed_3390_ = lean_unbox(v_skipAuxDecl_3385_);
v_res_3391_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3384_, v_skipAuxDecl_boxed_3390_, v_auxDeclToFullName_3386_, v___x_3387_, v_givenNameView_3388_, v_x_3389_);
lean_dec_ref(v_x_3389_);
lean_dec(v_auxDeclToFullName_3386_);
lean_dec(v_givenName_3384_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3392_, lean_object* v_skipAuxDecl_3393_, lean_object* v_auxDeclToFullName_3394_, lean_object* v___x_3395_, lean_object* v_givenNameView_3396_, lean_object* v_as_3397_, lean_object* v_i_3398_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3399_; lean_object* v_res_3400_; 
v_skipAuxDecl_boxed_3399_ = lean_unbox(v_skipAuxDecl_3393_);
v_res_3400_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3392_, v_skipAuxDecl_boxed_3399_, v_auxDeclToFullName_3394_, v___x_3395_, v_givenNameView_3396_, v_as_3397_, v_i_3398_);
lean_dec_ref(v_as_3397_);
lean_dec(v_auxDeclToFullName_3394_);
lean_dec(v_givenName_3392_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3401_, uint8_t v_skipAuxDecl_3402_, lean_object* v_auxDeclToFullName_3403_, lean_object* v___x_3404_, lean_object* v_givenNameView_3405_, lean_object* v_t_3406_){
_start:
{
lean_object* v_root_3407_; lean_object* v_tail_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v_root_3407_ = lean_ctor_get(v_t_3406_, 0);
v_tail_3408_ = lean_ctor_get(v_t_3406_, 1);
v___x_3409_ = lean_array_get_size(v_tail_3408_);
lean_inc_ref(v_givenNameView_3405_);
lean_inc(v___x_3404_);
v___x_3410_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3401_, v_skipAuxDecl_3402_, v_auxDeclToFullName_3403_, v___x_3404_, v_givenNameView_3405_, v_tail_3408_, v___x_3409_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3401_, v_skipAuxDecl_3402_, v_auxDeclToFullName_3403_, v___x_3404_, v_givenNameView_3405_, v_root_3407_);
return v___x_3411_;
}
else
{
lean_dec_ref(v_givenNameView_3405_);
lean_dec(v___x_3404_);
return v___x_3410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3412_, lean_object* v_skipAuxDecl_3413_, lean_object* v_auxDeclToFullName_3414_, lean_object* v___x_3415_, lean_object* v_givenNameView_3416_, lean_object* v_t_3417_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3418_; lean_object* v_res_3419_; 
v_skipAuxDecl_boxed_3418_ = lean_unbox(v_skipAuxDecl_3413_);
v_res_3419_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3412_, v_skipAuxDecl_boxed_3418_, v_auxDeclToFullName_3414_, v___x_3415_, v_givenNameView_3416_, v_t_3417_);
lean_dec_ref(v_t_3417_);
lean_dec(v_auxDeclToFullName_3414_);
lean_dec(v_givenName_3412_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3420_, lean_object* v_currNamespace_3421_, lean_object* v_decls_3422_, lean_object* v_givenNameView_3423_, uint8_t v_skipAuxDecl_3424_){
_start:
{
lean_object* v_givenName_3425_; lean_object* v_localDecl_x3f_3426_; 
lean_inc_ref(v_givenNameView_3423_);
v_givenName_3425_ = l_Lean_MacroScopesView_review(v_givenNameView_3423_);
v_localDecl_x3f_3426_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3425_, v_skipAuxDecl_3424_, v_auxDeclToFullName_3420_, v_currNamespace_3421_, v_givenNameView_3423_, v_decls_3422_);
if (lean_obj_tag(v_localDecl_x3f_3426_) == 0)
{
if (v_skipAuxDecl_3424_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3426_, v_givenName_3425_, v_decls_3422_);
lean_dec(v_givenName_3425_);
return v___x_3427_;
}
else
{
lean_dec(v_givenName_3425_);
return v_localDecl_x3f_3426_;
}
}
else
{
lean_dec(v_givenName_3425_);
return v_localDecl_x3f_3426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3428_, lean_object* v_currNamespace_3429_, lean_object* v_decls_3430_, lean_object* v_givenNameView_3431_, lean_object* v_skipAuxDecl_3432_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3433_; lean_object* v_res_3434_; 
v_skipAuxDecl_boxed_3433_ = lean_unbox(v_skipAuxDecl_3432_);
v_res_3434_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3428_, v_currNamespace_3429_, v_decls_3430_, v_givenNameView_3431_, v_skipAuxDecl_boxed_3433_);
lean_dec_ref(v_decls_3430_);
lean_dec(v_auxDeclToFullName_3428_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v_lctx_3443_; lean_object* v_toCold_3444_; lean_object* v_decls_3445_; lean_object* v_auxDeclToFullName_3446_; lean_object* v_currNamespace_3447_; lean_object* v_view_3448_; lean_object* v_name_3449_; lean_object* v_findLocalDecl_x3f_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; lean_object* v___x_3453_; 
v_lctx_3443_ = lean_ctor_get(v___y_3438_, 2);
v_toCold_3444_ = lean_ctor_get(v___y_3440_, 0);
v_decls_3445_ = lean_ctor_get(v_lctx_3443_, 1);
v_auxDeclToFullName_3446_ = lean_ctor_get(v_lctx_3443_, 2);
v_currNamespace_3447_ = lean_ctor_get(v_toCold_3444_, 4);
v_view_3448_ = l_Lean_extractMacroScopes(v_n_3435_);
v_name_3449_ = lean_ctor_get(v_view_3448_, 0);
lean_inc(v_name_3449_);
lean_inc_ref(v_decls_3445_);
lean_inc(v_currNamespace_3447_);
lean_inc(v_auxDeclToFullName_3446_);
v_findLocalDecl_x3f_3450_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3450_, 0, v_auxDeclToFullName_3446_);
lean_closure_set(v_findLocalDecl_x3f_3450_, 1, v_currNamespace_3447_);
lean_closure_set(v_findLocalDecl_x3f_3450_, 2, v_decls_3445_);
v___x_3451_ = lean_box(0);
v___x_3452_ = 0;
v___x_3453_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3448_, v_findLocalDecl_x3f_3450_, v_name_3449_, v___x_3451_, v___x_3452_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
lean_dec_ref(v_view_3448_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3463_, lean_object* v_b_3464_){
_start:
{
if (lean_obj_tag(v_as_x27_3463_) == 0)
{
lean_object* v___x_3466_; 
v___x_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3466_, 0, v_b_3464_);
return v___x_3466_;
}
else
{
lean_object* v_head_3467_; lean_object* v_tail_3468_; lean_object* v_config_3469_; lean_object* v_extensions_3470_; lean_object* v_extra_3471_; lean_object* v_extraInj_3472_; lean_object* v_extraFacts_3473_; lean_object* v_symPrios_3474_; lean_object* v_norm_3475_; lean_object* v_normProcs_3476_; lean_object* v_anchorRefs_x3f_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3486_; 
v_head_3467_ = lean_ctor_get(v_as_x27_3463_, 0);
v_tail_3468_ = lean_ctor_get(v_as_x27_3463_, 1);
v_config_3469_ = lean_ctor_get(v_b_3464_, 0);
v_extensions_3470_ = lean_ctor_get(v_b_3464_, 1);
v_extra_3471_ = lean_ctor_get(v_b_3464_, 2);
v_extraInj_3472_ = lean_ctor_get(v_b_3464_, 3);
v_extraFacts_3473_ = lean_ctor_get(v_b_3464_, 4);
v_symPrios_3474_ = lean_ctor_get(v_b_3464_, 5);
v_norm_3475_ = lean_ctor_get(v_b_3464_, 6);
v_normProcs_3476_ = lean_ctor_get(v_b_3464_, 7);
v_anchorRefs_x3f_3477_ = lean_ctor_get(v_b_3464_, 8);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_b_3464_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3479_ = v_b_3464_;
v_isShared_3480_ = v_isSharedCheck_3486_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_anchorRefs_x3f_3477_);
lean_inc(v_normProcs_3476_);
lean_inc(v_norm_3475_);
lean_inc(v_symPrios_3474_);
lean_inc(v_extraFacts_3473_);
lean_inc(v_extraInj_3472_);
lean_inc(v_extra_3471_);
lean_inc(v_extensions_3470_);
lean_inc(v_config_3469_);
lean_dec(v_b_3464_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3486_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3481_; lean_object* v___x_3483_; 
lean_inc(v_head_3467_);
v___x_3481_ = l_Lean_PersistentArray_push___redArg(v_extra_3471_, v_head_3467_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 2, v___x_3481_);
v___x_3483_ = v___x_3479_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_config_3469_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_extensions_3470_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v___x_3481_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_extraInj_3472_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v_extraFacts_3473_);
lean_ctor_set(v_reuseFailAlloc_3485_, 5, v_symPrios_3474_);
lean_ctor_set(v_reuseFailAlloc_3485_, 6, v_norm_3475_);
lean_ctor_set(v_reuseFailAlloc_3485_, 7, v_normProcs_3476_);
lean_ctor_set(v_reuseFailAlloc_3485_, 8, v_anchorRefs_x3f_3477_);
v___x_3483_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
v_as_x27_3463_ = v_tail_3468_;
v_b_3464_ = v___x_3483_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3487_, lean_object* v_b_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3487_, v_b_3488_);
lean_dec(v_as_x27_3487_);
return v_res_3490_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3493_ = l_Lean_stringToMessageData(v___x_3492_);
return v___x_3493_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3496_ = l_Lean_stringToMessageData(v___x_3495_);
return v___x_3496_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3499_ = l_Lean_stringToMessageData(v___x_3498_);
return v___x_3499_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3502_ = l_Lean_stringToMessageData(v___x_3501_);
return v___x_3502_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3505_ = l_Lean_stringToMessageData(v___x_3504_);
return v___x_3505_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3508_ = l_Lean_stringToMessageData(v___x_3507_);
return v___x_3508_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3511_ = l_Lean_stringToMessageData(v___x_3510_);
return v___x_3511_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3514_ = l_Lean_stringToMessageData(v___x_3513_);
return v___x_3514_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3517_ = l_Lean_stringToMessageData(v___x_3516_);
return v___x_3517_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3520_ = l_Lean_stringToMessageData(v___x_3519_);
return v___x_3520_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3523_ = l_Lean_stringToMessageData(v___x_3522_);
return v___x_3523_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__22));
v___x_3526_ = l_Lean_stringToMessageData(v___x_3525_);
return v___x_3526_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__24));
v___x_3529_ = l_Lean_stringToMessageData(v___x_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3530_, lean_object* v_p_3531_, lean_object* v_mod_x3f_3532_, lean_object* v_id_3533_, uint8_t v_minIndexable_3534_, uint8_t v_only_3535_, uint8_t v_incremental_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v___y_3545_; uint8_t v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; uint8_t v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v_a_3697_; lean_object* v___y_3920_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = lean_box(0);
lean_inc(v_id_3533_);
v___x_3932_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3533_, v___x_3931_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_a_3933_);
lean_dec_ref_known(v___x_3932_, 1);
v_a_3697_ = v_a_3933_;
goto v___jp_3696_;
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_4009_; 
v_a_3934_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3936_ = v___x_3932_;
v_isShared_3937_ = v_isSharedCheck_4009_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3932_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_4009_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3938_; uint8_t v___y_3940_; uint8_t v___x_4007_; 
v___x_3938_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4007_ = l_Lean_Exception_isInterrupt(v_a_3934_);
if (v___x_4007_ == 0)
{
uint8_t v___x_4008_; 
lean_inc(v_a_3934_);
v___x_4008_ = l_Lean_Exception_isRuntime(v_a_3934_);
v___y_3940_ = v___x_4008_;
goto v___jp_3939_;
}
else
{
v___y_3940_ = v___x_4007_;
goto v___jp_3939_;
}
v___jp_3939_:
{
if (v___y_3940_ == 0)
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
lean_del_object(v___x_3936_);
v___x_3941_ = l_Lean_TSyntax_getId(v_id_3533_);
lean_inc(v___x_3941_);
v___x_3942_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_3941_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
if (lean_obj_tag(v_a_3943_) == 0)
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_3941_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3973_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3947_ = v___x_3944_;
v_isShared_3948_ = v_isSharedCheck_3973_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3944_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3973_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
if (lean_obj_tag(v_a_3945_) == 1)
{
lean_del_object(v___x_3947_);
lean_dec(v_a_3934_);
if (lean_obj_tag(v_mod_x3f_3532_) == 1)
{
lean_object* v_val_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec_ref_known(v_a_3945_, 1);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_val_3949_ = lean_ctor_get(v_mod_x3f_3532_, 0);
lean_inc(v_val_3949_);
lean_dec_ref_known(v_mod_x3f_3532_, 1);
v___x_3950_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_3951_ = l_Lean_MessageData_ofName(v___x_3941_);
v___x_3952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3950_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_3954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3952_);
lean_ctor_set(v___x_3954_, 1, v___x_3953_);
v___x_3955_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_3949_, v___x_3954_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_val_3949_);
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3955_);
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
else
{
lean_object* v_val_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
lean_dec(v___x_3941_);
v_val_3964_ = lean_ctor_get(v_a_3945_, 0);
lean_inc(v_val_3964_);
lean_dec_ref_known(v_a_3945_, 1);
v___x_3965_ = lean_box(0);
lean_inc_ref(v_params_3530_);
v___x_3966_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3530_, v_val_3964_, v___x_3938_, v___x_3965_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_val_3964_);
v___y_3920_ = v___x_3966_;
goto v___jp_3919_;
}
}
else
{
lean_object* v___x_3967_; uint8_t v___x_3968_; 
lean_dec(v_a_3945_);
v___x_3967_ = l_Lean_Name_getPrefix(v___x_3941_);
lean_dec(v___x_3941_);
v___x_3968_ = l_Lean_Name_isAnonymous(v___x_3967_);
lean_dec(v___x_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
lean_del_object(v___x_3947_);
lean_dec(v_a_3934_);
v___x_3969_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3530_, v_p_3531_, v_mod_x3f_3532_, v_id_3533_, v_minIndexable_3534_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
return v___x_3969_;
}
else
{
lean_object* v___x_3971_; 
lean_dec(v_id_3533_);
lean_dec(v_mod_x3f_3532_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set_tag(v___x_3947_, 1);
lean_ctor_set(v___x_3947_, 0, v_a_3934_);
v___x_3971_ = v___x_3947_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3934_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_dec(v___x_3941_);
lean_dec(v_a_3934_);
lean_dec(v_id_3533_);
lean_dec(v_mod_x3f_3532_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3974_ = lean_ctor_get(v___x_3944_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3944_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3944_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec_ref_known(v_a_3943_, 1);
lean_dec(v___x_3941_);
lean_dec(v_a_3934_);
lean_dec(v_mod_x3f_3532_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v___x_3982_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__23);
lean_inc(v_id_3533_);
v___x_3983_ = l_Lean_MessageData_ofSyntax(v_id_3533_);
v___x_3984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3982_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
v___x_3985_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__25);
v___x_3986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3984_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
v___x_3987_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3533_, v___x_3986_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_id_3533_);
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3987_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3987_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec(v___x_3941_);
lean_dec(v_a_3934_);
lean_dec(v_id_3533_);
lean_dec(v_mod_x3f_3532_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3996_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3942_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3942_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
else
{
lean_object* v___x_4005_; 
lean_dec(v_id_3533_);
lean_dec(v_mod_x3f_3532_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
if (v_isShared_3937_ == 0)
{
v___x_4005_ = v___x_3936_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_3934_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
}
v___jp_3544_:
{
uint8_t v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = 0;
lean_inc(v___y_3545_);
v___x_3554_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3545_, v___x_3553_, v___y_3551_, v___y_3552_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3554_, 1);
if (lean_obj_tag(v_a_3555_) == 1)
{
lean_object* v_val_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_dec(v___y_3545_);
v_val_3556_ = lean_ctor_get(v_a_3555_, 0);
lean_inc_n(v_val_3556_, 2);
lean_dec_ref_known(v_a_3555_, 1);
v___x_3557_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3530_, v_val_3556_, v___x_3553_);
v___x_3558_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3556_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3569_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3569_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3569_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
if (lean_obj_tag(v_a_3559_) == 1)
{
lean_object* v_val_3563_; lean_object* v_ctors_3564_; lean_object* v___x_3565_; 
lean_del_object(v___x_3561_);
v_val_3563_ = lean_ctor_get(v_a_3559_, 0);
lean_inc(v_val_3563_);
lean_dec_ref_known(v_a_3559_, 1);
v_ctors_3564_ = lean_ctor_get(v_val_3563_, 4);
lean_inc(v_ctors_3564_);
lean_dec(v_val_3563_);
v___x_3565_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3531_, v_id_3533_, v_minIndexable_3534_, v_ctors_3564_, v___x_3557_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v_ctors_3564_);
lean_dec(v_p_3531_);
return v___x_3565_;
}
else
{
lean_object* v___x_3567_; 
lean_dec(v_a_3559_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3557_);
v___x_3567_ = v___x_3561_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3557_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec_ref(v___x_3557_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
v_a_3570_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3558_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3558_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
else
{
lean_object* v_toCold_3578_; lean_object* v_currRecDepth_3579_; lean_object* v_ref_3580_; uint8_t v_diag_3581_; uint8_t v_suppressElabErrors_3582_; lean_object* v___x_3583_; lean_object* v_ref_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_dec(v_a_3555_);
v_toCold_3578_ = lean_ctor_get(v___y_3551_, 0);
v_currRecDepth_3579_ = lean_ctor_get(v___y_3551_, 1);
v_ref_3580_ = lean_ctor_get(v___y_3551_, 2);
v_diag_3581_ = lean_ctor_get_uint8(v___y_3551_, sizeof(void*)*3);
v_suppressElabErrors_3582_ = lean_ctor_get_uint8(v___y_3551_, sizeof(void*)*3 + 1);
v___x_3583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_3584_ = l_Lean_replaceRef(v_p_3531_, v_ref_3580_);
lean_dec(v_p_3531_);
lean_inc(v_currRecDepth_3579_);
lean_inc_ref(v_toCold_3578_);
v___x_3585_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3585_, 0, v_toCold_3578_);
lean_ctor_set(v___x_3585_, 1, v_currRecDepth_3579_);
lean_ctor_set(v___x_3585_, 2, v_ref_3584_);
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*3, v_diag_3581_);
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*3 + 1, v_suppressElabErrors_3582_);
v___x_3586_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3530_, v_id_3533_, v___y_3545_, v___x_3583_, v_minIndexable_3534_, v___y_3546_, v___y_3546_, v___y_3549_, v___y_3550_, v___x_3585_, v___y_3552_);
lean_dec_ref_known(v___x_3585_, 3);
return v___x_3586_;
}
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec(v___y_3545_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3587_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3554_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3554_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
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
v___jp_3595_:
{
lean_object* v___x_3604_; 
v___x_3604_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3534_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
lean_dec_ref_known(v___x_3604_, 1);
v___x_3605_ = l_Lean_Meta_Grind_grindExt;
v___x_3606_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3605_, v___y_3603_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
lean_inc(v___y_3596_);
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___y_3596_);
v___x_3609_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3607_, v___x_3608_);
lean_dec_ref_known(v___x_3608_, 1);
lean_dec(v_a_3607_);
v___x_3610_ = lean_box(0);
v___x_3611_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3597_, v___x_3609_, v___x_3610_);
lean_dec(v___y_3597_);
v___x_3612_ = l_List_isEmpty___redArg(v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; 
lean_dec(v___y_3596_);
lean_dec(v_p_3531_);
v___x_3613_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3611_, v_params_3530_);
lean_dec(v___x_3611_);
return v___x_3613_;
}
else
{
lean_object* v___x_3614_; uint8_t v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v___x_3611_);
lean_dec_ref(v_params_3530_);
v___x_3614_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3615_ = 0;
v___x_3616_ = l_Lean_MessageData_ofConstName(v___y_3596_, v___x_3615_);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3614_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3531_, v___x_3619_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
lean_dec(v_p_3531_);
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3620_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3620_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_dec(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3629_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3606_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3606_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3637_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3604_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3604_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
v___jp_3645_:
{
lean_object* v___x_3652_; 
v___x_3652_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3534_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_toCold_3653_; lean_object* v_currRecDepth_3654_; lean_object* v_ref_3655_; uint8_t v_diag_3656_; uint8_t v_suppressElabErrors_3657_; lean_object* v_ref_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_dec_ref_known(v___x_3652_, 1);
v_toCold_3653_ = lean_ctor_get(v___y_3650_, 0);
v_currRecDepth_3654_ = lean_ctor_get(v___y_3650_, 1);
v_ref_3655_ = lean_ctor_get(v___y_3650_, 2);
v_diag_3656_ = lean_ctor_get_uint8(v___y_3650_, sizeof(void*)*3);
v_suppressElabErrors_3657_ = lean_ctor_get_uint8(v___y_3650_, sizeof(void*)*3 + 1);
v_ref_3658_ = l_Lean_replaceRef(v_p_3531_, v_ref_3655_);
lean_dec(v_p_3531_);
lean_inc(v_currRecDepth_3654_);
lean_inc_ref(v_toCold_3653_);
v___x_3659_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3659_, 0, v_toCold_3653_);
lean_ctor_set(v___x_3659_, 1, v_currRecDepth_3654_);
lean_ctor_set(v___x_3659_, 2, v_ref_3658_);
lean_ctor_set_uint8(v___x_3659_, sizeof(void*)*3, v_diag_3656_);
lean_ctor_set_uint8(v___x_3659_, sizeof(void*)*3 + 1, v_suppressElabErrors_3657_);
lean_inc(v___y_3647_);
v___x_3660_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3647_, v___y_3646_, v___x_3659_, v___y_3651_);
lean_dec_ref_known(v___x_3659_, 3);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3668_; 
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v___x_3660_, 0);
lean_dec(v_unused_3669_);
v___x_3662_ = v___x_3660_;
v_isShared_3663_ = v_isSharedCheck_3668_;
goto v_resetjp_3661_;
}
else
{
lean_dec(v___x_3660_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3668_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
v___x_3664_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3530_, v___y_3647_, v___y_3646_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3664_);
v___x_3666_ = v___x_3662_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec(v___y_3647_);
lean_dec_ref(v_params_3530_);
v_a_3670_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3660_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3660_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_dec(v___y_3647_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3678_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3652_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3652_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
v___jp_3686_:
{
lean_object* v_ctors_3694_; lean_object* v___x_3695_; 
v_ctors_3694_ = lean_ctor_get(v___y_3687_, 4);
lean_inc(v_ctors_3694_);
lean_dec_ref(v___y_3687_);
v___x_3695_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3531_, v_id_3533_, v_minIndexable_3534_, v_ctors_3694_, v_params_3530_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
lean_dec(v_ctors_3694_);
lean_dec(v_p_3531_);
return v___x_3695_;
}
v___jp_3696_:
{
uint8_t v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = 1;
lean_inc(v_a_3697_);
v___x_3699_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_3697_, v___x_3698_, v_a_3537_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_dec_ref_known(v___x_3699_, 1);
if (lean_obj_tag(v_mod_x3f_3532_) == 1)
{
lean_object* v_val_3700_; lean_object* v___x_3701_; 
v_val_3700_ = lean_ctor_get(v_mod_x3f_3532_, 0);
lean_inc(v_val_3700_);
lean_dec_ref_known(v_mod_x3f_3532_, 1);
v___x_3701_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3700_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3902_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3902_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3902_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
switch(lean_obj_tag(v_a_3702_))
{
case 0:
{
lean_object* v_k_3706_; 
lean_del_object(v___x_3704_);
v_k_3706_ = lean_ctor_get(v_a_3702_, 0);
lean_inc(v_k_3706_);
lean_dec_ref_known(v_a_3702_, 1);
if (lean_obj_tag(v_k_3706_) == 9)
{
lean_dec(v_id_3533_);
if (v_only_3535_ == 0)
{
lean_object* v_toCold_3707_; lean_object* v_currRecDepth_3708_; lean_object* v_ref_3709_; uint8_t v_diag_3710_; uint8_t v_suppressElabErrors_3711_; lean_object* v_ref_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v_toCold_3707_ = lean_ctor_get(v_a_3541_, 0);
v_currRecDepth_3708_ = lean_ctor_get(v_a_3541_, 1);
v_ref_3709_ = lean_ctor_get(v_a_3541_, 2);
v_diag_3710_ = lean_ctor_get_uint8(v_a_3541_, sizeof(void*)*3);
v_suppressElabErrors_3711_ = lean_ctor_get_uint8(v_a_3541_, sizeof(void*)*3 + 1);
v_ref_3712_ = l_Lean_replaceRef(v_p_3531_, v_ref_3709_);
lean_inc(v_currRecDepth_3708_);
lean_inc_ref(v_toCold_3707_);
v___x_3713_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3713_, 0, v_toCold_3707_);
lean_ctor_set(v___x_3713_, 1, v_currRecDepth_3708_);
lean_ctor_set(v___x_3713_, 2, v_ref_3712_);
lean_ctor_set_uint8(v___x_3713_, sizeof(void*)*3, v_diag_3710_);
lean_ctor_set_uint8(v___x_3713_, sizeof(void*)*3 + 1, v_suppressElabErrors_3711_);
v___x_3714_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3713_, v_a_3542_);
lean_dec_ref_known(v___x_3713_, 3);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_dec_ref_known(v___x_3714_, 1);
v___y_3596_ = v_a_3697_;
v___y_3597_ = v_k_3706_;
v___y_3598_ = v_a_3537_;
v___y_3599_ = v_a_3538_;
v___y_3600_ = v_a_3539_;
v___y_3601_ = v_a_3540_;
v___y_3602_ = v_a_3541_;
v___y_3603_ = v_a_3542_;
goto v___jp_3595_;
}
else
{
lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec(v_a_3697_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3714_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3714_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
else
{
v___y_3596_ = v_a_3697_;
v___y_3597_ = v_k_3706_;
v___y_3598_ = v_a_3537_;
v___y_3599_ = v_a_3538_;
v___y_3600_ = v_a_3539_;
v___y_3601_ = v_a_3540_;
v___y_3602_ = v_a_3541_;
v___y_3603_ = v_a_3542_;
goto v___jp_3595_;
}
}
else
{
lean_object* v_toCold_3723_; lean_object* v_currRecDepth_3724_; lean_object* v_ref_3725_; uint8_t v_diag_3726_; uint8_t v_suppressElabErrors_3727_; uint8_t v___x_3728_; lean_object* v_ref_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_toCold_3723_ = lean_ctor_get(v_a_3541_, 0);
v_currRecDepth_3724_ = lean_ctor_get(v_a_3541_, 1);
v_ref_3725_ = lean_ctor_get(v_a_3541_, 2);
v_diag_3726_ = lean_ctor_get_uint8(v_a_3541_, sizeof(void*)*3);
v_suppressElabErrors_3727_ = lean_ctor_get_uint8(v_a_3541_, sizeof(void*)*3 + 1);
v___x_3728_ = 0;
v_ref_3729_ = l_Lean_replaceRef(v_p_3531_, v_ref_3725_);
lean_dec(v_p_3531_);
lean_inc(v_currRecDepth_3724_);
lean_inc_ref(v_toCold_3723_);
v___x_3730_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3730_, 0, v_toCold_3723_);
lean_ctor_set(v___x_3730_, 1, v_currRecDepth_3724_);
lean_ctor_set(v___x_3730_, 2, v_ref_3729_);
lean_ctor_set_uint8(v___x_3730_, sizeof(void*)*3, v_diag_3726_);
lean_ctor_set_uint8(v___x_3730_, sizeof(void*)*3 + 1, v_suppressElabErrors_3727_);
v___x_3731_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3530_, v_id_3533_, v_a_3697_, v_k_3706_, v_minIndexable_3534_, v___x_3728_, v___x_3698_, v_a_3539_, v_a_3540_, v___x_3730_, v_a_3542_);
lean_dec_ref_known(v___x_3730_, 3);
return v___x_3731_;
}
}
case 1:
{
lean_del_object(v___x_3704_);
lean_dec(v_id_3533_);
if (v_incremental_3536_ == 0)
{
uint8_t v_eager_3732_; 
v_eager_3732_ = lean_ctor_get_uint8(v_a_3702_, 0);
lean_dec_ref_known(v_a_3702_, 0);
v___y_3646_ = v_eager_3732_;
v___y_3647_ = v_a_3697_;
v___y_3648_ = v_a_3539_;
v___y_3649_ = v_a_3540_;
v___y_3650_ = v_a_3541_;
v___y_3651_ = v_a_3542_;
goto v___jp_3645_;
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec_ref_known(v_a_3702_, 0);
lean_dec(v_a_3697_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v___x_3733_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3734_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3733_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
case 2:
{
uint8_t v___x_3743_; lean_object* v___x_3744_; 
lean_del_object(v___x_3704_);
v___x_3743_ = 0;
lean_inc(v_a_3697_);
v___x_3744_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3697_, v___x_3743_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref_known(v___x_3744_, 1);
if (lean_obj_tag(v_a_3745_) == 1)
{
lean_dec(v_a_3697_);
if (v_incremental_3536_ == 0)
{
lean_object* v_val_3746_; 
v_val_3746_ = lean_ctor_get(v_a_3745_, 0);
lean_inc(v_val_3746_);
lean_dec_ref_known(v_a_3745_, 1);
v___y_3687_ = v_val_3746_;
v___y_3688_ = v_a_3537_;
v___y_3689_ = v_a_3538_;
v___y_3690_ = v_a_3539_;
v___y_3691_ = v_a_3540_;
v___y_3692_ = v_a_3541_;
v___y_3693_ = v_a_3542_;
goto v___jp_3686_;
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec_ref_known(v_a_3745_, 1);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v___x_3747_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3748_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3747_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3748_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3748_);
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
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec(v_a_3745_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v___x_3757_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_3758_ = l_Lean_MessageData_ofConstName(v_a_3697_, v___x_3743_);
v___x_3759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_3761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3761_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3762_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3762_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
lean_dec(v_a_3697_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3771_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3773_ = v___x_3744_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3744_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
case 3:
{
lean_del_object(v___x_3704_);
v___y_3545_ = v_a_3697_;
v___y_3546_ = v___x_3698_;
v___y_3547_ = v_a_3537_;
v___y_3548_ = v_a_3538_;
v___y_3549_ = v_a_3539_;
v___y_3550_ = v_a_3540_;
v___y_3551_ = v_a_3541_;
v___y_3552_ = v_a_3542_;
goto v___jp_3544_;
}
case 4:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_del_object(v___x_3704_);
lean_dec(v_a_3697_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v___x_3779_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_3780_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3779_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3780_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3780_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
case 5:
{
lean_object* v_prio_3789_; lean_object* v___x_3790_; 
lean_del_object(v___x_3704_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
v_prio_3789_ = lean_ctor_get(v_a_3702_, 0);
lean_inc(v_prio_3789_);
lean_dec_ref_known(v_a_3702_, 1);
v___x_3790_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3534_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3814_; 
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; 
v_unused_3815_ = lean_ctor_get(v___x_3790_, 0);
lean_dec(v_unused_3815_);
v___x_3792_ = v___x_3790_;
v_isShared_3793_ = v_isSharedCheck_3814_;
goto v_resetjp_3791_;
}
else
{
lean_dec(v___x_3790_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3814_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v_config_3794_; lean_object* v_extensions_3795_; lean_object* v_extra_3796_; lean_object* v_extraInj_3797_; lean_object* v_extraFacts_3798_; lean_object* v_symPrios_3799_; lean_object* v_norm_3800_; lean_object* v_normProcs_3801_; lean_object* v_anchorRefs_x3f_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3813_; 
v_config_3794_ = lean_ctor_get(v_params_3530_, 0);
v_extensions_3795_ = lean_ctor_get(v_params_3530_, 1);
v_extra_3796_ = lean_ctor_get(v_params_3530_, 2);
v_extraInj_3797_ = lean_ctor_get(v_params_3530_, 3);
v_extraFacts_3798_ = lean_ctor_get(v_params_3530_, 4);
v_symPrios_3799_ = lean_ctor_get(v_params_3530_, 5);
v_norm_3800_ = lean_ctor_get(v_params_3530_, 6);
v_normProcs_3801_ = lean_ctor_get(v_params_3530_, 7);
v_anchorRefs_x3f_3802_ = lean_ctor_get(v_params_3530_, 8);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_params_3530_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3804_ = v_params_3530_;
v_isShared_3805_ = v_isSharedCheck_3813_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_anchorRefs_x3f_3802_);
lean_inc(v_normProcs_3801_);
lean_inc(v_norm_3800_);
lean_inc(v_symPrios_3799_);
lean_inc(v_extraFacts_3798_);
lean_inc(v_extraInj_3797_);
lean_inc(v_extra_3796_);
lean_inc(v_extensions_3795_);
lean_inc(v_config_3794_);
lean_dec(v_params_3530_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3813_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; lean_object* v___x_3808_; 
v___x_3806_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_3799_, v_a_3697_, v_prio_3789_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 5, v___x_3806_);
v___x_3808_ = v___x_3804_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_config_3794_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_extensions_3795_);
lean_ctor_set(v_reuseFailAlloc_3812_, 2, v_extra_3796_);
lean_ctor_set(v_reuseFailAlloc_3812_, 3, v_extraInj_3797_);
lean_ctor_set(v_reuseFailAlloc_3812_, 4, v_extraFacts_3798_);
lean_ctor_set(v_reuseFailAlloc_3812_, 5, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3812_, 6, v_norm_3800_);
lean_ctor_set(v_reuseFailAlloc_3812_, 7, v_normProcs_3801_);
lean_ctor_set(v_reuseFailAlloc_3812_, 8, v_anchorRefs_x3f_3802_);
v___x_3808_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
lean_object* v___x_3810_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3808_);
v___x_3810_ = v___x_3792_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec(v_prio_3789_);
lean_dec(v_a_3697_);
lean_dec_ref(v_params_3530_);
v_a_3816_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3790_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3790_);
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
case 6:
{
lean_object* v___x_3824_; 
lean_del_object(v___x_3704_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
v___x_3824_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3697_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3849_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3849_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3849_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v_config_3829_; lean_object* v_extensions_3830_; lean_object* v_extra_3831_; lean_object* v_extraInj_3832_; lean_object* v_extraFacts_3833_; lean_object* v_symPrios_3834_; lean_object* v_norm_3835_; lean_object* v_normProcs_3836_; lean_object* v_anchorRefs_x3f_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3848_; 
v_config_3829_ = lean_ctor_get(v_params_3530_, 0);
v_extensions_3830_ = lean_ctor_get(v_params_3530_, 1);
v_extra_3831_ = lean_ctor_get(v_params_3530_, 2);
v_extraInj_3832_ = lean_ctor_get(v_params_3530_, 3);
v_extraFacts_3833_ = lean_ctor_get(v_params_3530_, 4);
v_symPrios_3834_ = lean_ctor_get(v_params_3530_, 5);
v_norm_3835_ = lean_ctor_get(v_params_3530_, 6);
v_normProcs_3836_ = lean_ctor_get(v_params_3530_, 7);
v_anchorRefs_x3f_3837_ = lean_ctor_get(v_params_3530_, 8);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_params_3530_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3839_ = v_params_3530_;
v_isShared_3840_ = v_isSharedCheck_3848_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_anchorRefs_x3f_3837_);
lean_inc(v_normProcs_3836_);
lean_inc(v_norm_3835_);
lean_inc(v_symPrios_3834_);
lean_inc(v_extraFacts_3833_);
lean_inc(v_extraInj_3832_);
lean_inc(v_extra_3831_);
lean_inc(v_extensions_3830_);
lean_inc(v_config_3829_);
lean_dec(v_params_3530_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3848_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3841_; lean_object* v___x_3843_; 
v___x_3841_ = l_Lean_PersistentArray_push___redArg(v_extraInj_3832_, v_a_3825_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 3, v___x_3841_);
v___x_3843_ = v___x_3839_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_config_3829_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_extensions_3830_);
lean_ctor_set(v_reuseFailAlloc_3847_, 2, v_extra_3831_);
lean_ctor_set(v_reuseFailAlloc_3847_, 3, v___x_3841_);
lean_ctor_set(v_reuseFailAlloc_3847_, 4, v_extraFacts_3833_);
lean_ctor_set(v_reuseFailAlloc_3847_, 5, v_symPrios_3834_);
lean_ctor_set(v_reuseFailAlloc_3847_, 6, v_norm_3835_);
lean_ctor_set(v_reuseFailAlloc_3847_, 7, v_normProcs_3836_);
lean_ctor_set(v_reuseFailAlloc_3847_, 8, v_anchorRefs_x3f_3837_);
v___x_3843_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
lean_object* v___x_3845_; 
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3843_);
v___x_3845_ = v___x_3827_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref(v_params_3530_);
v_a_3850_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3824_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3824_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
case 7:
{
lean_object* v___x_3858_; lean_object* v___x_3860_; 
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
v___x_3858_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3530_, v_a_3697_);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3858_);
v___x_3860_ = v___x_3704_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3858_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
case 8:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec_ref_known(v_a_3702_, 0);
lean_del_object(v___x_3704_);
lean_dec(v_a_3697_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v___x_3862_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_3863_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3862_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3863_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
case 9:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_del_object(v___x_3704_);
lean_dec(v_a_3697_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v___x_3872_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_3873_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3872_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3873_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
case 10:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_del_object(v___x_3704_);
lean_dec(v_a_3697_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v___x_3882_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_3883_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3882_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3883_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3883_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
default: 
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
lean_del_object(v___x_3704_);
lean_dec(v_a_3697_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v___x_3892_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
v___x_3893_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3892_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec(v_a_3697_);
lean_dec(v_id_3533_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3903_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3701_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3701_);
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
else
{
lean_dec(v_mod_x3f_3532_);
v___y_3545_ = v_a_3697_;
v___y_3546_ = v___x_3698_;
v___y_3547_ = v_a_3537_;
v___y_3548_ = v_a_3538_;
v___y_3549_ = v_a_3539_;
v___y_3550_ = v_a_3540_;
v___y_3551_ = v_a_3541_;
v___y_3552_ = v_a_3542_;
goto v___jp_3544_;
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
lean_dec(v_a_3697_);
lean_dec(v_id_3533_);
lean_dec(v_mod_x3f_3532_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3911_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3699_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3699_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
v___jp_3919_:
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3930_; 
v_a_3921_ = lean_ctor_get(v___y_3920_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___y_3920_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3923_ = v___y_3920_;
v_isShared_3924_ = v_isSharedCheck_3930_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___y_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3930_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
if (lean_obj_tag(v_a_3921_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3927_; 
lean_dec(v_id_3533_);
lean_dec(v_mod_x3f_3532_);
lean_dec(v_p_3531_);
lean_dec_ref(v_params_3530_);
v_a_3925_ = lean_ctor_get(v_a_3921_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v_a_3921_, 1);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 0, v_a_3925_);
v___x_3927_ = v___x_3923_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
else
{
lean_object* v_a_3929_; 
lean_del_object(v___x_3923_);
v_a_3929_ = lean_ctor_get(v_a_3921_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v_a_3921_, 1);
v_a_3697_ = v_a_3929_;
goto v___jp_3696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4010_, lean_object* v_p_4011_, lean_object* v_mod_x3f_4012_, lean_object* v_id_4013_, lean_object* v_minIndexable_4014_, lean_object* v_only_4015_, lean_object* v_incremental_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_){
_start:
{
uint8_t v_minIndexable_boxed_4024_; uint8_t v_only_boxed_4025_; uint8_t v_incremental_boxed_4026_; lean_object* v_res_4027_; 
v_minIndexable_boxed_4024_ = lean_unbox(v_minIndexable_4014_);
v_only_boxed_4025_ = lean_unbox(v_only_4015_);
v_incremental_boxed_4026_ = lean_unbox(v_incremental_4016_);
v_res_4027_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4010_, v_p_4011_, v_mod_x3f_4012_, v_id_4013_, v_minIndexable_boxed_4024_, v_only_boxed_4025_, v_incremental_boxed_4026_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4028_, lean_object* v_id_4029_, uint8_t v_minIndexable_4030_, lean_object* v_as_4031_, lean_object* v_as_x27_4032_, lean_object* v_b_4033_, lean_object* v_a_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4028_, v_id_4029_, v_minIndexable_4030_, v_as_x27_4032_, v_b_4033_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4043_, lean_object* v_id_4044_, lean_object* v_minIndexable_4045_, lean_object* v_as_4046_, lean_object* v_as_x27_4047_, lean_object* v_b_4048_, lean_object* v_a_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
uint8_t v_minIndexable_boxed_4057_; lean_object* v_res_4058_; 
v_minIndexable_boxed_4057_ = lean_unbox(v_minIndexable_4045_);
v_res_4058_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4043_, v_id_4044_, v_minIndexable_boxed_4057_, v_as_4046_, v_as_x27_4047_, v_b_4048_, v_a_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v_as_x27_4047_);
lean_dec(v_as_4046_);
lean_dec(v_p_4043_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4059_, lean_object* v_as_x27_4060_, lean_object* v_b_4061_, lean_object* v_a_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4060_, v_b_4061_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4071_, lean_object* v_as_x27_4072_, lean_object* v_b_4073_, lean_object* v_a_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4071_, v_as_x27_4072_, v_b_4073_, v_a_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v_as_x27_4072_);
lean_dec(v_as_4071_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4083_, lean_object* v_ref_4084_, lean_object* v_msg_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4084_, v_msg_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4094_, lean_object* v_ref_4095_, lean_object* v_msg_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4094_, v_ref_4095_, v_msg_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v_ref_4095_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4105_, lean_object* v_id_4106_, uint8_t v_minIndexable_4107_, lean_object* v_as_4108_, lean_object* v_as_x27_4109_, lean_object* v_b_4110_, lean_object* v_a_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4105_, v_id_4106_, v_minIndexable_4107_, v_as_x27_4109_, v_b_4110_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4120_, lean_object* v_id_4121_, lean_object* v_minIndexable_4122_, lean_object* v_as_4123_, lean_object* v_as_x27_4124_, lean_object* v_b_4125_, lean_object* v_a_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
uint8_t v_minIndexable_boxed_4134_; lean_object* v_res_4135_; 
v_minIndexable_boxed_4134_ = lean_unbox(v_minIndexable_4122_);
v_res_4135_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4120_, v_id_4121_, v_minIndexable_boxed_4134_, v_as_4123_, v_as_x27_4124_, v_b_4125_, v_a_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v_as_x27_4124_);
lean_dec(v_as_4123_);
lean_dec(v_p_4120_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4136_, lean_object* v_t_4137_, lean_object* v_k_4138_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4137_, v_k_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4140_, lean_object* v_t_4141_, lean_object* v_k_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4140_, v_t_4141_, v_k_4142_);
lean_dec(v_k_4142_);
lean_dec(v_t_4141_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4144_, uint8_t v_skipAuxDecl_4145_, lean_object* v_auxDeclToFullName_4146_, lean_object* v___x_4147_, lean_object* v_givenNameView_4148_, lean_object* v_as_4149_, lean_object* v_i_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v___x_4152_; 
v___x_4152_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4144_, v_skipAuxDecl_4145_, v_auxDeclToFullName_4146_, v___x_4147_, v_givenNameView_4148_, v_as_4149_, v_i_4150_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4153_, lean_object* v_skipAuxDecl_4154_, lean_object* v_auxDeclToFullName_4155_, lean_object* v___x_4156_, lean_object* v_givenNameView_4157_, lean_object* v_as_4158_, lean_object* v_i_4159_, lean_object* v_a_4160_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4161_; lean_object* v_res_4162_; 
v_skipAuxDecl_boxed_4161_ = lean_unbox(v_skipAuxDecl_4154_);
v_res_4162_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4153_, v_skipAuxDecl_boxed_4161_, v_auxDeclToFullName_4155_, v___x_4156_, v_givenNameView_4157_, v_as_4158_, v_i_4159_, v_a_4160_);
lean_dec_ref(v_as_4158_);
lean_dec(v_auxDeclToFullName_4155_);
lean_dec(v_givenName_4153_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4163_, lean_object* v_givenName_4164_, lean_object* v_as_4165_, lean_object* v_i_4166_, lean_object* v_a_4167_){
_start:
{
lean_object* v___x_4168_; 
v___x_4168_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4163_, v_givenName_4164_, v_as_4165_, v_i_4166_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4169_, lean_object* v_givenName_4170_, lean_object* v_as_4171_, lean_object* v_i_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4169_, v_givenName_4170_, v_as_4171_, v_i_4172_, v_a_4173_);
lean_dec_ref(v_as_4171_);
lean_dec(v_givenName_4170_);
lean_dec(v_localDecl_x3f_4169_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4175_, uint8_t v_skipAuxDecl_4176_, lean_object* v_auxDeclToFullName_4177_, lean_object* v___x_4178_, lean_object* v_givenNameView_4179_, lean_object* v_as_4180_, lean_object* v_i_4181_, lean_object* v_a_4182_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4175_, v_skipAuxDecl_4176_, v_auxDeclToFullName_4177_, v___x_4178_, v_givenNameView_4179_, v_as_4180_, v_i_4181_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4184_, lean_object* v_skipAuxDecl_4185_, lean_object* v_auxDeclToFullName_4186_, lean_object* v___x_4187_, lean_object* v_givenNameView_4188_, lean_object* v_as_4189_, lean_object* v_i_4190_, lean_object* v_a_4191_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4192_; lean_object* v_res_4193_; 
v_skipAuxDecl_boxed_4192_ = lean_unbox(v_skipAuxDecl_4185_);
v_res_4193_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4184_, v_skipAuxDecl_boxed_4192_, v_auxDeclToFullName_4186_, v___x_4187_, v_givenNameView_4188_, v_as_4189_, v_i_4190_, v_a_4191_);
lean_dec_ref(v_as_4189_);
lean_dec(v_auxDeclToFullName_4186_);
lean_dec(v_givenName_4184_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4194_, lean_object* v_givenName_4195_, lean_object* v_as_4196_, lean_object* v_i_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4194_, v_givenName_4195_, v_as_4196_, v_i_4197_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4200_, lean_object* v_givenName_4201_, lean_object* v_as_4202_, lean_object* v_i_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4200_, v_givenName_4201_, v_as_4202_, v_i_4203_, v_a_4204_);
lean_dec_ref(v_as_4202_);
lean_dec(v_givenName_4201_);
lean_dec(v_localDecl_x3f_4200_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4206_, v___y_4211_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec_ref(v_opt_4215_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4224_, lean_object* v_msgData_4225_, uint8_t v_severity_4226_, uint8_t v_isSilent_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4224_, v_msgData_4225_, v_severity_4226_, v_isSilent_4227_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4236_, lean_object* v_msgData_4237_, lean_object* v_severity_4238_, lean_object* v_isSilent_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
uint8_t v_severity_boxed_4247_; uint8_t v_isSilent_boxed_4248_; lean_object* v_res_4249_; 
v_severity_boxed_4247_ = lean_unbox(v_severity_4238_);
v_isSilent_boxed_4248_ = lean_unbox(v_isSilent_4239_);
v_res_4249_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4236_, v_msgData_4237_, v_severity_boxed_4247_, v_isSilent_boxed_4248_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v_ref_4236_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4250_, uint8_t v___x_4251_, lean_object* v_b_4252_, lean_object* v_____r_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4261_ = lean_box(0);
v___x_4262_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4250_, v___x_4261_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4264_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc_n(v_a_4263_, 2);
lean_dec_ref_known(v___x_4262_, 1);
v___x_4264_ = l_Lean_Elab_Term_checkDeprecatedCore___redArg(v_a_4263_, v___x_4251_, v___y_4254_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4264_) == 0)
{
uint8_t v___x_4265_; lean_object* v___x_4266_; 
lean_dec_ref_known(v___x_4264_, 1);
v___x_4265_ = 0;
lean_inc(v_a_4263_);
v___x_4266_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4263_, v___x_4265_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4326_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4269_ = v___x_4266_;
v_isShared_4270_ = v_isSharedCheck_4326_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4266_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4326_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
if (lean_obj_tag(v_a_4267_) == 1)
{
lean_object* v_val_4271_; lean_object* v___x_4272_; 
lean_del_object(v___x_4269_);
lean_dec(v_a_4263_);
v_val_4271_ = lean_ctor_get(v_a_4267_, 0);
lean_inc_n(v_val_4271_, 2);
lean_dec_ref_known(v_a_4267_, 1);
v___x_4272_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4271_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v___x_4273_; 
lean_dec_ref_known(v___x_4272_, 1);
v___x_4273_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4252_, v_val_4271_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4283_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4276_ = v___x_4273_;
v_isShared_4277_ = v_isSharedCheck_4283_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4273_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4283_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4281_; 
v___x_4278_ = lean_box(0);
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
lean_ctor_set(v___x_4279_, 1, v_a_4274_);
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 0, v___x_4279_);
v___x_4281_ = v___x_4276_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4279_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
v_a_4284_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4273_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4273_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec(v_val_4271_);
lean_dec_ref(v_b_4252_);
v_a_4292_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4272_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4272_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
else
{
uint8_t v___x_4300_; 
lean_dec(v_a_4267_);
lean_inc(v_a_4263_);
v___x_4300_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4252_, v_a_4263_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; 
lean_del_object(v___x_4269_);
v___x_4301_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4252_, v_a_4263_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4311_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4304_ = v___x_4301_;
v_isShared_4305_ = v_isSharedCheck_4311_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4301_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4311_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4309_; 
v___x_4306_ = lean_box(0);
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
lean_ctor_set(v___x_4307_, 1, v_a_4302_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4307_);
v___x_4309_ = v___x_4304_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4307_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
v_a_4312_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4301_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4301_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
else
{
lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4324_; 
v___x_4320_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4252_, v_a_4263_);
v___x_4321_ = lean_box(0);
v___x_4322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4321_);
lean_ctor_set(v___x_4322_, 1, v___x_4320_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v___x_4322_);
v___x_4324_ = v___x_4269_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4322_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_dec(v_a_4263_);
lean_dec_ref(v_b_4252_);
v_a_4327_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4266_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4266_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec(v_a_4263_);
lean_dec_ref(v_b_4252_);
v_a_4335_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4264_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4264_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec_ref(v_b_4252_);
v_a_4343_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4262_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4262_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4351_, lean_object* v___x_4352_, lean_object* v_b_4353_, lean_object* v_____r_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
uint8_t v___x_17487__boxed_4362_; lean_object* v_res_4363_; 
v___x_17487__boxed_4362_ = lean_unbox(v___x_4352_);
v_res_4363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4351_, v___x_17487__boxed_4362_, v_b_4353_, v_____r_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4367_, lean_object* v_b_4368_, lean_object* v_a_4369_, uint8_t v___x_4370_, uint8_t v_only_4371_, uint8_t v_incremental_4372_, lean_object* v_x_4373_, lean_object* v_mod_x3f_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4382_ = lean_unsigned_to_nat(1u);
v___x_4383_ = l_Lean_Syntax_getArg(v___x_4367_, v___x_4382_);
if (v___x_4370_ == 0)
{
lean_object* v___x_4444_; uint8_t v___x_4445_; 
v___x_4444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4383_);
v___x_4445_ = l_Lean_Syntax_isOfKind(v___x_4383_, v___x_4444_);
if (v___x_4445_ == 0)
{
lean_object* v___x_4446_; 
v___x_4446_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4368_, v_a_4369_, v_mod_x3f_4374_, v___x_4383_, v___x_4370_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4456_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4449_ = v___x_4446_;
v_isShared_4450_ = v_isSharedCheck_4456_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4446_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4456_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4454_; 
v___x_4451_ = lean_box(0);
v___x_4452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
lean_ctor_set(v___x_4452_, 1, v_a_4447_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 0, v___x_4452_);
v___x_4454_ = v___x_4449_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4452_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
v_a_4457_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4446_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4446_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
else
{
goto v___jp_4404_;
}
}
else
{
goto v___jp_4404_;
}
v___jp_4384_:
{
lean_object* v___x_4385_; 
v___x_4385_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4368_, v_a_4369_, v_mod_x3f_4374_, v___x_4383_, v___x_4370_, v_only_4371_, v_incremental_4372_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4395_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4388_ = v___x_4385_;
v_isShared_4389_ = v_isSharedCheck_4395_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4385_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4395_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; 
v___x_4390_ = lean_box(0);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
lean_ctor_set(v___x_4391_, 1, v_a_4386_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v___x_4391_);
v___x_4393_ = v___x_4388_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
v_a_4396_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4385_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4385_);
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
v___jp_4404_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4405_ = l_Lean_TSyntax_getId(v___x_4383_);
v___x_4406_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4405_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
if (lean_obj_tag(v_a_4407_) == 1)
{
lean_object* v_val_4408_; lean_object* v_snd_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4434_; 
v_val_4408_ = lean_ctor_get(v_a_4407_, 0);
lean_inc(v_val_4408_);
lean_dec_ref_known(v_a_4407_, 1);
v_snd_4409_ = lean_ctor_get(v_val_4408_, 1);
v_isSharedCheck_4434_ = !lean_is_exclusive(v_val_4408_);
if (v_isSharedCheck_4434_ == 0)
{
lean_object* v_unused_4435_; 
v_unused_4435_ = lean_ctor_get(v_val_4408_, 0);
lean_dec(v_unused_4435_);
v___x_4411_ = v_val_4408_;
v_isShared_4412_ = v_isSharedCheck_4434_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_snd_4409_);
lean_dec(v_val_4408_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4434_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
if (lean_obj_tag(v_snd_4409_) == 1)
{
lean_object* v___x_4413_; 
lean_dec_ref_known(v_snd_4409_, 2);
v___x_4413_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4368_, v_a_4369_, v_mod_x3f_4374_, v___x_4383_, v___x_4370_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4425_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4416_ = v___x_4413_;
v_isShared_4417_ = v_isSharedCheck_4425_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4413_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4425_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4418_; lean_object* v___x_4420_; 
v___x_4418_ = lean_box(0);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 1, v_a_4414_);
lean_ctor_set(v___x_4411_, 0, v___x_4418_);
v___x_4420_ = v___x_4411_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4418_);
lean_ctor_set(v_reuseFailAlloc_4424_, 1, v_a_4414_);
v___x_4420_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4422_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4420_);
v___x_4422_ = v___x_4416_;
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
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_del_object(v___x_4411_);
v_a_4426_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4413_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4413_);
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
lean_del_object(v___x_4411_);
lean_dec(v_snd_4409_);
goto v___jp_4384_;
}
}
}
else
{
lean_dec(v_a_4407_);
goto v___jp_4384_;
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec(v___x_4383_);
lean_dec(v_mod_x3f_4374_);
lean_dec(v_a_4369_);
lean_dec_ref(v_b_4368_);
v_a_4436_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4406_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4406_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4465_, lean_object* v_b_4466_, lean_object* v_a_4467_, lean_object* v___x_4468_, lean_object* v_only_4469_, lean_object* v_incremental_4470_, lean_object* v_x_4471_, lean_object* v_mod_x3f_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
uint8_t v___x_17705__boxed_4480_; uint8_t v_only_boxed_4481_; uint8_t v_incremental_boxed_4482_; lean_object* v_res_4483_; 
v___x_17705__boxed_4480_ = lean_unbox(v___x_4468_);
v_only_boxed_4481_ = lean_unbox(v_only_4469_);
v_incremental_boxed_4482_ = lean_unbox(v_incremental_4470_);
v_res_4483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4465_, v_b_4466_, v_a_4467_, v___x_17705__boxed_4480_, v_only_boxed_4481_, v_incremental_boxed_4482_, v_x_4471_, v_mod_x3f_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___x_4465_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4484_, lean_object* v___x_4485_, lean_object* v_____r_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4484_, v___x_4485_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4504_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4497_ = v___x_4494_;
v_isShared_4498_ = v_isSharedCheck_4504_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4494_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4504_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4502_; 
v___x_4499_ = lean_box(0);
v___x_4500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
lean_ctor_set(v___x_4500_, 1, v_a_4495_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v___x_4500_);
v___x_4502_ = v___x_4497_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4500_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
v_a_4505_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4494_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4494_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4513_, lean_object* v___x_4514_, lean_object* v_____r_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4513_, v___x_4514_, v_____r_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___x_4514_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4524_, lean_object* v_b_4525_, lean_object* v_a_4526_, uint8_t v___x_4527_, uint8_t v_only_4528_, uint8_t v_incremental_4529_, uint8_t v___x_4530_, lean_object* v_x_4531_, lean_object* v_mod_x3f_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4540_ = lean_unsigned_to_nat(2u);
v___x_4541_ = l_Lean_Syntax_getArg(v___x_4524_, v___x_4540_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4602_; uint8_t v___x_4603_; 
v___x_4602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4541_);
v___x_4603_ = l_Lean_Syntax_isOfKind(v___x_4541_, v___x_4602_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; 
v___x_4604_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4525_, v_a_4526_, v_mod_x3f_4532_, v___x_4541_, v___x_4527_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4614_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4607_ = v___x_4604_;
v_isShared_4608_ = v_isSharedCheck_4614_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4604_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4614_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4612_; 
v___x_4609_ = lean_box(0);
v___x_4610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4609_);
lean_ctor_set(v___x_4610_, 1, v_a_4605_);
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 0, v___x_4610_);
v___x_4612_ = v___x_4607_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4610_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
v_a_4615_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4604_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4604_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
else
{
goto v___jp_4562_;
}
}
else
{
goto v___jp_4562_;
}
v___jp_4542_:
{
lean_object* v___x_4543_; 
v___x_4543_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4525_, v_a_4526_, v_mod_x3f_4532_, v___x_4541_, v___x_4527_, v_only_4528_, v_incremental_4529_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4553_; 
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4546_ = v___x_4543_;
v_isShared_4547_ = v_isSharedCheck_4553_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4543_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4553_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4551_; 
v___x_4548_ = lean_box(0);
v___x_4549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
lean_ctor_set(v___x_4549_, 1, v_a_4544_);
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 0, v___x_4549_);
v___x_4551_ = v___x_4546_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
v_a_4554_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4543_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4543_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
v___jp_4562_:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4563_ = l_Lean_TSyntax_getId(v___x_4541_);
v___x_4564_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4563_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4564_) == 0)
{
lean_object* v_a_4565_; 
v_a_4565_ = lean_ctor_get(v___x_4564_, 0);
lean_inc(v_a_4565_);
lean_dec_ref_known(v___x_4564_, 1);
if (lean_obj_tag(v_a_4565_) == 1)
{
lean_object* v_val_4566_; lean_object* v_snd_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4592_; 
v_val_4566_ = lean_ctor_get(v_a_4565_, 0);
lean_inc(v_val_4566_);
lean_dec_ref_known(v_a_4565_, 1);
v_snd_4567_ = lean_ctor_get(v_val_4566_, 1);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_val_4566_);
if (v_isSharedCheck_4592_ == 0)
{
lean_object* v_unused_4593_; 
v_unused_4593_ = lean_ctor_get(v_val_4566_, 0);
lean_dec(v_unused_4593_);
v___x_4569_ = v_val_4566_;
v_isShared_4570_ = v_isSharedCheck_4592_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_snd_4567_);
lean_dec(v_val_4566_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4592_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
if (lean_obj_tag(v_snd_4567_) == 1)
{
lean_object* v___x_4571_; 
lean_dec_ref_known(v_snd_4567_, 2);
v___x_4571_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4525_, v_a_4526_, v_mod_x3f_4532_, v___x_4541_, v___x_4527_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4583_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4574_ = v___x_4571_;
v_isShared_4575_ = v_isSharedCheck_4583_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4571_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4583_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4576_; lean_object* v___x_4578_; 
v___x_4576_ = lean_box(0);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 1, v_a_4572_);
lean_ctor_set(v___x_4569_, 0, v___x_4576_);
v___x_4578_ = v___x_4569_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v___x_4576_);
lean_ctor_set(v_reuseFailAlloc_4582_, 1, v_a_4572_);
v___x_4578_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4580_; 
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 0, v___x_4578_);
v___x_4580_ = v___x_4574_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4578_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_del_object(v___x_4569_);
v_a_4584_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4571_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4571_);
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
lean_del_object(v___x_4569_);
lean_dec(v_snd_4567_);
goto v___jp_4542_;
}
}
}
else
{
lean_dec(v_a_4565_);
goto v___jp_4542_;
}
}
else
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4601_; 
lean_dec(v___x_4541_);
lean_dec(v_mod_x3f_4532_);
lean_dec(v_a_4526_);
lean_dec_ref(v_b_4525_);
v_a_4594_ = lean_ctor_get(v___x_4564_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4596_ = v___x_4564_;
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v___x_4564_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4601_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4599_; 
if (v_isShared_4597_ == 0)
{
v___x_4599_ = v___x_4596_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4594_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4623_, lean_object* v_b_4624_, lean_object* v_a_4625_, lean_object* v___x_4626_, lean_object* v_only_4627_, lean_object* v_incremental_4628_, lean_object* v___x_4629_, lean_object* v_x_4630_, lean_object* v_mod_x3f_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
uint8_t v___x_17974__boxed_4639_; uint8_t v_only_boxed_4640_; uint8_t v_incremental_boxed_4641_; uint8_t v___x_17975__boxed_4642_; lean_object* v_res_4643_; 
v___x_17974__boxed_4639_ = lean_unbox(v___x_4626_);
v_only_boxed_4640_ = lean_unbox(v_only_4627_);
v_incremental_boxed_4641_ = lean_unbox(v_incremental_4628_);
v___x_17975__boxed_4642_ = lean_unbox(v___x_4629_);
v_res_4643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4623_, v_b_4624_, v_a_4625_, v___x_17974__boxed_4639_, v_only_boxed_4640_, v_incremental_boxed_4641_, v___x_17975__boxed_4642_, v_x_4630_, v_mod_x3f_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec(v___x_4623_);
return v_res_4643_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4652_ = l_Lean_stringToMessageData(v___x_4651_);
return v___x_4652_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13(void){
_start:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__12));
v___x_4679_ = l_Lean_stringToMessageData(v___x_4678_);
return v___x_4679_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4685_ = l_Lean_stringToMessageData(v___x_4684_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4686_, uint8_t v_only_4687_, uint8_t v_incremental_4688_, lean_object* v_as_4689_, size_t v_sz_4690_, size_t v_i_4691_, lean_object* v_b_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v_snd_4701_; lean_object* v___y_4706_; uint8_t v___y_4707_; lean_object* v_a_4711_; lean_object* v___y_4715_; uint8_t v___x_4719_; 
v___x_4719_ = lean_usize_dec_lt(v_i_4691_, v_sz_4690_);
if (v___x_4719_ == 0)
{
lean_object* v___x_4720_; 
v___x_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4720_, 0, v_b_4692_);
return v___x_4720_;
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4722_; uint8_t v___x_4723_; 
v_a_4721_ = lean_array_uget_borrowed(v_as_4689_, v_i_4691_);
v___x_4722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4721_);
v___x_4723_ = l_Lean_Syntax_isOfKind(v_a_4721_, v___x_4722_);
if (v___x_4723_ == 0)
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4724_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4721_);
v___x_4725_ = l_Lean_MessageData_ofSyntax(v_a_4721_);
v___x_4726_ = l_Lean_indentD(v___x_4725_);
v___x_4727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4724_);
lean_ctor_set(v___x_4727_, 1, v___x_4726_);
v___x_4728_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4727_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_dec_ref_known(v___x_4728_, 1);
v_snd_4701_ = v_b_4692_;
goto v___jp_4700_;
}
else
{
lean_object* v_a_4729_; 
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc(v_a_4729_);
lean_dec_ref_known(v___x_4728_, 1);
v_a_4711_ = v_a_4729_;
goto v___jp_4710_;
}
}
else
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; 
v___x_4730_ = lean_unsigned_to_nat(0u);
v___x_4731_ = l_Lean_Syntax_getArg(v_a_4721_, v___x_4730_);
v___x_4732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_4731_);
v___x_4733_ = l_Lean_Syntax_isOfKind(v___x_4731_, v___x_4732_);
if (v___x_4733_ == 0)
{
lean_object* v___x_4734_; uint8_t v___x_4735_; 
v___x_4734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_4731_);
v___x_4735_ = l_Lean_Syntax_isOfKind(v___x_4731_, v___x_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; uint8_t v___x_4737_; 
v___x_4736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_4731_);
v___x_4737_ = l_Lean_Syntax_isOfKind(v___x_4731_, v___x_4736_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4738_; uint8_t v___x_4739_; 
v___x_4738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_4731_);
v___x_4739_ = l_Lean_Syntax_isOfKind(v___x_4731_, v___x_4738_);
if (v___x_4739_ == 0)
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
lean_dec(v___x_4731_);
v___x_4740_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4721_);
v___x_4741_ = l_Lean_MessageData_ofSyntax(v_a_4721_);
v___x_4742_ = l_Lean_indentD(v___x_4741_);
v___x_4743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4740_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
v___x_4744_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4743_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_dec_ref_known(v___x_4744_, 1);
v_snd_4701_ = v_b_4692_;
goto v___jp_4700_;
}
else
{
lean_object* v_a_4745_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref_known(v___x_4744_, 1);
v_a_4711_ = v_a_4745_;
goto v___jp_4710_;
}
}
else
{
lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4746_ = lean_unsigned_to_nat(1u);
v___x_4747_ = l_Lean_Syntax_getArg(v___x_4731_, v___x_4746_);
lean_dec(v___x_4731_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4756_; uint8_t v___x_4757_; 
v___x_4756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15));
lean_inc(v___x_4747_);
v___x_4757_ = l_Lean_Syntax_isOfKind(v___x_4747_, v___x_4756_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
lean_dec(v___x_4747_);
v___x_4758_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4721_);
v___x_4759_ = l_Lean_MessageData_ofSyntax(v_a_4721_);
v___x_4760_ = l_Lean_indentD(v___x_4759_);
v___x_4761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4761_, 0, v___x_4758_);
lean_ctor_set(v___x_4761_, 1, v___x_4760_);
v___x_4762_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4761_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_dec_ref_known(v___x_4762_, 1);
v_snd_4701_ = v_b_4692_;
goto v___jp_4700_;
}
else
{
lean_object* v_a_4763_; 
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
lean_inc(v_a_4763_);
lean_dec_ref_known(v___x_4762_, 1);
v_a_4711_ = v_a_4763_;
goto v___jp_4710_;
}
}
else
{
goto v___jp_4748_;
}
}
else
{
goto v___jp_4748_;
}
v___jp_4748_:
{
if (v_only_4687_ == 0)
{
lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4749_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13);
v___x_4750_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_4747_, v___x_4749_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4750_) == 0)
{
lean_object* v_a_4751_; lean_object* v___x_4752_; 
v_a_4751_ = lean_ctor_get(v___x_4750_, 0);
lean_inc(v_a_4751_);
lean_dec_ref_known(v___x_4750_, 1);
lean_inc_ref(v_b_4692_);
v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4692_, v___x_4747_, v_a_4751_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___x_4747_);
v___y_4715_ = v___x_4752_;
goto v___jp_4714_;
}
else
{
lean_object* v_a_4753_; 
lean_dec(v___x_4747_);
v_a_4753_ = lean_ctor_get(v___x_4750_, 0);
lean_inc(v_a_4753_);
lean_dec_ref_known(v___x_4750_, 1);
v_a_4711_ = v_a_4753_;
goto v___jp_4710_;
}
}
else
{
lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4754_ = lean_box(0);
lean_inc_ref(v_b_4692_);
v___x_4755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4692_, v___x_4747_, v___x_4754_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___x_4747_);
v___y_4715_ = v___x_4755_;
goto v___jp_4714_;
}
}
}
}
else
{
lean_object* v___x_4764_; lean_object* v___x_4765_; uint8_t v___x_4766_; 
v___x_4764_ = lean_unsigned_to_nat(1u);
v___x_4765_ = l_Lean_Syntax_getArg(v___x_4731_, v___x_4764_);
v___x_4766_ = l_Lean_Syntax_isNone(v___x_4765_);
if (v___x_4766_ == 0)
{
uint8_t v___x_4767_; 
lean_inc(v___x_4765_);
v___x_4767_ = l_Lean_Syntax_matchesNull(v___x_4765_, v___x_4764_);
if (v___x_4767_ == 0)
{
lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
lean_dec(v___x_4765_);
lean_dec(v___x_4731_);
v___x_4768_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4721_);
v___x_4769_ = l_Lean_MessageData_ofSyntax(v_a_4721_);
v___x_4770_ = l_Lean_indentD(v___x_4769_);
v___x_4771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4768_);
lean_ctor_set(v___x_4771_, 1, v___x_4770_);
v___x_4772_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4771_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4772_) == 0)
{
lean_dec_ref_known(v___x_4772_, 1);
v_snd_4701_ = v_b_4692_;
goto v___jp_4700_;
}
else
{
lean_object* v_a_4773_; 
v_a_4773_ = lean_ctor_get(v___x_4772_, 0);
lean_inc(v_a_4773_);
lean_dec_ref_known(v___x_4772_, 1);
v_a_4711_ = v_a_4773_;
goto v___jp_4710_;
}
}
else
{
lean_object* v___x_4774_; 
v___x_4774_ = l_Lean_Syntax_getArg(v___x_4765_, v___x_4730_);
lean_dec(v___x_4765_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4779_; uint8_t v___x_4780_; 
v___x_4779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4774_);
v___x_4780_ = l_Lean_Syntax_isOfKind(v___x_4774_, v___x_4779_);
if (v___x_4780_ == 0)
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
lean_dec(v___x_4774_);
lean_dec(v___x_4731_);
v___x_4781_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4721_);
v___x_4782_ = l_Lean_MessageData_ofSyntax(v_a_4721_);
v___x_4783_ = l_Lean_indentD(v___x_4782_);
v___x_4784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4781_);
lean_ctor_set(v___x_4784_, 1, v___x_4783_);
v___x_4785_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4784_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_dec_ref_known(v___x_4785_, 1);
v_snd_4701_ = v_b_4692_;
goto v___jp_4700_;
}
else
{
lean_object* v_a_4786_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_a_4786_);
lean_dec_ref_known(v___x_4785_, 1);
v_a_4711_ = v_a_4786_;
goto v___jp_4710_;
}
}
else
{
goto v___jp_4775_;
}
}
else
{
goto v___jp_4775_;
}
v___jp_4775_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v___x_4776_ = lean_box(0);
v___x_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4774_);
lean_inc(v_a_4721_);
lean_inc_ref(v_b_4692_);
v___x_4778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4731_, v_b_4692_, v_a_4721_, v___x_4723_, v_only_4687_, v_incremental_4688_, v___x_4735_, v___x_4776_, v___x_4777_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___x_4731_);
v___y_4715_ = v___x_4778_;
goto v___jp_4714_;
}
}
}
else
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; 
lean_dec(v___x_4765_);
v___x_4787_ = lean_box(0);
v___x_4788_ = lean_box(0);
lean_inc(v_a_4721_);
lean_inc_ref(v_b_4692_);
v___x_4789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4731_, v_b_4692_, v_a_4721_, v___x_4723_, v_only_4687_, v_incremental_4688_, v___x_4735_, v___x_4787_, v___x_4788_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___x_4731_);
v___y_4715_ = v___x_4789_;
goto v___jp_4714_;
}
}
}
else
{
lean_object* v___x_4790_; uint8_t v___x_4791_; 
v___x_4790_ = l_Lean_Syntax_getArg(v___x_4731_, v___x_4730_);
v___x_4791_ = l_Lean_Syntax_isNone(v___x_4790_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4792_; uint8_t v___x_4793_; 
v___x_4792_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4790_);
v___x_4793_ = l_Lean_Syntax_matchesNull(v___x_4790_, v___x_4792_);
if (v___x_4793_ == 0)
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
lean_dec(v___x_4790_);
lean_dec(v___x_4731_);
v___x_4794_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4721_);
v___x_4795_ = l_Lean_MessageData_ofSyntax(v_a_4721_);
v___x_4796_ = l_Lean_indentD(v___x_4795_);
v___x_4797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4794_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
v___x_4798_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4797_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_dec_ref_known(v___x_4798_, 1);
v_snd_4701_ = v_b_4692_;
goto v___jp_4700_;
}
else
{
lean_object* v_a_4799_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
lean_inc(v_a_4799_);
lean_dec_ref_known(v___x_4798_, 1);
v_a_4711_ = v_a_4799_;
goto v___jp_4710_;
}
}
else
{
lean_object* v___x_4800_; 
v___x_4800_ = l_Lean_Syntax_getArg(v___x_4790_, v___x_4730_);
lean_dec(v___x_4790_);
if (v___x_4791_ == 0)
{
lean_object* v___x_4805_; uint8_t v___x_4806_; 
v___x_4805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4800_);
v___x_4806_ = l_Lean_Syntax_isOfKind(v___x_4800_, v___x_4805_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; 
lean_dec(v___x_4800_);
lean_dec(v___x_4731_);
v___x_4807_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4721_);
v___x_4808_ = l_Lean_MessageData_ofSyntax(v_a_4721_);
v___x_4809_ = l_Lean_indentD(v___x_4808_);
v___x_4810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4810_, 0, v___x_4807_);
lean_ctor_set(v___x_4810_, 1, v___x_4809_);
v___x_4811_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4810_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_dec_ref_known(v___x_4811_, 1);
v_snd_4701_ = v_b_4692_;
goto v___jp_4700_;
}
else
{
lean_object* v_a_4812_; 
v_a_4812_ = lean_ctor_get(v___x_4811_, 0);
lean_inc(v_a_4812_);
lean_dec_ref_known(v___x_4811_, 1);
v_a_4711_ = v_a_4812_;
goto v___jp_4710_;
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
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4802_ = lean_box(0);
v___x_4803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4800_);
lean_inc(v_a_4721_);
lean_inc_ref(v_b_4692_);
v___x_4804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4731_, v_b_4692_, v_a_4721_, v___x_4733_, v_only_4687_, v_incremental_4688_, v___x_4802_, v___x_4803_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___x_4731_);
v___y_4715_ = v___x_4804_;
goto v___jp_4714_;
}
}
}
else
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
lean_dec(v___x_4790_);
v___x_4813_ = lean_box(0);
v___x_4814_ = lean_box(0);
lean_inc(v_a_4721_);
lean_inc_ref(v_b_4692_);
v___x_4815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4731_, v_b_4692_, v_a_4721_, v___x_4733_, v_only_4687_, v_incremental_4688_, v___x_4813_, v___x_4814_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___x_4731_);
v___y_4715_ = v___x_4815_;
goto v___jp_4714_;
}
}
}
else
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; uint8_t v___x_4819_; 
v___x_4816_ = lean_unsigned_to_nat(1u);
v___x_4817_ = l_Lean_Syntax_getArg(v___x_4731_, v___x_4816_);
lean_dec(v___x_4731_);
v___x_4818_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4817_);
v___x_4819_ = l_Lean_Syntax_isOfKind(v___x_4817_, v___x_4818_);
if (v___x_4819_ == 0)
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
lean_dec(v___x_4817_);
v___x_4820_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4721_);
v___x_4821_ = l_Lean_MessageData_ofSyntax(v_a_4721_);
v___x_4822_ = l_Lean_indentD(v___x_4821_);
v___x_4823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4823_, 0, v___x_4820_);
lean_ctor_set(v___x_4823_, 1, v___x_4822_);
v___x_4824_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4823_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_dec_ref_known(v___x_4824_, 1);
v_snd_4701_ = v_b_4692_;
goto v___jp_4700_;
}
else
{
lean_object* v_a_4825_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4824_, 1);
v_a_4711_ = v_a_4825_;
goto v___jp_4710_;
}
}
else
{
if (v_incremental_4688_ == 0)
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4826_ = lean_box(0);
lean_inc_ref(v_b_4692_);
v___x_4827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4817_, v___x_4723_, v_b_4692_, v___x_4826_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
v___y_4715_ = v___x_4827_;
goto v___jp_4714_;
}
else
{
lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4828_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_4829_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4721_, v___x_4828_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v_a_4830_; lean_object* v___x_4831_; 
v_a_4830_ = lean_ctor_get(v___x_4829_, 0);
lean_inc(v_a_4830_);
lean_dec_ref_known(v___x_4829_, 1);
lean_inc_ref(v_b_4692_);
v___x_4831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4817_, v___x_4723_, v_b_4692_, v_a_4830_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
v___y_4715_ = v___x_4831_;
goto v___jp_4714_;
}
else
{
lean_object* v_a_4832_; 
lean_dec(v___x_4817_);
v_a_4832_ = lean_ctor_get(v___x_4829_, 0);
lean_inc(v_a_4832_);
lean_dec_ref_known(v___x_4829_, 1);
v_a_4711_ = v_a_4832_;
goto v___jp_4710_;
}
}
}
}
}
}
v___jp_4700_:
{
size_t v___x_4702_; size_t v___x_4703_; 
v___x_4702_ = ((size_t)1ULL);
v___x_4703_ = lean_usize_add(v_i_4691_, v___x_4702_);
v_i_4691_ = v___x_4703_;
v_b_4692_ = v_snd_4701_;
goto _start;
}
v___jp_4705_:
{
if (v___y_4707_ == 0)
{
if (v_lax_4686_ == 0)
{
lean_object* v___x_4708_; 
lean_dec_ref(v_b_4692_);
v___x_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4708_, 0, v___y_4706_);
return v___x_4708_;
}
else
{
lean_dec_ref(v___y_4706_);
v_snd_4701_ = v_b_4692_;
goto v___jp_4700_;
}
}
else
{
lean_object* v___x_4709_; 
lean_dec_ref(v_b_4692_);
v___x_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___y_4706_);
return v___x_4709_;
}
}
v___jp_4710_:
{
uint8_t v___x_4712_; 
v___x_4712_ = l_Lean_Exception_isInterrupt(v_a_4711_);
if (v___x_4712_ == 0)
{
uint8_t v___x_4713_; 
lean_inc_ref(v_a_4711_);
v___x_4713_ = l_Lean_Exception_isRuntime(v_a_4711_);
v___y_4706_ = v_a_4711_;
v___y_4707_ = v___x_4713_;
goto v___jp_4705_;
}
else
{
v___y_4706_ = v_a_4711_;
v___y_4707_ = v___x_4712_;
goto v___jp_4705_;
}
}
v___jp_4714_:
{
if (lean_obj_tag(v___y_4715_) == 0)
{
lean_object* v_a_4716_; lean_object* v_snd_4717_; 
lean_dec_ref(v_b_4692_);
v_a_4716_ = lean_ctor_get(v___y_4715_, 0);
lean_inc(v_a_4716_);
lean_dec_ref_known(v___y_4715_, 1);
v_snd_4717_ = lean_ctor_get(v_a_4716_, 1);
lean_inc(v_snd_4717_);
lean_dec(v_a_4716_);
v_snd_4701_ = v_snd_4717_;
goto v___jp_4700_;
}
else
{
lean_object* v_a_4718_; 
v_a_4718_ = lean_ctor_get(v___y_4715_, 0);
lean_inc(v_a_4718_);
lean_dec_ref_known(v___y_4715_, 1);
v_a_4711_ = v_a_4718_;
goto v___jp_4710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_4833_, lean_object* v_only_4834_, lean_object* v_incremental_4835_, lean_object* v_as_4836_, lean_object* v_sz_4837_, lean_object* v_i_4838_, lean_object* v_b_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
uint8_t v_lax_boxed_4847_; uint8_t v_only_boxed_4848_; uint8_t v_incremental_boxed_4849_; size_t v_sz_boxed_4850_; size_t v_i_boxed_4851_; lean_object* v_res_4852_; 
v_lax_boxed_4847_ = lean_unbox(v_lax_4833_);
v_only_boxed_4848_ = lean_unbox(v_only_4834_);
v_incremental_boxed_4849_ = lean_unbox(v_incremental_4835_);
v_sz_boxed_4850_ = lean_unbox_usize(v_sz_4837_);
lean_dec(v_sz_4837_);
v_i_boxed_4851_ = lean_unbox_usize(v_i_4838_);
lean_dec(v_i_4838_);
v_res_4852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_4847_, v_only_boxed_4848_, v_incremental_boxed_4849_, v_as_4836_, v_sz_boxed_4850_, v_i_boxed_4851_, v_b_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec_ref(v_as_4836_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_4853_, lean_object* v_ps_4854_, uint8_t v_only_4855_, uint8_t v_lax_4856_, uint8_t v_incremental_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_){
_start:
{
size_t v_sz_4865_; size_t v___x_4866_; lean_object* v___x_4867_; 
v_sz_4865_ = lean_array_size(v_ps_4854_);
v___x_4866_ = ((size_t)0ULL);
v___x_4867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_4856_, v_only_4855_, v_incremental_4857_, v_ps_4854_, v_sz_4865_, v___x_4866_, v_params_4853_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_4868_, lean_object* v_ps_4869_, lean_object* v_only_4870_, lean_object* v_lax_4871_, lean_object* v_incremental_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_){
_start:
{
uint8_t v_only_boxed_4880_; uint8_t v_lax_boxed_4881_; uint8_t v_incremental_boxed_4882_; lean_object* v_res_4883_; 
v_only_boxed_4880_ = lean_unbox(v_only_4870_);
v_lax_boxed_4881_ = lean_unbox(v_lax_4871_);
v_incremental_boxed_4882_ = lean_unbox(v_incremental_4872_);
v_res_4883_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_4868_, v_ps_4869_, v_only_boxed_4880_, v_lax_boxed_4881_, v_incremental_boxed_4882_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_);
lean_dec(v_a_4878_);
lean_dec_ref(v_a_4877_);
lean_dec(v_a_4876_);
lean_dec_ref(v_a_4875_);
lean_dec(v_a_4874_);
lean_dec_ref(v_a_4873_);
lean_dec_ref(v_ps_4869_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
lean_object* v_origin_4895_; 
v_origin_4895_ = lean_ctor_get(v_thm_4884_, 5);
if (lean_obj_tag(v_origin_4895_) == 0)
{
lean_object* v_declName_4896_; lean_object* v___x_4897_; 
lean_inc_ref(v_origin_4895_);
lean_dec_ref(v_thm_4884_);
v_declName_4896_ = lean_ctor_get(v_origin_4895_, 0);
lean_inc(v_declName_4896_);
lean_dec_ref_known(v_origin_4895_, 1);
v___x_4897_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_4896_, v_a_4892_, v_a_4893_);
return v___x_4897_;
}
else
{
lean_object* v_proof_4898_; lean_object* v___x_4899_; 
v_proof_4898_ = lean_ctor_get(v_thm_4884_, 1);
lean_inc_ref(v_proof_4898_);
lean_dec_ref(v_thm_4884_);
v___x_4899_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_4898_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
return v___x_4899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_);
lean_dec(v_a_4909_);
lean_dec_ref(v_a_4908_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
lean_dec(v_a_4903_);
lean_dec_ref(v_a_4902_);
lean_dec(v_a_4901_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_4912_, size_t v_sz_4913_, size_t v_i_4914_, lean_object* v_b_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_){
_start:
{
uint8_t v___x_4926_; 
v___x_4926_ = lean_usize_dec_lt(v_i_4914_, v_sz_4913_);
if (v___x_4926_ == 0)
{
lean_object* v___x_4927_; 
v___x_4927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4927_, 0, v_b_4915_);
return v___x_4927_;
}
else
{
lean_object* v_snd_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4954_; 
v_snd_4928_ = lean_ctor_get(v_b_4915_, 1);
v_isSharedCheck_4954_ = !lean_is_exclusive(v_b_4915_);
if (v_isSharedCheck_4954_ == 0)
{
lean_object* v_unused_4955_; 
v_unused_4955_ = lean_ctor_get(v_b_4915_, 0);
lean_dec(v_unused_4955_);
v___x_4930_ = v_b_4915_;
v_isShared_4931_ = v_isSharedCheck_4954_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_snd_4928_);
lean_dec(v_b_4915_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4954_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v_a_4932_; lean_object* v___x_4933_; 
v_a_4932_ = lean_array_uget_borrowed(v_as_4912_, v_i_4914_);
lean_inc(v_a_4932_);
v___x_4933_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_4932_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_);
if (lean_obj_tag(v___x_4933_) == 0)
{
lean_object* v_a_4934_; lean_object* v___x_4935_; lean_object* v_a_4937_; uint8_t v___x_4944_; 
v_a_4934_ = lean_ctor_get(v___x_4933_, 0);
lean_inc(v_a_4934_);
lean_dec_ref_known(v___x_4933_, 1);
v___x_4935_ = lean_box(0);
v___x_4944_ = lean_unbox(v_a_4934_);
lean_dec(v_a_4934_);
if (v___x_4944_ == 0)
{
v_a_4937_ = v_snd_4928_;
goto v___jp_4936_;
}
else
{
lean_object* v___x_4945_; 
lean_inc(v_a_4932_);
v___x_4945_ = l_Lean_PersistentArray_push___redArg(v_snd_4928_, v_a_4932_);
v_a_4937_ = v___x_4945_;
goto v___jp_4936_;
}
v___jp_4936_:
{
lean_object* v___x_4939_; 
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 1, v_a_4937_);
lean_ctor_set(v___x_4930_, 0, v___x_4935_);
v___x_4939_ = v___x_4930_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4935_);
lean_ctor_set(v_reuseFailAlloc_4943_, 1, v_a_4937_);
v___x_4939_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
size_t v___x_4940_; size_t v___x_4941_; 
v___x_4940_ = ((size_t)1ULL);
v___x_4941_ = lean_usize_add(v_i_4914_, v___x_4940_);
v_i_4914_ = v___x_4941_;
v_b_4915_ = v___x_4939_;
goto _start;
}
}
}
else
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4953_; 
lean_del_object(v___x_4930_);
lean_dec(v_snd_4928_);
v_a_4946_ = lean_ctor_get(v___x_4933_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4948_ = v___x_4933_;
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4933_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4951_; 
if (v_isShared_4949_ == 0)
{
v___x_4951_ = v___x_4948_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4946_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_4956_, lean_object* v_sz_4957_, lean_object* v_i_4958_, lean_object* v_b_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_){
_start:
{
size_t v_sz_boxed_4970_; size_t v_i_boxed_4971_; lean_object* v_res_4972_; 
v_sz_boxed_4970_ = lean_unbox_usize(v_sz_4957_);
lean_dec(v_sz_4957_);
v_i_boxed_4971_ = lean_unbox_usize(v_i_4958_);
lean_dec(v_i_4958_);
v_res_4972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_4956_, v_sz_boxed_4970_, v_i_boxed_4971_, v_b_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
lean_dec(v___y_4968_);
lean_dec_ref(v___y_4967_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
lean_dec(v___y_4962_);
lean_dec_ref(v___y_4961_);
lean_dec(v___y_4960_);
lean_dec_ref(v_as_4956_);
return v_res_4972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_4973_, size_t v_sz_4974_, size_t v_i_4975_, lean_object* v_b_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
uint8_t v___x_4987_; 
v___x_4987_ = lean_usize_dec_lt(v_i_4975_, v_sz_4974_);
if (v___x_4987_ == 0)
{
lean_object* v___x_4988_; 
v___x_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4988_, 0, v_b_4976_);
return v___x_4988_;
}
else
{
lean_object* v_snd_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_5015_; 
v_snd_4989_ = lean_ctor_get(v_b_4976_, 1);
v_isSharedCheck_5015_ = !lean_is_exclusive(v_b_4976_);
if (v_isSharedCheck_5015_ == 0)
{
lean_object* v_unused_5016_; 
v_unused_5016_ = lean_ctor_get(v_b_4976_, 0);
lean_dec(v_unused_5016_);
v___x_4991_ = v_b_4976_;
v_isShared_4992_ = v_isSharedCheck_5015_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_snd_4989_);
lean_dec(v_b_4976_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_5015_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v_a_4993_; lean_object* v___x_4994_; 
v_a_4993_ = lean_array_uget_borrowed(v_as_4973_, v_i_4975_);
lean_inc(v_a_4993_);
v___x_4994_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_4993_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_);
if (lean_obj_tag(v___x_4994_) == 0)
{
lean_object* v_a_4995_; lean_object* v___x_4996_; lean_object* v_a_4998_; uint8_t v___x_5005_; 
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc(v_a_4995_);
lean_dec_ref_known(v___x_4994_, 1);
v___x_4996_ = lean_box(0);
v___x_5005_ = lean_unbox(v_a_4995_);
lean_dec(v_a_4995_);
if (v___x_5005_ == 0)
{
v_a_4998_ = v_snd_4989_;
goto v___jp_4997_;
}
else
{
lean_object* v___x_5006_; 
lean_inc(v_a_4993_);
v___x_5006_ = l_Lean_PersistentArray_push___redArg(v_snd_4989_, v_a_4993_);
v_a_4998_ = v___x_5006_;
goto v___jp_4997_;
}
v___jp_4997_:
{
lean_object* v___x_5000_; 
if (v_isShared_4992_ == 0)
{
lean_ctor_set(v___x_4991_, 1, v_a_4998_);
lean_ctor_set(v___x_4991_, 0, v___x_4996_);
v___x_5000_ = v___x_4991_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_4996_);
lean_ctor_set(v_reuseFailAlloc_5004_, 1, v_a_4998_);
v___x_5000_ = v_reuseFailAlloc_5004_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
size_t v___x_5001_; size_t v___x_5002_; lean_object* v___x_5003_; 
v___x_5001_ = ((size_t)1ULL);
v___x_5002_ = lean_usize_add(v_i_4975_, v___x_5001_);
v___x_5003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_4973_, v_sz_4974_, v___x_5002_, v___x_5000_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_);
return v___x_5003_;
}
}
}
else
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5014_; 
lean_del_object(v___x_4991_);
lean_dec(v_snd_4989_);
v_a_5007_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5009_ = v___x_4994_;
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_4994_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v___x_5012_; 
if (v_isShared_5010_ == 0)
{
v___x_5012_ = v___x_5009_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_a_5007_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5017_, lean_object* v_sz_5018_, lean_object* v_i_5019_, lean_object* v_b_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
size_t v_sz_boxed_5031_; size_t v_i_boxed_5032_; lean_object* v_res_5033_; 
v_sz_boxed_5031_ = lean_unbox_usize(v_sz_5018_);
lean_dec(v_sz_5018_);
v_i_boxed_5032_ = lean_unbox_usize(v_i_5019_);
lean_dec(v_i_5019_);
v_res_5033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5017_, v_sz_boxed_5031_, v_i_boxed_5032_, v_b_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___y_5029_);
lean_dec_ref(v___y_5028_);
lean_dec(v___y_5027_);
lean_dec_ref(v___y_5026_);
lean_dec(v___y_5025_);
lean_dec_ref(v___y_5024_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v___y_5021_);
lean_dec_ref(v_as_5017_);
return v_res_5033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5034_, size_t v_sz_5035_, size_t v_i_5036_, lean_object* v_b_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_){
_start:
{
uint8_t v___x_5048_; 
v___x_5048_ = lean_usize_dec_lt(v_i_5036_, v_sz_5035_);
if (v___x_5048_ == 0)
{
lean_object* v___x_5049_; 
v___x_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5049_, 0, v_b_5037_);
return v___x_5049_;
}
else
{
lean_object* v_snd_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5076_; 
v_snd_5050_ = lean_ctor_get(v_b_5037_, 1);
v_isSharedCheck_5076_ = !lean_is_exclusive(v_b_5037_);
if (v_isSharedCheck_5076_ == 0)
{
lean_object* v_unused_5077_; 
v_unused_5077_ = lean_ctor_get(v_b_5037_, 0);
lean_dec(v_unused_5077_);
v___x_5052_ = v_b_5037_;
v_isShared_5053_ = v_isSharedCheck_5076_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_snd_5050_);
lean_dec(v_b_5037_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5076_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v_a_5054_; lean_object* v___x_5055_; 
v_a_5054_ = lean_array_uget_borrowed(v_as_5034_, v_i_5036_);
lean_inc(v_a_5054_);
v___x_5055_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5054_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_object* v_a_5056_; lean_object* v___x_5057_; lean_object* v_a_5059_; uint8_t v___x_5066_; 
v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc(v_a_5056_);
lean_dec_ref_known(v___x_5055_, 1);
v___x_5057_ = lean_box(0);
v___x_5066_ = lean_unbox(v_a_5056_);
lean_dec(v_a_5056_);
if (v___x_5066_ == 0)
{
v_a_5059_ = v_snd_5050_;
goto v___jp_5058_;
}
else
{
lean_object* v___x_5067_; 
lean_inc(v_a_5054_);
v___x_5067_ = l_Lean_PersistentArray_push___redArg(v_snd_5050_, v_a_5054_);
v_a_5059_ = v___x_5067_;
goto v___jp_5058_;
}
v___jp_5058_:
{
lean_object* v___x_5061_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 1, v_a_5059_);
lean_ctor_set(v___x_5052_, 0, v___x_5057_);
v___x_5061_ = v___x_5052_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5057_);
lean_ctor_set(v_reuseFailAlloc_5065_, 1, v_a_5059_);
v___x_5061_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
size_t v___x_5062_; size_t v___x_5063_; 
v___x_5062_ = ((size_t)1ULL);
v___x_5063_ = lean_usize_add(v_i_5036_, v___x_5062_);
v_i_5036_ = v___x_5063_;
v_b_5037_ = v___x_5061_;
goto _start;
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_del_object(v___x_5052_);
lean_dec(v_snd_5050_);
v_a_5068_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5055_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5055_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5078_, lean_object* v_sz_5079_, lean_object* v_i_5080_, lean_object* v_b_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_){
_start:
{
size_t v_sz_boxed_5092_; size_t v_i_boxed_5093_; lean_object* v_res_5094_; 
v_sz_boxed_5092_ = lean_unbox_usize(v_sz_5079_);
lean_dec(v_sz_5079_);
v_i_boxed_5093_ = lean_unbox_usize(v_i_5080_);
lean_dec(v_i_5080_);
v_res_5094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5078_, v_sz_boxed_5092_, v_i_boxed_5093_, v_b_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_);
lean_dec(v___y_5090_);
lean_dec_ref(v___y_5089_);
lean_dec(v___y_5088_);
lean_dec_ref(v___y_5087_);
lean_dec(v___y_5086_);
lean_dec_ref(v___y_5085_);
lean_dec(v___y_5084_);
lean_dec_ref(v___y_5083_);
lean_dec(v___y_5082_);
lean_dec_ref(v_as_5078_);
return v_res_5094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5095_, size_t v_sz_5096_, size_t v_i_5097_, lean_object* v_b_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
uint8_t v___x_5109_; 
v___x_5109_ = lean_usize_dec_lt(v_i_5097_, v_sz_5096_);
if (v___x_5109_ == 0)
{
lean_object* v___x_5110_; 
v___x_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5110_, 0, v_b_5098_);
return v___x_5110_;
}
else
{
lean_object* v_snd_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5137_; 
v_snd_5111_ = lean_ctor_get(v_b_5098_, 1);
v_isSharedCheck_5137_ = !lean_is_exclusive(v_b_5098_);
if (v_isSharedCheck_5137_ == 0)
{
lean_object* v_unused_5138_; 
v_unused_5138_ = lean_ctor_get(v_b_5098_, 0);
lean_dec(v_unused_5138_);
v___x_5113_ = v_b_5098_;
v_isShared_5114_ = v_isSharedCheck_5137_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_snd_5111_);
lean_dec(v_b_5098_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5137_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v_a_5115_; lean_object* v___x_5116_; 
v_a_5115_ = lean_array_uget_borrowed(v_as_5095_, v_i_5097_);
lean_inc(v_a_5115_);
v___x_5116_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5115_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
if (lean_obj_tag(v___x_5116_) == 0)
{
lean_object* v_a_5117_; lean_object* v___x_5118_; lean_object* v_a_5120_; uint8_t v___x_5127_; 
v_a_5117_ = lean_ctor_get(v___x_5116_, 0);
lean_inc(v_a_5117_);
lean_dec_ref_known(v___x_5116_, 1);
v___x_5118_ = lean_box(0);
v___x_5127_ = lean_unbox(v_a_5117_);
lean_dec(v_a_5117_);
if (v___x_5127_ == 0)
{
v_a_5120_ = v_snd_5111_;
goto v___jp_5119_;
}
else
{
lean_object* v___x_5128_; 
lean_inc(v_a_5115_);
v___x_5128_ = l_Lean_PersistentArray_push___redArg(v_snd_5111_, v_a_5115_);
v_a_5120_ = v___x_5128_;
goto v___jp_5119_;
}
v___jp_5119_:
{
lean_object* v___x_5122_; 
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 1, v_a_5120_);
lean_ctor_set(v___x_5113_, 0, v___x_5118_);
v___x_5122_ = v___x_5113_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v___x_5118_);
lean_ctor_set(v_reuseFailAlloc_5126_, 1, v_a_5120_);
v___x_5122_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
size_t v___x_5123_; size_t v___x_5124_; lean_object* v___x_5125_; 
v___x_5123_ = ((size_t)1ULL);
v___x_5124_ = lean_usize_add(v_i_5097_, v___x_5123_);
v___x_5125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5095_, v_sz_5096_, v___x_5124_, v___x_5122_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
return v___x_5125_;
}
}
}
else
{
lean_object* v_a_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5136_; 
lean_del_object(v___x_5113_);
lean_dec(v_snd_5111_);
v_a_5129_ = lean_ctor_get(v___x_5116_, 0);
v_isSharedCheck_5136_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5136_ == 0)
{
v___x_5131_ = v___x_5116_;
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_a_5129_);
lean_dec(v___x_5116_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5134_; 
if (v_isShared_5132_ == 0)
{
v___x_5134_ = v___x_5131_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_a_5129_);
v___x_5134_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
return v___x_5134_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5139_, lean_object* v_sz_5140_, lean_object* v_i_5141_, lean_object* v_b_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_){
_start:
{
size_t v_sz_boxed_5153_; size_t v_i_boxed_5154_; lean_object* v_res_5155_; 
v_sz_boxed_5153_ = lean_unbox_usize(v_sz_5140_);
lean_dec(v_sz_5140_);
v_i_boxed_5154_ = lean_unbox_usize(v_i_5141_);
lean_dec(v_i_5141_);
v_res_5155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5139_, v_sz_boxed_5153_, v_i_boxed_5154_, v_b_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_);
lean_dec(v___y_5151_);
lean_dec_ref(v___y_5150_);
lean_dec(v___y_5149_);
lean_dec_ref(v___y_5148_);
lean_dec(v___y_5147_);
lean_dec_ref(v___y_5146_);
lean_dec(v___y_5145_);
lean_dec_ref(v___y_5144_);
lean_dec(v___y_5143_);
lean_dec_ref(v_as_5139_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5156_, lean_object* v_n_5157_, lean_object* v_b_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_){
_start:
{
if (lean_obj_tag(v_n_5157_) == 0)
{
lean_object* v_cs_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; size_t v_sz_5172_; size_t v___x_5173_; lean_object* v___x_5174_; 
v_cs_5169_ = lean_ctor_get(v_n_5157_, 0);
v___x_5170_ = lean_box(0);
v___x_5171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5170_);
lean_ctor_set(v___x_5171_, 1, v_b_5158_);
v_sz_5172_ = lean_array_size(v_cs_5169_);
v___x_5173_ = ((size_t)0ULL);
v___x_5174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5156_, v_cs_5169_, v_sz_5172_, v___x_5173_, v___x_5171_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5189_; 
v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5177_ = v___x_5174_;
v_isShared_5178_ = v_isSharedCheck_5189_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5174_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5189_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v_fst_5179_; 
v_fst_5179_ = lean_ctor_get(v_a_5175_, 0);
if (lean_obj_tag(v_fst_5179_) == 0)
{
lean_object* v_snd_5180_; lean_object* v___x_5181_; lean_object* v___x_5183_; 
v_snd_5180_ = lean_ctor_get(v_a_5175_, 1);
lean_inc(v_snd_5180_);
lean_dec(v_a_5175_);
v___x_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5181_, 0, v_snd_5180_);
if (v_isShared_5178_ == 0)
{
lean_ctor_set(v___x_5177_, 0, v___x_5181_);
v___x_5183_ = v___x_5177_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
else
{
lean_object* v_val_5185_; lean_object* v___x_5187_; 
lean_inc_ref(v_fst_5179_);
lean_dec(v_a_5175_);
v_val_5185_ = lean_ctor_get(v_fst_5179_, 0);
lean_inc(v_val_5185_);
lean_dec_ref_known(v_fst_5179_, 1);
if (v_isShared_5178_ == 0)
{
lean_ctor_set(v___x_5177_, 0, v_val_5185_);
v___x_5187_ = v___x_5177_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_val_5185_);
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
else
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5197_; 
v_a_5190_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5192_ = v___x_5174_;
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5174_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5197_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5195_; 
if (v_isShared_5193_ == 0)
{
v___x_5195_ = v___x_5192_;
goto v_reusejp_5194_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
v___x_5195_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5194_;
}
v_reusejp_5194_:
{
return v___x_5195_;
}
}
}
}
else
{
lean_object* v_vs_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; size_t v_sz_5201_; size_t v___x_5202_; lean_object* v___x_5203_; 
v_vs_5198_ = lean_ctor_get(v_n_5157_, 0);
v___x_5199_ = lean_box(0);
v___x_5200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5199_);
lean_ctor_set(v___x_5200_, 1, v_b_5158_);
v_sz_5201_ = lean_array_size(v_vs_5198_);
v___x_5202_ = ((size_t)0ULL);
v___x_5203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5198_, v_sz_5201_, v___x_5202_, v___x_5200_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_);
if (lean_obj_tag(v___x_5203_) == 0)
{
lean_object* v_a_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5218_; 
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5206_ = v___x_5203_;
v_isShared_5207_ = v_isSharedCheck_5218_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_a_5204_);
lean_dec(v___x_5203_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5218_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v_fst_5208_; 
v_fst_5208_ = lean_ctor_get(v_a_5204_, 0);
if (lean_obj_tag(v_fst_5208_) == 0)
{
lean_object* v_snd_5209_; lean_object* v___x_5210_; lean_object* v___x_5212_; 
v_snd_5209_ = lean_ctor_get(v_a_5204_, 1);
lean_inc(v_snd_5209_);
lean_dec(v_a_5204_);
v___x_5210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5210_, 0, v_snd_5209_);
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v___x_5210_);
v___x_5212_ = v___x_5206_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5210_);
v___x_5212_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
return v___x_5212_;
}
}
else
{
lean_object* v_val_5214_; lean_object* v___x_5216_; 
lean_inc_ref(v_fst_5208_);
lean_dec(v_a_5204_);
v_val_5214_ = lean_ctor_get(v_fst_5208_, 0);
lean_inc(v_val_5214_);
lean_dec_ref_known(v_fst_5208_, 1);
if (v_isShared_5207_ == 0)
{
lean_ctor_set(v___x_5206_, 0, v_val_5214_);
v___x_5216_ = v___x_5206_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_val_5214_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
}
else
{
lean_object* v_a_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5226_; 
v_a_5219_ = lean_ctor_get(v___x_5203_, 0);
v_isSharedCheck_5226_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5221_ = v___x_5203_;
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_a_5219_);
lean_dec(v___x_5203_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5226_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
lean_object* v___x_5224_; 
if (v_isShared_5222_ == 0)
{
v___x_5224_ = v___x_5221_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_a_5219_);
v___x_5224_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
return v___x_5224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5227_, lean_object* v_as_5228_, size_t v_sz_5229_, size_t v_i_5230_, lean_object* v_b_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
uint8_t v___x_5242_; 
v___x_5242_ = lean_usize_dec_lt(v_i_5230_, v_sz_5229_);
if (v___x_5242_ == 0)
{
lean_object* v___x_5243_; 
v___x_5243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5243_, 0, v_b_5231_);
return v___x_5243_;
}
else
{
lean_object* v_snd_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5278_; 
v_snd_5244_ = lean_ctor_get(v_b_5231_, 1);
v_isSharedCheck_5278_ = !lean_is_exclusive(v_b_5231_);
if (v_isSharedCheck_5278_ == 0)
{
lean_object* v_unused_5279_; 
v_unused_5279_ = lean_ctor_get(v_b_5231_, 0);
lean_dec(v_unused_5279_);
v___x_5246_ = v_b_5231_;
v_isShared_5247_ = v_isSharedCheck_5278_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_snd_5244_);
lean_dec(v_b_5231_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5278_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v_a_5248_; lean_object* v___x_5249_; 
v_a_5248_ = lean_array_uget_borrowed(v_as_5228_, v_i_5230_);
lean_inc(v_snd_5244_);
v___x_5249_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5227_, v_a_5248_, v_snd_5244_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
if (lean_obj_tag(v___x_5249_) == 0)
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5269_; 
v_a_5250_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5252_ = v___x_5249_;
v_isShared_5253_ = v_isSharedCheck_5269_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5249_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5269_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
if (lean_obj_tag(v_a_5250_) == 0)
{
lean_object* v___x_5254_; lean_object* v___x_5256_; 
v___x_5254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5254_, 0, v_a_5250_);
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 0, v___x_5254_);
v___x_5256_ = v___x_5246_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5254_);
lean_ctor_set(v_reuseFailAlloc_5260_, 1, v_snd_5244_);
v___x_5256_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
lean_object* v___x_5258_; 
if (v_isShared_5253_ == 0)
{
lean_ctor_set(v___x_5252_, 0, v___x_5256_);
v___x_5258_ = v___x_5252_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v___x_5256_);
v___x_5258_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5257_;
}
v_reusejp_5257_:
{
return v___x_5258_;
}
}
}
else
{
lean_object* v_a_5261_; lean_object* v___x_5262_; lean_object* v___x_5264_; 
lean_del_object(v___x_5252_);
lean_dec(v_snd_5244_);
v_a_5261_ = lean_ctor_get(v_a_5250_, 0);
lean_inc(v_a_5261_);
lean_dec_ref_known(v_a_5250_, 1);
v___x_5262_ = lean_box(0);
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 1, v_a_5261_);
lean_ctor_set(v___x_5246_, 0, v___x_5262_);
v___x_5264_ = v___x_5246_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v___x_5262_);
lean_ctor_set(v_reuseFailAlloc_5268_, 1, v_a_5261_);
v___x_5264_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
size_t v___x_5265_; size_t v___x_5266_; 
v___x_5265_ = ((size_t)1ULL);
v___x_5266_ = lean_usize_add(v_i_5230_, v___x_5265_);
v_i_5230_ = v___x_5266_;
v_b_5231_ = v___x_5264_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5277_; 
lean_del_object(v___x_5246_);
lean_dec(v_snd_5244_);
v_a_5270_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5277_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5277_ == 0)
{
v___x_5272_ = v___x_5249_;
v_isShared_5273_ = v_isSharedCheck_5277_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_a_5270_);
lean_dec(v___x_5249_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5277_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5275_; 
if (v_isShared_5273_ == 0)
{
v___x_5275_ = v___x_5272_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_a_5270_);
v___x_5275_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
return v___x_5275_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5280_, lean_object* v_as_5281_, lean_object* v_sz_5282_, lean_object* v_i_5283_, lean_object* v_b_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
size_t v_sz_boxed_5295_; size_t v_i_boxed_5296_; lean_object* v_res_5297_; 
v_sz_boxed_5295_ = lean_unbox_usize(v_sz_5282_);
lean_dec(v_sz_5282_);
v_i_boxed_5296_ = lean_unbox_usize(v_i_5283_);
lean_dec(v_i_5283_);
v_res_5297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5280_, v_as_5281_, v_sz_boxed_5295_, v_i_boxed_5296_, v_b_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec_ref(v___y_5290_);
lean_dec(v___y_5289_);
lean_dec_ref(v___y_5288_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
lean_dec(v___y_5285_);
lean_dec_ref(v_as_5281_);
lean_dec_ref(v_init_5280_);
return v_res_5297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5298_, lean_object* v_n_5299_, lean_object* v_b_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_){
_start:
{
lean_object* v_res_5311_; 
v_res_5311_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5298_, v_n_5299_, v_b_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_);
lean_dec(v___y_5309_);
lean_dec_ref(v___y_5308_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v_n_5299_);
lean_dec_ref(v_init_5298_);
return v_res_5311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5312_, lean_object* v_init_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
lean_object* v_root_5324_; lean_object* v_tail_5325_; lean_object* v___x_5326_; 
v_root_5324_ = lean_ctor_get(v_t_5312_, 0);
v_tail_5325_ = lean_ctor_get(v_t_5312_, 1);
lean_inc_ref(v_init_5313_);
v___x_5326_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5313_, v_root_5324_, v_init_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
lean_dec_ref(v_init_5313_);
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5363_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5329_ = v___x_5326_;
v_isShared_5330_ = v_isSharedCheck_5363_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5326_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5363_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
if (lean_obj_tag(v_a_5327_) == 0)
{
lean_object* v_a_5331_; lean_object* v___x_5333_; 
v_a_5331_ = lean_ctor_get(v_a_5327_, 0);
lean_inc(v_a_5331_);
lean_dec_ref_known(v_a_5327_, 1);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 0, v_a_5331_);
v___x_5333_ = v___x_5329_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v_a_5331_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
else
{
lean_object* v_a_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; size_t v_sz_5338_; size_t v___x_5339_; lean_object* v___x_5340_; 
lean_del_object(v___x_5329_);
v_a_5335_ = lean_ctor_get(v_a_5327_, 0);
lean_inc(v_a_5335_);
lean_dec_ref_known(v_a_5327_, 1);
v___x_5336_ = lean_box(0);
v___x_5337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5336_);
lean_ctor_set(v___x_5337_, 1, v_a_5335_);
v_sz_5338_ = lean_array_size(v_tail_5325_);
v___x_5339_ = ((size_t)0ULL);
v___x_5340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5325_, v_sz_5338_, v___x_5339_, v___x_5337_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v_a_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5354_; 
v_a_5341_ = lean_ctor_get(v___x_5340_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5343_ = v___x_5340_;
v_isShared_5344_ = v_isSharedCheck_5354_;
goto v_resetjp_5342_;
}
else
{
lean_inc(v_a_5341_);
lean_dec(v___x_5340_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5354_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v_fst_5345_; 
v_fst_5345_ = lean_ctor_get(v_a_5341_, 0);
if (lean_obj_tag(v_fst_5345_) == 0)
{
lean_object* v_snd_5346_; lean_object* v___x_5348_; 
v_snd_5346_ = lean_ctor_get(v_a_5341_, 1);
lean_inc(v_snd_5346_);
lean_dec(v_a_5341_);
if (v_isShared_5344_ == 0)
{
lean_ctor_set(v___x_5343_, 0, v_snd_5346_);
v___x_5348_ = v___x_5343_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_snd_5346_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
else
{
lean_object* v_val_5350_; lean_object* v___x_5352_; 
lean_inc_ref(v_fst_5345_);
lean_dec(v_a_5341_);
v_val_5350_ = lean_ctor_get(v_fst_5345_, 0);
lean_inc(v_val_5350_);
lean_dec_ref_known(v_fst_5345_, 1);
if (v_isShared_5344_ == 0)
{
lean_ctor_set(v___x_5343_, 0, v_val_5350_);
v___x_5352_ = v___x_5343_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_val_5350_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
}
}
else
{
lean_object* v_a_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5362_; 
v_a_5355_ = lean_ctor_get(v___x_5340_, 0);
v_isSharedCheck_5362_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5362_ == 0)
{
v___x_5357_ = v___x_5340_;
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_a_5355_);
lean_dec(v___x_5340_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5362_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5360_; 
if (v_isShared_5358_ == 0)
{
v___x_5360_ = v___x_5357_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
v___x_5360_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
return v___x_5360_;
}
}
}
}
}
}
else
{
lean_object* v_a_5364_; lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5371_; 
v_a_5364_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5371_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5371_ == 0)
{
v___x_5366_ = v___x_5326_;
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
else
{
lean_inc(v_a_5364_);
lean_dec(v___x_5326_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v___x_5369_; 
if (v_isShared_5367_ == 0)
{
v___x_5369_ = v___x_5366_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_a_5364_);
v___x_5369_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
return v___x_5369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5372_, lean_object* v_init_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
lean_object* v_res_5384_; 
v_res_5384_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5372_, v_init_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
lean_dec(v___y_5380_);
lean_dec_ref(v___y_5379_);
lean_dec(v___y_5378_);
lean_dec_ref(v___y_5377_);
lean_dec(v___y_5376_);
lean_dec_ref(v___y_5375_);
lean_dec(v___y_5374_);
lean_dec_ref(v_t_5372_);
return v_res_5384_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; 
v___x_5385_ = lean_unsigned_to_nat(32u);
v___x_5386_ = lean_mk_empty_array_with_capacity(v___x_5385_);
v___x_5387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5387_, 0, v___x_5386_);
return v___x_5387_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v_result_5393_; 
v___x_5388_ = ((size_t)5ULL);
v___x_5389_ = lean_unsigned_to_nat(0u);
v___x_5390_ = lean_unsigned_to_nat(32u);
v___x_5391_ = lean_mk_empty_array_with_capacity(v___x_5390_);
v___x_5392_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5393_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5393_, 0, v___x_5392_);
lean_ctor_set(v_result_5393_, 1, v___x_5391_);
lean_ctor_set(v_result_5393_, 2, v___x_5389_);
lean_ctor_set(v_result_5393_, 3, v___x_5389_);
lean_ctor_set_usize(v_result_5393_, 4, v___x_5388_);
return v_result_5393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_){
_start:
{
lean_object* v_result_5405_; lean_object* v___x_5406_; 
v_result_5405_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5406_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5394_, v_result_5405_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_, v_a_5403_);
return v___x_5406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_){
_start:
{
lean_object* v_res_5418_; 
v_res_5418_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5407_, v_a_5408_, v_a_5409_, v_a_5410_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_);
lean_dec(v_a_5416_);
lean_dec_ref(v_a_5415_);
lean_dec(v_a_5414_);
lean_dec_ref(v_a_5413_);
lean_dec(v_a_5412_);
lean_dec_ref(v_a_5411_);
lean_dec(v_a_5410_);
lean_dec_ref(v_a_5409_);
lean_dec(v_a_5408_);
lean_dec_ref(v_thms_5407_);
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5421_, lean_object* v_newThms_5422_, lean_object* v_gmt_5423_, lean_object* v_numInstances_5424_, lean_object* v_numDelayedInstances_5425_, lean_object* v_num_5426_, lean_object* v_preInstances_5427_, lean_object* v_nextThmIdx_5428_, lean_object* v_matchEqNames_5429_, lean_object* v_delayedThmInsts_5430_, lean_object* v_nextDeclIdx_5431_, lean_object* v_enodeMap_5432_, lean_object* v_exprs_5433_, lean_object* v_parents_5434_, lean_object* v_congrTable_5435_, lean_object* v_appMap_5436_, lean_object* v_indicesFound_5437_, lean_object* v_newFacts_5438_, uint8_t v_inconsistent_5439_, lean_object* v_nextIdx_5440_, lean_object* v_newRawFacts_5441_, lean_object* v_facts_5442_, lean_object* v_extThms_5443_, lean_object* v_inj_5444_, lean_object* v_split_5445_, lean_object* v_clean_5446_, lean_object* v_sstates_5447_, lean_object* v_mvarId_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v___x_5459_; 
v___x_5459_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5421_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_object* v_a_5460_; lean_object* v___x_5461_; 
v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
lean_inc(v_a_5460_);
lean_dec_ref_known(v___x_5459_, 1);
v___x_5461_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5422_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
if (lean_obj_tag(v___x_5461_) == 0)
{
lean_object* v_a_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5473_; 
v_a_5462_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5464_ = v___x_5461_;
v_isShared_5465_ = v_isSharedCheck_5473_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_a_5462_);
lean_dec(v___x_5461_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5473_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5471_; 
v___x_5466_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5467_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5467_, 0, v___x_5466_);
lean_ctor_set(v___x_5467_, 1, v_gmt_5423_);
lean_ctor_set(v___x_5467_, 2, v_a_5460_);
lean_ctor_set(v___x_5467_, 3, v_a_5462_);
lean_ctor_set(v___x_5467_, 4, v_numInstances_5424_);
lean_ctor_set(v___x_5467_, 5, v_numDelayedInstances_5425_);
lean_ctor_set(v___x_5467_, 6, v_num_5426_);
lean_ctor_set(v___x_5467_, 7, v_preInstances_5427_);
lean_ctor_set(v___x_5467_, 8, v_nextThmIdx_5428_);
lean_ctor_set(v___x_5467_, 9, v_matchEqNames_5429_);
lean_ctor_set(v___x_5467_, 10, v_delayedThmInsts_5430_);
v___x_5468_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_5468_, 0, v_nextDeclIdx_5431_);
lean_ctor_set(v___x_5468_, 1, v_enodeMap_5432_);
lean_ctor_set(v___x_5468_, 2, v_exprs_5433_);
lean_ctor_set(v___x_5468_, 3, v_parents_5434_);
lean_ctor_set(v___x_5468_, 4, v_congrTable_5435_);
lean_ctor_set(v___x_5468_, 5, v_appMap_5436_);
lean_ctor_set(v___x_5468_, 6, v_indicesFound_5437_);
lean_ctor_set(v___x_5468_, 7, v_newFacts_5438_);
lean_ctor_set(v___x_5468_, 8, v_nextIdx_5440_);
lean_ctor_set(v___x_5468_, 9, v_newRawFacts_5441_);
lean_ctor_set(v___x_5468_, 10, v_facts_5442_);
lean_ctor_set(v___x_5468_, 11, v_extThms_5443_);
lean_ctor_set(v___x_5468_, 12, v___x_5467_);
lean_ctor_set(v___x_5468_, 13, v_inj_5444_);
lean_ctor_set(v___x_5468_, 14, v_split_5445_);
lean_ctor_set(v___x_5468_, 15, v_clean_5446_);
lean_ctor_set(v___x_5468_, 16, v_sstates_5447_);
lean_ctor_set_uint8(v___x_5468_, sizeof(void*)*17, v_inconsistent_5439_);
v___x_5469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5469_, 0, v___x_5468_);
lean_ctor_set(v___x_5469_, 1, v_mvarId_5448_);
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 0, v___x_5469_);
v___x_5471_ = v___x_5464_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v___x_5469_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
}
else
{
lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5481_; 
lean_dec(v_a_5460_);
lean_dec(v_mvarId_5448_);
lean_dec_ref(v_sstates_5447_);
lean_dec_ref(v_clean_5446_);
lean_dec_ref(v_split_5445_);
lean_dec_ref(v_inj_5444_);
lean_dec_ref(v_extThms_5443_);
lean_dec_ref(v_facts_5442_);
lean_dec_ref(v_newRawFacts_5441_);
lean_dec(v_nextIdx_5440_);
lean_dec_ref(v_newFacts_5438_);
lean_dec_ref(v_indicesFound_5437_);
lean_dec_ref(v_appMap_5436_);
lean_dec_ref(v_congrTable_5435_);
lean_dec_ref(v_parents_5434_);
lean_dec_ref(v_exprs_5433_);
lean_dec_ref(v_enodeMap_5432_);
lean_dec(v_nextDeclIdx_5431_);
lean_dec_ref(v_delayedThmInsts_5430_);
lean_dec_ref(v_matchEqNames_5429_);
lean_dec(v_nextThmIdx_5428_);
lean_dec_ref(v_preInstances_5427_);
lean_dec(v_num_5426_);
lean_dec(v_numDelayedInstances_5425_);
lean_dec(v_numInstances_5424_);
lean_dec(v_gmt_5423_);
v_a_5474_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5481_ == 0)
{
v___x_5476_ = v___x_5461_;
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5461_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5479_; 
if (v_isShared_5477_ == 0)
{
v___x_5479_ = v___x_5476_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5474_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
}
else
{
lean_object* v_a_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5489_; 
lean_dec(v_mvarId_5448_);
lean_dec_ref(v_sstates_5447_);
lean_dec_ref(v_clean_5446_);
lean_dec_ref(v_split_5445_);
lean_dec_ref(v_inj_5444_);
lean_dec_ref(v_extThms_5443_);
lean_dec_ref(v_facts_5442_);
lean_dec_ref(v_newRawFacts_5441_);
lean_dec(v_nextIdx_5440_);
lean_dec_ref(v_newFacts_5438_);
lean_dec_ref(v_indicesFound_5437_);
lean_dec_ref(v_appMap_5436_);
lean_dec_ref(v_congrTable_5435_);
lean_dec_ref(v_parents_5434_);
lean_dec_ref(v_exprs_5433_);
lean_dec_ref(v_enodeMap_5432_);
lean_dec(v_nextDeclIdx_5431_);
lean_dec_ref(v_delayedThmInsts_5430_);
lean_dec_ref(v_matchEqNames_5429_);
lean_dec(v_nextThmIdx_5428_);
lean_dec_ref(v_preInstances_5427_);
lean_dec(v_num_5426_);
lean_dec(v_numDelayedInstances_5425_);
lean_dec(v_numInstances_5424_);
lean_dec(v_gmt_5423_);
v_a_5482_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5489_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5489_ == 0)
{
v___x_5484_ = v___x_5459_;
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_a_5482_);
lean_dec(v___x_5459_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5489_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5487_; 
if (v_isShared_5485_ == 0)
{
v___x_5487_ = v___x_5484_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_a_5482_);
v___x_5487_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
return v___x_5487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5490_ = _args[0];
lean_object* v_newThms_5491_ = _args[1];
lean_object* v_gmt_5492_ = _args[2];
lean_object* v_numInstances_5493_ = _args[3];
lean_object* v_numDelayedInstances_5494_ = _args[4];
lean_object* v_num_5495_ = _args[5];
lean_object* v_preInstances_5496_ = _args[6];
lean_object* v_nextThmIdx_5497_ = _args[7];
lean_object* v_matchEqNames_5498_ = _args[8];
lean_object* v_delayedThmInsts_5499_ = _args[9];
lean_object* v_nextDeclIdx_5500_ = _args[10];
lean_object* v_enodeMap_5501_ = _args[11];
lean_object* v_exprs_5502_ = _args[12];
lean_object* v_parents_5503_ = _args[13];
lean_object* v_congrTable_5504_ = _args[14];
lean_object* v_appMap_5505_ = _args[15];
lean_object* v_indicesFound_5506_ = _args[16];
lean_object* v_newFacts_5507_ = _args[17];
lean_object* v_inconsistent_5508_ = _args[18];
lean_object* v_nextIdx_5509_ = _args[19];
lean_object* v_newRawFacts_5510_ = _args[20];
lean_object* v_facts_5511_ = _args[21];
lean_object* v_extThms_5512_ = _args[22];
lean_object* v_inj_5513_ = _args[23];
lean_object* v_split_5514_ = _args[24];
lean_object* v_clean_5515_ = _args[25];
lean_object* v_sstates_5516_ = _args[26];
lean_object* v_mvarId_5517_ = _args[27];
lean_object* v___y_5518_ = _args[28];
lean_object* v___y_5519_ = _args[29];
lean_object* v___y_5520_ = _args[30];
lean_object* v___y_5521_ = _args[31];
lean_object* v___y_5522_ = _args[32];
lean_object* v___y_5523_ = _args[33];
lean_object* v___y_5524_ = _args[34];
lean_object* v___y_5525_ = _args[35];
lean_object* v___y_5526_ = _args[36];
lean_object* v___y_5527_ = _args[37];
_start:
{
uint8_t v_inconsistent_boxed_5528_; lean_object* v_res_5529_; 
v_inconsistent_boxed_5528_ = lean_unbox(v_inconsistent_5508_);
v_res_5529_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5490_, v_newThms_5491_, v_gmt_5492_, v_numInstances_5493_, v_numDelayedInstances_5494_, v_num_5495_, v_preInstances_5496_, v_nextThmIdx_5497_, v_matchEqNames_5498_, v_delayedThmInsts_5499_, v_nextDeclIdx_5500_, v_enodeMap_5501_, v_exprs_5502_, v_parents_5503_, v_congrTable_5504_, v_appMap_5505_, v_indicesFound_5506_, v_newFacts_5507_, v_inconsistent_boxed_5528_, v_nextIdx_5509_, v_newRawFacts_5510_, v_facts_5511_, v_extThms_5512_, v_inj_5513_, v_split_5514_, v_clean_5515_, v_sstates_5516_, v_mvarId_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
lean_dec(v___y_5526_);
lean_dec_ref(v___y_5525_);
lean_dec(v___y_5524_);
lean_dec_ref(v___y_5523_);
lean_dec(v___y_5522_);
lean_dec_ref(v___y_5521_);
lean_dec(v___y_5520_);
lean_dec_ref(v___y_5519_);
lean_dec(v___y_5518_);
lean_dec_ref(v_newThms_5491_);
lean_dec_ref(v_thms_5490_);
return v_res_5529_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5530_; 
v___x_5530_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_5530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5531_, size_t v_i_5532_, lean_object* v_bs_5533_){
_start:
{
uint8_t v___x_5534_; 
v___x_5534_ = lean_usize_dec_lt(v_i_5532_, v_sz_5531_);
if (v___x_5534_ == 0)
{
return v_bs_5533_;
}
else
{
lean_object* v_v_5535_; lean_object* v_casesTypes_5536_; lean_object* v_extThms_5537_; lean_object* v_funCC_5538_; lean_object* v_inj_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5553_; 
v_v_5535_ = lean_array_uget(v_bs_5533_, v_i_5532_);
v_casesTypes_5536_ = lean_ctor_get(v_v_5535_, 0);
v_extThms_5537_ = lean_ctor_get(v_v_5535_, 1);
v_funCC_5538_ = lean_ctor_get(v_v_5535_, 2);
v_inj_5539_ = lean_ctor_get(v_v_5535_, 4);
v_isSharedCheck_5553_ = !lean_is_exclusive(v_v_5535_);
if (v_isSharedCheck_5553_ == 0)
{
lean_object* v_unused_5554_; 
v_unused_5554_ = lean_ctor_get(v_v_5535_, 3);
lean_dec(v_unused_5554_);
v___x_5541_ = v_v_5535_;
v_isShared_5542_ = v_isSharedCheck_5553_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_inj_5539_);
lean_inc(v_funCC_5538_);
lean_inc(v_extThms_5537_);
lean_inc(v_casesTypes_5536_);
lean_dec(v_v_5535_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5553_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5543_; lean_object* v_bs_x27_5544_; lean_object* v___x_5545_; lean_object* v___x_5547_; 
v___x_5543_ = lean_unsigned_to_nat(0u);
v_bs_x27_5544_ = lean_array_uset(v_bs_5533_, v_i_5532_, v___x_5543_);
v___x_5545_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5542_ == 0)
{
lean_ctor_set(v___x_5541_, 3, v___x_5545_);
v___x_5547_ = v___x_5541_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v_casesTypes_5536_);
lean_ctor_set(v_reuseFailAlloc_5552_, 1, v_extThms_5537_);
lean_ctor_set(v_reuseFailAlloc_5552_, 2, v_funCC_5538_);
lean_ctor_set(v_reuseFailAlloc_5552_, 3, v___x_5545_);
lean_ctor_set(v_reuseFailAlloc_5552_, 4, v_inj_5539_);
v___x_5547_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
size_t v___x_5548_; size_t v___x_5549_; lean_object* v___x_5550_; 
v___x_5548_ = ((size_t)1ULL);
v___x_5549_ = lean_usize_add(v_i_5532_, v___x_5548_);
v___x_5550_ = lean_array_uset(v_bs_x27_5544_, v_i_5532_, v___x_5547_);
v_i_5532_ = v___x_5549_;
v_bs_5533_ = v___x_5550_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5555_, lean_object* v_i_5556_, lean_object* v_bs_5557_){
_start:
{
size_t v_sz_boxed_5558_; size_t v_i_boxed_5559_; lean_object* v_res_5560_; 
v_sz_boxed_5558_ = lean_unbox_usize(v_sz_5555_);
lean_dec(v_sz_5555_);
v_i_boxed_5559_ = lean_unbox_usize(v_i_5556_);
lean_dec(v_i_5556_);
v_res_5560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5558_, v_i_boxed_5559_, v_bs_5557_);
return v_res_5560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5561_, lean_object* v_ps_5562_, uint8_t v_only_5563_, lean_object* v_k_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_a_5571_, lean_object* v_a_5572_){
_start:
{
lean_object* v___y_5575_; lean_object* v___y_5576_; lean_object* v___y_5577_; lean_object* v___y_5578_; lean_object* v___y_5579_; lean_object* v___y_5580_; lean_object* v___y_5581_; lean_object* v___y_5582_; lean_object* v___y_5583_; uint8_t v___y_5596_; uint8_t v___y_5597_; lean_object* v_params_5598_; lean_object* v___y_5599_; lean_object* v___y_5600_; lean_object* v___y_5601_; lean_object* v___y_5602_; lean_object* v___y_5603_; lean_object* v___y_5604_; lean_object* v___y_5605_; lean_object* v___y_5606_; uint8_t v___y_5707_; 
if (v_only_5563_ == 0)
{
lean_object* v___x_5729_; lean_object* v___x_5730_; uint8_t v___x_5731_; 
v___x_5729_ = lean_array_get_size(v_ps_5562_);
v___x_5730_ = lean_unsigned_to_nat(0u);
v___x_5731_ = lean_nat_dec_eq(v___x_5729_, v___x_5730_);
if (v___x_5731_ == 0)
{
v___y_5707_ = v___x_5731_;
goto v___jp_5706_;
}
else
{
lean_object* v___x_5732_; 
lean_dec_ref(v_params_5561_);
lean_inc(v_a_5572_);
lean_inc_ref(v_a_5571_);
lean_inc(v_a_5570_);
lean_inc_ref(v_a_5569_);
lean_inc(v_a_5568_);
lean_inc_ref(v_a_5567_);
lean_inc(v_a_5566_);
lean_inc_ref(v_a_5565_);
v___x_5732_ = lean_apply_9(v_k_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_, v_a_5572_, lean_box(0));
return v___x_5732_;
}
}
else
{
uint8_t v___x_5733_; 
v___x_5733_ = 0;
v___y_5707_ = v___x_5733_;
goto v___jp_5706_;
}
v___jp_5574_:
{
lean_object* v___x_5584_; lean_object* v___x_5585_; 
v___x_5584_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5584_, 0, v___y_5575_);
v___x_5585_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5584_, v___y_5576_, v___y_5577_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_);
if (lean_obj_tag(v___x_5585_) == 0)
{
lean_object* v___x_5586_; 
lean_dec_ref_known(v___x_5585_, 1);
lean_inc(v___y_5583_);
lean_inc_ref(v___y_5582_);
lean_inc(v___y_5581_);
lean_inc_ref(v___y_5580_);
lean_inc(v___y_5579_);
lean_inc_ref(v___y_5578_);
lean_inc(v___y_5577_);
v___x_5586_ = lean_apply_9(v_k_5564_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, lean_box(0));
return v___x_5586_;
}
else
{
lean_object* v_a_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5594_; 
lean_dec_ref(v___y_5576_);
lean_dec_ref(v_k_5564_);
v_a_5587_ = lean_ctor_get(v___x_5585_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v___x_5585_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5589_ = v___x_5585_;
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_a_5587_);
lean_dec(v___x_5585_);
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
v___jp_5595_:
{
lean_object* v___x_5607_; 
v___x_5607_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5598_, v_ps_5562_, v_only_5563_, v___y_5597_, v___y_5596_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
if (lean_obj_tag(v___x_5607_) == 0)
{
lean_object* v_a_5608_; lean_object* v_ctx_5609_; lean_object* v_anchorRefs_x3f_5610_; lean_object* v_toContext_5611_; lean_object* v_sctx_5612_; lean_object* v_methods_5613_; uint8_t v_sym_5614_; lean_object* v_simp_5615_; lean_object* v_simpMethods_5616_; lean_object* v_config_5617_; uint8_t v_cheapCases_5618_; uint8_t v_reportMVarIssue_5619_; lean_object* v_splitSource_5620_; lean_object* v_ematchDiagSource_5621_; lean_object* v_symPrios_5622_; lean_object* v_extensions_5623_; uint8_t v_debug_5624_; uint8_t v_ematchDiag_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; 
v_a_5608_ = lean_ctor_get(v___x_5607_, 0);
lean_inc_n(v_a_5608_, 2);
lean_dec_ref_known(v___x_5607_, 1);
v_ctx_5609_ = lean_ctor_get(v___y_5599_, 1);
v_anchorRefs_x3f_5610_ = lean_ctor_get(v_a_5608_, 8);
v_toContext_5611_ = lean_ctor_get(v___y_5599_, 0);
v_sctx_5612_ = lean_ctor_get(v___y_5599_, 2);
v_methods_5613_ = lean_ctor_get(v___y_5599_, 3);
v_sym_5614_ = lean_ctor_get_uint8(v___y_5599_, sizeof(void*)*5);
v_simp_5615_ = lean_ctor_get(v_ctx_5609_, 0);
v_simpMethods_5616_ = lean_ctor_get(v_ctx_5609_, 1);
v_config_5617_ = lean_ctor_get(v_ctx_5609_, 2);
v_cheapCases_5618_ = lean_ctor_get_uint8(v_ctx_5609_, sizeof(void*)*8);
v_reportMVarIssue_5619_ = lean_ctor_get_uint8(v_ctx_5609_, sizeof(void*)*8 + 1);
v_splitSource_5620_ = lean_ctor_get(v_ctx_5609_, 4);
v_ematchDiagSource_5621_ = lean_ctor_get(v_ctx_5609_, 5);
v_symPrios_5622_ = lean_ctor_get(v_ctx_5609_, 6);
v_extensions_5623_ = lean_ctor_get(v_ctx_5609_, 7);
v_debug_5624_ = lean_ctor_get_uint8(v_ctx_5609_, sizeof(void*)*8 + 2);
v_ematchDiag_5625_ = lean_ctor_get_uint8(v_ctx_5609_, sizeof(void*)*8 + 3);
lean_inc_ref(v_extensions_5623_);
lean_inc_ref(v_symPrios_5622_);
lean_inc(v_ematchDiagSource_5621_);
lean_inc(v_splitSource_5620_);
lean_inc(v_anchorRefs_x3f_5610_);
lean_inc_ref(v_config_5617_);
lean_inc_ref(v_simpMethods_5616_);
lean_inc_ref(v_simp_5615_);
v___x_5626_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_5626_, 0, v_simp_5615_);
lean_ctor_set(v___x_5626_, 1, v_simpMethods_5616_);
lean_ctor_set(v___x_5626_, 2, v_config_5617_);
lean_ctor_set(v___x_5626_, 3, v_anchorRefs_x3f_5610_);
lean_ctor_set(v___x_5626_, 4, v_splitSource_5620_);
lean_ctor_set(v___x_5626_, 5, v_ematchDiagSource_5621_);
lean_ctor_set(v___x_5626_, 6, v_symPrios_5622_);
lean_ctor_set(v___x_5626_, 7, v_extensions_5623_);
lean_ctor_set_uint8(v___x_5626_, sizeof(void*)*8, v_cheapCases_5618_);
lean_ctor_set_uint8(v___x_5626_, sizeof(void*)*8 + 1, v_reportMVarIssue_5619_);
lean_ctor_set_uint8(v___x_5626_, sizeof(void*)*8 + 2, v_debug_5624_);
lean_ctor_set_uint8(v___x_5626_, sizeof(void*)*8 + 3, v_ematchDiag_5625_);
lean_inc_ref(v_methods_5613_);
lean_inc_ref(v_sctx_5612_);
lean_inc_ref(v_toContext_5611_);
v___x_5627_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_5627_, 0, v_toContext_5611_);
lean_ctor_set(v___x_5627_, 1, v___x_5626_);
lean_ctor_set(v___x_5627_, 2, v_sctx_5612_);
lean_ctor_set(v___x_5627_, 3, v_methods_5613_);
lean_ctor_set(v___x_5627_, 4, v_a_5608_);
lean_ctor_set_uint8(v___x_5627_, sizeof(void*)*5, v_sym_5614_);
if (v_only_5563_ == 0)
{
v___y_5575_ = v_a_5608_;
v___y_5576_ = v___x_5627_;
v___y_5577_ = v___y_5600_;
v___y_5578_ = v___y_5601_;
v___y_5579_ = v___y_5602_;
v___y_5580_ = v___y_5603_;
v___y_5581_ = v___y_5604_;
v___y_5582_ = v___y_5605_;
v___y_5583_ = v___y_5606_;
goto v___jp_5574_;
}
else
{
lean_object* v___x_5628_; 
v___x_5628_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5600_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
if (lean_obj_tag(v___x_5628_) == 0)
{
lean_object* v_a_5629_; lean_object* v_toGoalState_5630_; lean_object* v_ematch_5631_; lean_object* v_mvarId_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5688_; 
v_a_5629_ = lean_ctor_get(v___x_5628_, 0);
lean_inc(v_a_5629_);
lean_dec_ref_known(v___x_5628_, 1);
v_toGoalState_5630_ = lean_ctor_get(v_a_5629_, 0);
lean_inc_ref(v_toGoalState_5630_);
v_ematch_5631_ = lean_ctor_get(v_toGoalState_5630_, 12);
lean_inc_ref(v_ematch_5631_);
v_mvarId_5632_ = lean_ctor_get(v_a_5629_, 1);
v_isSharedCheck_5688_ = !lean_is_exclusive(v_a_5629_);
if (v_isSharedCheck_5688_ == 0)
{
lean_object* v_unused_5689_; 
v_unused_5689_ = lean_ctor_get(v_a_5629_, 0);
lean_dec(v_unused_5689_);
v___x_5634_ = v_a_5629_;
v_isShared_5635_ = v_isSharedCheck_5688_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_mvarId_5632_);
lean_dec(v_a_5629_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5688_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v_nextDeclIdx_5636_; lean_object* v_enodeMap_5637_; lean_object* v_exprs_5638_; lean_object* v_parents_5639_; lean_object* v_congrTable_5640_; lean_object* v_appMap_5641_; lean_object* v_indicesFound_5642_; lean_object* v_newFacts_5643_; uint8_t v_inconsistent_5644_; lean_object* v_nextIdx_5645_; lean_object* v_newRawFacts_5646_; lean_object* v_facts_5647_; lean_object* v_extThms_5648_; lean_object* v_inj_5649_; lean_object* v_split_5650_; lean_object* v_clean_5651_; lean_object* v_sstates_5652_; lean_object* v_gmt_5653_; lean_object* v_thms_5654_; lean_object* v_newThms_5655_; lean_object* v_numInstances_5656_; lean_object* v_numDelayedInstances_5657_; lean_object* v_num_5658_; lean_object* v_preInstances_5659_; lean_object* v_nextThmIdx_5660_; lean_object* v_matchEqNames_5661_; lean_object* v_delayedThmInsts_5662_; lean_object* v___x_5663_; lean_object* v___f_5664_; lean_object* v___x_5665_; 
v_nextDeclIdx_5636_ = lean_ctor_get(v_toGoalState_5630_, 0);
lean_inc(v_nextDeclIdx_5636_);
v_enodeMap_5637_ = lean_ctor_get(v_toGoalState_5630_, 1);
lean_inc_ref(v_enodeMap_5637_);
v_exprs_5638_ = lean_ctor_get(v_toGoalState_5630_, 2);
lean_inc_ref(v_exprs_5638_);
v_parents_5639_ = lean_ctor_get(v_toGoalState_5630_, 3);
lean_inc_ref(v_parents_5639_);
v_congrTable_5640_ = lean_ctor_get(v_toGoalState_5630_, 4);
lean_inc_ref(v_congrTable_5640_);
v_appMap_5641_ = lean_ctor_get(v_toGoalState_5630_, 5);
lean_inc_ref(v_appMap_5641_);
v_indicesFound_5642_ = lean_ctor_get(v_toGoalState_5630_, 6);
lean_inc_ref(v_indicesFound_5642_);
v_newFacts_5643_ = lean_ctor_get(v_toGoalState_5630_, 7);
lean_inc_ref(v_newFacts_5643_);
v_inconsistent_5644_ = lean_ctor_get_uint8(v_toGoalState_5630_, sizeof(void*)*17);
v_nextIdx_5645_ = lean_ctor_get(v_toGoalState_5630_, 8);
lean_inc(v_nextIdx_5645_);
v_newRawFacts_5646_ = lean_ctor_get(v_toGoalState_5630_, 9);
lean_inc_ref(v_newRawFacts_5646_);
v_facts_5647_ = lean_ctor_get(v_toGoalState_5630_, 10);
lean_inc_ref(v_facts_5647_);
v_extThms_5648_ = lean_ctor_get(v_toGoalState_5630_, 11);
lean_inc_ref(v_extThms_5648_);
v_inj_5649_ = lean_ctor_get(v_toGoalState_5630_, 13);
lean_inc_ref(v_inj_5649_);
v_split_5650_ = lean_ctor_get(v_toGoalState_5630_, 14);
lean_inc_ref(v_split_5650_);
v_clean_5651_ = lean_ctor_get(v_toGoalState_5630_, 15);
lean_inc_ref(v_clean_5651_);
v_sstates_5652_ = lean_ctor_get(v_toGoalState_5630_, 16);
lean_inc_ref(v_sstates_5652_);
lean_dec_ref(v_toGoalState_5630_);
v_gmt_5653_ = lean_ctor_get(v_ematch_5631_, 1);
lean_inc(v_gmt_5653_);
v_thms_5654_ = lean_ctor_get(v_ematch_5631_, 2);
lean_inc_ref(v_thms_5654_);
v_newThms_5655_ = lean_ctor_get(v_ematch_5631_, 3);
lean_inc_ref(v_newThms_5655_);
v_numInstances_5656_ = lean_ctor_get(v_ematch_5631_, 4);
lean_inc(v_numInstances_5656_);
v_numDelayedInstances_5657_ = lean_ctor_get(v_ematch_5631_, 5);
lean_inc(v_numDelayedInstances_5657_);
v_num_5658_ = lean_ctor_get(v_ematch_5631_, 6);
lean_inc(v_num_5658_);
v_preInstances_5659_ = lean_ctor_get(v_ematch_5631_, 7);
lean_inc_ref(v_preInstances_5659_);
v_nextThmIdx_5660_ = lean_ctor_get(v_ematch_5631_, 8);
lean_inc(v_nextThmIdx_5660_);
v_matchEqNames_5661_ = lean_ctor_get(v_ematch_5631_, 9);
lean_inc_ref(v_matchEqNames_5661_);
v_delayedThmInsts_5662_ = lean_ctor_get(v_ematch_5631_, 10);
lean_inc_ref(v_delayedThmInsts_5662_);
lean_dec_ref(v_ematch_5631_);
v___x_5663_ = lean_box(v_inconsistent_5644_);
v___f_5664_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 38, 28);
lean_closure_set(v___f_5664_, 0, v_thms_5654_);
lean_closure_set(v___f_5664_, 1, v_newThms_5655_);
lean_closure_set(v___f_5664_, 2, v_gmt_5653_);
lean_closure_set(v___f_5664_, 3, v_numInstances_5656_);
lean_closure_set(v___f_5664_, 4, v_numDelayedInstances_5657_);
lean_closure_set(v___f_5664_, 5, v_num_5658_);
lean_closure_set(v___f_5664_, 6, v_preInstances_5659_);
lean_closure_set(v___f_5664_, 7, v_nextThmIdx_5660_);
lean_closure_set(v___f_5664_, 8, v_matchEqNames_5661_);
lean_closure_set(v___f_5664_, 9, v_delayedThmInsts_5662_);
lean_closure_set(v___f_5664_, 10, v_nextDeclIdx_5636_);
lean_closure_set(v___f_5664_, 11, v_enodeMap_5637_);
lean_closure_set(v___f_5664_, 12, v_exprs_5638_);
lean_closure_set(v___f_5664_, 13, v_parents_5639_);
lean_closure_set(v___f_5664_, 14, v_congrTable_5640_);
lean_closure_set(v___f_5664_, 15, v_appMap_5641_);
lean_closure_set(v___f_5664_, 16, v_indicesFound_5642_);
lean_closure_set(v___f_5664_, 17, v_newFacts_5643_);
lean_closure_set(v___f_5664_, 18, v___x_5663_);
lean_closure_set(v___f_5664_, 19, v_nextIdx_5645_);
lean_closure_set(v___f_5664_, 20, v_newRawFacts_5646_);
lean_closure_set(v___f_5664_, 21, v_facts_5647_);
lean_closure_set(v___f_5664_, 22, v_extThms_5648_);
lean_closure_set(v___f_5664_, 23, v_inj_5649_);
lean_closure_set(v___f_5664_, 24, v_split_5650_);
lean_closure_set(v___f_5664_, 25, v_clean_5651_);
lean_closure_set(v___f_5664_, 26, v_sstates_5652_);
lean_closure_set(v___f_5664_, 27, v_mvarId_5632_);
v___x_5665_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5664_, v___x_5627_, v___y_5600_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
if (lean_obj_tag(v___x_5665_) == 0)
{
lean_object* v_a_5666_; lean_object* v___x_5667_; lean_object* v___x_5669_; 
v_a_5666_ = lean_ctor_get(v___x_5665_, 0);
lean_inc(v_a_5666_);
lean_dec_ref_known(v___x_5665_, 1);
v___x_5667_ = lean_box(0);
if (v_isShared_5635_ == 0)
{
lean_ctor_set_tag(v___x_5634_, 1);
lean_ctor_set(v___x_5634_, 1, v___x_5667_);
lean_ctor_set(v___x_5634_, 0, v_a_5666_);
v___x_5669_ = v___x_5634_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_a_5666_);
lean_ctor_set(v_reuseFailAlloc_5679_, 1, v___x_5667_);
v___x_5669_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
lean_object* v___x_5670_; 
v___x_5670_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5669_, v___y_5600_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
if (lean_obj_tag(v___x_5670_) == 0)
{
lean_dec_ref_known(v___x_5670_, 1);
v___y_5575_ = v_a_5608_;
v___y_5576_ = v___x_5627_;
v___y_5577_ = v___y_5600_;
v___y_5578_ = v___y_5601_;
v___y_5579_ = v___y_5602_;
v___y_5580_ = v___y_5603_;
v___y_5581_ = v___y_5604_;
v___y_5582_ = v___y_5605_;
v___y_5583_ = v___y_5606_;
goto v___jp_5574_;
}
else
{
lean_object* v_a_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5678_; 
lean_dec_ref_known(v___x_5627_, 5);
lean_dec(v_a_5608_);
lean_dec_ref(v_k_5564_);
v_a_5671_ = lean_ctor_get(v___x_5670_, 0);
v_isSharedCheck_5678_ = !lean_is_exclusive(v___x_5670_);
if (v_isSharedCheck_5678_ == 0)
{
v___x_5673_ = v___x_5670_;
v_isShared_5674_ = v_isSharedCheck_5678_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_a_5671_);
lean_dec(v___x_5670_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5678_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
lean_object* v___x_5676_; 
if (v_isShared_5674_ == 0)
{
v___x_5676_ = v___x_5673_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_a_5671_);
v___x_5676_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
return v___x_5676_;
}
}
}
}
}
else
{
lean_object* v_a_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5687_; 
lean_del_object(v___x_5634_);
lean_dec_ref_known(v___x_5627_, 5);
lean_dec(v_a_5608_);
lean_dec_ref(v_k_5564_);
v_a_5680_ = lean_ctor_get(v___x_5665_, 0);
v_isSharedCheck_5687_ = !lean_is_exclusive(v___x_5665_);
if (v_isSharedCheck_5687_ == 0)
{
v___x_5682_ = v___x_5665_;
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_a_5680_);
lean_dec(v___x_5665_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
lean_object* v___x_5685_; 
if (v_isShared_5683_ == 0)
{
v___x_5685_ = v___x_5682_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_a_5680_);
v___x_5685_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
return v___x_5685_;
}
}
}
}
}
else
{
lean_object* v_a_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5697_; 
lean_dec_ref_known(v___x_5627_, 5);
lean_dec(v_a_5608_);
lean_dec_ref(v_k_5564_);
v_a_5690_ = lean_ctor_get(v___x_5628_, 0);
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5628_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5692_ = v___x_5628_;
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_a_5690_);
lean_dec(v___x_5628_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5695_; 
if (v_isShared_5693_ == 0)
{
v___x_5695_ = v___x_5692_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v_a_5690_);
v___x_5695_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
return v___x_5695_;
}
}
}
}
}
else
{
lean_object* v_a_5698_; lean_object* v___x_5700_; uint8_t v_isShared_5701_; uint8_t v_isSharedCheck_5705_; 
lean_dec_ref(v_k_5564_);
v_a_5698_ = lean_ctor_get(v___x_5607_, 0);
v_isSharedCheck_5705_ = !lean_is_exclusive(v___x_5607_);
if (v_isSharedCheck_5705_ == 0)
{
v___x_5700_ = v___x_5607_;
v_isShared_5701_ = v_isSharedCheck_5705_;
goto v_resetjp_5699_;
}
else
{
lean_inc(v_a_5698_);
lean_dec(v___x_5607_);
v___x_5700_ = lean_box(0);
v_isShared_5701_ = v_isSharedCheck_5705_;
goto v_resetjp_5699_;
}
v_resetjp_5699_:
{
lean_object* v___x_5703_; 
if (v_isShared_5701_ == 0)
{
v___x_5703_ = v___x_5700_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_a_5698_);
v___x_5703_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
return v___x_5703_;
}
}
}
}
v___jp_5706_:
{
uint8_t v___x_5708_; 
v___x_5708_ = 1;
if (v_only_5563_ == 0)
{
v___y_5596_ = v___x_5708_;
v___y_5597_ = v___y_5707_;
v_params_5598_ = v_params_5561_;
v___y_5599_ = v_a_5565_;
v___y_5600_ = v_a_5566_;
v___y_5601_ = v_a_5567_;
v___y_5602_ = v_a_5568_;
v___y_5603_ = v_a_5569_;
v___y_5604_ = v_a_5570_;
v___y_5605_ = v_a_5571_;
v___y_5606_ = v_a_5572_;
goto v___jp_5595_;
}
else
{
lean_object* v_config_5709_; lean_object* v_extensions_5710_; lean_object* v_extra_5711_; lean_object* v_extraInj_5712_; lean_object* v_extraFacts_5713_; lean_object* v_symPrios_5714_; lean_object* v_norm_5715_; lean_object* v_normProcs_5716_; lean_object* v___x_5718_; uint8_t v_isShared_5719_; uint8_t v_isSharedCheck_5727_; 
v_config_5709_ = lean_ctor_get(v_params_5561_, 0);
v_extensions_5710_ = lean_ctor_get(v_params_5561_, 1);
v_extra_5711_ = lean_ctor_get(v_params_5561_, 2);
v_extraInj_5712_ = lean_ctor_get(v_params_5561_, 3);
v_extraFacts_5713_ = lean_ctor_get(v_params_5561_, 4);
v_symPrios_5714_ = lean_ctor_get(v_params_5561_, 5);
v_norm_5715_ = lean_ctor_get(v_params_5561_, 6);
v_normProcs_5716_ = lean_ctor_get(v_params_5561_, 7);
v_isSharedCheck_5727_ = !lean_is_exclusive(v_params_5561_);
if (v_isSharedCheck_5727_ == 0)
{
lean_object* v_unused_5728_; 
v_unused_5728_ = lean_ctor_get(v_params_5561_, 8);
lean_dec(v_unused_5728_);
v___x_5718_ = v_params_5561_;
v_isShared_5719_ = v_isSharedCheck_5727_;
goto v_resetjp_5717_;
}
else
{
lean_inc(v_normProcs_5716_);
lean_inc(v_norm_5715_);
lean_inc(v_symPrios_5714_);
lean_inc(v_extraFacts_5713_);
lean_inc(v_extraInj_5712_);
lean_inc(v_extra_5711_);
lean_inc(v_extensions_5710_);
lean_inc(v_config_5709_);
lean_dec(v_params_5561_);
v___x_5718_ = lean_box(0);
v_isShared_5719_ = v_isSharedCheck_5727_;
goto v_resetjp_5717_;
}
v_resetjp_5717_:
{
size_t v_sz_5720_; size_t v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v_params_5725_; 
v_sz_5720_ = lean_array_size(v_extensions_5710_);
v___x_5721_ = ((size_t)0ULL);
v___x_5722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5720_, v___x_5721_, v_extensions_5710_);
v___x_5723_ = lean_box(0);
if (v_isShared_5719_ == 0)
{
lean_ctor_set(v___x_5718_, 8, v___x_5723_);
lean_ctor_set(v___x_5718_, 1, v___x_5722_);
v_params_5725_ = v___x_5718_;
goto v_reusejp_5724_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_config_5709_);
lean_ctor_set(v_reuseFailAlloc_5726_, 1, v___x_5722_);
lean_ctor_set(v_reuseFailAlloc_5726_, 2, v_extra_5711_);
lean_ctor_set(v_reuseFailAlloc_5726_, 3, v_extraInj_5712_);
lean_ctor_set(v_reuseFailAlloc_5726_, 4, v_extraFacts_5713_);
lean_ctor_set(v_reuseFailAlloc_5726_, 5, v_symPrios_5714_);
lean_ctor_set(v_reuseFailAlloc_5726_, 6, v_norm_5715_);
lean_ctor_set(v_reuseFailAlloc_5726_, 7, v_normProcs_5716_);
lean_ctor_set(v_reuseFailAlloc_5726_, 8, v___x_5723_);
v_params_5725_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5724_;
}
v_reusejp_5724_:
{
v___y_5596_ = v___x_5708_;
v___y_5597_ = v___y_5707_;
v_params_5598_ = v_params_5725_;
v___y_5599_ = v_a_5565_;
v___y_5600_ = v_a_5566_;
v___y_5601_ = v_a_5567_;
v___y_5602_ = v_a_5568_;
v___y_5603_ = v_a_5569_;
v___y_5604_ = v_a_5570_;
v___y_5605_ = v_a_5571_;
v___y_5606_ = v_a_5572_;
goto v___jp_5595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_5734_, lean_object* v_ps_5735_, lean_object* v_only_5736_, lean_object* v_k_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_, lean_object* v_a_5746_){
_start:
{
uint8_t v_only_boxed_5747_; lean_object* v_res_5748_; 
v_only_boxed_5747_ = lean_unbox(v_only_5736_);
v_res_5748_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5734_, v_ps_5735_, v_only_boxed_5747_, v_k_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_);
lean_dec(v_a_5745_);
lean_dec_ref(v_a_5744_);
lean_dec(v_a_5743_);
lean_dec_ref(v_a_5742_);
lean_dec(v_a_5741_);
lean_dec_ref(v_a_5740_);
lean_dec(v_a_5739_);
lean_dec_ref(v_a_5738_);
lean_dec_ref(v_ps_5735_);
return v_res_5748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_5749_, lean_object* v_params_5750_, lean_object* v_ps_5751_, uint8_t v_only_5752_, lean_object* v_k_5753_, lean_object* v_a_5754_, lean_object* v_a_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_){
_start:
{
lean_object* v___x_5763_; 
v___x_5763_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5750_, v_ps_5751_, v_only_5752_, v_k_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_, v_a_5760_, v_a_5761_);
return v___x_5763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_5764_, lean_object* v_params_5765_, lean_object* v_ps_5766_, lean_object* v_only_5767_, lean_object* v_k_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_){
_start:
{
uint8_t v_only_boxed_5778_; lean_object* v_res_5779_; 
v_only_boxed_5778_ = lean_unbox(v_only_5767_);
v_res_5779_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_5764_, v_params_5765_, v_ps_5766_, v_only_boxed_5778_, v_k_5768_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_);
lean_dec(v_a_5776_);
lean_dec_ref(v_a_5775_);
lean_dec(v_a_5774_);
lean_dec_ref(v_a_5773_);
lean_dec(v_a_5772_);
lean_dec_ref(v_a_5771_);
lean_dec(v_a_5770_);
lean_dec_ref(v_a_5769_);
lean_dec_ref(v_ps_5766_);
return v_res_5779_;
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
