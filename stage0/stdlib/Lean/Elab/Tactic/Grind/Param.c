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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
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
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_ctor_set(v___x_89_, 0, v___y_85_);
lean_ctor_set(v___x_89_, 1, v___y_88_);
lean_ctor_set(v___x_89_, 2, v___y_82_);
lean_ctor_set(v___x_89_, 3, v___y_80_);
lean_ctor_set(v___x_89_, 4, v___y_84_);
lean_ctor_set(v___x_89_, 5, v___y_83_);
lean_ctor_set(v___x_89_, 6, v___y_87_);
lean_ctor_set(v___x_89_, 7, v___y_81_);
lean_ctor_set(v___x_89_, 8, v___y_86_);
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
v___y_80_ = v_extraInj_94_;
v___y_81_ = v_normProcs_98_;
v___y_82_ = v_extra_93_;
v___y_83_ = v_symPrios_96_;
v___y_84_ = v_extraFacts_95_;
v___y_85_ = v_config_91_;
v___y_86_ = v_anchorRefs_x3f_99_;
v___y_87_ = v_norm_97_;
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
v___y_80_ = v_extraInj_94_;
v___y_81_ = v_normProcs_98_;
v___y_82_ = v_extra_93_;
v___y_83_ = v_symPrios_96_;
v___y_84_ = v_extraFacts_95_;
v___y_85_ = v_config_91_;
v___y_86_ = v_anchorRefs_x3f_99_;
v___y_87_ = v_norm_97_;
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
uint8_t v___x_2008__boxed_324_; size_t v_i_boxed_325_; size_t v_stop_boxed_326_; uint8_t v_res_327_; lean_object* v_r_328_; 
v___x_2008__boxed_324_ = lean_unbox(v___x_320_);
v_i_boxed_325_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_stop_boxed_326_ = lean_unbox_usize(v_stop_323_);
lean_dec(v_stop_323_);
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch_spec__1(v_params_319_, v___x_2008__boxed_324_, v_as_321_, v_i_boxed_325_, v_stop_boxed_326_);
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
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
if (v___x_390_ == 0)
{
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
lean_dec(v_declName_347_);
goto v___jp_365_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
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
return v___x_403_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
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
lean_inc(v_declName_347_);
v___x_413_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_containsEMatch(v_params_346_, v_declName_347_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_inc(v_declName_347_);
v___x_414_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_347_, v_a_350_, v_a_351_);
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
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
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
uint8_t v___y_4254__boxed_636_; uint8_t v_suppressElabErrors_boxed_637_; uint8_t v_res_638_; lean_object* v_r_639_; 
v___y_4254__boxed_636_ = lean_unbox(v___y_633_);
v_suppressElabErrors_boxed_637_ = lean_unbox(v_suppressElabErrors_634_);
v_res_638_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0(v___y_4254__boxed_636_, v_suppressElabErrors_boxed_637_, v_x_635_);
lean_dec(v_x_635_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(lean_object* v_ref_641_, lean_object* v_msgData_642_, uint8_t v_severity_643_, uint8_t v_isSilent_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
uint8_t v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; uint8_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_688_; lean_object* v___y_689_; uint8_t v___y_690_; uint8_t v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; uint8_t v___y_694_; lean_object* v___y_695_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; uint8_t v___y_716_; lean_object* v___y_717_; uint8_t v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_724_; uint8_t v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; uint8_t v___y_730_; uint8_t v___x_735_; uint8_t v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; uint8_t v___y_742_; uint8_t v___y_743_; uint8_t v___y_745_; uint8_t v___x_760_; 
v___x_735_ = 2;
v___x_760_ = l_Lean_instBEqMessageSeverity_beq(v_severity_643_, v___x_735_);
if (v___x_760_ == 0)
{
v___y_745_ = v___x_760_;
goto v___jp_744_;
}
else
{
uint8_t v___x_761_; 
lean_inc_ref(v_msgData_642_);
v___x_761_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_642_);
v___y_745_ = v___x_761_;
goto v___jp_744_;
}
v___jp_650_:
{
lean_object* v___x_660_; lean_object* v_currNamespace_661_; lean_object* v_openDecls_662_; lean_object* v_env_663_; lean_object* v_nextMacroScope_664_; lean_object* v_ngen_665_; lean_object* v_auxDeclNGen_666_; lean_object* v_traceState_667_; lean_object* v_cache_668_; lean_object* v_messages_669_; lean_object* v_infoState_670_; lean_object* v_snapshotTasks_671_; lean_object* v_newDecls_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_686_; 
v___x_660_ = lean_st_ref_take(v___y_659_);
v_currNamespace_661_ = lean_ctor_get(v___y_658_, 6);
v_openDecls_662_ = lean_ctor_get(v___y_658_, 7);
v_env_663_ = lean_ctor_get(v___x_660_, 0);
v_nextMacroScope_664_ = lean_ctor_get(v___x_660_, 1);
v_ngen_665_ = lean_ctor_get(v___x_660_, 2);
v_auxDeclNGen_666_ = lean_ctor_get(v___x_660_, 3);
v_traceState_667_ = lean_ctor_get(v___x_660_, 4);
v_cache_668_ = lean_ctor_get(v___x_660_, 5);
v_messages_669_ = lean_ctor_get(v___x_660_, 6);
v_infoState_670_ = lean_ctor_get(v___x_660_, 7);
v_snapshotTasks_671_ = lean_ctor_get(v___x_660_, 8);
v_newDecls_672_ = lean_ctor_get(v___x_660_, 9);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_686_ == 0)
{
v___x_674_ = v___x_660_;
v_isShared_675_ = v_isSharedCheck_686_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_newDecls_672_);
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
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_686_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
lean_inc(v_openDecls_662_);
lean_inc(v_currNamespace_661_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_currNamespace_661_);
lean_ctor_set(v___x_676_, 1, v_openDecls_662_);
v___x_677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___y_657_);
lean_inc_ref(v___y_656_);
lean_inc_ref(v___y_655_);
v___x_678_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_678_, 0, v___y_655_);
lean_ctor_set(v___x_678_, 1, v___y_653_);
lean_ctor_set(v___x_678_, 2, v___y_652_);
lean_ctor_set(v___x_678_, 3, v___y_656_);
lean_ctor_set(v___x_678_, 4, v___x_677_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*5, v___y_654_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*5 + 1, v___y_651_);
lean_ctor_set_uint8(v___x_678_, sizeof(void*)*5 + 2, v_isSilent_644_);
v___x_679_ = l_Lean_MessageLog_add(v___x_678_, v_messages_669_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 6, v___x_679_);
v___x_681_ = v___x_674_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_env_663_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_nextMacroScope_664_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_ngen_665_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_auxDeclNGen_666_);
lean_ctor_set(v_reuseFailAlloc_685_, 4, v_traceState_667_);
lean_ctor_set(v_reuseFailAlloc_685_, 5, v_cache_668_);
lean_ctor_set(v_reuseFailAlloc_685_, 6, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_685_, 7, v_infoState_670_);
lean_ctor_set(v_reuseFailAlloc_685_, 8, v_snapshotTasks_671_);
lean_ctor_set(v_reuseFailAlloc_685_, 9, v_newDecls_672_);
v___x_681_ = v_reuseFailAlloc_685_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_st_ref_set(v___y_659_, v___x_681_);
v___x_683_ = lean_box(0);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
v___jp_687_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_711_; 
v___x_696_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_642_);
v___x_697_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_696_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_711_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_711_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_711_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
lean_inc_ref_n(v___y_692_, 2);
v___x_702_ = l_Lean_FileMap_toPosition(v___y_692_, v___y_689_);
lean_dec(v___y_689_);
v___x_703_ = l_Lean_FileMap_toPosition(v___y_692_, v___y_695_);
lean_dec(v___y_695_);
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
v___x_705_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_690_ == 0)
{
lean_del_object(v___x_700_);
lean_dec_ref(v___y_688_);
v___y_651_ = v___y_691_;
v___y_652_ = v___x_704_;
v___y_653_ = v___x_702_;
v___y_654_ = v___y_694_;
v___y_655_ = v___y_693_;
v___y_656_ = v___x_705_;
v___y_657_ = v_a_698_;
v___y_658_ = v___y_647_;
v___y_659_ = v___y_648_;
goto v___jp_650_;
}
else
{
uint8_t v___x_706_; 
lean_inc(v_a_698_);
v___x_706_ = l_Lean_MessageData_hasTag(v___y_688_, v_a_698_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_709_; 
lean_dec_ref(v___x_704_);
lean_dec_ref(v___x_702_);
lean_dec(v_a_698_);
v___x_707_ = lean_box(0);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_707_);
v___x_709_ = v___x_700_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_del_object(v___x_700_);
v___y_651_ = v___y_691_;
v___y_652_ = v___x_704_;
v___y_653_ = v___x_702_;
v___y_654_ = v___y_694_;
v___y_655_ = v___y_693_;
v___y_656_ = v___x_705_;
v___y_657_ = v_a_698_;
v___y_658_ = v___y_647_;
v___y_659_ = v___y_648_;
goto v___jp_650_;
}
}
}
}
v___jp_712_:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_Syntax_getTailPos_x3f(v___y_714_, v___y_718_);
lean_dec(v___y_714_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_inc(v___y_720_);
v___y_688_ = v___y_713_;
v___y_689_ = v___y_720_;
v___y_690_ = v___y_716_;
v___y_691_ = v___y_715_;
v___y_692_ = v___y_717_;
v___y_693_ = v___y_719_;
v___y_694_ = v___y_718_;
v___y_695_ = v___y_720_;
goto v___jp_687_;
}
else
{
lean_object* v_val_722_; 
v_val_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_val_722_);
lean_dec_ref(v___x_721_);
v___y_688_ = v___y_713_;
v___y_689_ = v___y_720_;
v___y_690_ = v___y_716_;
v___y_691_ = v___y_715_;
v___y_692_ = v___y_717_;
v___y_693_ = v___y_719_;
v___y_694_ = v___y_718_;
v___y_695_ = v_val_722_;
goto v___jp_687_;
}
}
v___jp_723_:
{
lean_object* v_ref_731_; lean_object* v___x_732_; 
v_ref_731_ = l_Lean_replaceRef(v_ref_641_, v___y_726_);
v___x_732_ = l_Lean_Syntax_getPos_x3f(v_ref_731_, v___y_729_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v___x_733_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___y_713_ = v___y_724_;
v___y_714_ = v_ref_731_;
v___y_715_ = v___y_730_;
v___y_716_ = v___y_725_;
v___y_717_ = v___y_727_;
v___y_718_ = v___y_729_;
v___y_719_ = v___y_728_;
v___y_720_ = v___x_733_;
goto v___jp_712_;
}
else
{
lean_object* v_val_734_; 
v_val_734_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_val_734_);
lean_dec_ref(v___x_732_);
v___y_713_ = v___y_724_;
v___y_714_ = v_ref_731_;
v___y_715_ = v___y_730_;
v___y_716_ = v___y_725_;
v___y_717_ = v___y_727_;
v___y_718_ = v___y_729_;
v___y_719_ = v___y_728_;
v___y_720_ = v_val_734_;
goto v___jp_712_;
}
}
v___jp_736_:
{
if (v___y_743_ == 0)
{
v___y_724_ = v___y_739_;
v___y_725_ = v___y_737_;
v___y_726_ = v___y_738_;
v___y_727_ = v___y_740_;
v___y_728_ = v___y_741_;
v___y_729_ = v___y_742_;
v___y_730_ = v_severity_643_;
goto v___jp_723_;
}
else
{
v___y_724_ = v___y_739_;
v___y_725_ = v___y_737_;
v___y_726_ = v___y_738_;
v___y_727_ = v___y_740_;
v___y_728_ = v___y_741_;
v___y_729_ = v___y_742_;
v___y_730_ = v___x_735_;
goto v___jp_723_;
}
}
v___jp_744_:
{
if (v___y_745_ == 0)
{
lean_object* v_fileName_746_; lean_object* v_fileMap_747_; lean_object* v_options_748_; lean_object* v_ref_749_; uint8_t v_suppressElabErrors_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___f_753_; uint8_t v___x_754_; uint8_t v___x_755_; 
v_fileName_746_ = lean_ctor_get(v___y_647_, 0);
v_fileMap_747_ = lean_ctor_get(v___y_647_, 1);
v_options_748_ = lean_ctor_get(v___y_647_, 2);
v_ref_749_ = lean_ctor_get(v___y_647_, 5);
v_suppressElabErrors_750_ = lean_ctor_get_uint8(v___y_647_, sizeof(void*)*14 + 1);
v___x_751_ = lean_box(v___y_745_);
v___x_752_ = lean_box(v_suppressElabErrors_750_);
v___f_753_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_753_, 0, v___x_751_);
lean_closure_set(v___f_753_, 1, v___x_752_);
v___x_754_ = 1;
v___x_755_ = l_Lean_instBEqMessageSeverity_beq(v_severity_643_, v___x_754_);
if (v___x_755_ == 0)
{
v___y_737_ = v_suppressElabErrors_750_;
v___y_738_ = v_ref_749_;
v___y_739_ = v___f_753_;
v___y_740_ = v_fileMap_747_;
v___y_741_ = v_fileName_746_;
v___y_742_ = v___y_745_;
v___y_743_ = v___x_755_;
goto v___jp_736_;
}
else
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = l_Lean_warningAsError;
v___x_757_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_748_, v___x_756_);
v___y_737_ = v_suppressElabErrors_750_;
v___y_738_ = v_ref_749_;
v___y_739_ = v___f_753_;
v___y_740_ = v_fileMap_747_;
v___y_741_ = v_fileName_746_;
v___y_742_ = v___y_745_;
v___y_743_ = v___x_757_;
goto v___jp_736_;
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_dec_ref(v_msgData_642_);
v___x_758_ = lean_box(0);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_762_, lean_object* v_msgData_763_, lean_object* v_severity_764_, lean_object* v_isSilent_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
uint8_t v_severity_boxed_771_; uint8_t v_isSilent_boxed_772_; lean_object* v_res_773_; 
v_severity_boxed_771_ = lean_unbox(v_severity_764_);
v_isSilent_boxed_772_ = lean_unbox(v_isSilent_765_);
v_res_773_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_762_, v_msgData_763_, v_severity_boxed_771_, v_isSilent_boxed_772_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v_ref_762_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(lean_object* v_msgData_774_, uint8_t v_severity_775_, uint8_t v_isSilent_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_ref_782_; lean_object* v___x_783_; 
v_ref_782_ = lean_ctor_get(v___y_779_, 5);
v___x_783_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1(v_ref_782_, v_msgData_774_, v_severity_775_, v_isSilent_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0___boxed(lean_object* v_msgData_784_, lean_object* v_severity_785_, lean_object* v_isSilent_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
uint8_t v_severity_boxed_792_; uint8_t v_isSilent_boxed_793_; lean_object* v_res_794_; 
v_severity_boxed_792_ = lean_unbox(v_severity_785_);
v_isSilent_boxed_793_ = lean_unbox(v_isSilent_786_);
v_res_794_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_784_, v_severity_boxed_792_, v_isSilent_boxed_793_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(lean_object* v_msgData_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
uint8_t v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; 
v___x_801_ = 1;
v___x_802_ = 0;
v___x_803_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0(v_msgData_795_, v___x_801_, v___x_802_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0___boxed(lean_object* v_msgData_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v_msgData_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_810_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__0));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
if (lean_obj_tag(v_a_814_) == 0)
{
lean_object* v___x_816_; 
v___x_816_ = l_List_reverse___redArg(v_a_815_);
return v___x_816_;
}
else
{
lean_object* v_head_817_; lean_object* v_tail_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_831_; 
v_head_817_ = lean_ctor_get(v_a_814_, 0);
v_tail_818_ = lean_ctor_get(v_a_814_, 1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_a_814_);
if (v_isSharedCheck_831_ == 0)
{
v___x_820_ = v_a_814_;
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_tail_818_);
lean_inc(v_head_817_);
lean_dec(v_a_814_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v_minIndexable_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v_minIndexable_822_ = 0;
v___x_823_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_824_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_817_, v_minIndexable_822_);
lean_dec(v_head_817_);
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_823_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v_a_815_);
lean_ctor_set(v___x_820_, 0, v___x_826_);
v___x_828_ = v___x_820_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_a_815_);
v___x_828_ = v_reuseFailAlloc_830_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v_a_814_ = v_tail_818_;
v_a_815_ = v___x_828_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
if (lean_obj_tag(v_a_832_) == 0)
{
lean_object* v___x_834_; 
v___x_834_ = l_List_reverse___redArg(v_a_833_);
return v___x_834_;
}
else
{
lean_object* v_head_835_; lean_object* v_tail_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_844_; 
v_head_835_ = lean_ctor_get(v_a_832_, 0);
v_tail_836_ = lean_ctor_get(v_a_832_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_a_832_);
if (v_isSharedCheck_844_ == 0)
{
v___x_838_ = v_a_832_;
v_isShared_839_ = v_isSharedCheck_844_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_tail_836_);
lean_inc(v_head_835_);
lean_dec(v_a_832_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_844_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v_a_833_);
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_head_835_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_a_833_);
v___x_841_ = v_reuseFailAlloc_843_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
v_a_832_ = v_tail_836_;
v_a_833_ = v___x_841_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__0));
v___x_847_ = l_Lean_stringToMessageData(v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__2));
v___x_850_ = l_Lean_stringToMessageData(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__4));
v___x_853_ = l_Lean_stringToMessageData(v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(lean_object* v_s_854_, lean_object* v_declName_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_kinds_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v_ks_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___x_886_; lean_object* v___x_887_; 
lean_inc(v_declName_855_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v_declName_855_);
v___x_887_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_ExtensionStateArray_getKindsFor(v_s_854_, v___x_886_);
lean_dec_ref(v___x_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v_declName_855_);
v___x_888_ = lean_box(0);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
else
{
lean_object* v_head_890_; lean_object* v_tail_891_; uint8_t v_minIndexable_892_; uint8_t v_gen_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; 
v_head_890_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_head_890_);
v_tail_891_ = lean_ctor_get(v___x_887_, 1);
lean_inc(v_tail_891_);
v_minIndexable_892_ = 0;
if (lean_obj_tag(v_tail_891_) == 0)
{
lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_913_; 
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; lean_object* v_unused_915_; 
v_unused_914_ = lean_ctor_get(v___x_887_, 1);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v___x_887_, 0);
lean_dec(v_unused_915_);
v___x_905_ = v___x_887_;
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
else
{
lean_dec(v___x_887_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_907_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_908_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v_head_890_, v_minIndexable_892_);
lean_dec(v_head_890_);
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
if (v_isShared_906_ == 0)
{
lean_ctor_set_tag(v___x_905_, 7);
lean_ctor_set(v___x_905_, 1, v___x_909_);
lean_ctor_set(v___x_905_, 0, v___x_907_);
v___x_911_ = v___x_905_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
v_kinds_862_ = v___x_911_;
v___y_863_ = v_a_856_;
v___y_864_ = v_a_857_;
v___y_865_ = v_a_858_;
v___y_866_ = v_a_859_;
goto v___jp_861_;
}
}
}
else
{
lean_object* v_head_916_; 
v_head_916_ = lean_ctor_get(v_tail_891_, 0);
switch(lean_obj_tag(v_head_916_))
{
case 1:
{
lean_object* v_tail_917_; 
v_tail_917_ = lean_ctor_get(v_tail_891_, 1);
lean_inc(v_tail_917_);
lean_dec_ref(v_tail_891_);
if (lean_obj_tag(v_tail_917_) == 0)
{
if (lean_obj_tag(v_head_890_) == 0)
{
uint8_t v_gen_918_; 
lean_dec_ref(v___x_887_);
v_gen_918_ = lean_ctor_get_uint8(v_head_890_, 0);
lean_dec_ref(v_head_890_);
v_gen_894_ = v_gen_918_;
v___y_895_ = v_a_856_;
v___y_896_ = v_a_857_;
v___y_897_ = v_a_858_;
v___y_898_ = v_a_859_;
goto v___jp_893_;
}
else
{
lean_dec(v_head_890_);
v_ks_877_ = v___x_887_;
v___y_878_ = v_a_856_;
v___y_879_ = v_a_857_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
goto v___jp_876_;
}
}
else
{
lean_dec(v_tail_917_);
lean_dec(v_head_890_);
v_ks_877_ = v___x_887_;
v___y_878_ = v_a_856_;
v___y_879_ = v_a_857_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
goto v___jp_876_;
}
}
case 0:
{
lean_object* v_tail_919_; 
v_tail_919_ = lean_ctor_get(v_tail_891_, 1);
lean_inc(v_tail_919_);
lean_dec_ref(v_tail_891_);
if (lean_obj_tag(v_tail_919_) == 0)
{
if (lean_obj_tag(v_head_890_) == 1)
{
uint8_t v_gen_920_; 
lean_dec_ref(v___x_887_);
v_gen_920_ = lean_ctor_get_uint8(v_head_890_, 0);
lean_dec_ref(v_head_890_);
v_gen_894_ = v_gen_920_;
v___y_895_ = v_a_856_;
v___y_896_ = v_a_857_;
v___y_897_ = v_a_858_;
v___y_898_ = v_a_859_;
goto v___jp_893_;
}
else
{
lean_dec(v_head_890_);
v_ks_877_ = v___x_887_;
v___y_878_ = v_a_856_;
v___y_879_ = v_a_857_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
goto v___jp_876_;
}
}
else
{
lean_dec(v_tail_919_);
lean_dec(v_head_890_);
v_ks_877_ = v___x_887_;
v___y_878_ = v_a_856_;
v___y_879_ = v_a_857_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
goto v___jp_876_;
}
}
default: 
{
lean_dec_ref(v_tail_891_);
lean_dec(v_head_890_);
v_ks_877_ = v___x_887_;
v___y_878_ = v_a_856_;
v___y_879_ = v_a_857_;
v___y_880_ = v_a_858_;
v___y_881_ = v_a_859_;
goto v___jp_876_;
}
}
}
v___jp_893_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_899_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1___closed__1);
v___x_900_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_900_, 0, v_gen_894_);
v___x_901_ = l_Lean_Meta_Grind_EMatchTheoremKind_toAttribute(v___x_900_, v_minIndexable_892_);
lean_dec_ref(v___x_900_);
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_899_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v_kinds_862_ = v___x_903_;
v___y_863_ = v___y_895_;
v___y_864_ = v___y_896_;
v___y_865_ = v___y_897_;
v___y_866_ = v___y_898_;
goto v___jp_861_;
}
}
v___jp_861_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_867_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__1);
v___x_868_ = l_Lean_MessageData_ofName(v_declName_855_);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__3);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v_kinds_862_);
v___x_873_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0(v___x_874_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
return v___x_875_;
}
v___jp_876_:
{
lean_object* v___x_882_; lean_object* v_ks_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_882_ = lean_box(0);
v_ks_883_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__1(v_ks_877_, v___x_882_);
v___x_884_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__2(v_ks_883_, v___x_882_);
v___x_885_ = l_Lean_MessageData_ofList(v___x_884_);
v_kinds_862_ = v___x_885_;
v___y_863_ = v___y_878_;
v___y_864_ = v___y_879_;
v___y_865_ = v___y_880_;
v___y_866_ = v___y_881_;
goto v___jp_861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___boxed(lean_object* v_s_921_, lean_object* v_declName_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_s_921_, v_declName_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_s_921_);
return v_res_928_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_929_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__0);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
lean_ctor_set(v___x_934_, 2, v___x_933_);
lean_ctor_set(v___x_934_, 3, v___x_933_);
lean_ctor_set(v___x_934_, 4, v___x_932_);
lean_ctor_set(v___x_934_, 5, v___x_932_);
lean_ctor_set(v___x_934_, 6, v___x_932_);
lean_ctor_set(v___x_934_, 7, v___x_932_);
lean_ctor_set(v___x_934_, 8, v___x_932_);
lean_ctor_set(v___x_934_, 9, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_unsigned_to_nat(32u);
v___x_936_ = lean_mk_empty_array_with_capacity(v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_938_ = ((size_t)5ULL);
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = lean_unsigned_to_nat(32u);
v___x_941_ = lean_mk_empty_array_with_capacity(v___x_940_);
v___x_942_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__3);
v___x_943_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_ctor_set(v___x_943_, 2, v___x_939_);
lean_ctor_set(v___x_943_, 3, v___x_939_);
lean_ctor_set_usize(v___x_943_, 4, v___x_938_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_944_ = lean_box(1);
v___x_945_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__4);
v___x_946_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__1);
v___x_947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_945_);
lean_ctor_set(v___x_947_, 2, v___x_944_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(lean_object* v_msgData_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; lean_object* v_env_953_; lean_object* v_options_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_952_ = lean_st_ref_get(v___y_950_);
v_env_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc_ref(v_env_953_);
lean_dec(v___x_952_);
v_options_954_ = lean_ctor_get(v___y_949_, 2);
v___x_955_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_956_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_954_);
v___x_957_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_957_, 0, v_env_953_);
lean_ctor_set(v___x_957_, 1, v___x_955_);
lean_ctor_set(v___x_957_, 2, v___x_956_);
lean_ctor_set(v___x_957_, 3, v_options_954_);
v___x_958_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v_msgData_948_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___boxed(lean_object* v_msgData_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msgData_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_ref_969_; lean_object* v___x_970_; lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_979_; 
v_ref_969_ = lean_ctor_get(v___y_966_, 5);
v___x_970_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0(v_msg_965_, v___y_966_, v___y_967_);
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_979_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_979_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
lean_inc(v_ref_969_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_ref_969_);
lean_ctor_set(v___x_975_, 1, v_a_971_);
if (v_isShared_974_ == 0)
{
lean_ctor_set_tag(v___x_973_, 1);
lean_ctor_set(v___x_973_, 0, v___x_975_);
v___x_977_ = v___x_973_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg___boxed(lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_984_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__6));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(lean_object* v_s_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v_env_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1002_ = lean_st_ref_get(v_a_1000_);
v_env_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc_ref(v_env_1003_);
lean_dec(v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
v___x_1005_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__5));
lean_inc_ref(v_s_998_);
v___x_1006_ = l_Lean_Parser_runParserCategory(v_env_1003_, v___x_1004_, v_s_998_, v___x_1005_);
if (lean_obj_tag(v___x_1006_) == 1)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; 
lean_dec_ref(v_s_998_);
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref(v___x_1006_);
v___x_1008_ = l_Lean_Meta_Grind_getAttrKindCore(v_a_1007_, v_a_999_, v_a_1000_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec_ref(v___x_1006_);
v___x_1009_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__7);
v___x_1010_ = l_Lean_stringToMessageData(v_s_998_);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1011_, v_a_999_, v_a_1000_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___boxed(lean_object* v_s_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier(v_s_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(lean_object* v_00_u03b1_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v_msg_1019_, v___y_1020_, v___y_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_msg_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0(v_00_u03b1_1024_, v_msg_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_ref_1036_; lean_object* v___x_1037_; lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1046_; 
v_ref_1036_ = lean_ctor_get(v___y_1033_, 5);
v___x_1037_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
lean_inc(v_ref_1036_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_ref_1036_);
lean_ctor_set(v___x_1042_, 1, v_a_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set_tag(v___x_1040_, 1);
lean_ctor_set(v___x_1040_, 0, v___x_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg___boxed(lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1053_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__0));
v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(uint8_t v_minIndexable_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
if (v_minIndexable_1057_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___closed__1);
v___x_1066_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1065_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable___boxed(lean_object* v_minIndexable_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
uint8_t v_minIndexable_boxed_1073_; lean_object* v_res_1074_; 
v_minIndexable_boxed_1073_ = lean_unbox(v_minIndexable_1067_);
v_res_1074_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_boxed_1073_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(lean_object* v_00_u03b1_1075_, lean_object* v_msg_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___boxed(lean_object* v_00_u03b1_1083_, lean_object* v_msg_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0(v_00_u03b1_1083_, v_msg_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1090_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1099_ = l_Lean_stringToMessageData(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1108_ = l_Lean_stringToMessageData(v___x_1107_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1112_, lean_object* v_declHint_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v_env_1117_; uint8_t v___x_1118_; 
v___x_1116_ = lean_st_ref_get(v___y_1114_);
v_env_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc_ref(v_env_1117_);
lean_dec(v___x_1116_);
v___x_1118_ = l_Lean_Name_isAnonymous(v_declHint_1113_);
if (v___x_1118_ == 0)
{
uint8_t v_isExporting_1119_; 
v_isExporting_1119_ = lean_ctor_get_uint8(v_env_1117_, sizeof(void*)*8);
if (v_isExporting_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v_env_1117_);
lean_dec(v_declHint_1113_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_msg_1112_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
lean_inc_ref(v_env_1117_);
v___x_1121_ = l_Lean_Environment_setExporting(v_env_1117_, v___x_1118_);
lean_inc(v_declHint_1113_);
lean_inc_ref(v___x_1121_);
v___x_1122_ = l_Lean_Environment_contains(v___x_1121_, v_declHint_1113_, v_isExporting_1119_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v___x_1121_);
lean_dec_ref(v_env_1117_);
lean_dec(v_declHint_1113_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_msg_1112_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_c_1129_; lean_object* v___x_1130_; 
v___x_1124_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__2);
v___x_1125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0_spec__0___closed__5);
v___x_1126_ = l_Lean_Options_empty;
v___x_1127_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1121_);
lean_ctor_set(v___x_1127_, 1, v___x_1124_);
lean_ctor_set(v___x_1127_, 2, v___x_1125_);
lean_ctor_set(v___x_1127_, 3, v___x_1126_);
lean_inc(v_declHint_1113_);
v___x_1128_ = l_Lean_MessageData_ofConstName(v_declHint_1113_, v___x_1118_);
v_c_1129_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1129_, 0, v___x_1127_);
lean_ctor_set(v_c_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1117_, v_declHint_1113_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec_ref(v_env_1117_);
lean_dec(v_declHint_1113_);
v___x_1131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v_c_1129_);
v___x_1133_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_MessageData_note(v___x_1134_);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_msg_1112_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
return v___x_1137_;
}
else
{
lean_object* v_val_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1173_; 
v_val_1138_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1140_ = v___x_1130_;
v_isShared_1141_ = v_isSharedCheck_1173_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_val_1138_);
lean_dec(v___x_1130_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1173_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v_mod_1145_; uint8_t v___x_1146_; 
v___x_1142_ = lean_box(0);
v___x_1143_ = l_Lean_Environment_header(v_env_1117_);
lean_dec_ref(v_env_1117_);
v___x_1144_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1143_);
v_mod_1145_ = lean_array_get(v___x_1142_, v___x_1144_, v_val_1138_);
lean_dec(v_val_1138_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = l_Lean_isPrivateName(v_declHint_1113_);
lean_dec(v_declHint_1113_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v_c_1129_);
v___x_1149_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = l_Lean_MessageData_ofName(v_mod_1145_);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_MessageData_note(v___x_1154_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v_msg_1112_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1156_);
v___x_1158_ = v___x_1140_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
lean_ctor_set(v___x_1161_, 1, v_c_1129_);
v___x_1162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_MessageData_ofName(v_mod_1145_);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l_Lean_MessageData_note(v___x_1167_);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_msg_1112_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1169_);
v___x_1171_ = v___x_1140_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1174_; 
lean_dec_ref(v_env_1117_);
lean_dec(v_declHint_1113_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_msg_1112_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1175_, lean_object* v_declHint_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1175_, v_declHint_1176_, v___y_1177_);
lean_dec(v___y_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* v_msg_1180_, lean_object* v_declHint_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1197_; 
v___x_1187_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1180_, v_declHint_1181_, v___y_1185_);
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1192_ = l_Lean_unknownIdentifierMessageTag;
v___x_1193_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v_a_1188_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1193_);
v___x_1195_ = v___x_1190_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* v_msg_1198_, lean_object* v_declHint_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1198_, v_declHint_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1206_, lean_object* v_msg_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_fileName_1213_; lean_object* v_fileMap_1214_; lean_object* v_options_1215_; lean_object* v_currRecDepth_1216_; lean_object* v_maxRecDepth_1217_; lean_object* v_ref_1218_; lean_object* v_currNamespace_1219_; lean_object* v_openDecls_1220_; lean_object* v_initHeartbeats_1221_; lean_object* v_maxHeartbeats_1222_; lean_object* v_quotContext_1223_; lean_object* v_currMacroScope_1224_; uint8_t v_diag_1225_; lean_object* v_cancelTk_x3f_1226_; uint8_t v_suppressElabErrors_1227_; lean_object* v_inheritedTraceOptions_1228_; lean_object* v_ref_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_fileName_1213_ = lean_ctor_get(v___y_1210_, 0);
v_fileMap_1214_ = lean_ctor_get(v___y_1210_, 1);
v_options_1215_ = lean_ctor_get(v___y_1210_, 2);
v_currRecDepth_1216_ = lean_ctor_get(v___y_1210_, 3);
v_maxRecDepth_1217_ = lean_ctor_get(v___y_1210_, 4);
v_ref_1218_ = lean_ctor_get(v___y_1210_, 5);
v_currNamespace_1219_ = lean_ctor_get(v___y_1210_, 6);
v_openDecls_1220_ = lean_ctor_get(v___y_1210_, 7);
v_initHeartbeats_1221_ = lean_ctor_get(v___y_1210_, 8);
v_maxHeartbeats_1222_ = lean_ctor_get(v___y_1210_, 9);
v_quotContext_1223_ = lean_ctor_get(v___y_1210_, 10);
v_currMacroScope_1224_ = lean_ctor_get(v___y_1210_, 11);
v_diag_1225_ = lean_ctor_get_uint8(v___y_1210_, sizeof(void*)*14);
v_cancelTk_x3f_1226_ = lean_ctor_get(v___y_1210_, 12);
v_suppressElabErrors_1227_ = lean_ctor_get_uint8(v___y_1210_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1228_ = lean_ctor_get(v___y_1210_, 13);
v_ref_1229_ = l_Lean_replaceRef(v_ref_1206_, v_ref_1218_);
lean_inc_ref(v_inheritedTraceOptions_1228_);
lean_inc(v_cancelTk_x3f_1226_);
lean_inc(v_currMacroScope_1224_);
lean_inc(v_quotContext_1223_);
lean_inc(v_maxHeartbeats_1222_);
lean_inc(v_initHeartbeats_1221_);
lean_inc(v_openDecls_1220_);
lean_inc(v_currNamespace_1219_);
lean_inc(v_maxRecDepth_1217_);
lean_inc(v_currRecDepth_1216_);
lean_inc_ref(v_options_1215_);
lean_inc_ref(v_fileMap_1214_);
lean_inc_ref(v_fileName_1213_);
v___x_1230_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1230_, 0, v_fileName_1213_);
lean_ctor_set(v___x_1230_, 1, v_fileMap_1214_);
lean_ctor_set(v___x_1230_, 2, v_options_1215_);
lean_ctor_set(v___x_1230_, 3, v_currRecDepth_1216_);
lean_ctor_set(v___x_1230_, 4, v_maxRecDepth_1217_);
lean_ctor_set(v___x_1230_, 5, v_ref_1229_);
lean_ctor_set(v___x_1230_, 6, v_currNamespace_1219_);
lean_ctor_set(v___x_1230_, 7, v_openDecls_1220_);
lean_ctor_set(v___x_1230_, 8, v_initHeartbeats_1221_);
lean_ctor_set(v___x_1230_, 9, v_maxHeartbeats_1222_);
lean_ctor_set(v___x_1230_, 10, v_quotContext_1223_);
lean_ctor_set(v___x_1230_, 11, v_currMacroScope_1224_);
lean_ctor_set(v___x_1230_, 12, v_cancelTk_x3f_1226_);
lean_ctor_set(v___x_1230_, 13, v_inheritedTraceOptions_1228_);
lean_ctor_set_uint8(v___x_1230_, sizeof(void*)*14, v_diag_1225_);
lean_ctor_set_uint8(v___x_1230_, sizeof(void*)*14 + 1, v_suppressElabErrors_1227_);
v___x_1231_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v_msg_1207_, v___y_1208_, v___y_1209_, v___x_1230_, v___y_1211_);
lean_dec_ref(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1232_, lean_object* v_msg_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1232_, v_msg_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v_ref_1232_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1240_, lean_object* v_msg_1241_, lean_object* v_declHint_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; lean_object* v_a_1249_; lean_object* v___x_1250_; 
v___x_1248_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1241_, v_declHint_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref(v___x_1248_);
v___x_1250_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1240_, v_a_1249_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1251_, lean_object* v_msg_1252_, lean_object* v_declHint_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1251_, v_msg_1252_, v_declHint_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v_ref_1251_);
return v_res_1259_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1262_ = l_Lean_stringToMessageData(v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1263_, lean_object* v_constName_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1270_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1271_ = 0;
lean_inc(v_constName_1264_);
v___x_1272_ = l_Lean_MessageData_ofConstName(v_constName_1264_, v___x_1271_);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1270_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1263_, v___x_1275_, v_constName_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1277_, lean_object* v_constName_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1277_, v_constName_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v_ref_1277_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_constName_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_ref_1291_; lean_object* v___x_1292_; 
v_ref_1291_ = lean_ctor_get(v___y_1288_, 5);
v___x_1292_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1291_, v_constName_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(lean_object* v_constName_1300_, uint8_t v_skipRealize_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; lean_object* v_env_1308_; lean_object* v___x_1309_; 
v___x_1307_ = lean_st_ref_get(v___y_1305_);
v_env_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc_ref(v_env_1308_);
lean_dec(v___x_1307_);
lean_inc(v_constName_1300_);
v___x_1309_ = l_Lean_Environment_findAsync_x3f(v_env_1308_, v_constName_1300_, v_skipRealize_1301_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1300_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1310_;
}
else
{
lean_object* v_val_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v_constName_1300_);
v_val_1311_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1309_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_val_1311_);
lean_dec(v___x_1309_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set_tag(v___x_1313_, 0);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_val_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0___boxed(lean_object* v_constName_1319_, lean_object* v_skipRealize_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
uint8_t v_skipRealize_boxed_1326_; lean_object* v_res_1327_; 
v_skipRealize_boxed_1326_ = lean_unbox(v_skipRealize_1320_);
v_res_1327_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_constName_1319_, v_skipRealize_boxed_1326_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(lean_object* v_declName_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; lean_object* v_env_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1331_ = lean_st_ref_get(v___y_1329_);
v_env_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc_ref(v_env_1332_);
lean_dec(v___x_1331_);
v___x_1333_ = lean_get_reducibility_status(v_env_1332_, v_declName_1328_);
v___x_1334_ = lean_box(v___x_1333_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_declName_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1336_, v___y_1337_);
lean_dec(v___y_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(lean_object* v_declName_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1362_; 
v___x_1346_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1340_, v___y_1344_);
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1362_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1362_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
uint8_t v___x_1351_; 
v___x_1351_ = lean_unbox(v_a_1347_);
lean_dec(v_a_1347_);
if (v___x_1351_ == 0)
{
uint8_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1352_ = 1;
v___x_1353_ = lean_box(v___x_1352_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1353_);
v___x_1355_ = v___x_1349_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
else
{
uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1357_ = 0;
v___x_1358_ = lean_box(v___x_1357_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1358_);
v___x_1360_ = v___x_1349_;
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1___boxed(lean_object* v_declName_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
return v_res_1369_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__0));
v___x_1372_ = l_Lean_stringToMessageData(v___x_1371_);
return v___x_1372_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__2));
v___x_1375_ = l_Lean_stringToMessageData(v___x_1374_);
return v___x_1375_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__4));
v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
return v___x_1378_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__6));
v___x_1381_ = l_Lean_stringToMessageData(v___x_1380_);
return v___x_1381_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l_Lean_Elab_Tactic_addEMatchTheorem___closed__8));
v___x_1384_ = l_Lean_stringToMessageData(v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem(lean_object* v_params_1385_, lean_object* v_id_1386_, lean_object* v_declName_1387_, lean_object* v_kind_1388_, uint8_t v_minIndexable_1389_, uint8_t v_suggest_1390_, uint8_t v_warn_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v___y_1398_; lean_object* v_thm_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; uint8_t v___x_1453_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___x_1650_; 
v___x_1453_ = 0;
lean_inc(v_declName_1387_);
v___x_1650_ = l_Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0(v_declName_1387_, v___x_1453_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; uint8_t v_kind_1652_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref(v___x_1650_);
v_kind_1652_ = lean_ctor_get_uint8(v_a_1651_, sizeof(void*)*3);
lean_dec(v_a_1651_);
switch(v_kind_1652_)
{
case 1:
{
v___y_1581_ = v_a_1392_;
v___y_1582_ = v_a_1393_;
v___y_1583_ = v_a_1394_;
v___y_1584_ = v_a_1395_;
goto v___jp_1580_;
}
case 2:
{
v___y_1581_ = v_a_1392_;
v___y_1582_ = v_a_1393_;
v___y_1583_ = v_a_1394_;
v___y_1584_ = v_a_1395_;
goto v___jp_1580_;
}
case 6:
{
v___y_1581_ = v_a_1392_;
v___y_1582_ = v_a_1393_;
v___y_1583_ = v_a_1394_;
v___y_1584_ = v_a_1395_;
goto v___jp_1580_;
}
case 0:
{
lean_object* v___x_1653_; 
lean_dec(v_id_1386_);
lean_inc(v_declName_1387_);
v___x_1653_ = l_Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1(v_declName_1387_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; uint8_t v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref(v___x_1653_);
v___x_1655_ = lean_unbox(v_a_1654_);
lean_dec(v_a_1654_);
if (v___x_1655_ == 0)
{
v___y_1511_ = v_a_1392_;
v___y_1512_ = v_a_1393_;
v___y_1513_ = v_a_1394_;
v___y_1514_ = v_a_1395_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_kind_1388_);
lean_dec_ref(v_params_1385_);
v___x_1656_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1657_ = l_Lean_MessageData_ofConstName(v_declName_1387_, v___x_1453_);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__7, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__7_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__7);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1660_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec(v_kind_1388_);
lean_dec(v_declName_1387_);
lean_dec_ref(v_params_1385_);
v_a_1670_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1653_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1653_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
default: 
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec(v_kind_1388_);
lean_dec(v_id_1386_);
lean_dec_ref(v_params_1385_);
v___x_1678_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1679_ = l_Lean_MessageData_ofConstName(v_declName_1387_, v___x_1453_);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__9, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__9_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__9);
v___x_1682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1682_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v___x_1683_;
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec(v_kind_1388_);
lean_dec(v_declName_1387_);
lean_dec(v_id_1386_);
lean_dec_ref(v_params_1385_);
v_a_1684_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1650_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1650_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
v___jp_1397_:
{
lean_object* v_config_1399_; lean_object* v_extensions_1400_; lean_object* v_extra_1401_; lean_object* v_extraInj_1402_; lean_object* v_extraFacts_1403_; lean_object* v_symPrios_1404_; lean_object* v_norm_1405_; lean_object* v_normProcs_1406_; lean_object* v_anchorRefs_x3f_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1416_; 
v_config_1399_ = lean_ctor_get(v_params_1385_, 0);
v_extensions_1400_ = lean_ctor_get(v_params_1385_, 1);
v_extra_1401_ = lean_ctor_get(v_params_1385_, 2);
v_extraInj_1402_ = lean_ctor_get(v_params_1385_, 3);
v_extraFacts_1403_ = lean_ctor_get(v_params_1385_, 4);
v_symPrios_1404_ = lean_ctor_get(v_params_1385_, 5);
v_norm_1405_ = lean_ctor_get(v_params_1385_, 6);
v_normProcs_1406_ = lean_ctor_get(v_params_1385_, 7);
v_anchorRefs_x3f_1407_ = lean_ctor_get(v_params_1385_, 8);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_params_1385_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1409_ = v_params_1385_;
v_isShared_1410_ = v_isSharedCheck_1416_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_anchorRefs_x3f_1407_);
lean_inc(v_normProcs_1406_);
lean_inc(v_norm_1405_);
lean_inc(v_symPrios_1404_);
lean_inc(v_extraFacts_1403_);
lean_inc(v_extraInj_1402_);
lean_inc(v_extra_1401_);
lean_inc(v_extensions_1400_);
lean_inc(v_config_1399_);
lean_dec(v_params_1385_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1416_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = l_Lean_PersistentArray_push___redArg(v_extra_1401_, v___y_1398_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 2, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_config_1399_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_extensions_1400_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_extraInj_1402_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_extraFacts_1403_);
lean_ctor_set(v_reuseFailAlloc_1415_, 5, v_symPrios_1404_);
lean_ctor_set(v_reuseFailAlloc_1415_, 6, v_norm_1405_);
lean_ctor_set(v_reuseFailAlloc_1415_, 7, v_normProcs_1406_);
lean_ctor_set(v_reuseFailAlloc_1415_, 8, v_anchorRefs_x3f_1407_);
v___x_1413_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
}
v___jp_1417_:
{
if (v_warn_1391_ == 0)
{
lean_dec(v_declName_1387_);
v___y_1398_ = v_thm_1418_;
goto v___jp_1397_;
}
else
{
lean_object* v_extensions_1423_; lean_object* v_patterns_1424_; lean_object* v_origin_1425_; lean_object* v_cnstrs_1426_; uint8_t v___x_1427_; 
v_extensions_1423_ = lean_ctor_get(v_params_1385_, 1);
v_patterns_1424_ = lean_ctor_get(v_thm_1418_, 3);
v_origin_1425_ = lean_ctor_get(v_thm_1418_, 5);
v_cnstrs_1426_ = lean_ctor_get(v_thm_1418_, 7);
v___x_1427_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1423_, v_origin_1425_, v_patterns_1424_, v_cnstrs_1426_);
if (v___x_1427_ == 0)
{
lean_dec(v_declName_1387_);
v___y_1398_ = v_thm_1418_;
goto v___jp_1397_;
}
else
{
lean_object* v___x_1428_; 
v___x_1428_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1423_, v_declName_1387_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_dec_ref(v___x_1428_);
v___y_1398_ = v_thm_1418_;
goto v___jp_1397_;
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec_ref(v_thm_1418_);
lean_dec_ref(v_params_1385_);
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
}
v___jp_1437_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1449_ = l_Lean_PersistentArray_push___redArg(v___y_1442_, v___y_1441_);
v___x_1450_ = l_Lean_PersistentArray_push___redArg(v___x_1449_, v___y_1438_);
v___x_1451_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1451_, 0, v___y_1448_);
lean_ctor_set(v___x_1451_, 1, v___y_1439_);
lean_ctor_set(v___x_1451_, 2, v___x_1450_);
lean_ctor_set(v___x_1451_, 3, v___y_1445_);
lean_ctor_set(v___x_1451_, 4, v___y_1444_);
lean_ctor_set(v___x_1451_, 5, v___y_1443_);
lean_ctor_set(v___x_1451_, 6, v___y_1446_);
lean_ctor_set(v___x_1451_, 7, v___y_1440_);
lean_ctor_set(v___x_1451_, 8, v___y_1447_);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
v___jp_1454_:
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1389_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v___x_1459_);
lean_inc(v_declName_1387_);
v___x_1460_ = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(v_declName_1387_, v___x_1453_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1493_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1493_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1493_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
if (lean_obj_tag(v_a_1461_) == 1)
{
lean_object* v_val_1465_; lean_object* v_config_1466_; lean_object* v_extensions_1467_; lean_object* v_extra_1468_; lean_object* v_extraInj_1469_; lean_object* v_extraFacts_1470_; lean_object* v_symPrios_1471_; lean_object* v_norm_1472_; lean_object* v_normProcs_1473_; lean_object* v_anchorRefs_x3f_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_declName_1387_);
v_val_1465_ = lean_ctor_get(v_a_1461_, 0);
lean_inc(v_val_1465_);
lean_dec_ref(v_a_1461_);
v_config_1466_ = lean_ctor_get(v_params_1385_, 0);
v_extensions_1467_ = lean_ctor_get(v_params_1385_, 1);
v_extra_1468_ = lean_ctor_get(v_params_1385_, 2);
v_extraInj_1469_ = lean_ctor_get(v_params_1385_, 3);
v_extraFacts_1470_ = lean_ctor_get(v_params_1385_, 4);
v_symPrios_1471_ = lean_ctor_get(v_params_1385_, 5);
v_norm_1472_ = lean_ctor_get(v_params_1385_, 6);
v_normProcs_1473_ = lean_ctor_get(v_params_1385_, 7);
v_anchorRefs_x3f_1474_ = lean_ctor_get(v_params_1385_, 8);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_params_1385_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1476_ = v_params_1385_;
v_isShared_1477_ = v_isSharedCheck_1486_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_anchorRefs_x3f_1474_);
lean_inc(v_normProcs_1473_);
lean_inc(v_norm_1472_);
lean_inc(v_symPrios_1471_);
lean_inc(v_extraFacts_1470_);
lean_inc(v_extraInj_1469_);
lean_inc(v_extra_1468_);
lean_inc(v_extensions_1467_);
lean_inc(v_config_1466_);
lean_dec(v_params_1385_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1486_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1478_ = l_Array_toPArray_x27___redArg(v_val_1465_);
lean_dec(v_val_1465_);
v___x_1479_ = l_Lean_PersistentArray_append___redArg(v_extra_1468_, v___x_1478_);
lean_dec_ref(v___x_1478_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 2, v___x_1479_);
v___x_1481_ = v___x_1476_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_config_1466_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_extensions_1467_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_extraInj_1469_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v_extraFacts_1470_);
lean_ctor_set(v_reuseFailAlloc_1485_, 5, v_symPrios_1471_);
lean_ctor_set(v_reuseFailAlloc_1485_, 6, v_norm_1472_);
lean_ctor_set(v_reuseFailAlloc_1485_, 7, v_normProcs_1473_);
lean_ctor_set(v_reuseFailAlloc_1485_, 8, v_anchorRefs_x3f_1474_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1481_);
v___x_1483_ = v___x_1463_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_del_object(v___x_1463_);
lean_dec(v_a_1461_);
lean_dec_ref(v_params_1385_);
v___x_1487_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__1, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__1_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__1);
v___x_1488_ = l_Lean_MessageData_ofConstName(v_declName_1387_, v___x_1453_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1491_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_declName_1387_);
lean_dec_ref(v_params_1385_);
v_a_1494_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1460_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1460_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_declName_1387_);
lean_dec_ref(v_params_1385_);
v_a_1502_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1459_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1459_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
v___jp_1510_:
{
uint8_t v___x_1515_; 
v___x_1515_ = l_Lean_Meta_Grind_EMatchTheoremKind_isEqLhs(v_kind_1388_);
if (v___x_1515_ == 0)
{
uint8_t v___x_1516_; 
v___x_1516_ = l_Lean_Meta_Grind_EMatchTheoremKind_isDefault(v_kind_1388_);
lean_dec(v_kind_1388_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec_ref(v_params_1385_);
v___x_1517_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__3, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__3_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__3);
v___x_1518_ = l_Lean_MessageData_ofConstName(v_declName_1387_, v___x_1453_);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_obj_once(&l_Lean_Elab_Tactic_addEMatchTheorem___closed__5, &l_Lean_Elab_Tactic_addEMatchTheorem___closed__5_once, _init_l_Lean_Elab_Tactic_addEMatchTheorem___closed__5);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_1521_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1522_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1522_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
else
{
v___y_1455_ = v___y_1511_;
v___y_1456_ = v___y_1512_;
v___y_1457_ = v___y_1513_;
v___y_1458_ = v___y_1514_;
goto v___jp_1454_;
}
}
else
{
lean_dec(v_kind_1388_);
v___y_1455_ = v___y_1511_;
v___y_1456_ = v___y_1512_;
v___y_1457_ = v___y_1513_;
v___y_1458_ = v___y_1514_;
goto v___jp_1454_;
}
}
v___jp_1531_:
{
lean_object* v_symPrios_1536_; lean_object* v___x_1537_; 
v_symPrios_1536_ = lean_ctor_get(v_params_1385_, 5);
lean_inc_ref(v_symPrios_1536_);
lean_inc(v_declName_1387_);
v___x_1537_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1387_, v_kind_1388_, v_symPrios_1536_, v___x_1453_, v_minIndexable_1389_, v___y_1532_, v___y_1534_, v___y_1533_, v___y_1535_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref(v___x_1537_);
v_thm_1418_ = v_a_1538_;
v___y_1419_ = v___y_1532_;
v___y_1420_ = v___y_1534_;
v___y_1421_ = v___y_1533_;
v___y_1422_ = v___y_1535_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_declName_1387_);
lean_dec_ref(v_params_1385_);
v_a_1539_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1537_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1537_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
v___jp_1547_:
{
if (v_suggest_1390_ == 0)
{
lean_dec(v_id_1386_);
v___y_1532_ = v___y_1548_;
v___y_1533_ = v___y_1550_;
v___y_1534_ = v___y_1549_;
v___y_1535_ = v___y_1551_;
goto v___jp_1531_;
}
else
{
lean_object* v_options_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v_options_1552_ = lean_ctor_get(v___y_1550_, 2);
v___x_1553_ = l_Lean_Meta_Grind_backward_grind_inferPattern;
v___x_1554_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_1552_, v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v_symPrios_1555_; lean_object* v___x_1556_; 
lean_dec(v_kind_1388_);
v_symPrios_1555_ = lean_ctor_get(v_params_1385_, 5);
lean_inc_ref(v_symPrios_1555_);
lean_inc(v_declName_1387_);
v___x_1556_ = l_Lean_Meta_Grind_mkEMatchTheoremAndSuggest(v_id_1386_, v_declName_1387_, v_symPrios_1555_, v_minIndexable_1389_, v_suggest_1390_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1556_);
v_thm_1418_ = v_a_1557_;
v___y_1419_ = v___y_1548_;
v___y_1420_ = v___y_1549_;
v___y_1421_ = v___y_1550_;
v___y_1422_ = v___y_1551_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v_declName_1387_);
lean_dec_ref(v_params_1385_);
v_a_1558_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1556_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_dec(v_id_1386_);
v___y_1532_ = v___y_1548_;
v___y_1533_ = v___y_1550_;
v___y_1534_ = v___y_1549_;
v___y_1535_ = v___y_1551_;
goto v___jp_1531_;
}
}
}
v___jp_1566_:
{
lean_object* v___x_1571_; 
v___x_1571_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1389_, v___y_1569_, v___y_1568_, v___y_1570_, v___y_1567_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_dec_ref(v___x_1571_);
v___y_1548_ = v___y_1569_;
v___y_1549_ = v___y_1568_;
v___y_1550_ = v___y_1570_;
v___y_1551_ = v___y_1567_;
goto v___jp_1547_;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_kind_1388_);
lean_dec(v_declName_1387_);
lean_dec(v_id_1386_);
lean_dec_ref(v_params_1385_);
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
v___jp_1580_:
{
if (lean_obj_tag(v_kind_1388_) == 2)
{
uint8_t v_gen_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v_id_1386_);
v_gen_1585_ = lean_ctor_get_uint8(v_kind_1388_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_kind_1388_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1587_ = v_kind_1388_;
v_isShared_1588_ = v_isSharedCheck_1649_;
goto v_resetjp_1586_;
}
else
{
lean_dec(v_kind_1388_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1649_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; 
v___x_1589_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_1389_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_config_1590_; lean_object* v_extensions_1591_; lean_object* v_extra_1592_; lean_object* v_extraInj_1593_; lean_object* v_extraFacts_1594_; lean_object* v_symPrios_1595_; lean_object* v_norm_1596_; lean_object* v_normProcs_1597_; lean_object* v_anchorRefs_x3f_1598_; lean_object* v___x_1600_; 
lean_dec_ref(v___x_1589_);
v_config_1590_ = lean_ctor_get(v_params_1385_, 0);
lean_inc_ref(v_config_1590_);
v_extensions_1591_ = lean_ctor_get(v_params_1385_, 1);
lean_inc_ref(v_extensions_1591_);
v_extra_1592_ = lean_ctor_get(v_params_1385_, 2);
lean_inc_ref(v_extra_1592_);
v_extraInj_1593_ = lean_ctor_get(v_params_1385_, 3);
lean_inc_ref(v_extraInj_1593_);
v_extraFacts_1594_ = lean_ctor_get(v_params_1385_, 4);
lean_inc_ref(v_extraFacts_1594_);
v_symPrios_1595_ = lean_ctor_get(v_params_1385_, 5);
lean_inc_ref(v_symPrios_1595_);
v_norm_1596_ = lean_ctor_get(v_params_1385_, 6);
lean_inc_ref(v_norm_1596_);
v_normProcs_1597_ = lean_ctor_get(v_params_1385_, 7);
lean_inc_ref(v_normProcs_1597_);
v_anchorRefs_x3f_1598_ = lean_ctor_get(v_params_1385_, 8);
lean_inc(v_anchorRefs_x3f_1598_);
lean_dec_ref(v_params_1385_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 0);
v___x_1600_ = v___x_1587_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_1640_, 0, v_gen_1585_);
v___x_1600_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; 
lean_inc_ref(v_symPrios_1595_);
lean_inc(v_declName_1387_);
v___x_1601_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1387_, v___x_1600_, v_symPrios_1595_, v___x_1453_, v___x_1453_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1603_, 0, v_gen_1585_);
lean_inc_ref(v_symPrios_1595_);
lean_inc(v_declName_1387_);
v___x_1604_ = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(v_declName_1387_, v___x_1603_, v_symPrios_1595_, v___x_1453_, v___x_1453_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1604_) == 0)
{
if (v_warn_1391_ == 0)
{
lean_object* v_a_1605_; 
lean_dec(v_declName_1387_);
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1604_);
v___y_1438_ = v_a_1605_;
v___y_1439_ = v_extensions_1591_;
v___y_1440_ = v_normProcs_1597_;
v___y_1441_ = v_a_1602_;
v___y_1442_ = v_extra_1592_;
v___y_1443_ = v_symPrios_1595_;
v___y_1444_ = v_extraFacts_1594_;
v___y_1445_ = v_extraInj_1593_;
v___y_1446_ = v_norm_1596_;
v___y_1447_ = v_anchorRefs_x3f_1598_;
v___y_1448_ = v_config_1590_;
goto v___jp_1437_;
}
else
{
lean_object* v_a_1606_; lean_object* v_patterns_1607_; lean_object* v_origin_1608_; lean_object* v_cnstrs_1609_; uint8_t v___x_1610_; 
v_a_1606_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1606_);
lean_dec_ref(v___x_1604_);
v_patterns_1607_ = lean_ctor_get(v_a_1602_, 3);
v_origin_1608_ = lean_ctor_get(v_a_1602_, 5);
v_cnstrs_1609_ = lean_ctor_get(v_a_1602_, 7);
v___x_1610_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1591_, v_origin_1608_, v_patterns_1607_, v_cnstrs_1609_);
if (v___x_1610_ == 0)
{
lean_dec(v_declName_1387_);
v___y_1438_ = v_a_1606_;
v___y_1439_ = v_extensions_1591_;
v___y_1440_ = v_normProcs_1597_;
v___y_1441_ = v_a_1602_;
v___y_1442_ = v_extra_1592_;
v___y_1443_ = v_symPrios_1595_;
v___y_1444_ = v_extraFacts_1594_;
v___y_1445_ = v_extraInj_1593_;
v___y_1446_ = v_norm_1596_;
v___y_1447_ = v_anchorRefs_x3f_1598_;
v___y_1448_ = v_config_1590_;
goto v___jp_1437_;
}
else
{
lean_object* v_patterns_1611_; lean_object* v_origin_1612_; lean_object* v_cnstrs_1613_; uint8_t v___x_1614_; 
v_patterns_1611_ = lean_ctor_get(v_a_1606_, 3);
v_origin_1612_ = lean_ctor_get(v_a_1606_, 5);
v_cnstrs_1613_ = lean_ctor_get(v_a_1606_, 7);
v___x_1614_ = l_Lean_Meta_Grind_ExtensionStateArray_containsWithSamePatterns(v_extensions_1591_, v_origin_1612_, v_patterns_1611_, v_cnstrs_1613_);
if (v___x_1614_ == 0)
{
lean_dec(v_declName_1387_);
v___y_1438_ = v_a_1606_;
v___y_1439_ = v_extensions_1591_;
v___y_1440_ = v_normProcs_1597_;
v___y_1441_ = v_a_1602_;
v___y_1442_ = v_extra_1592_;
v___y_1443_ = v_symPrios_1595_;
v___y_1444_ = v_extraFacts_1594_;
v___y_1445_ = v_extraInj_1593_;
v___y_1446_ = v_norm_1596_;
v___y_1447_ = v_anchorRefs_x3f_1598_;
v___y_1448_ = v_config_1590_;
goto v___jp_1437_;
}
else
{
lean_object* v___x_1615_; 
v___x_1615_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg(v_extensions_1591_, v_declName_1387_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_dec_ref(v___x_1615_);
v___y_1438_ = v_a_1606_;
v___y_1439_ = v_extensions_1591_;
v___y_1440_ = v_normProcs_1597_;
v___y_1441_ = v_a_1602_;
v___y_1442_ = v_extra_1592_;
v___y_1443_ = v_symPrios_1595_;
v___y_1444_ = v_extraFacts_1594_;
v___y_1445_ = v_extraInj_1593_;
v___y_1446_ = v_norm_1596_;
v___y_1447_ = v_anchorRefs_x3f_1598_;
v___y_1448_ = v_config_1590_;
goto v___jp_1437_;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_a_1606_);
lean_dec(v_a_1602_);
lean_dec(v_anchorRefs_x3f_1598_);
lean_dec_ref(v_normProcs_1597_);
lean_dec_ref(v_norm_1596_);
lean_dec_ref(v_symPrios_1595_);
lean_dec_ref(v_extraFacts_1594_);
lean_dec_ref(v_extraInj_1593_);
lean_dec_ref(v_extra_1592_);
lean_dec_ref(v_extensions_1591_);
lean_dec_ref(v_config_1590_);
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
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
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_a_1602_);
lean_dec(v_anchorRefs_x3f_1598_);
lean_dec_ref(v_normProcs_1597_);
lean_dec_ref(v_norm_1596_);
lean_dec_ref(v_symPrios_1595_);
lean_dec_ref(v_extraFacts_1594_);
lean_dec_ref(v_extraInj_1593_);
lean_dec_ref(v_extra_1592_);
lean_dec_ref(v_extensions_1591_);
lean_dec_ref(v_config_1590_);
lean_dec(v_declName_1387_);
v_a_1624_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1604_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1604_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v_anchorRefs_x3f_1598_);
lean_dec_ref(v_normProcs_1597_);
lean_dec_ref(v_norm_1596_);
lean_dec_ref(v_symPrios_1595_);
lean_dec_ref(v_extraFacts_1594_);
lean_dec_ref(v_extraInj_1593_);
lean_dec_ref(v_extra_1592_);
lean_dec_ref(v_extensions_1591_);
lean_dec_ref(v_config_1590_);
lean_dec(v_declName_1387_);
v_a_1632_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1601_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1601_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_del_object(v___x_1587_);
lean_dec(v_declName_1387_);
lean_dec_ref(v_params_1385_);
v_a_1641_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1589_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1589_);
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
}
else
{
switch(lean_obj_tag(v_kind_1388_))
{
case 0:
{
v___y_1567_ = v___y_1584_;
v___y_1568_ = v___y_1582_;
v___y_1569_ = v___y_1581_;
v___y_1570_ = v___y_1583_;
goto v___jp_1566_;
}
case 1:
{
v___y_1567_ = v___y_1584_;
v___y_1568_ = v___y_1582_;
v___y_1569_ = v___y_1581_;
v___y_1570_ = v___y_1583_;
goto v___jp_1566_;
}
default: 
{
v___y_1548_ = v___y_1581_;
v___y_1549_ = v___y_1582_;
v___y_1550_ = v___y_1583_;
v___y_1551_ = v___y_1584_;
goto v___jp_1547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_addEMatchTheorem___boxed(lean_object* v_params_1692_, lean_object* v_id_1693_, lean_object* v_declName_1694_, lean_object* v_kind_1695_, lean_object* v_minIndexable_1696_, lean_object* v_suggest_1697_, lean_object* v_warn_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
uint8_t v_minIndexable_boxed_1704_; uint8_t v_suggest_boxed_1705_; uint8_t v_warn_boxed_1706_; lean_object* v_res_1707_; 
v_minIndexable_boxed_1704_ = lean_unbox(v_minIndexable_1696_);
v_suggest_boxed_1705_ = lean_unbox(v_suggest_1697_);
v_warn_boxed_1706_ = lean_unbox(v_warn_1698_);
v_res_1707_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_1692_, v_id_1693_, v_declName_1694_, v_kind_1695_, v_minIndexable_boxed_1704_, v_suggest_boxed_1705_, v_warn_boxed_1706_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(lean_object* v_declName_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___redArg(v_declName_1708_, v___y_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2___boxed(lean_object* v_declName_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__1_spec__2(v_declName_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_1722_, lean_object* v_constName_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___redArg(v_constName_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1730_, lean_object* v_constName_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0(v_00_u03b1_1730_, v_constName_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1738_, lean_object* v_ref_1739_, lean_object* v_constName_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___redArg(v_ref_1739_, v_constName_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1747_, lean_object* v_ref_1748_, lean_object* v_constName_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1(v_00_u03b1_1747_, v_ref_1748_, v_constName_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v_ref_1748_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_1756_, lean_object* v_ref_1757_, lean_object* v_msg_1758_, lean_object* v_declHint_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1757_, v_msg_1758_, v_declHint_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1766_, lean_object* v_ref_1767_, lean_object* v_msg_1768_, lean_object* v_declHint_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1766_, v_ref_1767_, v_msg_1768_, v_declHint_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v_ref_1767_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_msg_1776_, lean_object* v_declHint_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1776_, v_declHint_1777_, v___y_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1784_, lean_object* v_declHint_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1784_, v_declHint_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_1792_, lean_object* v_ref_1793_, lean_object* v_msg_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1793_, v_msg_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_ref_1802_, lean_object* v_msg_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getAsyncConstInfo___at___00Lean_Elab_Tactic_addEMatchTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1801_, v_ref_1802_, v_msg_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_ref_1802_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(lean_object* v_params_1812_, lean_object* v_val_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_config_1817_; lean_object* v_extensions_1818_; lean_object* v_extra_1819_; lean_object* v_extraInj_1820_; lean_object* v_extraFacts_1821_; lean_object* v_symPrios_1822_; lean_object* v_norm_1823_; lean_object* v_normProcs_1824_; lean_object* v_anchorRefs_x3f_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1855_; 
v_config_1817_ = lean_ctor_get(v_params_1812_, 0);
v_extensions_1818_ = lean_ctor_get(v_params_1812_, 1);
v_extra_1819_ = lean_ctor_get(v_params_1812_, 2);
v_extraInj_1820_ = lean_ctor_get(v_params_1812_, 3);
v_extraFacts_1821_ = lean_ctor_get(v_params_1812_, 4);
v_symPrios_1822_ = lean_ctor_get(v_params_1812_, 5);
v_norm_1823_ = lean_ctor_get(v_params_1812_, 6);
v_normProcs_1824_ = lean_ctor_get(v_params_1812_, 7);
v_anchorRefs_x3f_1825_ = lean_ctor_get(v_params_1812_, 8);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_params_1812_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1827_ = v_params_1812_;
v_isShared_1828_ = v_isSharedCheck_1855_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_anchorRefs_x3f_1825_);
lean_inc(v_normProcs_1824_);
lean_inc(v_norm_1823_);
lean_inc(v_symPrios_1822_);
lean_inc(v_extraFacts_1821_);
lean_inc(v_extraInj_1820_);
lean_inc(v_extra_1819_);
lean_inc(v_extensions_1818_);
lean_inc(v_config_1817_);
lean_dec(v_params_1812_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1855_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___y_1830_; 
if (lean_obj_tag(v_anchorRefs_x3f_1825_) == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___closed__0));
v___y_1830_ = v___x_1853_;
goto v___jp_1829_;
}
else
{
lean_object* v_val_1854_; 
v_val_1854_ = lean_ctor_get(v_anchorRefs_x3f_1825_, 0);
lean_inc(v_val_1854_);
lean_dec_ref(v_anchorRefs_x3f_1825_);
v___y_1830_ = v_val_1854_;
goto v___jp_1829_;
}
v___jp_1829_:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_val_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1844_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1836_ = lean_array_push(v___y_1830_, v_a_1832_);
v___x_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 8, v___x_1837_);
v___x_1839_ = v___x_1827_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_config_1817_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_extensions_1818_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_extra_1819_);
lean_ctor_set(v_reuseFailAlloc_1843_, 3, v_extraInj_1820_);
lean_ctor_set(v_reuseFailAlloc_1843_, 4, v_extraFacts_1821_);
lean_ctor_set(v_reuseFailAlloc_1843_, 5, v_symPrios_1822_);
lean_ctor_set(v_reuseFailAlloc_1843_, 6, v_norm_1823_);
lean_ctor_set(v_reuseFailAlloc_1843_, 7, v_normProcs_1824_);
lean_ctor_set(v_reuseFailAlloc_1843_, 8, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1839_);
v___x_1841_ = v___x_1834_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v___y_1830_);
lean_del_object(v___x_1827_);
lean_dec_ref(v_normProcs_1824_);
lean_dec_ref(v_norm_1823_);
lean_dec_ref(v_symPrios_1822_);
lean_dec_ref(v_extraFacts_1821_);
lean_dec_ref(v_extraInj_1820_);
lean_dec_ref(v_extra_1819_);
lean_dec_ref(v_extensions_1818_);
lean_dec_ref(v_config_1817_);
v_a_1845_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1831_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1831_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor___boxed(lean_object* v_params_1856_, lean_object* v_val_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_params_1856_, v_val_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_val_1857_);
return v_res_1861_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__0));
v___x_1864_ = l_Lean_stringToMessageData(v___x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(lean_object* v_params_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_config_1869_; uint8_t v_revert_1870_; 
v_config_1869_ = lean_ctor_get(v_params_1865_, 0);
v_revert_1870_ = lean_ctor_get_uint8(v_config_1869_, sizeof(void*)*13 + 29);
if (v_revert_1870_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___closed__1);
v___x_1874_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier_spec__0___redArg(v___x_1873_, v_a_1866_, v_a_1867_);
return v___x_1874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert___boxed(lean_object* v_params_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_1875_, v_a_1876_, v_a_1877_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec_ref(v_params_1875_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(lean_object* v_e_1880_, lean_object* v___y_1881_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = l_Lean_Expr_hasMVar(v_e_1880_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v_e_1880_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; lean_object* v_mctx_1886_; lean_object* v___x_1887_; lean_object* v_fst_1888_; lean_object* v_snd_1889_; lean_object* v___x_1890_; lean_object* v_cache_1891_; lean_object* v_zetaDeltaFVarIds_1892_; lean_object* v_postponed_1893_; lean_object* v_diag_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1903_; 
v___x_1885_ = lean_st_ref_get(v___y_1881_);
v_mctx_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc_ref(v_mctx_1886_);
lean_dec(v___x_1885_);
v___x_1887_ = l_Lean_instantiateMVarsCore(v_mctx_1886_, v_e_1880_);
v_fst_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_fst_1888_);
v_snd_1889_ = lean_ctor_get(v___x_1887_, 1);
lean_inc(v_snd_1889_);
lean_dec_ref(v___x_1887_);
v___x_1890_ = lean_st_ref_take(v___y_1881_);
v_cache_1891_ = lean_ctor_get(v___x_1890_, 1);
v_zetaDeltaFVarIds_1892_ = lean_ctor_get(v___x_1890_, 2);
v_postponed_1893_ = lean_ctor_get(v___x_1890_, 3);
v_diag_1894_ = lean_ctor_get(v___x_1890_, 4);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; 
v_unused_1904_ = lean_ctor_get(v___x_1890_, 0);
lean_dec(v_unused_1904_);
v___x_1896_ = v___x_1890_;
v_isShared_1897_ = v_isSharedCheck_1903_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_diag_1894_);
lean_inc(v_postponed_1893_);
lean_inc(v_zetaDeltaFVarIds_1892_);
lean_inc(v_cache_1891_);
lean_dec(v___x_1890_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1903_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v_snd_1889_);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_snd_1889_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_cache_1891_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_zetaDeltaFVarIds_1892_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_postponed_1893_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_diag_1894_);
v___x_1899_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_st_ref_set(v___y_1881_, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v_fst_1888_);
return v___x_1901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg___boxed(lean_object* v_e_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1905_, v___y_1906_);
lean_dec(v___y_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(lean_object* v_e_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_e_1909_, v___y_1913_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___boxed(lean_object* v_e_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0(v_e_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(lean_object* v_p_1929_, lean_object* v_term_1930_, lean_object* v___x_1931_, uint8_t v___x_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_fileName_1940_; lean_object* v_fileMap_1941_; lean_object* v_options_1942_; lean_object* v_currRecDepth_1943_; lean_object* v_maxRecDepth_1944_; lean_object* v_ref_1945_; lean_object* v_currNamespace_1946_; lean_object* v_openDecls_1947_; lean_object* v_initHeartbeats_1948_; lean_object* v_maxHeartbeats_1949_; lean_object* v_quotContext_1950_; lean_object* v_currMacroScope_1951_; uint8_t v_diag_1952_; lean_object* v_cancelTk_x3f_1953_; uint8_t v_suppressElabErrors_1954_; lean_object* v_inheritedTraceOptions_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2023_; 
v_fileName_1940_ = lean_ctor_get(v___y_1937_, 0);
v_fileMap_1941_ = lean_ctor_get(v___y_1937_, 1);
v_options_1942_ = lean_ctor_get(v___y_1937_, 2);
v_currRecDepth_1943_ = lean_ctor_get(v___y_1937_, 3);
v_maxRecDepth_1944_ = lean_ctor_get(v___y_1937_, 4);
v_ref_1945_ = lean_ctor_get(v___y_1937_, 5);
v_currNamespace_1946_ = lean_ctor_get(v___y_1937_, 6);
v_openDecls_1947_ = lean_ctor_get(v___y_1937_, 7);
v_initHeartbeats_1948_ = lean_ctor_get(v___y_1937_, 8);
v_maxHeartbeats_1949_ = lean_ctor_get(v___y_1937_, 9);
v_quotContext_1950_ = lean_ctor_get(v___y_1937_, 10);
v_currMacroScope_1951_ = lean_ctor_get(v___y_1937_, 11);
v_diag_1952_ = lean_ctor_get_uint8(v___y_1937_, sizeof(void*)*14);
v_cancelTk_x3f_1953_ = lean_ctor_get(v___y_1937_, 12);
v_suppressElabErrors_1954_ = lean_ctor_get_uint8(v___y_1937_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1955_ = lean_ctor_get(v___y_1937_, 13);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___y_1937_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_1957_ = v___y_1937_;
v_isShared_1958_ = v_isSharedCheck_2023_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_inheritedTraceOptions_1955_);
lean_inc(v_cancelTk_x3f_1953_);
lean_inc(v_currMacroScope_1951_);
lean_inc(v_quotContext_1950_);
lean_inc(v_maxHeartbeats_1949_);
lean_inc(v_initHeartbeats_1948_);
lean_inc(v_openDecls_1947_);
lean_inc(v_currNamespace_1946_);
lean_inc(v_ref_1945_);
lean_inc(v_maxRecDepth_1944_);
lean_inc(v_currRecDepth_1943_);
lean_inc(v_options_1942_);
lean_inc(v_fileMap_1941_);
lean_inc(v_fileName_1940_);
lean_dec(v___y_1937_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2023_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v_ref_1959_; lean_object* v___x_1961_; 
v_ref_1959_ = l_Lean_replaceRef(v_p_1929_, v_ref_1945_);
lean_dec(v_ref_1945_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 5, v_ref_1959_);
v___x_1961_ = v___x_1957_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_fileName_1940_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_fileMap_1941_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_options_1942_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_currRecDepth_1943_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_maxRecDepth_1944_);
lean_ctor_set(v_reuseFailAlloc_2022_, 5, v_ref_1959_);
lean_ctor_set(v_reuseFailAlloc_2022_, 6, v_currNamespace_1946_);
lean_ctor_set(v_reuseFailAlloc_2022_, 7, v_openDecls_1947_);
lean_ctor_set(v_reuseFailAlloc_2022_, 8, v_initHeartbeats_1948_);
lean_ctor_set(v_reuseFailAlloc_2022_, 9, v_maxHeartbeats_1949_);
lean_ctor_set(v_reuseFailAlloc_2022_, 10, v_quotContext_1950_);
lean_ctor_set(v_reuseFailAlloc_2022_, 11, v_currMacroScope_1951_);
lean_ctor_set(v_reuseFailAlloc_2022_, 12, v_cancelTk_x3f_1953_);
lean_ctor_set(v_reuseFailAlloc_2022_, 13, v_inheritedTraceOptions_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*14, v_diag_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*14 + 1, v_suppressElabErrors_1954_);
v___x_1961_ = v_reuseFailAlloc_2022_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_Elab_Term_elabTerm(v_term_1930_, v___x_1931_, v___x_1932_, v___x_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___x_1961_, v___y_1938_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; uint8_t v___x_1964_; lean_object* v___x_1965_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref(v___x_1962_);
v___x_1964_ = 1;
v___x_1965_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_1964_, v___x_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___x_1961_, v___y_1938_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2005_; 
lean_dec_ref(v___x_1965_);
v___x_1966_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__0___redArg(v_a_1963_, v___y_1936_);
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_2005_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2005_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Lean_Expr_hasSyntheticSorry(v_a_1967_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = l_Lean_Expr_eta(v_a_1967_);
v___x_1973_ = l_Lean_Expr_hasMVar(v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
lean_dec_ref(v___x_1961_);
v___x_1974_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___closed__0));
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
lean_ctor_set(v___x_1975_, 1, v___x_1972_);
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1976_);
v___x_1978_ = v___x_1969_;
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
else
{
lean_object* v___x_1980_; 
lean_del_object(v___x_1969_);
v___x_1980_ = l_Lean_Meta_abstractMVars(v___x_1972_, v___x_1932_, v___y_1935_, v___y_1936_, v___x_1961_, v___y_1938_);
lean_dec_ref(v___x_1961_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1992_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_1992_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1992_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_paramNames_1985_; lean_object* v_expr_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v_paramNames_1985_ = lean_ctor_get(v_a_1981_, 0);
lean_inc_ref(v_paramNames_1985_);
v_expr_1986_ = lean_ctor_get(v_a_1981_, 2);
lean_inc_ref(v_expr_1986_);
lean_dec(v_a_1981_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v_paramNames_1985_);
lean_ctor_set(v___x_1987_, 1, v_expr_1986_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1988_);
v___x_1990_ = v___x_1983_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
v_a_1993_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1980_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1980_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2003_; 
lean_dec(v_a_1967_);
lean_dec_ref(v___x_1961_);
v___x_2001_ = lean_box(0);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_2001_);
v___x_2003_ = v___x_1969_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
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
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_a_1963_);
lean_dec_ref(v___x_1961_);
v_a_2006_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1965_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1965_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec_ref(v___x_1961_);
v_a_2014_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_1962_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_1962_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed(lean_object* v_p_2024_, lean_object* v_term_2025_, lean_object* v___x_2026_, lean_object* v___x_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v___x_13869__boxed_2035_; lean_object* v_res_2036_; 
v___x_13869__boxed_2035_ = lean_unbox(v___x_2027_);
v_res_2036_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0(v_p_2024_, v_term_2025_, v___x_2026_, v___x_13869__boxed_2035_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v_p_2024_);
return v_res_2036_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__2));
v___x_2042_ = l_Lean_stringToMessageData(v___x_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(lean_object* v_params_2043_, lean_object* v_p_2044_, lean_object* v_fst_2045_, lean_object* v_snd_2046_, uint8_t v___x_2047_, uint8_t v_minIndexable_2048_, lean_object* v_kind_2049_, lean_object* v_idx_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_symPrios_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; 
v_symPrios_2056_ = lean_ctor_get(v_params_2043_, 5);
lean_inc_ref(v_symPrios_2056_);
lean_dec_ref(v_params_2043_);
v___x_2057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__1));
v___x_2058_ = lean_name_append_index_after(v___x_2057_, v_idx_2050_);
v___x_2059_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v_p_2044_);
v___x_2060_ = 0;
v___x_2061_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(v___x_2059_, v_fst_2045_, v_snd_2046_, v_kind_2049_, v_symPrios_2056_, v___x_2047_, v___x_2060_, v_minIndexable_2048_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2072_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2072_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2072_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
if (lean_obj_tag(v_a_2062_) == 1)
{
lean_object* v_val_2066_; lean_object* v___x_2068_; 
v_val_2066_ = lean_ctor_get(v_a_2062_, 0);
lean_inc(v_val_2066_);
lean_dec_ref(v_a_2062_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v_val_2066_);
v___x_2068_ = v___x_2064_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_val_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_del_object(v___x_2064_);
lean_dec(v_a_2062_);
v___x_2070_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___closed__3);
v___x_2071_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable_spec__0___redArg(v___x_2070_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
return v___x_2071_;
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
v_a_2073_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2061_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2061_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed(lean_object* v_params_2081_, lean_object* v_p_2082_, lean_object* v_fst_2083_, lean_object* v_snd_2084_, lean_object* v___x_2085_, lean_object* v_minIndexable_2086_, lean_object* v_kind_2087_, lean_object* v_idx_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v___x_14043__boxed_2094_; uint8_t v_minIndexable_boxed_2095_; lean_object* v_res_2096_; 
v___x_14043__boxed_2094_ = lean_unbox(v___x_2085_);
v_minIndexable_boxed_2095_ = lean_unbox(v_minIndexable_2086_);
v_res_2096_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1(v_params_2081_, v_p_2082_, v_fst_2083_, v_snd_2084_, v___x_14043__boxed_2094_, v_minIndexable_boxed_2095_, v_kind_2087_, v_idx_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2096_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_box(1);
v___x_2098_ = l_Lean_MessageData_ofFormat(v___x_2097_);
return v___x_2098_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__2));
v___x_2103_ = l_Lean_MessageData_ofFormat(v___x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
if (lean_obj_tag(v_x_2105_) == 0)
{
return v_x_2104_;
}
else
{
lean_object* v_head_2106_; lean_object* v_tail_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2129_; 
v_head_2106_ = lean_ctor_get(v_x_2105_, 0);
v_tail_2107_ = lean_ctor_get(v_x_2105_, 1);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_x_2105_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2109_ = v_x_2105_;
v_isShared_2110_ = v_isSharedCheck_2129_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_tail_2107_);
lean_inc(v_head_2106_);
lean_dec(v_x_2105_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2129_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_before_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2127_; 
v_before_2111_ = lean_ctor_get(v_head_2106_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_head_2106_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v_head_2106_, 1);
lean_dec(v_unused_2128_);
v___x_2113_ = v_head_2106_;
v_isShared_2114_ = v_isSharedCheck_2127_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_before_2111_);
lean_dec(v_head_2106_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2127_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2114_ == 0)
{
lean_ctor_set_tag(v___x_2113_, 7);
lean_ctor_set(v___x_2113_, 1, v___x_2115_);
lean_ctor_set(v___x_2113_, 0, v_x_2104_);
v___x_2117_ = v___x_2113_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_x_2104_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__3);
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 7);
lean_ctor_set(v___x_2109_, 1, v___x_2118_);
lean_ctor_set(v___x_2109_, 0, v___x_2117_);
v___x_2120_ = v___x_2109_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = l_Lean_MessageData_ofSyntax(v_before_2111_);
v___x_2122_ = l_Lean_indentD(v___x_2121_);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2120_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v_x_2104_ = v___x_2123_;
v_x_2105_ = v_tail_2107_;
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
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__1));
v___x_2134_ = l_Lean_MessageData_ofFormat(v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(lean_object* v_msgData_2135_, lean_object* v_macroStack_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_options_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v_options_2139_ = lean_ctor_get(v___y_2137_, 2);
v___x_2140_ = l_Lean_Elab_pp_macroStack;
v___x_2141_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; 
lean_dec(v_macroStack_2136_);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v_msgData_2135_);
return v___x_2142_;
}
else
{
if (lean_obj_tag(v_macroStack_2136_) == 0)
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v_msgData_2135_);
return v___x_2143_;
}
else
{
lean_object* v_head_2144_; lean_object* v_after_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2160_; 
v_head_2144_ = lean_ctor_get(v_macroStack_2136_, 0);
lean_inc(v_head_2144_);
v_after_2145_ = lean_ctor_get(v_head_2144_, 1);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_head_2144_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v_head_2144_, 0);
lean_dec(v_unused_2161_);
v___x_2147_ = v_head_2144_;
v_isShared_2148_ = v_isSharedCheck_2160_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_after_2145_);
lean_dec(v_head_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2160_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2___closed__0);
if (v_isShared_2148_ == 0)
{
lean_ctor_set_tag(v___x_2147_, 7);
lean_ctor_set(v___x_2147_, 1, v___x_2149_);
lean_ctor_set(v___x_2147_, 0, v_msgData_2135_);
v___x_2151_ = v___x_2147_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_msgData_2135_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v_msgData_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2152_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___closed__2);
v___x_2153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = l_Lean_MessageData_ofSyntax(v_after_2145_);
v___x_2155_ = l_Lean_indentD(v___x_2154_);
v_msgData_2156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2156_, 0, v___x_2153_);
lean_ctor_set(v_msgData_2156_, 1, v___x_2155_);
v___x_2157_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1_spec__2(v_msgData_2156_, v_macroStack_2136_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2162_, lean_object* v_macroStack_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2162_, v_macroStack_2163_, v___y_2164_);
lean_dec_ref(v___y_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(lean_object* v_msg_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_ref_2175_; lean_object* v___x_2176_; lean_object* v_a_2177_; lean_object* v_macroStack_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2189_; 
v_ref_2175_ = lean_ctor_get(v___y_2172_, 5);
v___x_2176_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v_msg_2167_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref(v___x_2176_);
v_macroStack_2178_ = lean_ctor_get(v___y_2168_, 1);
v___x_2179_ = l_Lean_Elab_getBetterRef(v_ref_2175_, v_macroStack_2178_);
lean_inc(v_macroStack_2178_);
v___x_2180_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_a_2177_, v_macroStack_2178_, v___y_2172_);
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2189_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2189_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2179_);
lean_ctor_set(v___x_2185_, 1, v_a_2181_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set_tag(v___x_2183_, 1);
lean_ctor_set(v___x_2183_, 0, v___x_2185_);
v___x_2187_ = v___x_2183_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg___boxed(lean_object* v_msg_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
return v_res_2198_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__0));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__2));
v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__4));
v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
return v___x_2207_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__7));
v___x_2212_ = l_Lean_stringToMessageData(v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(lean_object* v_params_2213_, lean_object* v_p_2214_, lean_object* v_mod_x3f_2215_, lean_object* v_term_2216_, uint8_t v_minIndexable_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2288_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v_kind_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v_fileName_2523_; lean_object* v_fileMap_2524_; lean_object* v_options_2525_; lean_object* v_currRecDepth_2526_; lean_object* v_maxRecDepth_2527_; lean_object* v_ref_2528_; lean_object* v_currNamespace_2529_; lean_object* v_openDecls_2530_; lean_object* v_initHeartbeats_2531_; lean_object* v_maxHeartbeats_2532_; lean_object* v_quotContext_2533_; lean_object* v_currMacroScope_2534_; uint8_t v_diag_2535_; lean_object* v_cancelTk_x3f_2536_; uint8_t v_suppressElabErrors_2537_; lean_object* v_inheritedTraceOptions_2538_; lean_object* v_ref_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v_fileName_2523_ = lean_ctor_get(v_a_2222_, 0);
v_fileMap_2524_ = lean_ctor_get(v_a_2222_, 1);
v_options_2525_ = lean_ctor_get(v_a_2222_, 2);
v_currRecDepth_2526_ = lean_ctor_get(v_a_2222_, 3);
v_maxRecDepth_2527_ = lean_ctor_get(v_a_2222_, 4);
v_ref_2528_ = lean_ctor_get(v_a_2222_, 5);
v_currNamespace_2529_ = lean_ctor_get(v_a_2222_, 6);
v_openDecls_2530_ = lean_ctor_get(v_a_2222_, 7);
v_initHeartbeats_2531_ = lean_ctor_get(v_a_2222_, 8);
v_maxHeartbeats_2532_ = lean_ctor_get(v_a_2222_, 9);
v_quotContext_2533_ = lean_ctor_get(v_a_2222_, 10);
v_currMacroScope_2534_ = lean_ctor_get(v_a_2222_, 11);
v_diag_2535_ = lean_ctor_get_uint8(v_a_2222_, sizeof(void*)*14);
v_cancelTk_x3f_2536_ = lean_ctor_get(v_a_2222_, 12);
v_suppressElabErrors_2537_ = lean_ctor_get_uint8(v_a_2222_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2538_ = lean_ctor_get(v_a_2222_, 13);
v_ref_2539_ = l_Lean_replaceRef(v_p_2214_, v_ref_2528_);
lean_inc_ref(v_inheritedTraceOptions_2538_);
lean_inc(v_cancelTk_x3f_2536_);
lean_inc(v_currMacroScope_2534_);
lean_inc(v_quotContext_2533_);
lean_inc(v_maxHeartbeats_2532_);
lean_inc(v_initHeartbeats_2531_);
lean_inc(v_openDecls_2530_);
lean_inc(v_currNamespace_2529_);
lean_inc(v_maxRecDepth_2527_);
lean_inc(v_currRecDepth_2526_);
lean_inc_ref(v_options_2525_);
lean_inc_ref(v_fileMap_2524_);
lean_inc_ref(v_fileName_2523_);
v___x_2540_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2540_, 0, v_fileName_2523_);
lean_ctor_set(v___x_2540_, 1, v_fileMap_2524_);
lean_ctor_set(v___x_2540_, 2, v_options_2525_);
lean_ctor_set(v___x_2540_, 3, v_currRecDepth_2526_);
lean_ctor_set(v___x_2540_, 4, v_maxRecDepth_2527_);
lean_ctor_set(v___x_2540_, 5, v_ref_2539_);
lean_ctor_set(v___x_2540_, 6, v_currNamespace_2529_);
lean_ctor_set(v___x_2540_, 7, v_openDecls_2530_);
lean_ctor_set(v___x_2540_, 8, v_initHeartbeats_2531_);
lean_ctor_set(v___x_2540_, 9, v_maxHeartbeats_2532_);
lean_ctor_set(v___x_2540_, 10, v_quotContext_2533_);
lean_ctor_set(v___x_2540_, 11, v_currMacroScope_2534_);
lean_ctor_set(v___x_2540_, 12, v_cancelTk_x3f_2536_);
lean_ctor_set(v___x_2540_, 13, v_inheritedTraceOptions_2538_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*14, v_diag_2535_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*14 + 1, v_suppressElabErrors_2537_);
v___x_2541_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_checkNoRevert(v_params_2213_, v___x_2540_, v_a_2223_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_dec_ref(v___x_2541_);
if (lean_obj_tag(v_mod_x3f_2215_) == 1)
{
lean_object* v_val_2542_; lean_object* v___x_2543_; 
v_val_2542_ = lean_ctor_get(v_mod_x3f_2215_, 0);
lean_inc(v_val_2542_);
v___x_2543_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_2542_, v___x_2540_, v_a_2223_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
switch(lean_obj_tag(v_a_2544_))
{
case 0:
{
lean_object* v_k_2562_; 
v_k_2562_ = lean_ctor_get(v_a_2544_, 0);
lean_inc(v_k_2562_);
lean_dec_ref(v_a_2544_);
if (lean_obj_tag(v_k_2562_) == 9)
{
lean_dec_ref(v_mod_x3f_2215_);
lean_dec(v_term_2216_);
lean_dec(v_p_2214_);
lean_dec_ref(v_params_2213_);
v___y_2546_ = v_a_2218_;
v___y_2547_ = v_a_2219_;
v___y_2548_ = v_a_2220_;
v___y_2549_ = v_a_2221_;
v___y_2550_ = v___x_2540_;
v___y_2551_ = v_a_2223_;
goto v___jp_2545_;
}
else
{
v_kind_2450_ = v_k_2562_;
v___y_2451_ = v_a_2218_;
v___y_2452_ = v_a_2219_;
v___y_2453_ = v_a_2220_;
v___y_2454_ = v_a_2221_;
v___y_2455_ = v___x_2540_;
v___y_2456_ = v_a_2223_;
goto v___jp_2449_;
}
}
case 1:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_mod_x3f_2215_);
lean_dec(v_term_2216_);
lean_dec(v_p_2214_);
lean_dec_ref(v_params_2213_);
v___x_2563_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2564_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2563_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v___x_2540_, v_a_2223_);
lean_dec_ref(v___x_2540_);
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
case 3:
{
v___y_2516_ = v_a_2218_;
v___y_2517_ = v_a_2219_;
v___y_2518_ = v_a_2220_;
v___y_2519_ = v_a_2221_;
v___y_2520_ = v___x_2540_;
v___y_2521_ = v_a_2223_;
goto v___jp_2515_;
}
case 5:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_mod_x3f_2215_);
lean_dec(v_term_2216_);
lean_dec(v_p_2214_);
lean_dec_ref(v_params_2213_);
v___x_2573_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2574_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2573_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v___x_2540_, v_a_2223_);
lean_dec_ref(v___x_2540_);
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
case 8:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_mod_x3f_2215_);
lean_dec(v_term_2216_);
lean_dec(v_p_2214_);
lean_dec_ref(v_params_2213_);
v___x_2583_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2584_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2583_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v___x_2540_, v_a_2223_);
lean_dec_ref(v___x_2540_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
default: 
{
lean_dec(v_a_2544_);
lean_dec_ref(v_mod_x3f_2215_);
lean_dec(v_term_2216_);
lean_dec(v_p_2214_);
lean_dec_ref(v_params_2213_);
v___y_2546_ = v_a_2218_;
v___y_2547_ = v_a_2219_;
v___y_2548_ = v_a_2220_;
v___y_2549_ = v_a_2221_;
v___y_2550_ = v___x_2540_;
v___y_2551_ = v_a_2223_;
goto v___jp_2545_;
}
}
v___jp_2545_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
v___x_2552_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__8);
v___x_2553_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2552_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec_ref(v___y_2550_);
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref(v_mod_x3f_2215_);
lean_dec_ref(v___x_2540_);
lean_dec(v_term_2216_);
lean_dec(v_p_2214_);
lean_dec_ref(v_params_2213_);
v_a_2593_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2543_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2543_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
v___y_2516_ = v_a_2218_;
v___y_2517_ = v_a_2219_;
v___y_2518_ = v_a_2220_;
v___y_2519_ = v_a_2221_;
v___y_2520_ = v___x_2540_;
v___y_2521_ = v_a_2223_;
goto v___jp_2515_;
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v___x_2540_);
lean_dec(v_term_2216_);
lean_dec(v_mod_x3f_2215_);
lean_dec(v_p_2214_);
lean_dec_ref(v_params_2213_);
v_a_2601_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2541_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2541_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
v___jp_2225_:
{
lean_object* v___x_2242_; 
lean_inc(v___y_2241_);
lean_inc(v___y_2239_);
lean_inc_ref(v___y_2238_);
v___x_2242_ = lean_apply_7(v___y_2227_, v___y_2235_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, lean_box(0));
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2252_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2252_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2252_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2247_ = l_Lean_PersistentArray_push___redArg(v___y_2226_, v_a_2243_);
v___x_2248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2248_, 0, v___y_2230_);
lean_ctor_set(v___x_2248_, 1, v___y_2236_);
lean_ctor_set(v___x_2248_, 2, v___x_2247_);
lean_ctor_set(v___x_2248_, 3, v___y_2234_);
lean_ctor_set(v___x_2248_, 4, v___y_2233_);
lean_ctor_set(v___x_2248_, 5, v___y_2231_);
lean_ctor_set(v___x_2248_, 6, v___y_2228_);
lean_ctor_set(v___x_2248_, 7, v___y_2232_);
lean_ctor_set(v___x_2248_, 8, v___y_2229_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2248_);
v___x_2250_ = v___x_2245_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec_ref(v___y_2236_);
lean_dec_ref(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___y_2226_);
v_a_2253_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2242_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2242_);
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
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_2261_:
{
lean_object* v___x_2278_; 
v___x_2278_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2217_, v___y_2267_, v___y_2272_, v___y_2265_, v___y_2277_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_dec_ref(v___x_2278_);
v___y_2226_ = v___y_2268_;
v___y_2227_ = v___y_2269_;
v___y_2228_ = v___y_2262_;
v___y_2229_ = v___y_2263_;
v___y_2230_ = v___y_2270_;
v___y_2231_ = v___y_2271_;
v___y_2232_ = v___y_2273_;
v___y_2233_ = v___y_2264_;
v___y_2234_ = v___y_2274_;
v___y_2235_ = v___y_2275_;
v___y_2236_ = v___y_2266_;
v___y_2237_ = v___y_2276_;
v___y_2238_ = v___y_2267_;
v___y_2239_ = v___y_2272_;
v___y_2240_ = v___y_2265_;
v___y_2241_ = v___y_2277_;
goto v___jp_2225_;
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec_ref(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
v___jp_2287_:
{
lean_object* v_config_2289_; lean_object* v_extensions_2290_; lean_object* v_extra_2291_; lean_object* v_extraInj_2292_; lean_object* v_extraFacts_2293_; lean_object* v_symPrios_2294_; lean_object* v_norm_2295_; lean_object* v_normProcs_2296_; lean_object* v_anchorRefs_x3f_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2306_; 
v_config_2289_ = lean_ctor_get(v_params_2213_, 0);
v_extensions_2290_ = lean_ctor_get(v_params_2213_, 1);
v_extra_2291_ = lean_ctor_get(v_params_2213_, 2);
v_extraInj_2292_ = lean_ctor_get(v_params_2213_, 3);
v_extraFacts_2293_ = lean_ctor_get(v_params_2213_, 4);
v_symPrios_2294_ = lean_ctor_get(v_params_2213_, 5);
v_norm_2295_ = lean_ctor_get(v_params_2213_, 6);
v_normProcs_2296_ = lean_ctor_get(v_params_2213_, 7);
v_anchorRefs_x3f_2297_ = lean_ctor_get(v_params_2213_, 8);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_params_2213_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2299_ = v_params_2213_;
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_anchorRefs_x3f_2297_);
lean_inc(v_normProcs_2296_);
lean_inc(v_norm_2295_);
lean_inc(v_symPrios_2294_);
lean_inc(v_extraFacts_2293_);
lean_inc(v_extraInj_2292_);
lean_inc(v_extra_2291_);
lean_inc(v_extensions_2290_);
lean_inc(v_config_2289_);
lean_dec(v_params_2213_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2306_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = l_Lean_PersistentArray_push___redArg(v_extraFacts_2293_, v___y_2288_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 4, v___x_2301_);
v___x_2303_ = v___x_2299_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_config_2289_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_extensions_2290_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v_extra_2291_);
lean_ctor_set(v_reuseFailAlloc_2305_, 3, v_extraInj_2292_);
lean_ctor_set(v_reuseFailAlloc_2305_, 4, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2305_, 5, v_symPrios_2294_);
lean_ctor_set(v_reuseFailAlloc_2305_, 6, v_norm_2295_);
lean_ctor_set(v_reuseFailAlloc_2305_, 7, v_normProcs_2296_);
lean_ctor_set(v_reuseFailAlloc_2305_, 8, v_anchorRefs_x3f_2297_);
v___x_2303_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
}
}
v___jp_2307_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2317_ = lean_array_get_size(v___y_2309_);
lean_dec_ref(v___y_2309_);
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = lean_nat_dec_eq(v___x_2317_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v___y_2308_);
lean_dec_ref(v_params_2213_);
v___x_2320_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__1);
v___x_2321_ = l_Lean_indentExpr(v___y_2310_);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2322_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec_ref(v___y_2315_);
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
else
{
lean_dec_ref(v___y_2315_);
lean_dec_ref(v___y_2310_);
v___y_2288_ = v___y_2308_;
goto v___jp_2287_;
}
}
v___jp_2332_:
{
uint8_t v___x_2344_; 
v___x_2344_ = l_Lean_Expr_isForall(v___y_2337_);
if (v___x_2344_ == 0)
{
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2333_);
if (lean_obj_tag(v_mod_x3f_2215_) == 0)
{
v___y_2308_ = v___y_2334_;
v___y_2309_ = v___y_2335_;
v___y_2310_ = v___y_2337_;
v___y_2311_ = v___y_2338_;
v___y_2312_ = v___y_2339_;
v___y_2313_ = v___y_2340_;
v___y_2314_ = v___y_2341_;
v___y_2315_ = v___y_2342_;
v___y_2316_ = v___y_2343_;
goto v___jp_2307_;
}
else
{
lean_dec_ref(v_mod_x3f_2215_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec_ref(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec_ref(v_params_2213_);
v___x_2345_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__3);
v___x_2346_ = l_Lean_indentExpr(v___y_2337_);
v___x_2347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2347_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec_ref(v___y_2342_);
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
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
else
{
v___y_2308_ = v___y_2334_;
v___y_2309_ = v___y_2335_;
v___y_2310_ = v___y_2337_;
v___y_2311_ = v___y_2338_;
v___y_2312_ = v___y_2339_;
v___y_2313_ = v___y_2340_;
v___y_2314_ = v___y_2341_;
v___y_2315_ = v___y_2342_;
v___y_2316_ = v___y_2343_;
goto v___jp_2307_;
}
}
}
else
{
lean_object* v_extra_2357_; 
lean_dec_ref(v___y_2337_);
lean_dec_ref(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v_mod_x3f_2215_);
v_extra_2357_ = lean_ctor_get(v_params_2213_, 2);
lean_inc_ref(v_extra_2357_);
if (lean_obj_tag(v___y_2336_) == 2)
{
lean_object* v_config_2358_; lean_object* v_extensions_2359_; lean_object* v_extraInj_2360_; lean_object* v_extraFacts_2361_; lean_object* v_symPrios_2362_; lean_object* v_norm_2363_; lean_object* v_normProcs_2364_; lean_object* v_anchorRefs_x3f_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2420_; 
v_config_2358_ = lean_ctor_get(v_params_2213_, 0);
v_extensions_2359_ = lean_ctor_get(v_params_2213_, 1);
v_extraInj_2360_ = lean_ctor_get(v_params_2213_, 3);
v_extraFacts_2361_ = lean_ctor_get(v_params_2213_, 4);
v_symPrios_2362_ = lean_ctor_get(v_params_2213_, 5);
v_norm_2363_ = lean_ctor_get(v_params_2213_, 6);
v_normProcs_2364_ = lean_ctor_get(v_params_2213_, 7);
v_anchorRefs_x3f_2365_ = lean_ctor_get(v_params_2213_, 8);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_params_2213_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v_params_2213_, 2);
lean_dec(v_unused_2421_);
v___x_2367_ = v_params_2213_;
v_isShared_2368_ = v_isSharedCheck_2420_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_anchorRefs_x3f_2365_);
lean_inc(v_normProcs_2364_);
lean_inc(v_norm_2363_);
lean_inc(v_symPrios_2362_);
lean_inc(v_extraFacts_2361_);
lean_inc(v_extraInj_2360_);
lean_inc(v_extensions_2359_);
lean_inc(v_config_2358_);
lean_dec(v_params_2213_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2420_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v_size_2369_; uint8_t v_gen_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2419_; 
v_size_2369_ = lean_ctor_get(v_extra_2357_, 2);
v_gen_2370_ = lean_ctor_get_uint8(v___y_2336_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___y_2336_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2372_ = v___y_2336_;
v_isShared_2373_ = v_isSharedCheck_2419_;
goto v_resetjp_2371_;
}
else
{
lean_dec(v___y_2336_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2419_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; 
v___x_2374_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_2217_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v___x_2376_; 
lean_dec_ref(v___x_2374_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set_tag(v___x_2372_, 0);
v___x_2376_ = v___x_2372_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v_reuseFailAlloc_2410_, 0, v_gen_2370_);
v___x_2376_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; 
lean_inc_ref(v___y_2333_);
lean_inc(v___y_2343_);
lean_inc_ref(v___y_2342_);
lean_inc(v___y_2341_);
lean_inc_ref(v___y_2340_);
lean_inc(v_size_2369_);
v___x_2377_ = lean_apply_7(v___y_2333_, v___x_2376_, v_size_2369_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, lean_box(0));
if (lean_obj_tag(v___x_2377_) == 0)
{
lean_object* v_a_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_a_2378_ = lean_ctor_get(v___x_2377_, 0);
lean_inc(v_a_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2379_, 0, v_gen_2370_);
lean_inc(v___y_2343_);
lean_inc(v___y_2341_);
lean_inc_ref(v___y_2340_);
lean_inc(v_size_2369_);
v___x_2380_ = lean_apply_7(v___y_2333_, v___x_2379_, v_size_2369_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, lean_box(0));
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2393_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2383_ = v___x_2380_;
v_isShared_2384_ = v_isSharedCheck_2393_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2393_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2385_ = l_Lean_PersistentArray_push___redArg(v_extra_2357_, v_a_2378_);
v___x_2386_ = l_Lean_PersistentArray_push___redArg(v___x_2385_, v_a_2381_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 2, v___x_2386_);
v___x_2388_ = v___x_2367_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_config_2358_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_extensions_2359_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2392_, 3, v_extraInj_2360_);
lean_ctor_set(v_reuseFailAlloc_2392_, 4, v_extraFacts_2361_);
lean_ctor_set(v_reuseFailAlloc_2392_, 5, v_symPrios_2362_);
lean_ctor_set(v_reuseFailAlloc_2392_, 6, v_norm_2363_);
lean_ctor_set(v_reuseFailAlloc_2392_, 7, v_normProcs_2364_);
lean_ctor_set(v_reuseFailAlloc_2392_, 8, v_anchorRefs_x3f_2365_);
v___x_2388_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2388_);
v___x_2390_ = v___x_2383_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec(v_a_2378_);
lean_del_object(v___x_2367_);
lean_dec(v_anchorRefs_x3f_2365_);
lean_dec_ref(v_normProcs_2364_);
lean_dec_ref(v_norm_2363_);
lean_dec_ref(v_symPrios_2362_);
lean_dec_ref(v_extraFacts_2361_);
lean_dec_ref(v_extraInj_2360_);
lean_dec_ref(v_extensions_2359_);
lean_dec_ref(v_config_2358_);
lean_dec_ref(v_extra_2357_);
v_a_2394_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2380_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2380_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_del_object(v___x_2367_);
lean_dec(v_anchorRefs_x3f_2365_);
lean_dec_ref(v_normProcs_2364_);
lean_dec_ref(v_norm_2363_);
lean_dec_ref(v_symPrios_2362_);
lean_dec_ref(v_extraFacts_2361_);
lean_dec_ref(v_extraInj_2360_);
lean_dec_ref(v_extensions_2359_);
lean_dec_ref(v_config_2358_);
lean_dec_ref(v_extra_2357_);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___y_2333_);
v_a_2402_ = lean_ctor_get(v___x_2377_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2377_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2377_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2377_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_del_object(v___x_2372_);
lean_del_object(v___x_2367_);
lean_dec(v_anchorRefs_x3f_2365_);
lean_dec_ref(v_normProcs_2364_);
lean_dec_ref(v_norm_2363_);
lean_dec_ref(v_symPrios_2362_);
lean_dec_ref(v_extraFacts_2361_);
lean_dec_ref(v_extraInj_2360_);
lean_dec_ref(v_extensions_2359_);
lean_dec_ref(v_config_2358_);
lean_dec_ref(v_extra_2357_);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___y_2333_);
v_a_2411_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2374_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2374_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
else
{
switch(lean_obj_tag(v___y_2336_))
{
case 0:
{
lean_object* v_config_2422_; lean_object* v_extensions_2423_; lean_object* v_extraInj_2424_; lean_object* v_extraFacts_2425_; lean_object* v_symPrios_2426_; lean_object* v_norm_2427_; lean_object* v_normProcs_2428_; lean_object* v_anchorRefs_x3f_2429_; lean_object* v_size_2430_; 
v_config_2422_ = lean_ctor_get(v_params_2213_, 0);
lean_inc_ref(v_config_2422_);
v_extensions_2423_ = lean_ctor_get(v_params_2213_, 1);
lean_inc_ref(v_extensions_2423_);
v_extraInj_2424_ = lean_ctor_get(v_params_2213_, 3);
lean_inc_ref(v_extraInj_2424_);
v_extraFacts_2425_ = lean_ctor_get(v_params_2213_, 4);
lean_inc_ref(v_extraFacts_2425_);
v_symPrios_2426_ = lean_ctor_get(v_params_2213_, 5);
lean_inc_ref(v_symPrios_2426_);
v_norm_2427_ = lean_ctor_get(v_params_2213_, 6);
lean_inc_ref(v_norm_2427_);
v_normProcs_2428_ = lean_ctor_get(v_params_2213_, 7);
lean_inc_ref(v_normProcs_2428_);
v_anchorRefs_x3f_2429_ = lean_ctor_get(v_params_2213_, 8);
lean_inc(v_anchorRefs_x3f_2429_);
lean_dec_ref(v_params_2213_);
v_size_2430_ = lean_ctor_get(v_extra_2357_, 2);
lean_inc(v_size_2430_);
v___y_2262_ = v_norm_2427_;
v___y_2263_ = v_anchorRefs_x3f_2429_;
v___y_2264_ = v_extraFacts_2425_;
v___y_2265_ = v___y_2342_;
v___y_2266_ = v_extensions_2423_;
v___y_2267_ = v___y_2340_;
v___y_2268_ = v_extra_2357_;
v___y_2269_ = v___y_2333_;
v___y_2270_ = v_config_2422_;
v___y_2271_ = v_symPrios_2426_;
v___y_2272_ = v___y_2341_;
v___y_2273_ = v_normProcs_2428_;
v___y_2274_ = v_extraInj_2424_;
v___y_2275_ = v___y_2336_;
v___y_2276_ = v_size_2430_;
v___y_2277_ = v___y_2343_;
goto v___jp_2261_;
}
case 1:
{
lean_object* v_config_2431_; lean_object* v_extensions_2432_; lean_object* v_extraInj_2433_; lean_object* v_extraFacts_2434_; lean_object* v_symPrios_2435_; lean_object* v_norm_2436_; lean_object* v_normProcs_2437_; lean_object* v_anchorRefs_x3f_2438_; lean_object* v_size_2439_; 
v_config_2431_ = lean_ctor_get(v_params_2213_, 0);
lean_inc_ref(v_config_2431_);
v_extensions_2432_ = lean_ctor_get(v_params_2213_, 1);
lean_inc_ref(v_extensions_2432_);
v_extraInj_2433_ = lean_ctor_get(v_params_2213_, 3);
lean_inc_ref(v_extraInj_2433_);
v_extraFacts_2434_ = lean_ctor_get(v_params_2213_, 4);
lean_inc_ref(v_extraFacts_2434_);
v_symPrios_2435_ = lean_ctor_get(v_params_2213_, 5);
lean_inc_ref(v_symPrios_2435_);
v_norm_2436_ = lean_ctor_get(v_params_2213_, 6);
lean_inc_ref(v_norm_2436_);
v_normProcs_2437_ = lean_ctor_get(v_params_2213_, 7);
lean_inc_ref(v_normProcs_2437_);
v_anchorRefs_x3f_2438_ = lean_ctor_get(v_params_2213_, 8);
lean_inc(v_anchorRefs_x3f_2438_);
lean_dec_ref(v_params_2213_);
v_size_2439_ = lean_ctor_get(v_extra_2357_, 2);
lean_inc(v_size_2439_);
v___y_2262_ = v_norm_2436_;
v___y_2263_ = v_anchorRefs_x3f_2438_;
v___y_2264_ = v_extraFacts_2434_;
v___y_2265_ = v___y_2342_;
v___y_2266_ = v_extensions_2432_;
v___y_2267_ = v___y_2340_;
v___y_2268_ = v_extra_2357_;
v___y_2269_ = v___y_2333_;
v___y_2270_ = v_config_2431_;
v___y_2271_ = v_symPrios_2435_;
v___y_2272_ = v___y_2341_;
v___y_2273_ = v_normProcs_2437_;
v___y_2274_ = v_extraInj_2433_;
v___y_2275_ = v___y_2336_;
v___y_2276_ = v_size_2439_;
v___y_2277_ = v___y_2343_;
goto v___jp_2261_;
}
default: 
{
lean_object* v_config_2440_; lean_object* v_extensions_2441_; lean_object* v_extraInj_2442_; lean_object* v_extraFacts_2443_; lean_object* v_symPrios_2444_; lean_object* v_norm_2445_; lean_object* v_normProcs_2446_; lean_object* v_anchorRefs_x3f_2447_; lean_object* v_size_2448_; 
v_config_2440_ = lean_ctor_get(v_params_2213_, 0);
lean_inc_ref(v_config_2440_);
v_extensions_2441_ = lean_ctor_get(v_params_2213_, 1);
lean_inc_ref(v_extensions_2441_);
v_extraInj_2442_ = lean_ctor_get(v_params_2213_, 3);
lean_inc_ref(v_extraInj_2442_);
v_extraFacts_2443_ = lean_ctor_get(v_params_2213_, 4);
lean_inc_ref(v_extraFacts_2443_);
v_symPrios_2444_ = lean_ctor_get(v_params_2213_, 5);
lean_inc_ref(v_symPrios_2444_);
v_norm_2445_ = lean_ctor_get(v_params_2213_, 6);
lean_inc_ref(v_norm_2445_);
v_normProcs_2446_ = lean_ctor_get(v_params_2213_, 7);
lean_inc_ref(v_normProcs_2446_);
v_anchorRefs_x3f_2447_ = lean_ctor_get(v_params_2213_, 8);
lean_inc(v_anchorRefs_x3f_2447_);
lean_dec_ref(v_params_2213_);
v_size_2448_ = lean_ctor_get(v_extra_2357_, 2);
lean_inc(v_size_2448_);
v___y_2226_ = v_extra_2357_;
v___y_2227_ = v___y_2333_;
v___y_2228_ = v_norm_2445_;
v___y_2229_ = v_anchorRefs_x3f_2447_;
v___y_2230_ = v_config_2440_;
v___y_2231_ = v_symPrios_2444_;
v___y_2232_ = v_normProcs_2446_;
v___y_2233_ = v_extraFacts_2443_;
v___y_2234_ = v_extraInj_2442_;
v___y_2235_ = v___y_2336_;
v___y_2236_ = v_extensions_2441_;
v___y_2237_ = v_size_2448_;
v___y_2238_ = v___y_2340_;
v___y_2239_ = v___y_2341_;
v___y_2240_ = v___y_2342_;
v___y_2241_ = v___y_2343_;
goto v___jp_2225_;
}
}
}
}
}
v___jp_2449_:
{
lean_object* v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; 
v___x_2457_ = lean_box(0);
v___x_2458_ = 1;
v___x_2459_ = lean_box(v___x_2458_);
lean_inc(v_p_2214_);
v___f_2460_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2460_, 0, v_p_2214_);
lean_closure_set(v___f_2460_, 1, v_term_2216_);
lean_closure_set(v___f_2460_, 2, v___x_2457_);
lean_closure_set(v___f_2460_, 3, v___x_2459_);
v___x_2461_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(v___f_2460_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2506_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2506_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2506_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
if (lean_obj_tag(v_a_2462_) == 1)
{
lean_object* v_val_2466_; lean_object* v_fst_2467_; lean_object* v_snd_2468_; lean_object* v___x_2469_; 
lean_del_object(v___x_2464_);
v_val_2466_ = lean_ctor_get(v_a_2462_, 0);
lean_inc(v_val_2466_);
lean_dec_ref(v_a_2462_);
v_fst_2467_ = lean_ctor_get(v_val_2466_, 0);
lean_inc(v_fst_2467_);
v_snd_2468_ = lean_ctor_get(v_val_2466_, 1);
lean_inc_n(v_snd_2468_, 2);
lean_dec(v_val_2466_);
lean_inc(v___y_2456_);
lean_inc_ref(v___y_2455_);
lean_inc(v___y_2454_);
lean_inc_ref(v___y_2453_);
v___x_2469_ = lean_infer_type(v_snd_2468_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2471_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc_n(v_a_2470_, 2);
lean_dec_ref(v___x_2469_);
v___x_2471_ = l_Lean_Meta_isProp(v_a_2470_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___f_2475_; uint8_t v___x_2476_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref(v___x_2471_);
v___x_2473_ = lean_box(v___x_2458_);
v___x_2474_ = lean_box(v_minIndexable_2217_);
lean_inc(v_snd_2468_);
lean_inc(v_fst_2467_);
lean_inc_ref(v_params_2213_);
v___f_2475_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___lam__1___boxed), 13, 6);
lean_closure_set(v___f_2475_, 0, v_params_2213_);
lean_closure_set(v___f_2475_, 1, v_p_2214_);
lean_closure_set(v___f_2475_, 2, v_fst_2467_);
lean_closure_set(v___f_2475_, 3, v_snd_2468_);
lean_closure_set(v___f_2475_, 4, v___x_2473_);
lean_closure_set(v___f_2475_, 5, v___x_2474_);
v___x_2476_ = lean_unbox(v_a_2472_);
lean_dec(v_a_2472_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v___f_2475_);
lean_dec(v_a_2470_);
lean_dec(v_snd_2468_);
lean_dec(v_fst_2467_);
lean_dec(v_kind_2450_);
lean_dec(v_mod_x3f_2215_);
lean_dec_ref(v_params_2213_);
v___x_2477_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__5);
v___x_2478_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_2477_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec_ref(v___y_2455_);
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
else
{
v___y_2333_ = v___f_2475_;
v___y_2334_ = v_snd_2468_;
v___y_2335_ = v_fst_2467_;
v___y_2336_ = v_kind_2450_;
v___y_2337_ = v_a_2470_;
v___y_2338_ = v___y_2451_;
v___y_2339_ = v___y_2452_;
v___y_2340_ = v___y_2453_;
v___y_2341_ = v___y_2454_;
v___y_2342_ = v___y_2455_;
v___y_2343_ = v___y_2456_;
goto v___jp_2332_;
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_a_2470_);
lean_dec(v_snd_2468_);
lean_dec(v_fst_2467_);
lean_dec_ref(v___y_2455_);
lean_dec(v_kind_2450_);
lean_dec(v_mod_x3f_2215_);
lean_dec(v_p_2214_);
lean_dec_ref(v_params_2213_);
v_a_2487_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2471_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2471_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v_snd_2468_);
lean_dec(v_fst_2467_);
lean_dec_ref(v___y_2455_);
lean_dec(v_kind_2450_);
lean_dec(v_mod_x3f_2215_);
lean_dec(v_p_2214_);
lean_dec_ref(v_params_2213_);
v_a_2495_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2469_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2469_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_object* v___x_2504_; 
lean_dec(v_a_2462_);
lean_dec_ref(v___y_2455_);
lean_dec(v_kind_2450_);
lean_dec(v_mod_x3f_2215_);
lean_dec(v_p_2214_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v_params_2213_);
v___x_2504_ = v___x_2464_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_params_2213_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_dec_ref(v___y_2455_);
lean_dec(v_kind_2450_);
lean_dec(v_mod_x3f_2215_);
lean_dec(v_p_2214_);
lean_dec_ref(v_params_2213_);
v_a_2507_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2461_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2461_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
v___jp_2515_:
{
lean_object* v___x_2522_; 
v___x_2522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_kind_2450_ = v___x_2522_;
v___y_2451_ = v___y_2516_;
v___y_2452_ = v___y_2517_;
v___y_2453_ = v___y_2518_;
v___y_2454_ = v___y_2519_;
v___y_2455_ = v___y_2520_;
v___y_2456_ = v___y_2521_;
goto v___jp_2449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___boxed(lean_object* v_params_2609_, lean_object* v_p_2610_, lean_object* v_mod_x3f_2611_, lean_object* v_term_2612_, lean_object* v_minIndexable_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
uint8_t v_minIndexable_boxed_2621_; lean_object* v_res_2622_; 
v_minIndexable_boxed_2621_ = lean_unbox(v_minIndexable_2613_);
v_res_2622_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_2609_, v_p_2610_, v_mod_x3f_2611_, v_term_2612_, v_minIndexable_boxed_2621_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(lean_object* v_00_u03b1_2623_, lean_object* v_msg_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___boxed(lean_object* v_00_u03b1_2633_, lean_object* v_msg_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1(v_00_u03b1_2633_, v_msg_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(lean_object* v_msgData_2643_, lean_object* v_macroStack_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___redArg(v_msgData_2643_, v_macroStack_2644_, v___y_2649_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1___boxed(lean_object* v_msgData_2653_, lean_object* v_macroStack_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1_spec__1(v_msgData_2653_, v_macroStack_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(lean_object* v_params_2663_, lean_object* v_val_2664_, lean_object* v_____r_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___x_2673_; lean_object* v_ext_2674_; lean_object* v_toEnvExtension_2675_; lean_object* v_env_2676_; lean_object* v_config_2677_; lean_object* v_extensions_2678_; lean_object* v_extra_2679_; lean_object* v_extraInj_2680_; lean_object* v_extraFacts_2681_; lean_object* v_symPrios_2682_; lean_object* v_norm_2683_; lean_object* v_normProcs_2684_; lean_object* v_anchorRefs_x3f_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2698_; 
v___x_2673_ = lean_st_ref_get(v___y_2671_);
v_ext_2674_ = lean_ctor_get(v_val_2664_, 1);
v_toEnvExtension_2675_ = lean_ctor_get(v_ext_2674_, 0);
v_env_2676_ = lean_ctor_get(v___x_2673_, 0);
lean_inc_ref(v_env_2676_);
lean_dec(v___x_2673_);
v_config_2677_ = lean_ctor_get(v_params_2663_, 0);
v_extensions_2678_ = lean_ctor_get(v_params_2663_, 1);
v_extra_2679_ = lean_ctor_get(v_params_2663_, 2);
v_extraInj_2680_ = lean_ctor_get(v_params_2663_, 3);
v_extraFacts_2681_ = lean_ctor_get(v_params_2663_, 4);
v_symPrios_2682_ = lean_ctor_get(v_params_2663_, 5);
v_norm_2683_ = lean_ctor_get(v_params_2663_, 6);
v_normProcs_2684_ = lean_ctor_get(v_params_2663_, 7);
v_anchorRefs_x3f_2685_ = lean_ctor_get(v_params_2663_, 8);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_params_2663_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2687_ = v_params_2663_;
v_isShared_2688_ = v_isSharedCheck_2698_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_anchorRefs_x3f_2685_);
lean_inc(v_normProcs_2684_);
lean_inc(v_norm_2683_);
lean_inc(v_symPrios_2682_);
lean_inc(v_extraFacts_2681_);
lean_inc(v_extraInj_2680_);
lean_inc(v_extra_2679_);
lean_inc(v_extensions_2678_);
lean_inc(v_config_2677_);
lean_dec(v_params_2663_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2698_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_asyncMode_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v_asyncMode_2689_ = lean_ctor_get(v_toEnvExtension_2675_, 2);
v___x_2690_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2691_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2690_, v_val_2664_, v_env_2676_, v_asyncMode_2689_);
v___x_2692_ = lean_array_push(v_extensions_2678_, v___x_2691_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v___x_2692_);
v___x_2694_ = v___x_2687_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_config_2677_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v_extra_2679_);
lean_ctor_set(v_reuseFailAlloc_2697_, 3, v_extraInj_2680_);
lean_ctor_set(v_reuseFailAlloc_2697_, 4, v_extraFacts_2681_);
lean_ctor_set(v_reuseFailAlloc_2697_, 5, v_symPrios_2682_);
lean_ctor_set(v_reuseFailAlloc_2697_, 6, v_norm_2683_);
lean_ctor_set(v_reuseFailAlloc_2697_, 7, v_normProcs_2684_);
lean_ctor_set(v_reuseFailAlloc_2697_, 8, v_anchorRefs_x3f_2685_);
v___x_2694_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
return v___x_2696_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0___boxed(lean_object* v_params_2699_, lean_object* v_val_2700_, lean_object* v_____r_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_2699_, v_val_2700_, v_____r_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v_val_2700_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(lean_object* v_p_2710_, lean_object* v_id_2711_, uint8_t v_minIndexable_2712_, lean_object* v_as_x27_2713_, lean_object* v_b_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
if (lean_obj_tag(v_as_x27_2713_) == 0)
{
lean_object* v___x_2720_; 
lean_dec(v_id_2711_);
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_b_2714_);
return v___x_2720_;
}
else
{
lean_object* v_head_2721_; lean_object* v_tail_2722_; lean_object* v_fileName_2723_; lean_object* v_fileMap_2724_; lean_object* v_options_2725_; lean_object* v_currRecDepth_2726_; lean_object* v_maxRecDepth_2727_; lean_object* v_ref_2728_; lean_object* v_currNamespace_2729_; lean_object* v_openDecls_2730_; lean_object* v_initHeartbeats_2731_; lean_object* v_maxHeartbeats_2732_; lean_object* v_quotContext_2733_; lean_object* v_currMacroScope_2734_; uint8_t v_diag_2735_; lean_object* v_cancelTk_x3f_2736_; uint8_t v_suppressElabErrors_2737_; lean_object* v_inheritedTraceOptions_2738_; uint8_t v___x_2739_; lean_object* v___x_2740_; lean_object* v_ref_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v_head_2721_ = lean_ctor_get(v_as_x27_2713_, 0);
v_tail_2722_ = lean_ctor_get(v_as_x27_2713_, 1);
v_fileName_2723_ = lean_ctor_get(v___y_2717_, 0);
v_fileMap_2724_ = lean_ctor_get(v___y_2717_, 1);
v_options_2725_ = lean_ctor_get(v___y_2717_, 2);
v_currRecDepth_2726_ = lean_ctor_get(v___y_2717_, 3);
v_maxRecDepth_2727_ = lean_ctor_get(v___y_2717_, 4);
v_ref_2728_ = lean_ctor_get(v___y_2717_, 5);
v_currNamespace_2729_ = lean_ctor_get(v___y_2717_, 6);
v_openDecls_2730_ = lean_ctor_get(v___y_2717_, 7);
v_initHeartbeats_2731_ = lean_ctor_get(v___y_2717_, 8);
v_maxHeartbeats_2732_ = lean_ctor_get(v___y_2717_, 9);
v_quotContext_2733_ = lean_ctor_get(v___y_2717_, 10);
v_currMacroScope_2734_ = lean_ctor_get(v___y_2717_, 11);
v_diag_2735_ = lean_ctor_get_uint8(v___y_2717_, sizeof(void*)*14);
v_cancelTk_x3f_2736_ = lean_ctor_get(v___y_2717_, 12);
v_suppressElabErrors_2737_ = lean_ctor_get_uint8(v___y_2717_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2738_ = lean_ctor_get(v___y_2717_, 13);
v___x_2739_ = 0;
v___x_2740_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v_ref_2741_ = l_Lean_replaceRef(v_p_2710_, v_ref_2728_);
lean_inc_ref(v_inheritedTraceOptions_2738_);
lean_inc(v_cancelTk_x3f_2736_);
lean_inc(v_currMacroScope_2734_);
lean_inc(v_quotContext_2733_);
lean_inc(v_maxHeartbeats_2732_);
lean_inc(v_initHeartbeats_2731_);
lean_inc(v_openDecls_2730_);
lean_inc(v_currNamespace_2729_);
lean_inc(v_maxRecDepth_2727_);
lean_inc(v_currRecDepth_2726_);
lean_inc_ref(v_options_2725_);
lean_inc_ref(v_fileMap_2724_);
lean_inc_ref(v_fileName_2723_);
v___x_2742_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2742_, 0, v_fileName_2723_);
lean_ctor_set(v___x_2742_, 1, v_fileMap_2724_);
lean_ctor_set(v___x_2742_, 2, v_options_2725_);
lean_ctor_set(v___x_2742_, 3, v_currRecDepth_2726_);
lean_ctor_set(v___x_2742_, 4, v_maxRecDepth_2727_);
lean_ctor_set(v___x_2742_, 5, v_ref_2741_);
lean_ctor_set(v___x_2742_, 6, v_currNamespace_2729_);
lean_ctor_set(v___x_2742_, 7, v_openDecls_2730_);
lean_ctor_set(v___x_2742_, 8, v_initHeartbeats_2731_);
lean_ctor_set(v___x_2742_, 9, v_maxHeartbeats_2732_);
lean_ctor_set(v___x_2742_, 10, v_quotContext_2733_);
lean_ctor_set(v___x_2742_, 11, v_currMacroScope_2734_);
lean_ctor_set(v___x_2742_, 12, v_cancelTk_x3f_2736_);
lean_ctor_set(v___x_2742_, 13, v_inheritedTraceOptions_2738_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*14, v_diag_2735_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*14 + 1, v_suppressElabErrors_2737_);
lean_inc(v_head_2721_);
lean_inc(v_id_2711_);
v___x_2743_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2714_, v_id_2711_, v_head_2721_, v___x_2740_, v_minIndexable_2712_, v___x_2739_, v___x_2739_, v___y_2715_, v___y_2716_, v___x_2742_, v___y_2718_);
lean_dec_ref(v___x_2742_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref(v___x_2743_);
v_as_x27_2713_ = v_tail_2722_;
v_b_2714_ = v_a_2744_;
goto _start;
}
else
{
lean_dec(v_id_2711_);
return v___x_2743_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg___boxed(lean_object* v_p_2746_, lean_object* v_id_2747_, lean_object* v_minIndexable_2748_, lean_object* v_as_x27_2749_, lean_object* v_b_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
uint8_t v_minIndexable_boxed_2756_; lean_object* v_res_2757_; 
v_minIndexable_boxed_2756_ = lean_unbox(v_minIndexable_2748_);
v_res_2757_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_2746_, v_id_2747_, v_minIndexable_boxed_2756_, v_as_x27_2749_, v_b_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v_as_x27_2749_);
lean_dec(v_p_2746_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(lean_object* v_k_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
if (lean_obj_tag(v_a_2759_) == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = l_List_reverse___redArg(v_a_2760_);
return v___x_2761_;
}
else
{
lean_object* v_head_2762_; lean_object* v_tail_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2774_; 
v_head_2762_ = lean_ctor_get(v_a_2759_, 0);
v_tail_2763_ = lean_ctor_get(v_a_2759_, 1);
v_isSharedCheck_2774_ = !lean_is_exclusive(v_a_2759_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2765_ = v_a_2759_;
v_isShared_2766_ = v_isSharedCheck_2774_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_tail_2763_);
lean_inc(v_head_2762_);
lean_dec(v_a_2759_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2774_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v_kind_2767_; uint8_t v___x_2768_; 
v_kind_2767_ = lean_ctor_get(v_head_2762_, 6);
v___x_2768_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_kind_2767_, v_k_2758_);
if (v___x_2768_ == 0)
{
lean_del_object(v___x_2765_);
lean_dec(v_head_2762_);
v_a_2759_ = v_tail_2763_;
goto _start;
}
else
{
lean_object* v___x_2771_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 1, v_a_2760_);
v___x_2771_ = v___x_2765_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_head_2762_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_a_2760_);
v___x_2771_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
v_a_2759_ = v_tail_2763_;
v_a_2760_ = v___x_2771_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1___boxed(lean_object* v_k_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v_k_2775_, v_a_2776_, v_a_2777_);
lean_dec(v_k_2775_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(lean_object* v_ref_2779_, lean_object* v_msg_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_fileName_2788_; lean_object* v_fileMap_2789_; lean_object* v_options_2790_; lean_object* v_currRecDepth_2791_; lean_object* v_maxRecDepth_2792_; lean_object* v_ref_2793_; lean_object* v_currNamespace_2794_; lean_object* v_openDecls_2795_; lean_object* v_initHeartbeats_2796_; lean_object* v_maxHeartbeats_2797_; lean_object* v_quotContext_2798_; lean_object* v_currMacroScope_2799_; uint8_t v_diag_2800_; lean_object* v_cancelTk_x3f_2801_; uint8_t v_suppressElabErrors_2802_; lean_object* v_inheritedTraceOptions_2803_; lean_object* v_ref_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_fileName_2788_ = lean_ctor_get(v___y_2785_, 0);
v_fileMap_2789_ = lean_ctor_get(v___y_2785_, 1);
v_options_2790_ = lean_ctor_get(v___y_2785_, 2);
v_currRecDepth_2791_ = lean_ctor_get(v___y_2785_, 3);
v_maxRecDepth_2792_ = lean_ctor_get(v___y_2785_, 4);
v_ref_2793_ = lean_ctor_get(v___y_2785_, 5);
v_currNamespace_2794_ = lean_ctor_get(v___y_2785_, 6);
v_openDecls_2795_ = lean_ctor_get(v___y_2785_, 7);
v_initHeartbeats_2796_ = lean_ctor_get(v___y_2785_, 8);
v_maxHeartbeats_2797_ = lean_ctor_get(v___y_2785_, 9);
v_quotContext_2798_ = lean_ctor_get(v___y_2785_, 10);
v_currMacroScope_2799_ = lean_ctor_get(v___y_2785_, 11);
v_diag_2800_ = lean_ctor_get_uint8(v___y_2785_, sizeof(void*)*14);
v_cancelTk_x3f_2801_ = lean_ctor_get(v___y_2785_, 12);
v_suppressElabErrors_2802_ = lean_ctor_get_uint8(v___y_2785_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2803_ = lean_ctor_get(v___y_2785_, 13);
v_ref_2804_ = l_Lean_replaceRef(v_ref_2779_, v_ref_2793_);
lean_inc_ref(v_inheritedTraceOptions_2803_);
lean_inc(v_cancelTk_x3f_2801_);
lean_inc(v_currMacroScope_2799_);
lean_inc(v_quotContext_2798_);
lean_inc(v_maxHeartbeats_2797_);
lean_inc(v_initHeartbeats_2796_);
lean_inc(v_openDecls_2795_);
lean_inc(v_currNamespace_2794_);
lean_inc(v_maxRecDepth_2792_);
lean_inc(v_currRecDepth_2791_);
lean_inc_ref(v_options_2790_);
lean_inc_ref(v_fileMap_2789_);
lean_inc_ref(v_fileName_2788_);
v___x_2805_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2805_, 0, v_fileName_2788_);
lean_ctor_set(v___x_2805_, 1, v_fileMap_2789_);
lean_ctor_set(v___x_2805_, 2, v_options_2790_);
lean_ctor_set(v___x_2805_, 3, v_currRecDepth_2791_);
lean_ctor_set(v___x_2805_, 4, v_maxRecDepth_2792_);
lean_ctor_set(v___x_2805_, 5, v_ref_2804_);
lean_ctor_set(v___x_2805_, 6, v_currNamespace_2794_);
lean_ctor_set(v___x_2805_, 7, v_openDecls_2795_);
lean_ctor_set(v___x_2805_, 8, v_initHeartbeats_2796_);
lean_ctor_set(v___x_2805_, 9, v_maxHeartbeats_2797_);
lean_ctor_set(v___x_2805_, 10, v_quotContext_2798_);
lean_ctor_set(v___x_2805_, 11, v_currMacroScope_2799_);
lean_ctor_set(v___x_2805_, 12, v_cancelTk_x3f_2801_);
lean_ctor_set(v___x_2805_, 13, v_inheritedTraceOptions_2803_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*14, v_diag_2800_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*14 + 1, v_suppressElabErrors_2802_);
v___x_2806_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v_msg_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___x_2805_, v___y_2786_);
lean_dec_ref(v___x_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg___boxed(lean_object* v_ref_2807_, lean_object* v_msg_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_2807_, v_msg_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v_ref_2807_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(lean_object* v_p_2817_, lean_object* v_id_2818_, uint8_t v_minIndexable_2819_, lean_object* v_as_x27_2820_, lean_object* v_b_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
if (lean_obj_tag(v_as_x27_2820_) == 0)
{
lean_object* v___x_2827_; 
lean_dec(v_id_2818_);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v_b_2821_);
return v___x_2827_;
}
else
{
lean_object* v_head_2828_; lean_object* v_tail_2829_; lean_object* v_fileName_2830_; lean_object* v_fileMap_2831_; lean_object* v_options_2832_; lean_object* v_currRecDepth_2833_; lean_object* v_maxRecDepth_2834_; lean_object* v_ref_2835_; lean_object* v_currNamespace_2836_; lean_object* v_openDecls_2837_; lean_object* v_initHeartbeats_2838_; lean_object* v_maxHeartbeats_2839_; lean_object* v_quotContext_2840_; lean_object* v_currMacroScope_2841_; uint8_t v_diag_2842_; lean_object* v_cancelTk_x3f_2843_; uint8_t v_suppressElabErrors_2844_; lean_object* v_inheritedTraceOptions_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; lean_object* v_ref_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v_head_2828_ = lean_ctor_get(v_as_x27_2820_, 0);
v_tail_2829_ = lean_ctor_get(v_as_x27_2820_, 1);
v_fileName_2830_ = lean_ctor_get(v___y_2824_, 0);
v_fileMap_2831_ = lean_ctor_get(v___y_2824_, 1);
v_options_2832_ = lean_ctor_get(v___y_2824_, 2);
v_currRecDepth_2833_ = lean_ctor_get(v___y_2824_, 3);
v_maxRecDepth_2834_ = lean_ctor_get(v___y_2824_, 4);
v_ref_2835_ = lean_ctor_get(v___y_2824_, 5);
v_currNamespace_2836_ = lean_ctor_get(v___y_2824_, 6);
v_openDecls_2837_ = lean_ctor_get(v___y_2824_, 7);
v_initHeartbeats_2838_ = lean_ctor_get(v___y_2824_, 8);
v_maxHeartbeats_2839_ = lean_ctor_get(v___y_2824_, 9);
v_quotContext_2840_ = lean_ctor_get(v___y_2824_, 10);
v_currMacroScope_2841_ = lean_ctor_get(v___y_2824_, 11);
v_diag_2842_ = lean_ctor_get_uint8(v___y_2824_, sizeof(void*)*14);
v_cancelTk_x3f_2843_ = lean_ctor_get(v___y_2824_, 12);
v_suppressElabErrors_2844_ = lean_ctor_get_uint8(v___y_2824_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2845_ = lean_ctor_get(v___y_2824_, 13);
v___x_2846_ = 0;
v___x_2847_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_2848_ = 1;
v_ref_2849_ = l_Lean_replaceRef(v_p_2817_, v_ref_2835_);
lean_inc_ref(v_inheritedTraceOptions_2845_);
lean_inc(v_cancelTk_x3f_2843_);
lean_inc(v_currMacroScope_2841_);
lean_inc(v_quotContext_2840_);
lean_inc(v_maxHeartbeats_2839_);
lean_inc(v_initHeartbeats_2838_);
lean_inc(v_openDecls_2837_);
lean_inc(v_currNamespace_2836_);
lean_inc(v_maxRecDepth_2834_);
lean_inc(v_currRecDepth_2833_);
lean_inc_ref(v_options_2832_);
lean_inc_ref(v_fileMap_2831_);
lean_inc_ref(v_fileName_2830_);
v___x_2850_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2850_, 0, v_fileName_2830_);
lean_ctor_set(v___x_2850_, 1, v_fileMap_2831_);
lean_ctor_set(v___x_2850_, 2, v_options_2832_);
lean_ctor_set(v___x_2850_, 3, v_currRecDepth_2833_);
lean_ctor_set(v___x_2850_, 4, v_maxRecDepth_2834_);
lean_ctor_set(v___x_2850_, 5, v_ref_2849_);
lean_ctor_set(v___x_2850_, 6, v_currNamespace_2836_);
lean_ctor_set(v___x_2850_, 7, v_openDecls_2837_);
lean_ctor_set(v___x_2850_, 8, v_initHeartbeats_2838_);
lean_ctor_set(v___x_2850_, 9, v_maxHeartbeats_2839_);
lean_ctor_set(v___x_2850_, 10, v_quotContext_2840_);
lean_ctor_set(v___x_2850_, 11, v_currMacroScope_2841_);
lean_ctor_set(v___x_2850_, 12, v_cancelTk_x3f_2843_);
lean_ctor_set(v___x_2850_, 13, v_inheritedTraceOptions_2845_);
lean_ctor_set_uint8(v___x_2850_, sizeof(void*)*14, v_diag_2842_);
lean_ctor_set_uint8(v___x_2850_, sizeof(void*)*14 + 1, v_suppressElabErrors_2844_);
lean_inc(v_head_2828_);
lean_inc(v_id_2818_);
v___x_2851_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_b_2821_, v_id_2818_, v_head_2828_, v___x_2847_, v_minIndexable_2819_, v___x_2846_, v___x_2848_, v___y_2822_, v___y_2823_, v___x_2850_, v___y_2825_);
lean_dec_ref(v___x_2850_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___x_2851_);
v_as_x27_2820_ = v_tail_2829_;
v_b_2821_ = v_a_2852_;
goto _start;
}
else
{
lean_dec(v_id_2818_);
return v___x_2851_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg___boxed(lean_object* v_p_2854_, lean_object* v_id_2855_, lean_object* v_minIndexable_2856_, lean_object* v_as_x27_2857_, lean_object* v_b_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
uint8_t v_minIndexable_boxed_2864_; lean_object* v_res_2865_; 
v_minIndexable_boxed_2864_ = lean_unbox(v_minIndexable_2856_);
v_res_2865_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_2854_, v_id_2855_, v_minIndexable_boxed_2864_, v_as_x27_2857_, v_b_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v_as_x27_2857_);
lean_dec(v_p_2854_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(lean_object* v_x_2866_){
_start:
{
if (lean_obj_tag(v_x_2866_) == 0)
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_box(0);
return v___x_2867_;
}
else
{
lean_object* v_head_2868_; lean_object* v_tail_2869_; lean_object* v_fst_2870_; uint8_t v___x_2871_; 
v_head_2868_ = lean_ctor_get(v_x_2866_, 0);
v_tail_2869_ = lean_ctor_get(v_x_2866_, 1);
v_fst_2870_ = lean_ctor_get(v_head_2868_, 0);
v___x_2871_ = l_Lean_isPrivateName(v_fst_2870_);
if (v___x_2871_ == 0)
{
v_x_2866_ = v_tail_2869_;
goto _start;
}
else
{
lean_object* v___x_2873_; 
lean_inc(v_head_2868_);
v___x_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2873_, 0, v_head_2868_);
return v___x_2873_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16___boxed(lean_object* v_x_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_x_2874_);
lean_dec(v_x_2874_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(lean_object* v_ref_2876_, lean_object* v_msgData_2877_, uint8_t v_severity_2878_, uint8_t v_isSilent_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; uint8_t v___y_2889_; uint8_t v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; uint8_t v___y_2926_; uint8_t v___y_2927_; uint8_t v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; uint8_t v___y_2951_; uint8_t v___y_2952_; lean_object* v___y_2953_; uint8_t v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; uint8_t v___y_2962_; uint8_t v___y_2963_; lean_object* v___y_2964_; uint8_t v___y_2965_; uint8_t v___x_2970_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; uint8_t v___y_2976_; uint8_t v___y_2977_; uint8_t v___y_2978_; uint8_t v___y_2980_; uint8_t v___x_2995_; 
v___x_2970_ = 2;
v___x_2995_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2878_, v___x_2970_);
if (v___x_2995_ == 0)
{
v___y_2980_ = v___x_2995_;
goto v___jp_2979_;
}
else
{
uint8_t v___x_2996_; 
lean_inc_ref(v_msgData_2877_);
v___x_2996_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2877_);
v___y_2980_ = v___x_2996_;
goto v___jp_2979_;
}
v___jp_2885_:
{
lean_object* v___x_2895_; lean_object* v_currNamespace_2896_; lean_object* v_openDecls_2897_; lean_object* v_env_2898_; lean_object* v_nextMacroScope_2899_; lean_object* v_ngen_2900_; lean_object* v_auxDeclNGen_2901_; lean_object* v_traceState_2902_; lean_object* v_cache_2903_; lean_object* v_messages_2904_; lean_object* v_infoState_2905_; lean_object* v_snapshotTasks_2906_; lean_object* v_newDecls_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2921_; 
v___x_2895_ = lean_st_ref_take(v___y_2894_);
v_currNamespace_2896_ = lean_ctor_get(v___y_2893_, 6);
v_openDecls_2897_ = lean_ctor_get(v___y_2893_, 7);
v_env_2898_ = lean_ctor_get(v___x_2895_, 0);
v_nextMacroScope_2899_ = lean_ctor_get(v___x_2895_, 1);
v_ngen_2900_ = lean_ctor_get(v___x_2895_, 2);
v_auxDeclNGen_2901_ = lean_ctor_get(v___x_2895_, 3);
v_traceState_2902_ = lean_ctor_get(v___x_2895_, 4);
v_cache_2903_ = lean_ctor_get(v___x_2895_, 5);
v_messages_2904_ = lean_ctor_get(v___x_2895_, 6);
v_infoState_2905_ = lean_ctor_get(v___x_2895_, 7);
v_snapshotTasks_2906_ = lean_ctor_get(v___x_2895_, 8);
v_newDecls_2907_ = lean_ctor_get(v___x_2895_, 9);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2909_ = v___x_2895_;
v_isShared_2910_ = v_isSharedCheck_2921_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_newDecls_2907_);
lean_inc(v_snapshotTasks_2906_);
lean_inc(v_infoState_2905_);
lean_inc(v_messages_2904_);
lean_inc(v_cache_2903_);
lean_inc(v_traceState_2902_);
lean_inc(v_auxDeclNGen_2901_);
lean_inc(v_ngen_2900_);
lean_inc(v_nextMacroScope_2899_);
lean_inc(v_env_2898_);
lean_dec(v___x_2895_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2921_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
lean_inc(v_openDecls_2897_);
lean_inc(v_currNamespace_2896_);
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v_currNamespace_2896_);
lean_ctor_set(v___x_2911_, 1, v_openDecls_2897_);
v___x_2912_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v___y_2892_);
lean_inc_ref(v___y_2888_);
lean_inc_ref(v___y_2887_);
v___x_2913_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2913_, 0, v___y_2887_);
lean_ctor_set(v___x_2913_, 1, v___y_2891_);
lean_ctor_set(v___x_2913_, 2, v___y_2886_);
lean_ctor_set(v___x_2913_, 3, v___y_2888_);
lean_ctor_set(v___x_2913_, 4, v___x_2912_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*5, v___y_2890_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*5 + 1, v___y_2889_);
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*5 + 2, v_isSilent_2879_);
v___x_2914_ = l_Lean_MessageLog_add(v___x_2913_, v_messages_2904_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 6, v___x_2914_);
v___x_2916_ = v___x_2909_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_env_2898_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v_nextMacroScope_2899_);
lean_ctor_set(v_reuseFailAlloc_2920_, 2, v_ngen_2900_);
lean_ctor_set(v_reuseFailAlloc_2920_, 3, v_auxDeclNGen_2901_);
lean_ctor_set(v_reuseFailAlloc_2920_, 4, v_traceState_2902_);
lean_ctor_set(v_reuseFailAlloc_2920_, 5, v_cache_2903_);
lean_ctor_set(v_reuseFailAlloc_2920_, 6, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_2920_, 7, v_infoState_2905_);
lean_ctor_set(v_reuseFailAlloc_2920_, 8, v_snapshotTasks_2906_);
lean_ctor_set(v_reuseFailAlloc_2920_, 9, v_newDecls_2907_);
v___x_2916_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = lean_st_ref_set(v___y_2894_, v___x_2916_);
v___x_2918_ = lean_box(0);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
}
v___jp_2922_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2946_; 
v___x_2931_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2877_);
v___x_2932_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__4(v___x_2931_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2946_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2946_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
lean_inc_ref_n(v___y_2929_, 2);
v___x_2937_ = l_Lean_FileMap_toPosition(v___y_2929_, v___y_2925_);
lean_dec(v___y_2925_);
v___x_2938_ = l_Lean_FileMap_toPosition(v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
v___x_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
v___x_2940_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___closed__0));
if (v___y_2928_ == 0)
{
lean_del_object(v___x_2935_);
lean_dec_ref(v___y_2923_);
v___y_2886_ = v___x_2939_;
v___y_2887_ = v___y_2924_;
v___y_2888_ = v___x_2940_;
v___y_2889_ = v___y_2927_;
v___y_2890_ = v___y_2926_;
v___y_2891_ = v___x_2937_;
v___y_2892_ = v_a_2933_;
v___y_2893_ = v___y_2882_;
v___y_2894_ = v___y_2883_;
goto v___jp_2885_;
}
else
{
uint8_t v___x_2941_; 
lean_inc(v_a_2933_);
v___x_2941_ = l_Lean_MessageData_hasTag(v___y_2923_, v_a_2933_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2944_; 
lean_dec_ref(v___x_2939_);
lean_dec_ref(v___x_2937_);
lean_dec(v_a_2933_);
v___x_2942_ = lean_box(0);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 0, v___x_2942_);
v___x_2944_ = v___x_2935_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
else
{
lean_del_object(v___x_2935_);
v___y_2886_ = v___x_2939_;
v___y_2887_ = v___y_2924_;
v___y_2888_ = v___x_2940_;
v___y_2889_ = v___y_2927_;
v___y_2890_ = v___y_2926_;
v___y_2891_ = v___x_2937_;
v___y_2892_ = v_a_2933_;
v___y_2893_ = v___y_2882_;
v___y_2894_ = v___y_2883_;
goto v___jp_2885_;
}
}
}
}
v___jp_2947_:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Syntax_getTailPos_x3f(v___y_2949_, v___y_2952_);
lean_dec(v___y_2949_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_inc(v___y_2955_);
v___y_2923_ = v___y_2948_;
v___y_2924_ = v___y_2950_;
v___y_2925_ = v___y_2955_;
v___y_2926_ = v___y_2952_;
v___y_2927_ = v___y_2951_;
v___y_2928_ = v___y_2954_;
v___y_2929_ = v___y_2953_;
v___y_2930_ = v___y_2955_;
goto v___jp_2922_;
}
else
{
lean_object* v_val_2957_; 
v_val_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_val_2957_);
lean_dec_ref(v___x_2956_);
v___y_2923_ = v___y_2948_;
v___y_2924_ = v___y_2950_;
v___y_2925_ = v___y_2955_;
v___y_2926_ = v___y_2952_;
v___y_2927_ = v___y_2951_;
v___y_2928_ = v___y_2954_;
v___y_2929_ = v___y_2953_;
v___y_2930_ = v_val_2957_;
goto v___jp_2922_;
}
}
v___jp_2958_:
{
lean_object* v_ref_2966_; lean_object* v___x_2967_; 
v_ref_2966_ = l_Lean_replaceRef(v_ref_2876_, v___y_2961_);
v___x_2967_ = l_Lean_Syntax_getPos_x3f(v_ref_2966_, v___y_2962_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v___x_2968_; 
v___x_2968_ = lean_unsigned_to_nat(0u);
v___y_2948_ = v___y_2959_;
v___y_2949_ = v_ref_2966_;
v___y_2950_ = v___y_2960_;
v___y_2951_ = v___y_2965_;
v___y_2952_ = v___y_2962_;
v___y_2953_ = v___y_2964_;
v___y_2954_ = v___y_2963_;
v___y_2955_ = v___x_2968_;
goto v___jp_2947_;
}
else
{
lean_object* v_val_2969_; 
v_val_2969_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_val_2969_);
lean_dec_ref(v___x_2967_);
v___y_2948_ = v___y_2959_;
v___y_2949_ = v_ref_2966_;
v___y_2950_ = v___y_2960_;
v___y_2951_ = v___y_2965_;
v___y_2952_ = v___y_2962_;
v___y_2953_ = v___y_2964_;
v___y_2954_ = v___y_2963_;
v___y_2955_ = v_val_2969_;
goto v___jp_2947_;
}
}
v___jp_2971_:
{
if (v___y_2978_ == 0)
{
v___y_2959_ = v___y_2972_;
v___y_2960_ = v___y_2973_;
v___y_2961_ = v___y_2974_;
v___y_2962_ = v___y_2977_;
v___y_2963_ = v___y_2976_;
v___y_2964_ = v___y_2975_;
v___y_2965_ = v_severity_2878_;
goto v___jp_2958_;
}
else
{
v___y_2959_ = v___y_2972_;
v___y_2960_ = v___y_2973_;
v___y_2961_ = v___y_2974_;
v___y_2962_ = v___y_2977_;
v___y_2963_ = v___y_2976_;
v___y_2964_ = v___y_2975_;
v___y_2965_ = v___x_2970_;
goto v___jp_2958_;
}
}
v___jp_2979_:
{
if (v___y_2980_ == 0)
{
lean_object* v_fileName_2981_; lean_object* v_fileMap_2982_; lean_object* v_options_2983_; lean_object* v_ref_2984_; uint8_t v_suppressElabErrors_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___f_2988_; uint8_t v___x_2989_; uint8_t v___x_2990_; 
v_fileName_2981_ = lean_ctor_get(v___y_2882_, 0);
v_fileMap_2982_ = lean_ctor_get(v___y_2882_, 1);
v_options_2983_ = lean_ctor_get(v___y_2882_, 2);
v_ref_2984_ = lean_ctor_get(v___y_2882_, 5);
v_suppressElabErrors_2985_ = lean_ctor_get_uint8(v___y_2882_, sizeof(void*)*14 + 1);
v___x_2986_ = lean_box(v___y_2980_);
v___x_2987_ = lean_box(v_suppressElabErrors_2985_);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2988_, 0, v___x_2986_);
lean_closure_set(v___f_2988_, 1, v___x_2987_);
v___x_2989_ = 1;
v___x_2990_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2878_, v___x_2989_);
if (v___x_2990_ == 0)
{
v___y_2972_ = v___f_2988_;
v___y_2973_ = v_fileName_2981_;
v___y_2974_ = v_ref_2984_;
v___y_2975_ = v_fileMap_2982_;
v___y_2976_ = v_suppressElabErrors_2985_;
v___y_2977_ = v___y_2980_;
v___y_2978_ = v___x_2990_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_2991_; uint8_t v___x_2992_; 
v___x_2991_ = l_Lean_warningAsError;
v___x_2992_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_2983_, v___x_2991_);
v___y_2972_ = v___f_2988_;
v___y_2973_ = v_fileName_2981_;
v___y_2974_ = v_ref_2984_;
v___y_2975_ = v_fileMap_2982_;
v___y_2976_ = v_suppressElabErrors_2985_;
v___y_2977_ = v___y_2980_;
v___y_2978_ = v___x_2992_;
goto v___jp_2971_;
}
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_dec_ref(v_msgData_2877_);
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg___boxed(lean_object* v_ref_2997_, lean_object* v_msgData_2998_, lean_object* v_severity_2999_, lean_object* v_isSilent_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
uint8_t v_severity_boxed_3006_; uint8_t v_isSilent_boxed_3007_; lean_object* v_res_3008_; 
v_severity_boxed_3006_ = lean_unbox(v_severity_2999_);
v_isSilent_boxed_3007_ = lean_unbox(v_isSilent_3000_);
v_res_3008_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_2997_, v_msgData_2998_, v_severity_boxed_3006_, v_isSilent_boxed_3007_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v_ref_2997_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(lean_object* v_msgData_3009_, uint8_t v_severity_3010_, uint8_t v_isSilent_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v_ref_3019_; lean_object* v___x_3020_; 
v_ref_3019_ = lean_ctor_get(v___y_3016_, 5);
v___x_3020_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_3019_, v_msgData_3009_, v_severity_3010_, v_isSilent_3011_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21___boxed(lean_object* v_msgData_3021_, lean_object* v_severity_3022_, lean_object* v_isSilent_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
uint8_t v_severity_boxed_3031_; uint8_t v_isSilent_boxed_3032_; lean_object* v_res_3033_; 
v_severity_boxed_3031_ = lean_unbox(v_severity_3022_);
v_isSilent_boxed_3032_ = lean_unbox(v_isSilent_3023_);
v_res_3033_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3021_, v_severity_boxed_3031_, v_isSilent_boxed_3032_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(lean_object* v_msgData_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
uint8_t v___x_3042_; uint8_t v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = 1;
v___x_3043_ = 0;
v___x_3044_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21(v_msgData_3034_, v___x_3042_, v___x_3043_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19___boxed(lean_object* v_msgData_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v_msgData_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(lean_object* v_opt_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_options_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_options_3057_ = lean_ctor_get(v___y_3055_, 2);
v___x_3058_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg_spec__0_spec__0_spec__1_spec__5(v_options_3057_, v_opt_3054_);
v___x_3059_ = lean_box(v___x_3058_);
v___x_3060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg___boxed(lean_object* v_opt_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_3061_, v___y_3062_);
lean_dec_ref(v___y_3062_);
lean_dec_ref(v_opt_3061_);
return v_res_3064_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__0));
v___x_3067_ = l_Lean_stringToMessageData(v___x_3066_);
return v___x_3067_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__2));
v___x_3070_ = l_Lean_stringToMessageData(v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(lean_object* v_id_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3079_; lean_object* v_env_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3102_; 
v___x_3079_ = lean_st_ref_get(v___y_3077_);
v_env_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc_ref(v_env_3080_);
lean_dec(v___x_3079_);
v___x_3081_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_3082_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v___x_3081_, v___y_3076_);
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3102_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3102_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
uint8_t v_isExporting_3092_; 
v_isExporting_3092_ = lean_ctor_get_uint8(v_env_3080_, sizeof(void*)*8);
lean_dec_ref(v_env_3080_);
if (v_isExporting_3092_ == 0)
{
lean_dec(v_a_3083_);
lean_dec(v_id_3071_);
goto v___jp_3087_;
}
else
{
uint8_t v___x_3093_; 
v___x_3093_ = l_Lean_isPrivateName(v_id_3071_);
if (v___x_3093_ == 0)
{
lean_dec(v_a_3083_);
lean_dec(v_id_3071_);
goto v___jp_3087_;
}
else
{
uint8_t v___x_3094_; 
v___x_3094_ = lean_unbox(v_a_3083_);
lean_dec(v_a_3083_);
if (v___x_3094_ == 0)
{
lean_dec(v_id_3071_);
goto v___jp_3087_;
}
else
{
lean_object* v___x_3095_; uint8_t v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
lean_del_object(v___x_3085_);
v___x_3095_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__1);
v___x_3096_ = 0;
v___x_3097_ = l_Lean_MessageData_ofConstName(v_id_3071_, v___x_3096_);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3095_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___closed__3);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3098_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19(v___x_3100_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
return v___x_3101_;
}
}
}
v___jp_3087_:
{
lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3088_ = lean_box(0);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v___x_3088_);
v___x_3090_ = v___x_3085_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17___boxed(lean_object* v_id_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_id_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(lean_object* v_id_3112_, uint8_t v_enableLog_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v___x_3121_; lean_object* v_env_3122_; lean_object* v_options_3123_; lean_object* v_currNamespace_3124_; lean_object* v_openDecls_3125_; lean_object* v___x_3126_; lean_object* v_env_3127_; lean_object* v_res_3128_; 
v___x_3121_ = lean_st_ref_get(v___y_3119_);
v_env_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc_ref(v_env_3122_);
lean_dec(v___x_3121_);
v_options_3123_ = lean_ctor_get(v___y_3118_, 2);
v_currNamespace_3124_ = lean_ctor_get(v___y_3118_, 6);
v_openDecls_3125_ = lean_ctor_get(v___y_3118_, 7);
v___x_3126_ = lean_st_ref_get(v___y_3119_);
v_env_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc_ref(v_env_3127_);
lean_dec(v___x_3126_);
lean_inc(v_openDecls_3125_);
lean_inc(v_currNamespace_3124_);
v_res_3128_ = l_Lean_ResolveName_resolveGlobalName(v_env_3122_, v_options_3123_, v_currNamespace_3124_, v_openDecls_3125_, v_id_3112_);
if (v_enableLog_3113_ == 0)
{
lean_object* v___x_3129_; 
lean_dec_ref(v_env_3127_);
v___x_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3129_, 0, v_res_3128_);
return v___x_3129_;
}
else
{
uint8_t v_isExporting_3130_; 
v_isExporting_3130_ = lean_ctor_get_uint8(v_env_3127_, sizeof(void*)*8);
lean_dec_ref(v_env_3127_);
if (v_isExporting_3130_ == 0)
{
lean_object* v___x_3131_; 
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v_res_3128_);
return v___x_3131_;
}
else
{
lean_object* v___x_3132_; 
v___x_3132_ = l_List_find_x3f___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__16(v_res_3128_);
if (lean_obj_tag(v___x_3132_) == 1)
{
lean_object* v_val_3133_; lean_object* v_fst_3134_; lean_object* v___x_3135_; 
v_val_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_val_3133_);
lean_dec_ref(v___x_3132_);
v_fst_3134_ = lean_ctor_get(v_val_3133_, 0);
lean_inc(v_fst_3134_);
lean_dec(v_val_3133_);
v___x_3135_ = l_Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17(v_fst_3134_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3142_ == 0)
{
lean_object* v_unused_3143_; 
v_unused_3143_ = lean_ctor_get(v___x_3135_, 0);
lean_dec(v_unused_3143_);
v___x_3137_ = v___x_3135_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_dec(v___x_3135_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v_res_3128_);
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_res_3128_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_res_3128_);
v_a_3144_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3135_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3135_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v___x_3152_; 
lean_dec(v___x_3132_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v_res_3128_);
return v___x_3152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13___boxed(lean_object* v_id_3153_, lean_object* v_enableLog_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v_enableLog_boxed_3162_; lean_object* v_res_3163_; 
v_enableLog_boxed_3162_ = lean_unbox(v_enableLog_3154_);
v_res_3163_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v_id_3153_, v_enableLog_boxed_3162_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(lean_object* v_a_3164_, lean_object* v_a_3165_){
_start:
{
if (lean_obj_tag(v_a_3164_) == 0)
{
lean_object* v___x_3166_; 
v___x_3166_ = l_List_reverse___redArg(v_a_3165_);
return v___x_3166_;
}
else
{
lean_object* v_head_3167_; lean_object* v_tail_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3179_; 
v_head_3167_ = lean_ctor_get(v_a_3164_, 0);
v_tail_3168_ = lean_ctor_get(v_a_3164_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v_a_3164_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3170_ = v_a_3164_;
v_isShared_3171_ = v_isSharedCheck_3179_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_tail_3168_);
lean_inc(v_head_3167_);
lean_dec(v_a_3164_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3179_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_snd_3172_; uint8_t v___x_3173_; 
v_snd_3172_ = lean_ctor_get(v_head_3167_, 1);
v___x_3173_ = l_List_isEmpty___redArg(v_snd_3172_);
if (v___x_3173_ == 0)
{
lean_del_object(v___x_3170_);
lean_dec(v_head_3167_);
v_a_3164_ = v_tail_3168_;
goto _start;
}
else
{
lean_object* v___x_3176_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v_a_3165_);
v___x_3176_ = v___x_3170_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_head_3167_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_a_3165_);
v___x_3176_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
v_a_3164_ = v_tail_3168_;
v_a_3165_ = v___x_3176_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(lean_object* v_view_3180_, lean_object* v_findLocalDecl_x3f_3181_, lean_object* v_n_3182_, lean_object* v_projs_3183_, uint8_t v_globalDeclFound_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___y_3193_; lean_object* v___y_3194_; uint8_t v_globalDeclFoundNext_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v_imported_3204_; lean_object* v_ctx_3205_; lean_object* v_scopes_3206_; lean_object* v_givenNameView_3207_; uint8_t v___y_3209_; 
v_imported_3204_ = lean_ctor_get(v_view_3180_, 1);
v_ctx_3205_ = lean_ctor_get(v_view_3180_, 2);
v_scopes_3206_ = lean_ctor_get(v_view_3180_, 3);
lean_inc(v_scopes_3206_);
lean_inc(v_ctx_3205_);
lean_inc(v_imported_3204_);
lean_inc(v_n_3182_);
v_givenNameView_3207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_3207_, 0, v_n_3182_);
lean_ctor_set(v_givenNameView_3207_, 1, v_imported_3204_);
lean_ctor_set(v_givenNameView_3207_, 2, v_ctx_3205_);
lean_ctor_set(v_givenNameView_3207_, 3, v_scopes_3206_);
if (v_globalDeclFound_3184_ == 0)
{
v___y_3209_ = v_globalDeclFound_3184_;
goto v___jp_3208_;
}
else
{
uint8_t v___x_3244_; 
v___x_3244_ = l_List_isEmpty___redArg(v_projs_3183_);
if (v___x_3244_ == 0)
{
v___y_3209_ = v_globalDeclFound_3184_;
goto v___jp_3208_;
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = 0;
v___y_3209_ = v___x_3245_;
goto v___jp_3208_;
}
}
v___jp_3192_:
{
lean_object* v___x_3202_; 
v___x_3202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___y_3194_);
lean_ctor_set(v___x_3202_, 1, v_projs_3183_);
v_n_3182_ = v___y_3193_;
v_projs_3183_ = v___x_3202_;
v_globalDeclFound_3184_ = v_globalDeclFoundNext_3195_;
v___y_3185_ = v___y_3196_;
v___y_3186_ = v___y_3197_;
v___y_3187_ = v___y_3198_;
v___y_3188_ = v___y_3199_;
v___y_3189_ = v___y_3200_;
v___y_3190_ = v___y_3201_;
goto _start;
}
v___jp_3208_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = lean_box(v___y_3209_);
lean_inc_ref(v_findLocalDecl_x3f_3181_);
lean_inc_ref(v_givenNameView_3207_);
v___x_3211_ = lean_apply_2(v_findLocalDecl_x3f_3181_, v_givenNameView_3207_, v___x_3210_);
if (lean_obj_tag(v___x_3211_) == 0)
{
if (lean_obj_tag(v_n_3182_) == 1)
{
if (v_globalDeclFound_3184_ == 0)
{
lean_object* v_pre_3212_; lean_object* v_str_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v_pre_3212_ = lean_ctor_get(v_n_3182_, 0);
lean_inc(v_pre_3212_);
v_str_3213_ = lean_ctor_get(v_n_3182_, 1);
lean_inc_ref(v_str_3213_);
lean_dec_ref(v_n_3182_);
v___x_3214_ = l_Lean_MacroScopesView_review(v_givenNameView_3207_);
v___x_3215_ = l_Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13(v___x_3214_, v_globalDeclFound_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3217_; lean_object* v_r_3218_; uint8_t v___x_3219_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref(v___x_3215_);
v___x_3217_ = lean_box(0);
v_r_3218_ = l_List_filterTR_loop___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__14(v_a_3216_, v___x_3217_);
v___x_3219_ = l_List_isEmpty___redArg(v_r_3218_);
lean_dec(v_r_3218_);
if (v___x_3219_ == 0)
{
uint8_t v_globalDeclFoundNext_3220_; 
v_globalDeclFoundNext_3220_ = 1;
v___y_3193_ = v_pre_3212_;
v___y_3194_ = v_str_3213_;
v_globalDeclFoundNext_3195_ = v_globalDeclFoundNext_3220_;
v___y_3196_ = v___y_3185_;
v___y_3197_ = v___y_3186_;
v___y_3198_ = v___y_3187_;
v___y_3199_ = v___y_3188_;
v___y_3200_ = v___y_3189_;
v___y_3201_ = v___y_3190_;
goto v___jp_3192_;
}
else
{
v___y_3193_ = v_pre_3212_;
v___y_3194_ = v_str_3213_;
v_globalDeclFoundNext_3195_ = v_globalDeclFound_3184_;
v___y_3196_ = v___y_3185_;
v___y_3197_ = v___y_3186_;
v___y_3198_ = v___y_3187_;
v___y_3199_ = v___y_3188_;
v___y_3200_ = v___y_3189_;
v___y_3201_ = v___y_3190_;
goto v___jp_3192_;
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec_ref(v_str_3213_);
lean_dec(v_pre_3212_);
lean_dec(v_projs_3183_);
lean_dec_ref(v_findLocalDecl_x3f_3181_);
v_a_3221_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3215_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3215_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_object* v_pre_3229_; lean_object* v_str_3230_; 
lean_dec_ref(v_givenNameView_3207_);
v_pre_3229_ = lean_ctor_get(v_n_3182_, 0);
lean_inc(v_pre_3229_);
v_str_3230_ = lean_ctor_get(v_n_3182_, 1);
lean_inc_ref(v_str_3230_);
lean_dec_ref(v_n_3182_);
v___y_3193_ = v_pre_3229_;
v___y_3194_ = v_str_3230_;
v_globalDeclFoundNext_3195_ = v_globalDeclFound_3184_;
v___y_3196_ = v___y_3185_;
v___y_3197_ = v___y_3186_;
v___y_3198_ = v___y_3187_;
v___y_3199_ = v___y_3188_;
v___y_3200_ = v___y_3189_;
v___y_3201_ = v___y_3190_;
goto v___jp_3192_;
}
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_dec_ref(v_givenNameView_3207_);
lean_dec(v_projs_3183_);
lean_dec(v_n_3182_);
lean_dec_ref(v_findLocalDecl_x3f_3181_);
v___x_3231_ = lean_box(0);
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
return v___x_3232_;
}
}
else
{
lean_object* v_val_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3243_; 
lean_dec_ref(v_givenNameView_3207_);
lean_dec(v_n_3182_);
lean_dec_ref(v_findLocalDecl_x3f_3181_);
v_val_3233_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3235_ = v___x_3211_;
v_isShared_3236_ = v_isSharedCheck_3243_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_val_3233_);
lean_dec(v___x_3211_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3243_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3237_ = l_Lean_LocalDecl_toExpr(v_val_3233_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
lean_ctor_set(v___x_3238_, 1, v_projs_3183_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3238_);
v___x_3240_ = v___x_3235_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
return v___x_3241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8___boxed(lean_object* v_view_3246_, lean_object* v_findLocalDecl_x3f_3247_, lean_object* v_n_3248_, lean_object* v_projs_3249_, lean_object* v_globalDeclFound_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
uint8_t v_globalDeclFound_boxed_3258_; lean_object* v_res_3259_; 
v_globalDeclFound_boxed_3258_ = lean_unbox(v_globalDeclFound_3250_);
v_res_3259_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3246_, v_findLocalDecl_x3f_3247_, v_n_3248_, v_projs_3249_, v_globalDeclFound_boxed_3258_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec_ref(v_view_3246_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(lean_object* v_localDecl_x3f_3260_, lean_object* v_givenName_3261_, lean_object* v_as_3262_, lean_object* v_i_3263_){
_start:
{
lean_object* v_zero_3264_; uint8_t v_isZero_3265_; 
v_zero_3264_ = lean_unsigned_to_nat(0u);
v_isZero_3265_ = lean_nat_dec_eq(v_i_3263_, v_zero_3264_);
if (v_isZero_3265_ == 1)
{
lean_object* v___x_3266_; 
lean_dec(v_i_3263_);
v___x_3266_ = lean_box(0);
return v___x_3266_;
}
else
{
lean_object* v_one_3267_; lean_object* v_n_3268_; lean_object* v___y_3270_; lean_object* v___x_3272_; 
v_one_3267_ = lean_unsigned_to_nat(1u);
v_n_3268_ = lean_nat_sub(v_i_3263_, v_one_3267_);
lean_dec(v_i_3263_);
v___x_3272_ = lean_array_fget_borrowed(v_as_3262_, v_n_3268_);
if (lean_obj_tag(v___x_3272_) == 0)
{
v___y_3270_ = v___x_3272_;
goto v___jp_3269_;
}
else
{
lean_object* v_val_3273_; uint8_t v___x_3274_; 
v_val_3273_ = lean_ctor_get(v___x_3272_, 0);
v___x_3274_ = l_Lean_LocalDecl_isAuxDecl(v_val_3273_);
if (v___x_3274_ == 0)
{
v___y_3270_ = v_localDecl_x3f_3260_;
goto v___jp_3269_;
}
else
{
lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = l_Lean_LocalDecl_userName(v_val_3273_);
v___x_3276_ = lean_name_eq(v___x_3275_, v_givenName_3261_);
lean_dec(v___x_3275_);
if (v___x_3276_ == 0)
{
v_i_3263_ = v_n_3268_;
goto _start;
}
else
{
v___y_3270_ = v___x_3272_;
goto v___jp_3269_;
}
}
}
v___jp_3269_:
{
if (lean_obj_tag(v___y_3270_) == 0)
{
v_i_3263_ = v_n_3268_;
goto _start;
}
else
{
lean_dec(v_n_3268_);
lean_inc_ref(v___y_3270_);
return v___y_3270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_localDecl_x3f_3278_, lean_object* v_givenName_3279_, lean_object* v_as_3280_, lean_object* v_i_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3278_, v_givenName_3279_, v_as_3280_, v_i_3281_);
lean_dec_ref(v_as_3280_);
lean_dec(v_givenName_3279_);
lean_dec(v_localDecl_x3f_3278_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(lean_object* v_localDecl_x3f_3283_, lean_object* v_givenName_3284_, lean_object* v_as_3285_, lean_object* v_i_3286_){
_start:
{
lean_object* v_zero_3287_; uint8_t v_isZero_3288_; 
v_zero_3287_ = lean_unsigned_to_nat(0u);
v_isZero_3288_ = lean_nat_dec_eq(v_i_3286_, v_zero_3287_);
if (v_isZero_3288_ == 1)
{
lean_object* v___x_3289_; 
lean_dec(v_i_3286_);
v___x_3289_ = lean_box(0);
return v___x_3289_;
}
else
{
lean_object* v_one_3290_; lean_object* v_n_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_one_3290_ = lean_unsigned_to_nat(1u);
v_n_3291_ = lean_nat_sub(v_i_3286_, v_one_3290_);
lean_dec(v_i_3286_);
v___x_3292_ = lean_array_fget_borrowed(v_as_3285_, v_n_3291_);
v___x_3293_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3283_, v_givenName_3284_, v___x_3292_);
if (lean_obj_tag(v___x_3293_) == 0)
{
v_i_3286_ = v_n_3291_;
goto _start;
}
else
{
lean_dec(v_n_3291_);
return v___x_3293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(lean_object* v_localDecl_x3f_3295_, lean_object* v_givenName_3296_, lean_object* v_x_3297_){
_start:
{
if (lean_obj_tag(v_x_3297_) == 0)
{
lean_object* v_cs_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_cs_3298_ = lean_ctor_get(v_x_3297_, 0);
v___x_3299_ = lean_array_get_size(v_cs_3298_);
v___x_3300_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3295_, v_givenName_3296_, v_cs_3298_, v___x_3299_);
return v___x_3300_;
}
else
{
lean_object* v_vs_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_vs_3301_ = lean_ctor_get(v_x_3297_, 0);
v___x_3302_ = lean_array_get_size(v_vs_3301_);
v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3295_, v_givenName_3296_, v_vs_3301_, v___x_3302_);
return v___x_3303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11___boxed(lean_object* v_localDecl_x3f_3304_, lean_object* v_givenName_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3304_, v_givenName_3305_, v_x_3306_);
lean_dec_ref(v_x_3306_);
lean_dec(v_givenName_3305_);
lean_dec(v_localDecl_x3f_3304_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_localDecl_x3f_3308_, lean_object* v_givenName_3309_, lean_object* v_as_3310_, lean_object* v_i_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_3308_, v_givenName_3309_, v_as_3310_, v_i_3311_);
lean_dec_ref(v_as_3310_);
lean_dec(v_givenName_3309_);
lean_dec(v_localDecl_x3f_3308_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(lean_object* v_localDecl_x3f_3313_, lean_object* v_givenName_3314_, lean_object* v_t_3315_){
_start:
{
lean_object* v_root_3316_; lean_object* v_tail_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_root_3316_ = lean_ctor_get(v_t_3315_, 0);
v_tail_3317_ = lean_ctor_get(v_t_3315_, 1);
v___x_3318_ = lean_array_get_size(v_tail_3317_);
v___x_3319_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_3313_, v_givenName_3314_, v_tail_3317_, v___x_3318_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11(v_localDecl_x3f_3313_, v_givenName_3314_, v_root_3316_);
return v___x_3320_;
}
else
{
return v___x_3319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7___boxed(lean_object* v_localDecl_x3f_3321_, lean_object* v_givenName_3322_, lean_object* v_t_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3321_, v_givenName_3322_, v_t_3323_);
lean_dec_ref(v_t_3323_);
lean_dec(v_givenName_3322_);
lean_dec(v_localDecl_x3f_3321_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(lean_object* v_t_3325_, lean_object* v_k_3326_){
_start:
{
if (lean_obj_tag(v_t_3325_) == 0)
{
lean_object* v_k_3327_; lean_object* v_v_3328_; lean_object* v_l_3329_; lean_object* v_r_3330_; uint8_t v___x_3331_; 
v_k_3327_ = lean_ctor_get(v_t_3325_, 1);
v_v_3328_ = lean_ctor_get(v_t_3325_, 2);
v_l_3329_ = lean_ctor_get(v_t_3325_, 3);
v_r_3330_ = lean_ctor_get(v_t_3325_, 4);
v___x_3331_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3326_, v_k_3327_);
switch(v___x_3331_)
{
case 0:
{
v_t_3325_ = v_l_3329_;
goto _start;
}
case 1:
{
lean_object* v___x_3333_; 
lean_inc(v_v_3328_);
v___x_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3333_, 0, v_v_3328_);
return v___x_3333_;
}
default: 
{
v_t_3325_ = v_r_3330_;
goto _start;
}
}
}
else
{
lean_object* v___x_3335_; 
v___x_3335_ = lean_box(0);
return v___x_3335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg___boxed(lean_object* v_t_3336_, lean_object* v_k_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_3336_, v_k_3337_);
lean_dec(v_k_3337_);
lean_dec(v_t_3336_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(lean_object* v_localDecl_3339_, lean_object* v_givenName_3340_){
_start:
{
lean_object* v___x_3341_; uint8_t v___x_3342_; 
v___x_3341_ = l_Lean_LocalDecl_userName(v_localDecl_3339_);
v___x_3342_ = lean_name_eq(v___x_3341_, v_givenName_3340_);
lean_dec(v___x_3341_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; 
lean_dec_ref(v_localDecl_3339_);
v___x_3343_ = lean_box(0);
return v___x_3343_;
}
else
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3344_, 0, v_localDecl_3339_);
return v___x_3344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_localDecl_3345_, lean_object* v_givenName_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_localDecl_3345_, v_givenName_3346_);
lean_dec(v_givenName_3346_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(lean_object* v_givenName_3348_, uint8_t v_skipAuxDecl_3349_, lean_object* v_auxDeclToFullName_3350_, lean_object* v___x_3351_, lean_object* v_givenNameView_3352_, lean_object* v_as_3353_, lean_object* v_i_3354_){
_start:
{
lean_object* v_zero_3355_; uint8_t v_isZero_3356_; 
v_zero_3355_ = lean_unsigned_to_nat(0u);
v_isZero_3356_ = lean_nat_dec_eq(v_i_3354_, v_zero_3355_);
if (v_isZero_3356_ == 1)
{
lean_object* v___x_3357_; 
lean_dec(v_i_3354_);
lean_dec_ref(v_givenNameView_3352_);
lean_dec(v___x_3351_);
v___x_3357_ = lean_box(0);
return v___x_3357_;
}
else
{
lean_object* v_one_3358_; lean_object* v_n_3359_; lean_object* v___y_3361_; lean_object* v___x_3363_; 
v_one_3358_ = lean_unsigned_to_nat(1u);
v_n_3359_ = lean_nat_sub(v_i_3354_, v_one_3358_);
lean_dec(v_i_3354_);
v___x_3363_ = lean_array_fget_borrowed(v_as_3353_, v_n_3359_);
if (lean_obj_tag(v___x_3363_) == 0)
{
v___y_3361_ = v___x_3363_;
goto v___jp_3360_;
}
else
{
lean_object* v_val_3364_; uint8_t v___x_3365_; 
v_val_3364_ = lean_ctor_get(v___x_3363_, 0);
v___x_3365_ = l_Lean_LocalDecl_isAuxDecl(v_val_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; 
lean_inc(v_val_3364_);
v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3364_, v_givenName_3348_);
v___y_3361_ = v___x_3366_;
goto v___jp_3360_;
}
else
{
if (v_skipAuxDecl_3349_ == 0)
{
if (v___x_3365_ == 0)
{
v_i_3354_ = v_n_3359_;
goto _start;
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = l_Lean_LocalDecl_fvarId(v_val_3364_);
v___x_3369_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_auxDeclToFullName_3350_, v___x_3368_);
lean_dec(v___x_3368_);
if (lean_obj_tag(v___x_3369_) == 1)
{
lean_object* v_val_3370_; lean_object* v_fullDeclView_3371_; lean_object* v___y_3373_; lean_object* v_name_3394_; lean_object* v___x_3395_; 
v_val_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_val_3370_);
lean_dec_ref(v___x_3369_);
v_fullDeclView_3371_ = l_Lean_extractMacroScopes(v_val_3370_);
v_name_3394_ = lean_ctor_get(v_fullDeclView_3371_, 0);
lean_inc_n(v_name_3394_, 2);
v___x_3395_ = lean_private_to_user_name(v_name_3394_);
if (lean_obj_tag(v___x_3395_) == 0)
{
v___y_3373_ = v_name_3394_;
goto v___jp_3372_;
}
else
{
lean_object* v_val_3396_; 
lean_dec(v_name_3394_);
v_val_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_val_3396_);
lean_dec_ref(v___x_3395_);
v___y_3373_ = v_val_3396_;
goto v___jp_3372_;
}
v___jp_3372_:
{
lean_object* v_imported_3374_; lean_object* v_ctx_3375_; lean_object* v_scopes_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3392_; 
v_imported_3374_ = lean_ctor_get(v_fullDeclView_3371_, 1);
v_ctx_3375_ = lean_ctor_get(v_fullDeclView_3371_, 2);
v_scopes_3376_ = lean_ctor_get(v_fullDeclView_3371_, 3);
v_isSharedCheck_3392_ = !lean_is_exclusive(v_fullDeclView_3371_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v_fullDeclView_3371_, 0);
lean_dec(v_unused_3393_);
v___x_3378_ = v_fullDeclView_3371_;
v_isShared_3379_ = v_isSharedCheck_3392_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_scopes_3376_);
lean_inc(v_ctx_3375_);
lean_inc(v_imported_3374_);
lean_dec(v_fullDeclView_3371_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3392_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v_fullDeclView_3381_; 
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___y_3373_);
v_fullDeclView_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___y_3373_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_imported_3374_);
lean_ctor_set(v_reuseFailAlloc_3391_, 2, v_ctx_3375_);
lean_ctor_set(v_reuseFailAlloc_3391_, 3, v_scopes_3376_);
v_fullDeclView_3381_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v_fullDeclName_3382_; uint8_t v___x_3383_; 
lean_inc_ref(v_fullDeclView_3381_);
v_fullDeclName_3382_ = l_Lean_MacroScopesView_review(v_fullDeclView_3381_);
v___x_3383_ = l_Lean_Name_isPrefixOf(v___x_3351_, v_fullDeclName_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; 
lean_dec_ref(v_fullDeclView_3381_);
lean_inc(v___x_3351_);
lean_inc_ref(v_givenNameView_3352_);
lean_inc(v_val_3364_);
v___x_3384_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_3364_, v_givenNameView_3352_, v_fullDeclName_3382_, v___x_3351_);
lean_dec(v_fullDeclName_3382_);
v___y_3361_ = v___x_3384_;
goto v___jp_3360_;
}
else
{
lean_object* v___x_3385_; lean_object* v_localDeclNameView_3386_; uint8_t v___x_3387_; 
lean_dec(v_fullDeclName_3382_);
v___x_3385_ = l_Lean_LocalDecl_userName(v_val_3364_);
v_localDeclNameView_3386_ = l_Lean_extractMacroScopes(v___x_3385_);
v___x_3387_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_3386_, v_givenNameView_3352_);
lean_dec_ref(v_localDeclNameView_3386_);
if (v___x_3387_ == 0)
{
lean_dec_ref(v_fullDeclView_3381_);
v_i_3354_ = v_n_3359_;
goto _start;
}
else
{
uint8_t v___x_3389_; 
v___x_3389_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_3352_, v_fullDeclView_3381_);
lean_dec_ref(v_fullDeclView_3381_);
if (v___x_3389_ == 0)
{
v_i_3354_ = v_n_3359_;
goto _start;
}
else
{
lean_inc_ref(v___x_3363_);
v___y_3361_ = v___x_3363_;
goto v___jp_3360_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3397_; 
lean_dec(v___x_3369_);
lean_inc(v_val_3364_);
v___x_3397_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___lam__0(v_val_3364_, v_givenName_3348_);
v___y_3361_ = v___x_3397_;
goto v___jp_3360_;
}
}
}
else
{
v_i_3354_ = v_n_3359_;
goto _start;
}
}
}
v___jp_3360_:
{
if (lean_obj_tag(v___y_3361_) == 0)
{
v_i_3354_ = v_n_3359_;
goto _start;
}
else
{
lean_dec(v_n_3359_);
lean_dec_ref(v_givenNameView_3352_);
lean_dec(v___x_3351_);
return v___y_3361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_givenName_3399_, lean_object* v_skipAuxDecl_3400_, lean_object* v_auxDeclToFullName_3401_, lean_object* v___x_3402_, lean_object* v_givenNameView_3403_, lean_object* v_as_3404_, lean_object* v_i_3405_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3406_; lean_object* v_res_3407_; 
v_skipAuxDecl_boxed_3406_ = lean_unbox(v_skipAuxDecl_3400_);
v_res_3407_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3399_, v_skipAuxDecl_boxed_3406_, v_auxDeclToFullName_3401_, v___x_3402_, v_givenNameView_3403_, v_as_3404_, v_i_3405_);
lean_dec_ref(v_as_3404_);
lean_dec(v_auxDeclToFullName_3401_);
lean_dec(v_givenName_3399_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(lean_object* v_givenName_3408_, uint8_t v_skipAuxDecl_3409_, lean_object* v_auxDeclToFullName_3410_, lean_object* v___x_3411_, lean_object* v_givenNameView_3412_, lean_object* v_as_3413_, lean_object* v_i_3414_){
_start:
{
lean_object* v_zero_3415_; uint8_t v_isZero_3416_; 
v_zero_3415_ = lean_unsigned_to_nat(0u);
v_isZero_3416_ = lean_nat_dec_eq(v_i_3414_, v_zero_3415_);
if (v_isZero_3416_ == 1)
{
lean_object* v___x_3417_; 
lean_dec(v_i_3414_);
lean_dec_ref(v_givenNameView_3412_);
lean_dec(v___x_3411_);
v___x_3417_ = lean_box(0);
return v___x_3417_;
}
else
{
lean_object* v_one_3418_; lean_object* v_n_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v_one_3418_ = lean_unsigned_to_nat(1u);
v_n_3419_ = lean_nat_sub(v_i_3414_, v_one_3418_);
lean_dec(v_i_3414_);
v___x_3420_ = lean_array_fget_borrowed(v_as_3413_, v_n_3419_);
lean_inc_ref(v_givenNameView_3412_);
lean_inc(v___x_3411_);
v___x_3421_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3408_, v_skipAuxDecl_3409_, v_auxDeclToFullName_3410_, v___x_3411_, v_givenNameView_3412_, v___x_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
v_i_3414_ = v_n_3419_;
goto _start;
}
else
{
lean_dec(v_n_3419_);
lean_dec_ref(v_givenNameView_3412_);
lean_dec(v___x_3411_);
return v___x_3421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(lean_object* v_givenName_3423_, uint8_t v_skipAuxDecl_3424_, lean_object* v_auxDeclToFullName_3425_, lean_object* v___x_3426_, lean_object* v_givenNameView_3427_, lean_object* v_x_3428_){
_start:
{
if (lean_obj_tag(v_x_3428_) == 0)
{
lean_object* v_cs_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_cs_3429_ = lean_ctor_get(v_x_3428_, 0);
v___x_3430_ = lean_array_get_size(v_cs_3429_);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3423_, v_skipAuxDecl_3424_, v_auxDeclToFullName_3425_, v___x_3426_, v_givenNameView_3427_, v_cs_3429_, v___x_3430_);
return v___x_3431_;
}
else
{
lean_object* v_vs_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v_vs_3432_ = lean_ctor_get(v_x_3428_, 0);
v___x_3433_ = lean_array_get_size(v_vs_3432_);
v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3423_, v_skipAuxDecl_3424_, v_auxDeclToFullName_3425_, v___x_3426_, v_givenNameView_3427_, v_vs_3432_, v___x_3433_);
return v___x_3434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8___boxed(lean_object* v_givenName_3435_, lean_object* v_skipAuxDecl_3436_, lean_object* v_auxDeclToFullName_3437_, lean_object* v___x_3438_, lean_object* v_givenNameView_3439_, lean_object* v_x_3440_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3441_; lean_object* v_res_3442_; 
v_skipAuxDecl_boxed_3441_ = lean_unbox(v_skipAuxDecl_3436_);
v_res_3442_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3435_, v_skipAuxDecl_boxed_3441_, v_auxDeclToFullName_3437_, v___x_3438_, v_givenNameView_3439_, v_x_3440_);
lean_dec_ref(v_x_3440_);
lean_dec(v_auxDeclToFullName_3437_);
lean_dec(v_givenName_3435_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg___boxed(lean_object* v_givenName_3443_, lean_object* v_skipAuxDecl_3444_, lean_object* v_auxDeclToFullName_3445_, lean_object* v___x_3446_, lean_object* v_givenNameView_3447_, lean_object* v_as_3448_, lean_object* v_i_3449_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3450_; lean_object* v_res_3451_; 
v_skipAuxDecl_boxed_3450_ = lean_unbox(v_skipAuxDecl_3444_);
v_res_3451_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_3443_, v_skipAuxDecl_boxed_3450_, v_auxDeclToFullName_3445_, v___x_3446_, v_givenNameView_3447_, v_as_3448_, v_i_3449_);
lean_dec_ref(v_as_3448_);
lean_dec(v_auxDeclToFullName_3445_);
lean_dec(v_givenName_3443_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(lean_object* v_givenName_3452_, uint8_t v_skipAuxDecl_3453_, lean_object* v_auxDeclToFullName_3454_, lean_object* v___x_3455_, lean_object* v_givenNameView_3456_, lean_object* v_t_3457_){
_start:
{
lean_object* v_root_3458_; lean_object* v_tail_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v_root_3458_ = lean_ctor_get(v_t_3457_, 0);
v_tail_3459_ = lean_ctor_get(v_t_3457_, 1);
v___x_3460_ = lean_array_get_size(v_tail_3459_);
lean_inc_ref(v_givenNameView_3456_);
lean_inc(v___x_3455_);
v___x_3461_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_3452_, v_skipAuxDecl_3453_, v_auxDeclToFullName_3454_, v___x_3455_, v_givenNameView_3456_, v_tail_3459_, v___x_3460_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8(v_givenName_3452_, v_skipAuxDecl_3453_, v_auxDeclToFullName_3454_, v___x_3455_, v_givenNameView_3456_, v_root_3458_);
return v___x_3462_;
}
else
{
lean_dec_ref(v_givenNameView_3456_);
lean_dec(v___x_3455_);
return v___x_3461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6___boxed(lean_object* v_givenName_3463_, lean_object* v_skipAuxDecl_3464_, lean_object* v_auxDeclToFullName_3465_, lean_object* v___x_3466_, lean_object* v_givenNameView_3467_, lean_object* v_t_3468_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3469_; lean_object* v_res_3470_; 
v_skipAuxDecl_boxed_3469_ = lean_unbox(v_skipAuxDecl_3464_);
v_res_3470_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3463_, v_skipAuxDecl_boxed_3469_, v_auxDeclToFullName_3465_, v___x_3466_, v_givenNameView_3467_, v_t_3468_);
lean_dec_ref(v_t_3468_);
lean_dec(v_auxDeclToFullName_3465_);
lean_dec(v_givenName_3463_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(lean_object* v_auxDeclToFullName_3471_, lean_object* v_currNamespace_3472_, lean_object* v_decls_3473_, lean_object* v_givenNameView_3474_, uint8_t v_skipAuxDecl_3475_){
_start:
{
lean_object* v_givenName_3476_; lean_object* v_localDecl_x3f_3477_; 
lean_inc_ref(v_givenNameView_3474_);
v_givenName_3476_ = l_Lean_MacroScopesView_review(v_givenNameView_3474_);
v_localDecl_x3f_3477_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6(v_givenName_3476_, v_skipAuxDecl_3475_, v_auxDeclToFullName_3471_, v_currNamespace_3472_, v_givenNameView_3474_, v_decls_3473_);
if (lean_obj_tag(v_localDecl_x3f_3477_) == 0)
{
if (v_skipAuxDecl_3475_ == 0)
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7(v_localDecl_x3f_3477_, v_givenName_3476_, v_decls_3473_);
lean_dec(v_givenName_3476_);
return v___x_3478_;
}
else
{
lean_dec(v_givenName_3476_);
return v_localDecl_x3f_3477_;
}
}
else
{
lean_dec(v_givenName_3476_);
return v_localDecl_x3f_3477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed(lean_object* v_auxDeclToFullName_3479_, lean_object* v_currNamespace_3480_, lean_object* v_decls_3481_, lean_object* v_givenNameView_3482_, lean_object* v_skipAuxDecl_3483_){
_start:
{
uint8_t v_skipAuxDecl_boxed_3484_; lean_object* v_res_3485_; 
v_skipAuxDecl_boxed_3484_ = lean_unbox(v_skipAuxDecl_3483_);
v_res_3485_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0(v_auxDeclToFullName_3479_, v_currNamespace_3480_, v_decls_3481_, v_givenNameView_3482_, v_skipAuxDecl_boxed_3484_);
lean_dec_ref(v_decls_3481_);
lean_dec(v_auxDeclToFullName_3479_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(lean_object* v_n_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_lctx_3494_; lean_object* v_decls_3495_; lean_object* v_auxDeclToFullName_3496_; lean_object* v_currNamespace_3497_; lean_object* v_view_3498_; lean_object* v_name_3499_; lean_object* v_findLocalDecl_x3f_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; 
v_lctx_3494_ = lean_ctor_get(v___y_3489_, 2);
v_decls_3495_ = lean_ctor_get(v_lctx_3494_, 1);
v_auxDeclToFullName_3496_ = lean_ctor_get(v_lctx_3494_, 2);
v_currNamespace_3497_ = lean_ctor_get(v___y_3491_, 6);
v_view_3498_ = l_Lean_extractMacroScopes(v_n_3486_);
v_name_3499_ = lean_ctor_get(v_view_3498_, 0);
lean_inc(v_name_3499_);
lean_inc_ref(v_decls_3495_);
lean_inc(v_currNamespace_3497_);
lean_inc(v_auxDeclToFullName_3496_);
v_findLocalDecl_x3f_3500_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___lam__0___boxed), 5, 3);
lean_closure_set(v_findLocalDecl_x3f_3500_, 0, v_auxDeclToFullName_3496_);
lean_closure_set(v_findLocalDecl_x3f_3500_, 1, v_currNamespace_3497_);
lean_closure_set(v_findLocalDecl_x3f_3500_, 2, v_decls_3495_);
v___x_3501_ = lean_box(0);
v___x_3502_ = 0;
v___x_3503_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8(v_view_3498_, v_findLocalDecl_x3f_3500_, v_name_3499_, v___x_3501_, v___x_3502_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec_ref(v_view_3498_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5___boxed(lean_object* v_n_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v_n_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(lean_object* v_as_x27_3513_, lean_object* v_b_3514_){
_start:
{
if (lean_obj_tag(v_as_x27_3513_) == 0)
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3516_, 0, v_b_3514_);
return v___x_3516_;
}
else
{
lean_object* v_head_3517_; lean_object* v_tail_3518_; lean_object* v_config_3519_; lean_object* v_extensions_3520_; lean_object* v_extra_3521_; lean_object* v_extraInj_3522_; lean_object* v_extraFacts_3523_; lean_object* v_symPrios_3524_; lean_object* v_norm_3525_; lean_object* v_normProcs_3526_; lean_object* v_anchorRefs_x3f_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3536_; 
v_head_3517_ = lean_ctor_get(v_as_x27_3513_, 0);
v_tail_3518_ = lean_ctor_get(v_as_x27_3513_, 1);
v_config_3519_ = lean_ctor_get(v_b_3514_, 0);
v_extensions_3520_ = lean_ctor_get(v_b_3514_, 1);
v_extra_3521_ = lean_ctor_get(v_b_3514_, 2);
v_extraInj_3522_ = lean_ctor_get(v_b_3514_, 3);
v_extraFacts_3523_ = lean_ctor_get(v_b_3514_, 4);
v_symPrios_3524_ = lean_ctor_get(v_b_3514_, 5);
v_norm_3525_ = lean_ctor_get(v_b_3514_, 6);
v_normProcs_3526_ = lean_ctor_get(v_b_3514_, 7);
v_anchorRefs_x3f_3527_ = lean_ctor_get(v_b_3514_, 8);
v_isSharedCheck_3536_ = !lean_is_exclusive(v_b_3514_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3529_ = v_b_3514_;
v_isShared_3530_ = v_isSharedCheck_3536_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_anchorRefs_x3f_3527_);
lean_inc(v_normProcs_3526_);
lean_inc(v_norm_3525_);
lean_inc(v_symPrios_3524_);
lean_inc(v_extraFacts_3523_);
lean_inc(v_extraInj_3522_);
lean_inc(v_extra_3521_);
lean_inc(v_extensions_3520_);
lean_inc(v_config_3519_);
lean_dec(v_b_3514_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3536_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3531_; lean_object* v___x_3533_; 
lean_inc(v_head_3517_);
v___x_3531_ = l_Lean_PersistentArray_push___redArg(v_extra_3521_, v_head_3517_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 2, v___x_3531_);
v___x_3533_ = v___x_3529_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_config_3519_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_extensions_3520_);
lean_ctor_set(v_reuseFailAlloc_3535_, 2, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3535_, 3, v_extraInj_3522_);
lean_ctor_set(v_reuseFailAlloc_3535_, 4, v_extraFacts_3523_);
lean_ctor_set(v_reuseFailAlloc_3535_, 5, v_symPrios_3524_);
lean_ctor_set(v_reuseFailAlloc_3535_, 6, v_norm_3525_);
lean_ctor_set(v_reuseFailAlloc_3535_, 7, v_normProcs_3526_);
lean_ctor_set(v_reuseFailAlloc_3535_, 8, v_anchorRefs_x3f_3527_);
v___x_3533_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
v_as_x27_3513_ = v_tail_3518_;
v_b_3514_ = v___x_3533_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg___boxed(lean_object* v_as_x27_3537_, lean_object* v_b_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_3537_, v_b_3538_);
lean_dec(v_as_x27_3537_);
return v_res_3540_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__0));
v___x_3543_ = l_Lean_stringToMessageData(v___x_3542_);
return v___x_3543_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3(void){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3545_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__2));
v___x_3546_ = l_Lean_stringToMessageData(v___x_3545_);
return v___x_3546_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5(void){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__4));
v___x_3549_ = l_Lean_stringToMessageData(v___x_3548_);
return v___x_3549_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__6));
v___x_3552_ = l_Lean_stringToMessageData(v___x_3551_);
return v___x_3552_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__8));
v___x_3555_ = l_Lean_stringToMessageData(v___x_3554_);
return v___x_3555_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__10));
v___x_3558_ = l_Lean_stringToMessageData(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__12));
v___x_3561_ = l_Lean_stringToMessageData(v___x_3560_);
return v___x_3561_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__14));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__16));
v___x_3567_ = l_Lean_stringToMessageData(v___x_3566_);
return v___x_3567_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__18));
v___x_3570_ = l_Lean_stringToMessageData(v___x_3569_);
return v___x_3570_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__20));
v___x_3573_ = l_Lean_stringToMessageData(v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(lean_object* v_params_3574_, lean_object* v_p_3575_, lean_object* v_mod_x3f_3576_, lean_object* v_id_3577_, uint8_t v_minIndexable_3578_, uint8_t v_only_3579_, uint8_t v_incremental_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; uint8_t v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v_a_3763_; lean_object* v___y_3988_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_box(0);
lean_inc(v_id_3577_);
v___x_4000_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_id_3577_, v___x_3999_, v_a_3585_, v_a_3586_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_4000_);
v_a_3763_ = v_a_4001_;
goto v___jp_3762_;
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4076_; 
v_a_4002_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4004_ = v___x_4000_;
v_isShared_4005_ = v_isSharedCheck_4076_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_4000_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4076_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
uint8_t v___y_4007_; uint8_t v___x_4074_; 
v___x_4074_ = l_Lean_Exception_isInterrupt(v_a_4002_);
if (v___x_4074_ == 0)
{
uint8_t v___x_4075_; 
lean_inc(v_a_4002_);
v___x_4075_ = l_Lean_Exception_isRuntime(v_a_4002_);
v___y_4007_ = v___x_4075_;
goto v___jp_4006_;
}
else
{
v___y_4007_ = v___x_4074_;
goto v___jp_4006_;
}
v___jp_4006_:
{
if (v___y_4007_ == 0)
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_del_object(v___x_4004_);
v___x_4008_ = l_Lean_TSyntax_getId(v_id_3577_);
lean_inc(v___x_4008_);
v___x_4009_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4008_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref(v___x_4009_);
if (lean_obj_tag(v_a_4010_) == 0)
{
lean_object* v___x_4011_; 
v___x_4011_ = l_Lean_Meta_Grind_getExtension_x3f(v___x_4008_, v_a_3585_, v_a_3586_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4040_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4014_ = v___x_4011_;
v_isShared_4015_ = v_isSharedCheck_4040_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4011_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4040_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
if (lean_obj_tag(v_a_4012_) == 1)
{
lean_del_object(v___x_4014_);
lean_dec(v_a_4002_);
if (lean_obj_tag(v_mod_x3f_3576_) == 1)
{
lean_object* v_val_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec_ref(v_a_4012_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_val_4016_ = lean_ctor_get(v_mod_x3f_3576_, 0);
lean_inc(v_val_4016_);
lean_dec_ref(v_mod_x3f_3576_);
v___x_4017_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__17);
v___x_4018_ = l_Lean_MessageData_ofName(v___x_4008_);
v___x_4019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4017_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
v___x_4020_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_warnRedundantEMatchArg___closed__5);
v___x_4021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4019_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
v___x_4022_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_val_4016_, v___x_4021_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
lean_dec(v_val_4016_);
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4022_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4022_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
else
{
lean_object* v_val_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_dec(v___x_4008_);
v_val_4031_ = lean_ctor_get(v_a_4012_, 0);
lean_inc(v_val_4031_);
lean_dec_ref(v_a_4012_);
v___x_4032_ = lean_box(0);
lean_inc_ref(v_params_3574_);
v___x_4033_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___lam__0(v_params_3574_, v_val_4031_, v___x_4032_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
lean_dec(v_val_4031_);
v___y_3988_ = v___x_4033_;
goto v___jp_3987_;
}
}
else
{
lean_object* v___x_4034_; uint8_t v___x_4035_; 
lean_dec(v_a_4012_);
v___x_4034_ = l_Lean_Name_getPrefix(v___x_4008_);
lean_dec(v___x_4008_);
v___x_4035_ = l_Lean_Name_isAnonymous(v___x_4034_);
lean_dec(v___x_4034_);
if (v___x_4035_ == 0)
{
lean_object* v___x_4036_; 
lean_del_object(v___x_4014_);
lean_dec(v_a_4002_);
v___x_4036_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_params_3574_, v_p_3575_, v_mod_x3f_3576_, v_id_3577_, v_minIndexable_3578_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
return v___x_4036_;
}
else
{
lean_object* v___x_4038_; 
lean_dec(v_id_3577_);
lean_dec(v_mod_x3f_3576_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
if (v_isShared_4015_ == 0)
{
lean_ctor_set_tag(v___x_4014_, 1);
lean_ctor_set(v___x_4014_, 0, v_a_4002_);
v___x_4038_ = v___x_4014_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4002_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec(v___x_4008_);
lean_dec(v_a_4002_);
lean_dec(v_id_3577_);
lean_dec(v_mod_x3f_3576_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_4041_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4011_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4011_);
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
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec_ref(v_a_4010_);
lean_dec(v___x_4008_);
lean_dec(v_a_4002_);
lean_dec(v_mod_x3f_3576_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v___x_4049_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__19);
lean_inc(v_id_3577_);
v___x_4050_ = l_Lean_MessageData_ofSyntax(v_id_3577_);
v___x_4051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4049_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__21);
v___x_4053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4051_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_id_3577_, v___x_4053_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
lean_dec(v_id_3577_);
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
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec(v___x_4008_);
lean_dec(v_a_4002_);
lean_dec(v_id_3577_);
lean_dec(v_mod_x3f_3576_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_4063_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4009_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4009_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
else
{
lean_object* v___x_4072_; 
lean_dec(v_id_3577_);
lean_dec(v_mod_x3f_3576_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
if (v_isShared_4005_ == 0)
{
v___x_4072_ = v___x_4004_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4002_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
}
v___jp_3588_:
{
uint8_t v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = 0;
lean_inc(v___y_3589_);
v___x_3597_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v___y_3589_, v___x_3596_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref(v___x_3597_);
if (lean_obj_tag(v_a_3598_) == 1)
{
lean_object* v_val_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
lean_dec(v___y_3589_);
v_val_3599_ = lean_ctor_get(v_a_3598_, 0);
lean_inc_n(v_val_3599_, 2);
lean_dec_ref(v_a_3598_);
v___x_3600_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3574_, v_val_3599_, v___x_3596_);
v___x_3601_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_3599_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3612_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3612_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3612_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
if (lean_obj_tag(v_a_3602_) == 1)
{
lean_object* v_val_3606_; lean_object* v_ctors_3607_; lean_object* v___x_3608_; 
lean_del_object(v___x_3604_);
v_val_3606_ = lean_ctor_get(v_a_3602_, 0);
lean_inc(v_val_3606_);
lean_dec_ref(v_a_3602_);
v_ctors_3607_ = lean_ctor_get(v_val_3606_, 4);
lean_inc(v_ctors_3607_);
lean_dec(v_val_3606_);
v___x_3608_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_3575_, v_id_3577_, v_minIndexable_3578_, v_ctors_3607_, v___x_3600_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec(v_ctors_3607_);
lean_dec(v_p_3575_);
return v___x_3608_;
}
else
{
lean_object* v___x_3610_; 
lean_dec(v_a_3602_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3600_);
v___x_3610_ = v___x_3604_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3600_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
else
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
lean_dec_ref(v___x_3600_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
v_a_3613_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3615_ = v___x_3601_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3601_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
else
{
lean_object* v_fileName_3621_; lean_object* v_fileMap_3622_; lean_object* v_options_3623_; lean_object* v_currRecDepth_3624_; lean_object* v_maxRecDepth_3625_; lean_object* v_ref_3626_; lean_object* v_currNamespace_3627_; lean_object* v_openDecls_3628_; lean_object* v_initHeartbeats_3629_; lean_object* v_maxHeartbeats_3630_; lean_object* v_quotContext_3631_; lean_object* v_currMacroScope_3632_; uint8_t v_diag_3633_; lean_object* v_cancelTk_x3f_3634_; uint8_t v_suppressElabErrors_3635_; lean_object* v_inheritedTraceOptions_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; lean_object* v_ref_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_dec(v_a_3598_);
v_fileName_3621_ = lean_ctor_get(v___y_3594_, 0);
v_fileMap_3622_ = lean_ctor_get(v___y_3594_, 1);
v_options_3623_ = lean_ctor_get(v___y_3594_, 2);
v_currRecDepth_3624_ = lean_ctor_get(v___y_3594_, 3);
v_maxRecDepth_3625_ = lean_ctor_get(v___y_3594_, 4);
v_ref_3626_ = lean_ctor_get(v___y_3594_, 5);
v_currNamespace_3627_ = lean_ctor_get(v___y_3594_, 6);
v_openDecls_3628_ = lean_ctor_get(v___y_3594_, 7);
v_initHeartbeats_3629_ = lean_ctor_get(v___y_3594_, 8);
v_maxHeartbeats_3630_ = lean_ctor_get(v___y_3594_, 9);
v_quotContext_3631_ = lean_ctor_get(v___y_3594_, 10);
v_currMacroScope_3632_ = lean_ctor_get(v___y_3594_, 11);
v_diag_3633_ = lean_ctor_get_uint8(v___y_3594_, sizeof(void*)*14);
v_cancelTk_x3f_3634_ = lean_ctor_get(v___y_3594_, 12);
v_suppressElabErrors_3635_ = lean_ctor_get_uint8(v___y_3594_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3636_ = lean_ctor_get(v___y_3594_, 13);
v___x_3637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam___closed__6));
v___x_3638_ = 1;
v_ref_3639_ = l_Lean_replaceRef(v_p_3575_, v_ref_3626_);
lean_dec(v_p_3575_);
lean_inc_ref(v_inheritedTraceOptions_3636_);
lean_inc(v_cancelTk_x3f_3634_);
lean_inc(v_currMacroScope_3632_);
lean_inc(v_quotContext_3631_);
lean_inc(v_maxHeartbeats_3630_);
lean_inc(v_initHeartbeats_3629_);
lean_inc(v_openDecls_3628_);
lean_inc(v_currNamespace_3627_);
lean_inc(v_maxRecDepth_3625_);
lean_inc(v_currRecDepth_3624_);
lean_inc_ref(v_options_3623_);
lean_inc_ref(v_fileMap_3622_);
lean_inc_ref(v_fileName_3621_);
v___x_3640_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3640_, 0, v_fileName_3621_);
lean_ctor_set(v___x_3640_, 1, v_fileMap_3622_);
lean_ctor_set(v___x_3640_, 2, v_options_3623_);
lean_ctor_set(v___x_3640_, 3, v_currRecDepth_3624_);
lean_ctor_set(v___x_3640_, 4, v_maxRecDepth_3625_);
lean_ctor_set(v___x_3640_, 5, v_ref_3639_);
lean_ctor_set(v___x_3640_, 6, v_currNamespace_3627_);
lean_ctor_set(v___x_3640_, 7, v_openDecls_3628_);
lean_ctor_set(v___x_3640_, 8, v_initHeartbeats_3629_);
lean_ctor_set(v___x_3640_, 9, v_maxHeartbeats_3630_);
lean_ctor_set(v___x_3640_, 10, v_quotContext_3631_);
lean_ctor_set(v___x_3640_, 11, v_currMacroScope_3632_);
lean_ctor_set(v___x_3640_, 12, v_cancelTk_x3f_3634_);
lean_ctor_set(v___x_3640_, 13, v_inheritedTraceOptions_3636_);
lean_ctor_set_uint8(v___x_3640_, sizeof(void*)*14, v_diag_3633_);
lean_ctor_set_uint8(v___x_3640_, sizeof(void*)*14 + 1, v_suppressElabErrors_3635_);
v___x_3641_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3574_, v_id_3577_, v___y_3589_, v___x_3637_, v_minIndexable_3578_, v___x_3638_, v___x_3638_, v___y_3592_, v___y_3593_, v___x_3640_, v___y_3595_);
lean_dec_ref(v___x_3640_);
return v___x_3641_;
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec(v___y_3589_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_3642_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3597_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3597_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
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
v___jp_3650_:
{
lean_object* v___x_3659_; 
v___x_3659_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3578_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
lean_dec_ref(v___x_3659_);
v___x_3660_ = l_Lean_Meta_Grind_grindExt;
v___x_3661_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3660_, v___y_3658_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref(v___x_3661_);
lean_inc(v___y_3651_);
v___x_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___y_3651_);
v___x_3664_ = l_Lean_Meta_Grind_Theorems_find___redArg(v_a_3662_, v___x_3663_);
lean_dec_ref(v___x_3663_);
lean_dec(v_a_3662_);
v___x_3665_ = lean_box(0);
v___x_3666_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__1(v___y_3652_, v___x_3664_, v___x_3665_);
lean_dec(v___y_3652_);
v___x_3667_ = l_List_isEmpty___redArg(v___x_3666_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3668_; 
lean_dec(v___y_3651_);
lean_dec(v_p_3575_);
v___x_3668_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v___x_3666_, v_params_3574_);
lean_dec(v___x_3666_);
return v___x_3668_;
}
else
{
lean_object* v___x_3669_; uint8_t v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec(v___x_3666_);
lean_dec_ref(v_params_3574_);
v___x_3669_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__1);
v___x_3670_ = 0;
v___x_3671_ = l_Lean_MessageData_ofConstName(v___y_3651_, v___x_3670_);
v___x_3672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3669_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
v___x_3673_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__3);
v___x_3674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3672_);
lean_ctor_set(v___x_3674_, 1, v___x_3673_);
v___x_3675_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_p_3575_, v___x_3674_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v_p_3575_);
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_dec(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_3684_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3661_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3661_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_3692_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3659_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3659_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
v___jp_3700_:
{
lean_object* v___x_3707_; 
v___x_3707_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3578_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_fileName_3708_; lean_object* v_fileMap_3709_; lean_object* v_options_3710_; lean_object* v_currRecDepth_3711_; lean_object* v_maxRecDepth_3712_; lean_object* v_ref_3713_; lean_object* v_currNamespace_3714_; lean_object* v_openDecls_3715_; lean_object* v_initHeartbeats_3716_; lean_object* v_maxHeartbeats_3717_; lean_object* v_quotContext_3718_; lean_object* v_currMacroScope_3719_; uint8_t v_diag_3720_; lean_object* v_cancelTk_x3f_3721_; uint8_t v_suppressElabErrors_3722_; lean_object* v_inheritedTraceOptions_3723_; lean_object* v_ref_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec_ref(v___x_3707_);
v_fileName_3708_ = lean_ctor_get(v___y_3705_, 0);
v_fileMap_3709_ = lean_ctor_get(v___y_3705_, 1);
v_options_3710_ = lean_ctor_get(v___y_3705_, 2);
v_currRecDepth_3711_ = lean_ctor_get(v___y_3705_, 3);
v_maxRecDepth_3712_ = lean_ctor_get(v___y_3705_, 4);
v_ref_3713_ = lean_ctor_get(v___y_3705_, 5);
v_currNamespace_3714_ = lean_ctor_get(v___y_3705_, 6);
v_openDecls_3715_ = lean_ctor_get(v___y_3705_, 7);
v_initHeartbeats_3716_ = lean_ctor_get(v___y_3705_, 8);
v_maxHeartbeats_3717_ = lean_ctor_get(v___y_3705_, 9);
v_quotContext_3718_ = lean_ctor_get(v___y_3705_, 10);
v_currMacroScope_3719_ = lean_ctor_get(v___y_3705_, 11);
v_diag_3720_ = lean_ctor_get_uint8(v___y_3705_, sizeof(void*)*14);
v_cancelTk_x3f_3721_ = lean_ctor_get(v___y_3705_, 12);
v_suppressElabErrors_3722_ = lean_ctor_get_uint8(v___y_3705_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3723_ = lean_ctor_get(v___y_3705_, 13);
v_ref_3724_ = l_Lean_replaceRef(v_p_3575_, v_ref_3713_);
lean_dec(v_p_3575_);
lean_inc_ref(v_inheritedTraceOptions_3723_);
lean_inc(v_cancelTk_x3f_3721_);
lean_inc(v_currMacroScope_3719_);
lean_inc(v_quotContext_3718_);
lean_inc(v_maxHeartbeats_3717_);
lean_inc(v_initHeartbeats_3716_);
lean_inc(v_openDecls_3715_);
lean_inc(v_currNamespace_3714_);
lean_inc(v_maxRecDepth_3712_);
lean_inc(v_currRecDepth_3711_);
lean_inc_ref(v_options_3710_);
lean_inc_ref(v_fileMap_3709_);
lean_inc_ref(v_fileName_3708_);
v___x_3725_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3725_, 0, v_fileName_3708_);
lean_ctor_set(v___x_3725_, 1, v_fileMap_3709_);
lean_ctor_set(v___x_3725_, 2, v_options_3710_);
lean_ctor_set(v___x_3725_, 3, v_currRecDepth_3711_);
lean_ctor_set(v___x_3725_, 4, v_maxRecDepth_3712_);
lean_ctor_set(v___x_3725_, 5, v_ref_3724_);
lean_ctor_set(v___x_3725_, 6, v_currNamespace_3714_);
lean_ctor_set(v___x_3725_, 7, v_openDecls_3715_);
lean_ctor_set(v___x_3725_, 8, v_initHeartbeats_3716_);
lean_ctor_set(v___x_3725_, 9, v_maxHeartbeats_3717_);
lean_ctor_set(v___x_3725_, 10, v_quotContext_3718_);
lean_ctor_set(v___x_3725_, 11, v_currMacroScope_3719_);
lean_ctor_set(v___x_3725_, 12, v_cancelTk_x3f_3721_);
lean_ctor_set(v___x_3725_, 13, v_inheritedTraceOptions_3723_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*14, v_diag_3720_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*14 + 1, v_suppressElabErrors_3722_);
lean_inc(v___y_3702_);
v___x_3726_ = l_Lean_Meta_Grind_validateCasesAttr(v___y_3702_, v___y_3701_, v___x_3725_, v___y_3706_);
lean_dec_ref(v___x_3725_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3734_; 
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; 
v_unused_3735_ = lean_ctor_get(v___x_3726_, 0);
lean_dec(v_unused_3735_);
v___x_3728_ = v___x_3726_;
v_isShared_3729_ = v_isSharedCheck_3734_;
goto v_resetjp_3727_;
}
else
{
lean_dec(v___x_3726_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3734_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3730_; lean_object* v___x_3732_; 
v___x_3730_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertCasesTypes(v_params_3574_, v___y_3702_, v___y_3701_);
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 0, v___x_3730_);
v___x_3732_ = v___x_3728_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3730_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v___y_3702_);
lean_dec_ref(v_params_3574_);
v_a_3736_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3726_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3726_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec(v___y_3702_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_3744_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3707_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3707_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
v___jp_3752_:
{
lean_object* v_ctors_3760_; lean_object* v___x_3761_; 
v_ctors_3760_ = lean_ctor_get(v___y_3753_, 4);
lean_inc(v_ctors_3760_);
lean_dec_ref(v___y_3753_);
v___x_3761_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_3575_, v_id_3577_, v_minIndexable_3578_, v_ctors_3760_, v_params_3574_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
lean_dec(v_ctors_3760_);
lean_dec(v_p_3575_);
return v___x_3761_;
}
v___jp_3762_:
{
lean_object* v___x_3764_; 
lean_inc(v_a_3763_);
v___x_3764_ = l_Lean_Linter_checkDeprecated(v_a_3763_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_dec_ref(v___x_3764_);
if (lean_obj_tag(v_mod_x3f_3576_) == 1)
{
lean_object* v_val_3765_; lean_object* v___x_3766_; 
v_val_3765_ = lean_ctor_get(v_mod_x3f_3576_, 0);
lean_inc(v_val_3765_);
lean_dec_ref(v_mod_x3f_3576_);
v___x_3766_ = l_Lean_Meta_Grind_getAttrKindCore(v_val_3765_, v_a_3585_, v_a_3586_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3970_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3970_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3970_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
switch(lean_obj_tag(v_a_3767_))
{
case 0:
{
lean_object* v_k_3771_; 
lean_del_object(v___x_3769_);
v_k_3771_ = lean_ctor_get(v_a_3767_, 0);
lean_inc(v_k_3771_);
lean_dec_ref(v_a_3767_);
if (lean_obj_tag(v_k_3771_) == 9)
{
lean_dec(v_id_3577_);
if (v_only_3579_ == 0)
{
lean_object* v_fileName_3772_; lean_object* v_fileMap_3773_; lean_object* v_options_3774_; lean_object* v_currRecDepth_3775_; lean_object* v_maxRecDepth_3776_; lean_object* v_ref_3777_; lean_object* v_currNamespace_3778_; lean_object* v_openDecls_3779_; lean_object* v_initHeartbeats_3780_; lean_object* v_maxHeartbeats_3781_; lean_object* v_quotContext_3782_; lean_object* v_currMacroScope_3783_; uint8_t v_diag_3784_; lean_object* v_cancelTk_x3f_3785_; uint8_t v_suppressElabErrors_3786_; lean_object* v_inheritedTraceOptions_3787_; lean_object* v_ref_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v_fileName_3772_ = lean_ctor_get(v_a_3585_, 0);
v_fileMap_3773_ = lean_ctor_get(v_a_3585_, 1);
v_options_3774_ = lean_ctor_get(v_a_3585_, 2);
v_currRecDepth_3775_ = lean_ctor_get(v_a_3585_, 3);
v_maxRecDepth_3776_ = lean_ctor_get(v_a_3585_, 4);
v_ref_3777_ = lean_ctor_get(v_a_3585_, 5);
v_currNamespace_3778_ = lean_ctor_get(v_a_3585_, 6);
v_openDecls_3779_ = lean_ctor_get(v_a_3585_, 7);
v_initHeartbeats_3780_ = lean_ctor_get(v_a_3585_, 8);
v_maxHeartbeats_3781_ = lean_ctor_get(v_a_3585_, 9);
v_quotContext_3782_ = lean_ctor_get(v_a_3585_, 10);
v_currMacroScope_3783_ = lean_ctor_get(v_a_3585_, 11);
v_diag_3784_ = lean_ctor_get_uint8(v_a_3585_, sizeof(void*)*14);
v_cancelTk_x3f_3785_ = lean_ctor_get(v_a_3585_, 12);
v_suppressElabErrors_3786_ = lean_ctor_get_uint8(v_a_3585_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3787_ = lean_ctor_get(v_a_3585_, 13);
v_ref_3788_ = l_Lean_replaceRef(v_p_3575_, v_ref_3777_);
lean_inc_ref(v_inheritedTraceOptions_3787_);
lean_inc(v_cancelTk_x3f_3785_);
lean_inc(v_currMacroScope_3783_);
lean_inc(v_quotContext_3782_);
lean_inc(v_maxHeartbeats_3781_);
lean_inc(v_initHeartbeats_3780_);
lean_inc(v_openDecls_3779_);
lean_inc(v_currNamespace_3778_);
lean_inc(v_maxRecDepth_3776_);
lean_inc(v_currRecDepth_3775_);
lean_inc_ref(v_options_3774_);
lean_inc_ref(v_fileMap_3773_);
lean_inc_ref(v_fileName_3772_);
v___x_3789_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3789_, 0, v_fileName_3772_);
lean_ctor_set(v___x_3789_, 1, v_fileMap_3773_);
lean_ctor_set(v___x_3789_, 2, v_options_3774_);
lean_ctor_set(v___x_3789_, 3, v_currRecDepth_3775_);
lean_ctor_set(v___x_3789_, 4, v_maxRecDepth_3776_);
lean_ctor_set(v___x_3789_, 5, v_ref_3788_);
lean_ctor_set(v___x_3789_, 6, v_currNamespace_3778_);
lean_ctor_set(v___x_3789_, 7, v_openDecls_3779_);
lean_ctor_set(v___x_3789_, 8, v_initHeartbeats_3780_);
lean_ctor_set(v___x_3789_, 9, v_maxHeartbeats_3781_);
lean_ctor_set(v___x_3789_, 10, v_quotContext_3782_);
lean_ctor_set(v___x_3789_, 11, v_currMacroScope_3783_);
lean_ctor_set(v___x_3789_, 12, v_cancelTk_x3f_3785_);
lean_ctor_set(v___x_3789_, 13, v_inheritedTraceOptions_3787_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*14, v_diag_3784_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*14 + 1, v_suppressElabErrors_3786_);
v___x_3790_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___x_3789_, v_a_3586_);
lean_dec_ref(v___x_3789_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_dec_ref(v___x_3790_);
v___y_3651_ = v_a_3763_;
v___y_3652_ = v_k_3771_;
v___y_3653_ = v_a_3581_;
v___y_3654_ = v_a_3582_;
v___y_3655_ = v_a_3583_;
v___y_3656_ = v_a_3584_;
v___y_3657_ = v_a_3585_;
v___y_3658_ = v_a_3586_;
goto v___jp_3650_;
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec(v_a_3763_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3790_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3790_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
v___y_3651_ = v_a_3763_;
v___y_3652_ = v_k_3771_;
v___y_3653_ = v_a_3581_;
v___y_3654_ = v_a_3582_;
v___y_3655_ = v_a_3583_;
v___y_3656_ = v_a_3584_;
v___y_3657_ = v_a_3585_;
v___y_3658_ = v_a_3586_;
goto v___jp_3650_;
}
}
else
{
lean_object* v_fileName_3799_; lean_object* v_fileMap_3800_; lean_object* v_options_3801_; lean_object* v_currRecDepth_3802_; lean_object* v_maxRecDepth_3803_; lean_object* v_ref_3804_; lean_object* v_currNamespace_3805_; lean_object* v_openDecls_3806_; lean_object* v_initHeartbeats_3807_; lean_object* v_maxHeartbeats_3808_; lean_object* v_quotContext_3809_; lean_object* v_currMacroScope_3810_; uint8_t v_diag_3811_; lean_object* v_cancelTk_x3f_3812_; uint8_t v_suppressElabErrors_3813_; lean_object* v_inheritedTraceOptions_3814_; uint8_t v___x_3815_; uint8_t v___x_3816_; lean_object* v_ref_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v_fileName_3799_ = lean_ctor_get(v_a_3585_, 0);
v_fileMap_3800_ = lean_ctor_get(v_a_3585_, 1);
v_options_3801_ = lean_ctor_get(v_a_3585_, 2);
v_currRecDepth_3802_ = lean_ctor_get(v_a_3585_, 3);
v_maxRecDepth_3803_ = lean_ctor_get(v_a_3585_, 4);
v_ref_3804_ = lean_ctor_get(v_a_3585_, 5);
v_currNamespace_3805_ = lean_ctor_get(v_a_3585_, 6);
v_openDecls_3806_ = lean_ctor_get(v_a_3585_, 7);
v_initHeartbeats_3807_ = lean_ctor_get(v_a_3585_, 8);
v_maxHeartbeats_3808_ = lean_ctor_get(v_a_3585_, 9);
v_quotContext_3809_ = lean_ctor_get(v_a_3585_, 10);
v_currMacroScope_3810_ = lean_ctor_get(v_a_3585_, 11);
v_diag_3811_ = lean_ctor_get_uint8(v_a_3585_, sizeof(void*)*14);
v_cancelTk_x3f_3812_ = lean_ctor_get(v_a_3585_, 12);
v_suppressElabErrors_3813_ = lean_ctor_get_uint8(v_a_3585_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3814_ = lean_ctor_get(v_a_3585_, 13);
v___x_3815_ = 0;
v___x_3816_ = 1;
v_ref_3817_ = l_Lean_replaceRef(v_p_3575_, v_ref_3804_);
lean_dec(v_p_3575_);
lean_inc_ref(v_inheritedTraceOptions_3814_);
lean_inc(v_cancelTk_x3f_3812_);
lean_inc(v_currMacroScope_3810_);
lean_inc(v_quotContext_3809_);
lean_inc(v_maxHeartbeats_3808_);
lean_inc(v_initHeartbeats_3807_);
lean_inc(v_openDecls_3806_);
lean_inc(v_currNamespace_3805_);
lean_inc(v_maxRecDepth_3803_);
lean_inc(v_currRecDepth_3802_);
lean_inc_ref(v_options_3801_);
lean_inc_ref(v_fileMap_3800_);
lean_inc_ref(v_fileName_3799_);
v___x_3818_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3818_, 0, v_fileName_3799_);
lean_ctor_set(v___x_3818_, 1, v_fileMap_3800_);
lean_ctor_set(v___x_3818_, 2, v_options_3801_);
lean_ctor_set(v___x_3818_, 3, v_currRecDepth_3802_);
lean_ctor_set(v___x_3818_, 4, v_maxRecDepth_3803_);
lean_ctor_set(v___x_3818_, 5, v_ref_3817_);
lean_ctor_set(v___x_3818_, 6, v_currNamespace_3805_);
lean_ctor_set(v___x_3818_, 7, v_openDecls_3806_);
lean_ctor_set(v___x_3818_, 8, v_initHeartbeats_3807_);
lean_ctor_set(v___x_3818_, 9, v_maxHeartbeats_3808_);
lean_ctor_set(v___x_3818_, 10, v_quotContext_3809_);
lean_ctor_set(v___x_3818_, 11, v_currMacroScope_3810_);
lean_ctor_set(v___x_3818_, 12, v_cancelTk_x3f_3812_);
lean_ctor_set(v___x_3818_, 13, v_inheritedTraceOptions_3814_);
lean_ctor_set_uint8(v___x_3818_, sizeof(void*)*14, v_diag_3811_);
lean_ctor_set_uint8(v___x_3818_, sizeof(void*)*14 + 1, v_suppressElabErrors_3813_);
v___x_3819_ = l_Lean_Elab_Tactic_addEMatchTheorem(v_params_3574_, v_id_3577_, v_a_3763_, v_k_3771_, v_minIndexable_3578_, v___x_3815_, v___x_3816_, v_a_3583_, v_a_3584_, v___x_3818_, v_a_3586_);
lean_dec_ref(v___x_3818_);
return v___x_3819_;
}
}
case 1:
{
lean_del_object(v___x_3769_);
lean_dec(v_id_3577_);
if (v_incremental_3580_ == 0)
{
uint8_t v_eager_3820_; 
v_eager_3820_ = lean_ctor_get_uint8(v_a_3767_, 0);
lean_dec_ref(v_a_3767_);
v___y_3701_ = v_eager_3820_;
v___y_3702_ = v_a_3763_;
v___y_3703_ = v_a_3583_;
v___y_3704_ = v_a_3584_;
v___y_3705_ = v_a_3585_;
v___y_3706_ = v_a_3586_;
goto v___jp_3700_;
}
else
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3763_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v___x_3821_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3822_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3821_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
case 2:
{
uint8_t v___x_3831_; lean_object* v___x_3832_; 
lean_del_object(v___x_3769_);
v___x_3831_ = 0;
lean_inc(v_a_3763_);
v___x_3832_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_a_3763_, v___x_3831_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref(v___x_3832_);
if (lean_obj_tag(v_a_3833_) == 1)
{
lean_dec(v_a_3763_);
if (v_incremental_3580_ == 0)
{
lean_object* v_val_3834_; 
v_val_3834_ = lean_ctor_get(v_a_3833_, 0);
lean_inc(v_val_3834_);
lean_dec_ref(v_a_3833_);
v___y_3753_ = v_val_3834_;
v___y_3754_ = v_a_3581_;
v___y_3755_ = v_a_3582_;
v___y_3756_ = v_a_3583_;
v___y_3757_ = v_a_3584_;
v___y_3758_ = v_a_3585_;
v___y_3759_ = v_a_3586_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec_ref(v_a_3833_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v___x_3835_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__5);
v___x_3836_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3835_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
else
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_dec(v_a_3833_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v___x_3845_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__7);
v___x_3846_ = l_Lean_MessageData_ofConstName(v_a_3763_, v___x_3831_);
v___x_3847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3845_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__9);
v___x_3849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3847_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
v___x_3850_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3849_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3850_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3850_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec(v_a_3763_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_3859_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3832_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3832_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
case 3:
{
lean_del_object(v___x_3769_);
v___y_3589_ = v_a_3763_;
v___y_3590_ = v_a_3581_;
v___y_3591_ = v_a_3582_;
v___y_3592_ = v_a_3583_;
v___y_3593_ = v_a_3584_;
v___y_3594_ = v_a_3585_;
v___y_3595_ = v_a_3586_;
goto v___jp_3588_;
}
case 4:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_del_object(v___x_3769_);
lean_dec(v_a_3763_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v___x_3867_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__11);
v___x_3868_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3867_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
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
case 5:
{
lean_object* v_prio_3877_; lean_object* v___x_3878_; 
lean_del_object(v___x_3769_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
v_prio_3877_ = lean_ctor_get(v_a_3767_, 0);
lean_inc(v_prio_3877_);
lean_dec_ref(v_a_3767_);
v___x_3878_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_ensureNoMinIndexable(v_minIndexable_3578_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3902_; 
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3902_ == 0)
{
lean_object* v_unused_3903_; 
v_unused_3903_ = lean_ctor_get(v___x_3878_, 0);
lean_dec(v_unused_3903_);
v___x_3880_ = v___x_3878_;
v_isShared_3881_ = v_isSharedCheck_3902_;
goto v_resetjp_3879_;
}
else
{
lean_dec(v___x_3878_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3902_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v_config_3882_; lean_object* v_extensions_3883_; lean_object* v_extra_3884_; lean_object* v_extraInj_3885_; lean_object* v_extraFacts_3886_; lean_object* v_symPrios_3887_; lean_object* v_norm_3888_; lean_object* v_normProcs_3889_; lean_object* v_anchorRefs_x3f_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3901_; 
v_config_3882_ = lean_ctor_get(v_params_3574_, 0);
v_extensions_3883_ = lean_ctor_get(v_params_3574_, 1);
v_extra_3884_ = lean_ctor_get(v_params_3574_, 2);
v_extraInj_3885_ = lean_ctor_get(v_params_3574_, 3);
v_extraFacts_3886_ = lean_ctor_get(v_params_3574_, 4);
v_symPrios_3887_ = lean_ctor_get(v_params_3574_, 5);
v_norm_3888_ = lean_ctor_get(v_params_3574_, 6);
v_normProcs_3889_ = lean_ctor_get(v_params_3574_, 7);
v_anchorRefs_x3f_3890_ = lean_ctor_get(v_params_3574_, 8);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_params_3574_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3892_ = v_params_3574_;
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
lean_dec(v_params_3574_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3901_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3894_ = l_Lean_Meta_Grind_SymbolPriorities_insert(v_symPrios_3887_, v_a_3763_, v_prio_3877_);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 5, v___x_3894_);
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
lean_ctor_set(v_reuseFailAlloc_3900_, 3, v_extraInj_3885_);
lean_ctor_set(v_reuseFailAlloc_3900_, 4, v_extraFacts_3886_);
lean_ctor_set(v_reuseFailAlloc_3900_, 5, v___x_3894_);
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
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
lean_dec(v_prio_3877_);
lean_dec(v_a_3763_);
lean_dec_ref(v_params_3574_);
v_a_3904_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3878_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3878_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
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
case 6:
{
lean_object* v___x_3912_; 
lean_del_object(v___x_3769_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
v___x_3912_ = l_Lean_Meta_Grind_mkInjectiveTheorem(v_a_3763_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3937_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3915_ = v___x_3912_;
v_isShared_3916_ = v_isSharedCheck_3937_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3912_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3937_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v_config_3917_; lean_object* v_extensions_3918_; lean_object* v_extra_3919_; lean_object* v_extraInj_3920_; lean_object* v_extraFacts_3921_; lean_object* v_symPrios_3922_; lean_object* v_norm_3923_; lean_object* v_normProcs_3924_; lean_object* v_anchorRefs_x3f_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3936_; 
v_config_3917_ = lean_ctor_get(v_params_3574_, 0);
v_extensions_3918_ = lean_ctor_get(v_params_3574_, 1);
v_extra_3919_ = lean_ctor_get(v_params_3574_, 2);
v_extraInj_3920_ = lean_ctor_get(v_params_3574_, 3);
v_extraFacts_3921_ = lean_ctor_get(v_params_3574_, 4);
v_symPrios_3922_ = lean_ctor_get(v_params_3574_, 5);
v_norm_3923_ = lean_ctor_get(v_params_3574_, 6);
v_normProcs_3924_ = lean_ctor_get(v_params_3574_, 7);
v_anchorRefs_x3f_3925_ = lean_ctor_get(v_params_3574_, 8);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_params_3574_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3927_ = v_params_3574_;
v_isShared_3928_ = v_isSharedCheck_3936_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_anchorRefs_x3f_3925_);
lean_inc(v_normProcs_3924_);
lean_inc(v_norm_3923_);
lean_inc(v_symPrios_3922_);
lean_inc(v_extraFacts_3921_);
lean_inc(v_extraInj_3920_);
lean_inc(v_extra_3919_);
lean_inc(v_extensions_3918_);
lean_inc(v_config_3917_);
lean_dec(v_params_3574_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3936_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3929_ = l_Lean_PersistentArray_push___redArg(v_extraInj_3920_, v_a_3913_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 3, v___x_3929_);
v___x_3931_ = v___x_3927_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_config_3917_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_extensions_3918_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_extra_3919_);
lean_ctor_set(v_reuseFailAlloc_3935_, 3, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3935_, 4, v_extraFacts_3921_);
lean_ctor_set(v_reuseFailAlloc_3935_, 5, v_symPrios_3922_);
lean_ctor_set(v_reuseFailAlloc_3935_, 6, v_norm_3923_);
lean_ctor_set(v_reuseFailAlloc_3935_, 7, v_normProcs_3924_);
lean_ctor_set(v_reuseFailAlloc_3935_, 8, v_anchorRefs_x3f_3925_);
v___x_3931_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3933_; 
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 0, v___x_3931_);
v___x_3933_ = v___x_3915_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3931_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec_ref(v_params_3574_);
v_a_3938_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3912_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3912_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
case 7:
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
v___x_3946_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_insertFunCC(v_params_3574_, v_a_3763_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v___x_3946_);
v___x_3948_ = v___x_3769_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3946_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
case 8:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3959_; 
lean_dec_ref(v_a_3767_);
lean_del_object(v___x_3769_);
lean_dec(v_a_3763_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v___x_3950_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__13);
v___x_3951_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3950_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3954_ = v___x_3951_;
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
default: 
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_del_object(v___x_3769_);
lean_dec(v_a_3763_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v___x_3960_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___closed__15);
v___x_3961_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_3960_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3961_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3961_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec(v_a_3763_);
lean_dec(v_id_3577_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_3971_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3766_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3766_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
else
{
lean_dec(v_mod_x3f_3576_);
v___y_3589_ = v_a_3763_;
v___y_3590_ = v_a_3581_;
v___y_3591_ = v_a_3582_;
v___y_3592_ = v_a_3583_;
v___y_3593_ = v_a_3584_;
v___y_3594_ = v_a_3585_;
v___y_3595_ = v_a_3586_;
goto v___jp_3588_;
}
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3986_; 
lean_dec(v_a_3763_);
lean_dec(v_id_3577_);
lean_dec(v_mod_x3f_3576_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_3979_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3981_ = v___x_3764_;
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3764_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3984_; 
if (v_isShared_3982_ == 0)
{
v___x_3984_ = v___x_3981_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
v___jp_3987_:
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3998_; 
v_a_3989_ = lean_ctor_get(v___y_3988_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___y_3988_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3991_ = v___y_3988_;
v_isShared_3992_ = v_isSharedCheck_3998_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___y_3988_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3998_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
if (lean_obj_tag(v_a_3989_) == 0)
{
lean_object* v_a_3993_; lean_object* v___x_3995_; 
lean_dec(v_id_3577_);
lean_dec(v_mod_x3f_3576_);
lean_dec(v_p_3575_);
lean_dec_ref(v_params_3574_);
v_a_3993_ = lean_ctor_get(v_a_3989_, 0);
lean_inc(v_a_3993_);
lean_dec_ref(v_a_3989_);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 0, v_a_3993_);
v___x_3995_ = v___x_3991_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3993_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
else
{
lean_object* v_a_3997_; 
lean_del_object(v___x_3991_);
v_a_3997_ = lean_ctor_get(v_a_3989_, 0);
lean_inc(v_a_3997_);
lean_dec_ref(v_a_3989_);
v_a_3763_ = v_a_3997_;
goto v___jp_3762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam___boxed(lean_object* v_params_4077_, lean_object* v_p_4078_, lean_object* v_mod_x3f_4079_, lean_object* v_id_4080_, lean_object* v_minIndexable_4081_, lean_object* v_only_4082_, lean_object* v_incremental_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
uint8_t v_minIndexable_boxed_4091_; uint8_t v_only_boxed_4092_; uint8_t v_incremental_boxed_4093_; lean_object* v_res_4094_; 
v_minIndexable_boxed_4091_ = lean_unbox(v_minIndexable_4081_);
v_only_boxed_4092_ = lean_unbox(v_only_4082_);
v_incremental_boxed_4093_ = lean_unbox(v_incremental_4083_);
v_res_4094_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_params_4077_, v_p_4078_, v_mod_x3f_4079_, v_id_4080_, v_minIndexable_boxed_4091_, v_only_boxed_4092_, v_incremental_boxed_4093_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
lean_dec(v_a_4087_);
lean_dec_ref(v_a_4086_);
lean_dec(v_a_4085_);
lean_dec_ref(v_a_4084_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(lean_object* v_p_4095_, lean_object* v_id_4096_, uint8_t v_minIndexable_4097_, lean_object* v_as_4098_, lean_object* v_as_x27_4099_, lean_object* v_b_4100_, lean_object* v_a_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___redArg(v_p_4095_, v_id_4096_, v_minIndexable_4097_, v_as_x27_4099_, v_b_4100_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0___boxed(lean_object* v_p_4110_, lean_object* v_id_4111_, lean_object* v_minIndexable_4112_, lean_object* v_as_4113_, lean_object* v_as_x27_4114_, lean_object* v_b_4115_, lean_object* v_a_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
uint8_t v_minIndexable_boxed_4124_; lean_object* v_res_4125_; 
v_minIndexable_boxed_4124_ = lean_unbox(v_minIndexable_4112_);
v_res_4125_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__0(v_p_4110_, v_id_4111_, v_minIndexable_boxed_4124_, v_as_4113_, v_as_x27_4114_, v_b_4115_, v_a_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v_as_x27_4114_);
lean_dec(v_as_4113_);
lean_dec(v_p_4110_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(lean_object* v_as_4126_, lean_object* v_as_x27_4127_, lean_object* v_b_4128_, lean_object* v_a_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___redArg(v_as_x27_4127_, v_b_4128_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2___boxed(lean_object* v_as_4138_, lean_object* v_as_x27_4139_, lean_object* v_b_4140_, lean_object* v_a_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__2(v_as_4138_, v_as_x27_4139_, v_b_4140_, v_a_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v_as_x27_4139_);
lean_dec(v_as_4138_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(lean_object* v_00_u03b1_4150_, lean_object* v_ref_4151_, lean_object* v_msg_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_ref_4151_, v_msg_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___boxed(lean_object* v_00_u03b1_4161_, lean_object* v_ref_4162_, lean_object* v_msg_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3(v_00_u03b1_4161_, v_ref_4162_, v_msg_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec_ref(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v_ref_4162_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(lean_object* v_p_4172_, lean_object* v_id_4173_, uint8_t v_minIndexable_4174_, lean_object* v_as_4175_, lean_object* v_as_x27_4176_, lean_object* v_b_4177_, lean_object* v_a_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___redArg(v_p_4172_, v_id_4173_, v_minIndexable_4174_, v_as_x27_4176_, v_b_4177_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4___boxed(lean_object* v_p_4187_, lean_object* v_id_4188_, lean_object* v_minIndexable_4189_, lean_object* v_as_4190_, lean_object* v_as_x27_4191_, lean_object* v_b_4192_, lean_object* v_a_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
uint8_t v_minIndexable_boxed_4201_; lean_object* v_res_4202_; 
v_minIndexable_boxed_4201_ = lean_unbox(v_minIndexable_4189_);
v_res_4202_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__4(v_p_4187_, v_id_4188_, v_minIndexable_boxed_4201_, v_as_4190_, v_as_x27_4191_, v_b_4192_, v_a_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v_as_x27_4191_);
lean_dec(v_as_4190_);
lean_dec(v_p_4187_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(lean_object* v_00_u03b4_4203_, lean_object* v_t_4204_, lean_object* v_k_4205_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___redArg(v_t_4204_, v_k_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5___boxed(lean_object* v_00_u03b4_4207_, lean_object* v_t_4208_, lean_object* v_k_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__5(v_00_u03b4_4207_, v_t_4208_, v_k_4209_);
lean_dec(v_k_4209_);
lean_dec(v_t_4208_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(lean_object* v_givenName_4211_, uint8_t v_skipAuxDecl_4212_, lean_object* v_auxDeclToFullName_4213_, lean_object* v___x_4214_, lean_object* v_givenNameView_4215_, lean_object* v_as_4216_, lean_object* v_i_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v___x_4219_; 
v___x_4219_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___redArg(v_givenName_4211_, v_skipAuxDecl_4212_, v_auxDeclToFullName_4213_, v___x_4214_, v_givenNameView_4215_, v_as_4216_, v_i_4217_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7___boxed(lean_object* v_givenName_4220_, lean_object* v_skipAuxDecl_4221_, lean_object* v_auxDeclToFullName_4222_, lean_object* v___x_4223_, lean_object* v_givenNameView_4224_, lean_object* v_as_4225_, lean_object* v_i_4226_, lean_object* v_a_4227_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4228_; lean_object* v_res_4229_; 
v_skipAuxDecl_boxed_4228_ = lean_unbox(v_skipAuxDecl_4221_);
v_res_4229_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__7(v_givenName_4220_, v_skipAuxDecl_boxed_4228_, v_auxDeclToFullName_4222_, v___x_4223_, v_givenNameView_4224_, v_as_4225_, v_i_4226_, v_a_4227_);
lean_dec_ref(v_as_4225_);
lean_dec(v_auxDeclToFullName_4222_);
lean_dec(v_givenName_4220_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(lean_object* v_localDecl_x3f_4230_, lean_object* v_givenName_4231_, lean_object* v_as_4232_, lean_object* v_i_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___x_4235_; 
v___x_4235_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___redArg(v_localDecl_x3f_4230_, v_givenName_4231_, v_as_4232_, v_i_4233_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10___boxed(lean_object* v_localDecl_x3f_4236_, lean_object* v_givenName_4237_, lean_object* v_as_4238_, lean_object* v_i_4239_, lean_object* v_a_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__10(v_localDecl_x3f_4236_, v_givenName_4237_, v_as_4238_, v_i_4239_, v_a_4240_);
lean_dec_ref(v_as_4238_);
lean_dec(v_givenName_4237_);
lean_dec(v_localDecl_x3f_4236_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(lean_object* v_givenName_4242_, uint8_t v_skipAuxDecl_4243_, lean_object* v_auxDeclToFullName_4244_, lean_object* v___x_4245_, lean_object* v_givenNameView_4246_, lean_object* v_as_4247_, lean_object* v_i_4248_, lean_object* v_a_4249_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___redArg(v_givenName_4242_, v_skipAuxDecl_4243_, v_auxDeclToFullName_4244_, v___x_4245_, v_givenNameView_4246_, v_as_4247_, v_i_4248_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9___boxed(lean_object* v_givenName_4251_, lean_object* v_skipAuxDecl_4252_, lean_object* v_auxDeclToFullName_4253_, lean_object* v___x_4254_, lean_object* v_givenNameView_4255_, lean_object* v_as_4256_, lean_object* v_i_4257_, lean_object* v_a_4258_){
_start:
{
uint8_t v_skipAuxDecl_boxed_4259_; lean_object* v_res_4260_; 
v_skipAuxDecl_boxed_4259_ = lean_unbox(v_skipAuxDecl_4252_);
v_res_4260_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__6_spec__8_spec__9(v_givenName_4251_, v_skipAuxDecl_boxed_4259_, v_auxDeclToFullName_4253_, v___x_4254_, v_givenNameView_4255_, v_as_4256_, v_i_4257_, v_a_4258_);
lean_dec_ref(v_as_4256_);
lean_dec(v_auxDeclToFullName_4253_);
lean_dec(v_givenName_4251_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(lean_object* v_localDecl_x3f_4261_, lean_object* v_givenName_4262_, lean_object* v_as_4263_, lean_object* v_i_4264_, lean_object* v_a_4265_){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___redArg(v_localDecl_x3f_4261_, v_givenName_4262_, v_as_4263_, v_i_4264_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13___boxed(lean_object* v_localDecl_x3f_4267_, lean_object* v_givenName_4268_, lean_object* v_as_4269_, lean_object* v_i_4270_, lean_object* v_a_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__7_spec__11_spec__13(v_localDecl_x3f_4267_, v_givenName_4268_, v_as_4269_, v_i_4270_, v_a_4271_);
lean_dec_ref(v_as_4269_);
lean_dec(v_givenName_4268_);
lean_dec(v_localDecl_x3f_4267_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(lean_object* v_opt_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___redArg(v_opt_4273_, v___y_4278_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18___boxed(lean_object* v_opt_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__18(v_opt_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec_ref(v_opt_4282_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(lean_object* v_ref_4291_, lean_object* v_msgData_4292_, uint8_t v_severity_4293_, uint8_t v_isSilent_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___redArg(v_ref_4291_, v_msgData_4292_, v_severity_4293_, v_isSilent_4294_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22___boxed(lean_object* v_ref_4303_, lean_object* v_msgData_4304_, lean_object* v_severity_4305_, lean_object* v_isSilent_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
uint8_t v_severity_boxed_4314_; uint8_t v_isSilent_boxed_4315_; lean_object* v_res_4316_; 
v_severity_boxed_4314_ = lean_unbox(v_severity_4305_);
v_isSilent_boxed_4315_ = lean_unbox(v_isSilent_4306_);
v_res_4316_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_resolveGlobalName___at___00__private_Lean_ResolveName_0__Lean_resolveLocalName_loop___at___00Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5_spec__8_spec__13_spec__17_spec__19_spec__21_spec__22(v_ref_4303_, v_msgData_4304_, v_severity_boxed_4314_, v_isSilent_boxed_4315_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v_ref_4303_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(lean_object* v___x_4317_, lean_object* v_b_4318_, lean_object* v_____r_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = lean_box(0);
v___x_4328_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_4317_, v___x_4327_, v___y_4324_, v___y_4325_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4330_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc_n(v_a_4329_, 2);
lean_dec_ref(v___x_4328_);
v___x_4330_ = l_Lean_Linter_checkDeprecated(v_a_4329_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
if (lean_obj_tag(v___x_4330_) == 0)
{
uint8_t v___x_4331_; lean_object* v___x_4332_; 
lean_dec_ref(v___x_4330_);
v___x_4331_ = 0;
lean_inc(v_a_4329_);
v___x_4332_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_a_4329_, v___x_4331_, v___y_4324_, v___y_4325_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4392_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4335_ = v___x_4332_;
v_isShared_4336_ = v_isSharedCheck_4392_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4332_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4392_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
if (lean_obj_tag(v_a_4333_) == 1)
{
lean_object* v_val_4337_; lean_object* v___x_4338_; 
lean_del_object(v___x_4335_);
lean_dec(v_a_4329_);
v_val_4337_ = lean_ctor_get(v_a_4333_, 0);
lean_inc_n(v_val_4337_, 2);
lean_dec_ref(v_a_4333_);
v___x_4338_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_val_4337_, v___y_4324_, v___y_4325_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v___x_4339_; 
lean_dec_ref(v___x_4338_);
v___x_4339_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseCasesTypes(v_b_4318_, v_val_4337_, v___y_4324_, v___y_4325_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4349_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4342_ = v___x_4339_;
v_isShared_4343_ = v_isSharedCheck_4349_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4339_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4349_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4347_; 
v___x_4344_ = lean_box(0);
v___x_4345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4344_);
lean_ctor_set(v___x_4345_, 1, v_a_4340_);
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 0, v___x_4345_);
v___x_4347_ = v___x_4342_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4345_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4357_; 
v_a_4350_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4352_ = v___x_4339_;
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v___x_4339_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4357_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4355_; 
if (v_isShared_4353_ == 0)
{
v___x_4355_ = v___x_4352_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
v___x_4355_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
return v___x_4355_;
}
}
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
lean_dec(v_val_4337_);
lean_dec_ref(v_b_4318_);
v_a_4358_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4338_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4338_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
else
{
uint8_t v___x_4366_; 
lean_dec(v_a_4333_);
lean_inc(v_a_4329_);
v___x_4366_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_isInjectiveTheorem(v_b_4318_, v_a_4329_);
if (v___x_4366_ == 0)
{
lean_object* v___x_4367_; 
lean_del_object(v___x_4335_);
v___x_4367_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseEMatch(v_b_4318_, v_a_4329_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4377_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4377_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4377_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4375_; 
v___x_4372_ = lean_box(0);
v___x_4373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4372_);
lean_ctor_set(v___x_4373_, 1, v_a_4368_);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 0, v___x_4373_);
v___x_4375_ = v___x_4370_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4373_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
v_a_4378_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4367_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4367_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
else
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4390_; 
v___x_4386_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Meta_Grind_Params_eraseInj(v_b_4318_, v_a_4329_);
v___x_4387_ = lean_box(0);
v___x_4388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
lean_ctor_set(v___x_4388_, 1, v___x_4386_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v___x_4388_);
v___x_4390_ = v___x_4335_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4388_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_dec(v_a_4329_);
lean_dec_ref(v_b_4318_);
v_a_4393_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4332_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4332_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_a_4329_);
lean_dec_ref(v_b_4318_);
v_a_4401_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4330_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4330_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec_ref(v_b_4318_);
v_a_4409_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4328_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4328_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3___boxed(lean_object* v___x_4417_, lean_object* v_b_4418_, lean_object* v_____r_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4417_, v_b_4418_, v_____r_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(lean_object* v___x_4431_, lean_object* v_b_4432_, lean_object* v_a_4433_, uint8_t v___x_4434_, uint8_t v_only_4435_, uint8_t v_incremental_4436_, lean_object* v_x_4437_, lean_object* v_mod_x3f_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; uint8_t v___x_4449_; 
v___x_4446_ = lean_unsigned_to_nat(1u);
v___x_4447_ = l_Lean_Syntax_getArg(v___x_4431_, v___x_4446_);
v___x_4448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4447_);
v___x_4449_ = l_Lean_Syntax_isOfKind(v___x_4447_, v___x_4448_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; 
v___x_4450_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4432_, v_a_4433_, v_mod_x3f_4438_, v___x_4447_, v___x_4449_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4460_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4453_ = v___x_4450_;
v_isShared_4454_ = v_isSharedCheck_4460_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4450_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4460_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4458_; 
v___x_4455_ = lean_box(0);
v___x_4456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4456_, 0, v___x_4455_);
lean_ctor_set(v___x_4456_, 1, v_a_4451_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4456_);
v___x_4458_ = v___x_4453_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
v_a_4461_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4450_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4450_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = l_Lean_TSyntax_getId(v___x_4447_);
v___x_4470_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4469_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
lean_inc(v_a_4471_);
lean_dec_ref(v___x_4470_);
if (lean_obj_tag(v_a_4471_) == 1)
{
lean_object* v_val_4498_; lean_object* v_snd_4499_; lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4524_; 
v_val_4498_ = lean_ctor_get(v_a_4471_, 0);
lean_inc(v_val_4498_);
lean_dec_ref(v_a_4471_);
v_snd_4499_ = lean_ctor_get(v_val_4498_, 1);
v_isSharedCheck_4524_ = !lean_is_exclusive(v_val_4498_);
if (v_isSharedCheck_4524_ == 0)
{
lean_object* v_unused_4525_; 
v_unused_4525_ = lean_ctor_get(v_val_4498_, 0);
lean_dec(v_unused_4525_);
v___x_4501_ = v_val_4498_;
v_isShared_4502_ = v_isSharedCheck_4524_;
goto v_resetjp_4500_;
}
else
{
lean_inc(v_snd_4499_);
lean_dec(v_val_4498_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4524_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
if (lean_obj_tag(v_snd_4499_) == 1)
{
lean_object* v___x_4503_; 
lean_dec_ref(v_snd_4499_);
v___x_4503_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4432_, v_a_4433_, v_mod_x3f_4438_, v___x_4447_, v___x_4434_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4515_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4506_ = v___x_4503_;
v_isShared_4507_ = v_isSharedCheck_4515_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4503_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4515_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4508_ = lean_box(0);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 1, v_a_4504_);
lean_ctor_set(v___x_4501_, 0, v___x_4508_);
v___x_4510_ = v___x_4501_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_a_4504_);
v___x_4510_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4512_; 
if (v_isShared_4507_ == 0)
{
lean_ctor_set(v___x_4506_, 0, v___x_4510_);
v___x_4512_ = v___x_4506_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_del_object(v___x_4501_);
v_a_4516_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4503_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4503_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
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
lean_del_object(v___x_4501_);
lean_dec(v_snd_4499_);
v___y_4473_ = v___y_4439_;
v___y_4474_ = v___y_4440_;
v___y_4475_ = v___y_4441_;
v___y_4476_ = v___y_4442_;
v___y_4477_ = v___y_4443_;
v___y_4478_ = v___y_4444_;
goto v___jp_4472_;
}
}
}
else
{
lean_dec(v_a_4471_);
v___y_4473_ = v___y_4439_;
v___y_4474_ = v___y_4440_;
v___y_4475_ = v___y_4441_;
v___y_4476_ = v___y_4442_;
v___y_4477_ = v___y_4443_;
v___y_4478_ = v___y_4444_;
goto v___jp_4472_;
}
v___jp_4472_:
{
lean_object* v___x_4479_; 
v___x_4479_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4432_, v_a_4433_, v_mod_x3f_4438_, v___x_4447_, v___x_4434_, v_only_4435_, v_incremental_4436_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4489_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4482_ = v___x_4479_;
v_isShared_4483_ = v_isSharedCheck_4489_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4479_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4489_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4487_; 
v___x_4484_ = lean_box(0);
v___x_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
lean_ctor_set(v___x_4485_, 1, v_a_4480_);
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 0, v___x_4485_);
v___x_4487_ = v___x_4482_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
v_a_4490_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4479_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4479_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v___x_4447_);
lean_dec(v_mod_x3f_4438_);
lean_dec(v_a_4433_);
lean_dec_ref(v_b_4432_);
v_a_4526_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___x_4470_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4470_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___boxed(lean_object* v___x_4534_, lean_object* v_b_4535_, lean_object* v_a_4536_, lean_object* v___x_4537_, lean_object* v_only_4538_, lean_object* v_incremental_4539_, lean_object* v_x_4540_, lean_object* v_mod_x3f_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
uint8_t v___x_23950__boxed_4549_; uint8_t v_only_boxed_4550_; uint8_t v_incremental_boxed_4551_; lean_object* v_res_4552_; 
v___x_23950__boxed_4549_ = lean_unbox(v___x_4537_);
v_only_boxed_4550_ = lean_unbox(v_only_4538_);
v_incremental_boxed_4551_ = lean_unbox(v_incremental_4539_);
v_res_4552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4534_, v_b_4535_, v_a_4536_, v___x_23950__boxed_4549_, v_only_boxed_4550_, v_incremental_boxed_4551_, v_x_4540_, v_mod_x3f_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___x_4534_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(lean_object* v_b_4553_, lean_object* v___x_4554_, lean_object* v_____r_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processAnchor(v_b_4553_, v___x_4554_, v___y_4560_, v___y_4561_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4573_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4566_ = v___x_4563_;
v_isShared_4567_ = v_isSharedCheck_4573_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4563_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4573_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4571_; 
v___x_4568_ = lean_box(0);
v___x_4569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
lean_ctor_set(v___x_4569_, 1, v_a_4564_);
if (v_isShared_4567_ == 0)
{
lean_ctor_set(v___x_4566_, 0, v___x_4569_);
v___x_4571_ = v___x_4566_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4569_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
else
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
v_a_4574_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4563_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4563_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0___boxed(lean_object* v_b_4582_, lean_object* v___x_4583_, lean_object* v_____r_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4582_, v___x_4583_, v_____r_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___x_4583_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(lean_object* v___x_4593_, lean_object* v_b_4594_, lean_object* v_a_4595_, uint8_t v___x_4596_, uint8_t v_only_4597_, uint8_t v_incremental_4598_, lean_object* v_x_4599_, lean_object* v_mod_x3f_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; 
v___x_4608_ = lean_unsigned_to_nat(2u);
v___x_4609_ = l_Lean_Syntax_getArg(v___x_4593_, v___x_4608_);
v___x_4610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4609_);
v___x_4611_ = l_Lean_Syntax_isOfKind(v___x_4609_, v___x_4610_);
if (v___x_4611_ == 0)
{
lean_object* v___x_4612_; 
v___x_4612_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4594_, v_a_4595_, v_mod_x3f_4600_, v___x_4609_, v___x_4596_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4622_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4615_ = v___x_4612_;
v_isShared_4616_ = v_isSharedCheck_4622_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4612_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4622_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
v___x_4617_ = lean_box(0);
v___x_4618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
lean_ctor_set(v___x_4618_, 1, v_a_4613_);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4618_);
v___x_4620_ = v___x_4615_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4618_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
v_a_4623_ = lean_ctor_get(v___x_4612_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4612_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4612_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4612_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
else
{
lean_object* v___x_4631_; lean_object* v___x_4632_; 
v___x_4631_ = l_Lean_TSyntax_getId(v___x_4609_);
v___x_4632_ = l_Lean_resolveLocalName___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__5(v___x_4631_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; lean_object* v___y_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
lean_inc(v_a_4633_);
lean_dec_ref(v___x_4632_);
if (lean_obj_tag(v_a_4633_) == 1)
{
lean_object* v_val_4660_; lean_object* v_snd_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4686_; 
v_val_4660_ = lean_ctor_get(v_a_4633_, 0);
lean_inc(v_val_4660_);
lean_dec_ref(v_a_4633_);
v_snd_4661_ = lean_ctor_get(v_val_4660_, 1);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_val_4660_);
if (v_isSharedCheck_4686_ == 0)
{
lean_object* v_unused_4687_; 
v_unused_4687_ = lean_ctor_get(v_val_4660_, 0);
lean_dec(v_unused_4687_);
v___x_4663_ = v_val_4660_;
v_isShared_4664_ = v_isSharedCheck_4686_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_snd_4661_);
lean_dec(v_val_4660_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4686_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
if (lean_obj_tag(v_snd_4661_) == 1)
{
lean_object* v___x_4665_; 
lean_dec_ref(v_snd_4661_);
v___x_4665_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam(v_b_4594_, v_a_4595_, v_mod_x3f_4600_, v___x_4609_, v___x_4596_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4677_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4668_ = v___x_4665_;
v_isShared_4669_ = v_isSharedCheck_4677_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4677_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4670_; lean_object* v___x_4672_; 
v___x_4670_ = lean_box(0);
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 1, v_a_4666_);
lean_ctor_set(v___x_4663_, 0, v___x_4670_);
v___x_4672_ = v___x_4663_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_a_4666_);
v___x_4672_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
lean_object* v___x_4674_; 
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 0, v___x_4672_);
v___x_4674_ = v___x_4668_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4672_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
lean_del_object(v___x_4663_);
v_a_4678_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4665_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4665_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
else
{
lean_del_object(v___x_4663_);
lean_dec(v_snd_4661_);
v___y_4635_ = v___y_4601_;
v___y_4636_ = v___y_4602_;
v___y_4637_ = v___y_4603_;
v___y_4638_ = v___y_4604_;
v___y_4639_ = v___y_4605_;
v___y_4640_ = v___y_4606_;
goto v___jp_4634_;
}
}
}
else
{
lean_dec(v_a_4633_);
v___y_4635_ = v___y_4601_;
v___y_4636_ = v___y_4602_;
v___y_4637_ = v___y_4603_;
v___y_4638_ = v___y_4604_;
v___y_4639_ = v___y_4605_;
v___y_4640_ = v___y_4606_;
goto v___jp_4634_;
}
v___jp_4634_:
{
lean_object* v___x_4641_; 
v___x_4641_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam(v_b_4594_, v_a_4595_, v_mod_x3f_4600_, v___x_4609_, v___x_4596_, v_only_4597_, v_incremental_4598_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
if (lean_obj_tag(v___x_4641_) == 0)
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4651_; 
v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4641_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4644_ = v___x_4641_;
v_isShared_4645_ = v_isSharedCheck_4651_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_dec(v___x_4641_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4651_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4649_; 
v___x_4646_ = lean_box(0);
v___x_4647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4646_);
lean_ctor_set(v___x_4647_, 1, v_a_4642_);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 0, v___x_4647_);
v___x_4649_ = v___x_4644_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4647_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
v_a_4652_ = lean_ctor_get(v___x_4641_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4641_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4641_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4641_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
}
else
{
lean_object* v_a_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4695_; 
lean_dec(v___x_4609_);
lean_dec(v_mod_x3f_4600_);
lean_dec(v_a_4595_);
lean_dec_ref(v_b_4594_);
v_a_4688_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4690_ = v___x_4632_;
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_a_4688_);
lean_dec(v___x_4632_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4695_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4693_; 
if (v_isShared_4691_ == 0)
{
v___x_4693_ = v___x_4690_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4688_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1___boxed(lean_object* v___x_4696_, lean_object* v_b_4697_, lean_object* v_a_4698_, lean_object* v___x_4699_, lean_object* v_only_4700_, lean_object* v_incremental_4701_, lean_object* v_x_4702_, lean_object* v_mod_x3f_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
uint8_t v___x_24229__boxed_4711_; uint8_t v_only_boxed_4712_; uint8_t v_incremental_boxed_4713_; lean_object* v_res_4714_; 
v___x_24229__boxed_4711_ = lean_unbox(v___x_4699_);
v_only_boxed_4712_ = lean_unbox(v_only_4700_);
v_incremental_boxed_4713_ = lean_unbox(v_incremental_4701_);
v_res_4714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4696_, v_b_4697_, v_a_4698_, v___x_24229__boxed_4711_, v_only_boxed_4712_, v_incremental_boxed_4713_, v_x_4702_, v_mod_x3f_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
lean_dec(v___x_4696_);
return v_res_4714_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__2));
v___x_4723_ = l_Lean_stringToMessageData(v___x_4722_);
return v___x_4723_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15(void){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__14));
v___x_4753_ = l_Lean_stringToMessageData(v___x_4752_);
return v___x_4753_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17(void){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__16));
v___x_4756_ = l_Lean_stringToMessageData(v___x_4755_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(uint8_t v_lax_4757_, uint8_t v_only_4758_, uint8_t v_incremental_4759_, lean_object* v_as_4760_, size_t v_sz_4761_, size_t v_i_4762_, lean_object* v_b_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v_snd_4772_; lean_object* v___y_4777_; uint8_t v___y_4778_; lean_object* v_a_4782_; lean_object* v___y_4786_; uint8_t v___x_4790_; 
v___x_4790_ = lean_usize_dec_lt(v_i_4762_, v_sz_4761_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; 
v___x_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4791_, 0, v_b_4763_);
return v___x_4791_;
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4793_; uint8_t v___x_4794_; 
v_a_4792_ = lean_array_uget_borrowed(v_as_4760_, v_i_4762_);
v___x_4793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__1));
lean_inc(v_a_4792_);
v___x_4794_ = l_Lean_Syntax_isOfKind(v_a_4792_, v___x_4793_);
if (v___x_4794_ == 0)
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4795_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4792_);
v___x_4796_ = l_Lean_MessageData_ofSyntax(v_a_4792_);
v___x_4797_ = l_Lean_indentD(v___x_4796_);
v___x_4798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4795_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
v___x_4799_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4798_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_dec_ref(v___x_4799_);
v_snd_4772_ = v_b_4763_;
goto v___jp_4771_;
}
else
{
lean_object* v_a_4800_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
lean_inc(v_a_4800_);
lean_dec_ref(v___x_4799_);
v_a_4782_ = v_a_4800_;
goto v___jp_4781_;
}
}
else
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; uint8_t v___x_4804_; 
v___x_4801_ = lean_unsigned_to_nat(0u);
v___x_4802_ = l_Lean_Syntax_getArg(v_a_4792_, v___x_4801_);
v___x_4803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__5));
lean_inc(v___x_4802_);
v___x_4804_ = l_Lean_Syntax_isOfKind(v___x_4802_, v___x_4803_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; uint8_t v___x_4806_; 
v___x_4805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__7));
lean_inc(v___x_4802_);
v___x_4806_ = l_Lean_Syntax_isOfKind(v___x_4802_, v___x_4805_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4807_; uint8_t v___x_4808_; 
v___x_4807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__9));
lean_inc(v___x_4802_);
v___x_4808_ = l_Lean_Syntax_isOfKind(v___x_4802_, v___x_4807_);
if (v___x_4808_ == 0)
{
lean_object* v___x_4809_; uint8_t v___x_4810_; 
v___x_4809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__11));
lean_inc(v___x_4802_);
v___x_4810_ = l_Lean_Syntax_isOfKind(v___x_4802_, v___x_4809_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
lean_dec(v___x_4802_);
v___x_4811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4792_);
v___x_4812_ = l_Lean_MessageData_ofSyntax(v_a_4792_);
v___x_4813_ = l_Lean_indentD(v___x_4812_);
v___x_4814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4811_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
v___x_4815_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4814_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_dec_ref(v___x_4815_);
v_snd_4772_ = v_b_4763_;
goto v___jp_4771_;
}
else
{
lean_object* v_a_4816_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
lean_inc(v_a_4816_);
lean_dec_ref(v___x_4815_);
v_a_4782_ = v_a_4816_;
goto v___jp_4781_;
}
}
else
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; uint8_t v___x_4820_; 
v___x_4817_ = lean_unsigned_to_nat(1u);
v___x_4818_ = l_Lean_Syntax_getArg(v___x_4802_, v___x_4817_);
lean_dec(v___x_4802_);
v___x_4819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__13));
lean_inc(v___x_4818_);
v___x_4820_ = l_Lean_Syntax_isOfKind(v___x_4818_, v___x_4819_);
if (v___x_4820_ == 0)
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
lean_dec(v___x_4818_);
v___x_4821_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4792_);
v___x_4822_ = l_Lean_MessageData_ofSyntax(v_a_4792_);
v___x_4823_ = l_Lean_indentD(v___x_4822_);
v___x_4824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4821_);
lean_ctor_set(v___x_4824_, 1, v___x_4823_);
v___x_4825_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4824_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_dec_ref(v___x_4825_);
v_snd_4772_ = v_b_4763_;
goto v___jp_4771_;
}
else
{
lean_object* v_a_4826_; 
v_a_4826_ = lean_ctor_get(v___x_4825_, 0);
lean_inc(v_a_4826_);
lean_dec_ref(v___x_4825_);
v_a_4782_ = v_a_4826_;
goto v___jp_4781_;
}
}
else
{
if (v_only_4758_ == 0)
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__15);
v___x_4828_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v___x_4818_, v___x_4827_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v___x_4830_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref(v___x_4828_);
lean_inc_ref(v_b_4763_);
v___x_4830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4763_, v___x_4818_, v_a_4829_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___x_4818_);
v___y_4786_ = v___x_4830_;
goto v___jp_4785_;
}
else
{
lean_object* v_a_4831_; 
lean_dec(v___x_4818_);
v_a_4831_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4831_);
lean_dec_ref(v___x_4828_);
v_a_4782_ = v_a_4831_;
goto v___jp_4781_;
}
}
else
{
lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4832_ = lean_box(0);
lean_inc_ref(v_b_4763_);
v___x_4833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__0(v_b_4763_, v___x_4818_, v___x_4832_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___x_4818_);
v___y_4786_ = v___x_4833_;
goto v___jp_4785_;
}
}
}
}
else
{
lean_object* v___x_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v___x_4834_ = lean_unsigned_to_nat(1u);
v___x_4835_ = l_Lean_Syntax_getArg(v___x_4802_, v___x_4834_);
v___x_4836_ = l_Lean_Syntax_isNone(v___x_4835_);
if (v___x_4836_ == 0)
{
uint8_t v___x_4837_; 
lean_inc(v___x_4835_);
v___x_4837_ = l_Lean_Syntax_matchesNull(v___x_4835_, v___x_4834_);
if (v___x_4837_ == 0)
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
lean_dec(v___x_4835_);
lean_dec(v___x_4802_);
v___x_4838_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4792_);
v___x_4839_ = l_Lean_MessageData_ofSyntax(v_a_4792_);
v___x_4840_ = l_Lean_indentD(v___x_4839_);
v___x_4841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4838_);
lean_ctor_set(v___x_4841_, 1, v___x_4840_);
v___x_4842_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4841_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_dec_ref(v___x_4842_);
v_snd_4772_ = v_b_4763_;
goto v___jp_4771_;
}
else
{
lean_object* v_a_4843_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
lean_inc(v_a_4843_);
lean_dec_ref(v___x_4842_);
v_a_4782_ = v_a_4843_;
goto v___jp_4781_;
}
}
else
{
lean_object* v___x_4844_; lean_object* v___x_4845_; uint8_t v___x_4846_; 
v___x_4844_ = l_Lean_Syntax_getArg(v___x_4835_, v___x_4801_);
lean_dec(v___x_4835_);
v___x_4845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4844_);
v___x_4846_ = l_Lean_Syntax_isOfKind(v___x_4844_, v___x_4845_);
if (v___x_4846_ == 0)
{
lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; 
lean_dec(v___x_4844_);
lean_dec(v___x_4802_);
v___x_4847_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4792_);
v___x_4848_ = l_Lean_MessageData_ofSyntax(v_a_4792_);
v___x_4849_ = l_Lean_indentD(v___x_4848_);
v___x_4850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4847_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
v___x_4851_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4850_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_dec_ref(v___x_4851_);
v_snd_4772_ = v_b_4763_;
goto v___jp_4771_;
}
else
{
lean_object* v_a_4852_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref(v___x_4851_);
v_a_4782_ = v_a_4852_;
goto v___jp_4781_;
}
}
else
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4853_ = lean_box(0);
v___x_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4844_);
lean_inc(v_a_4792_);
lean_inc_ref(v_b_4763_);
v___x_4855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4802_, v_b_4763_, v_a_4792_, v___x_4790_, v_only_4758_, v_incremental_4759_, v___x_4853_, v___x_4854_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___x_4802_);
v___y_4786_ = v___x_4855_;
goto v___jp_4785_;
}
}
}
else
{
lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
lean_dec(v___x_4835_);
v___x_4856_ = lean_box(0);
v___x_4857_ = lean_box(0);
lean_inc(v_a_4792_);
lean_inc_ref(v_b_4763_);
v___x_4858_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__1(v___x_4802_, v_b_4763_, v_a_4792_, v___x_4790_, v_only_4758_, v_incremental_4759_, v___x_4856_, v___x_4857_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___x_4802_);
v___y_4786_ = v___x_4858_;
goto v___jp_4785_;
}
}
}
else
{
lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4859_ = l_Lean_Syntax_getArg(v___x_4802_, v___x_4801_);
v___x_4860_ = l_Lean_Syntax_isNone(v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; uint8_t v___x_4862_; 
v___x_4861_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4859_);
v___x_4862_ = l_Lean_Syntax_matchesNull(v___x_4859_, v___x_4861_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
lean_dec(v___x_4859_);
lean_dec(v___x_4802_);
v___x_4863_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4792_);
v___x_4864_ = l_Lean_MessageData_ofSyntax(v_a_4792_);
v___x_4865_ = l_Lean_indentD(v___x_4864_);
v___x_4866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4863_);
lean_ctor_set(v___x_4866_, 1, v___x_4865_);
v___x_4867_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4866_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_dec_ref(v___x_4867_);
v_snd_4772_ = v_b_4763_;
goto v___jp_4771_;
}
else
{
lean_object* v_a_4868_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
lean_inc(v_a_4868_);
lean_dec_ref(v___x_4867_);
v_a_4782_ = v_a_4868_;
goto v___jp_4781_;
}
}
else
{
lean_object* v___x_4869_; lean_object* v___x_4870_; uint8_t v___x_4871_; 
v___x_4869_ = l_Lean_Syntax_getArg(v___x_4859_, v___x_4801_);
lean_dec(v___x_4859_);
v___x_4870_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_parseModifier___closed__4));
lean_inc(v___x_4869_);
v___x_4871_ = l_Lean_Syntax_isOfKind(v___x_4869_, v___x_4870_);
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; 
lean_dec(v___x_4869_);
lean_dec(v___x_4802_);
v___x_4872_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4792_);
v___x_4873_ = l_Lean_MessageData_ofSyntax(v_a_4792_);
v___x_4874_ = l_Lean_indentD(v___x_4873_);
v___x_4875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4875_, 0, v___x_4872_);
lean_ctor_set(v___x_4875_, 1, v___x_4874_);
v___x_4876_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4875_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_dec_ref(v___x_4876_);
v_snd_4772_ = v_b_4763_;
goto v___jp_4771_;
}
else
{
lean_object* v_a_4877_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_a_4877_);
lean_dec_ref(v___x_4876_);
v_a_4782_ = v_a_4877_;
goto v___jp_4781_;
}
}
else
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4878_ = lean_box(0);
v___x_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4869_);
lean_inc(v_a_4792_);
lean_inc_ref(v_b_4763_);
v___x_4880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4802_, v_b_4763_, v_a_4792_, v___x_4804_, v_only_4758_, v_incremental_4759_, v___x_4878_, v___x_4879_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___x_4802_);
v___y_4786_ = v___x_4880_;
goto v___jp_4785_;
}
}
}
else
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
lean_dec(v___x_4859_);
v___x_4881_ = lean_box(0);
v___x_4882_ = lean_box(0);
lean_inc(v_a_4792_);
lean_inc_ref(v_b_4763_);
v___x_4883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2(v___x_4802_, v_b_4763_, v_a_4792_, v___x_4804_, v_only_4758_, v_incremental_4759_, v___x_4881_, v___x_4882_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___x_4802_);
v___y_4786_ = v___x_4883_;
goto v___jp_4785_;
}
}
}
else
{
lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; uint8_t v___x_4887_; 
v___x_4884_ = lean_unsigned_to_nat(1u);
v___x_4885_ = l_Lean_Syntax_getArg(v___x_4802_, v___x_4884_);
lean_dec(v___x_4802_);
v___x_4886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__2___closed__1));
lean_inc(v___x_4885_);
v___x_4887_ = l_Lean_Syntax_isOfKind(v___x_4885_, v___x_4886_);
if (v___x_4887_ == 0)
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; 
lean_dec(v___x_4885_);
v___x_4888_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__3);
lean_inc(v_a_4792_);
v___x_4889_ = l_Lean_MessageData_ofSyntax(v_a_4792_);
v___x_4890_ = l_Lean_indentD(v___x_4889_);
v___x_4891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4888_);
lean_ctor_set(v___x_4891_, 1, v___x_4890_);
v___x_4892_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processTermParam_spec__1___redArg(v___x_4891_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_dec_ref(v___x_4892_);
v_snd_4772_ = v_b_4763_;
goto v___jp_4771_;
}
else
{
lean_object* v_a_4893_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4893_);
lean_dec_ref(v___x_4892_);
v_a_4782_ = v_a_4893_;
goto v___jp_4781_;
}
}
else
{
if (v_incremental_4759_ == 0)
{
lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4894_ = lean_box(0);
lean_inc_ref(v_b_4763_);
v___x_4895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4885_, v_b_4763_, v___x_4894_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
v___y_4786_ = v___x_4895_;
goto v___jp_4785_;
}
else
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4896_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___closed__17);
v___x_4897_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_processParam_spec__3___redArg(v_a_4792_, v___x_4896_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; lean_object* v___x_4899_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4898_);
lean_dec_ref(v___x_4897_);
lean_inc_ref(v_b_4763_);
v___x_4899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___lam__3(v___x_4885_, v_b_4763_, v_a_4898_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
v___y_4786_ = v___x_4899_;
goto v___jp_4785_;
}
else
{
lean_object* v_a_4900_; 
lean_dec(v___x_4885_);
v_a_4900_ = lean_ctor_get(v___x_4897_, 0);
lean_inc(v_a_4900_);
lean_dec_ref(v___x_4897_);
v_a_4782_ = v_a_4900_;
goto v___jp_4781_;
}
}
}
}
}
}
v___jp_4771_:
{
size_t v___x_4773_; size_t v___x_4774_; 
v___x_4773_ = ((size_t)1ULL);
v___x_4774_ = lean_usize_add(v_i_4762_, v___x_4773_);
v_i_4762_ = v___x_4774_;
v_b_4763_ = v_snd_4772_;
goto _start;
}
v___jp_4776_:
{
if (v___y_4778_ == 0)
{
if (v_lax_4757_ == 0)
{
lean_object* v___x_4779_; 
lean_dec_ref(v_b_4763_);
v___x_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4779_, 0, v___y_4777_);
return v___x_4779_;
}
else
{
lean_dec_ref(v___y_4777_);
v_snd_4772_ = v_b_4763_;
goto v___jp_4771_;
}
}
else
{
lean_object* v___x_4780_; 
lean_dec_ref(v_b_4763_);
v___x_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___y_4777_);
return v___x_4780_;
}
}
v___jp_4781_:
{
uint8_t v___x_4783_; 
v___x_4783_ = l_Lean_Exception_isInterrupt(v_a_4782_);
if (v___x_4783_ == 0)
{
uint8_t v___x_4784_; 
lean_inc_ref(v_a_4782_);
v___x_4784_ = l_Lean_Exception_isRuntime(v_a_4782_);
v___y_4777_ = v_a_4782_;
v___y_4778_ = v___x_4784_;
goto v___jp_4776_;
}
else
{
v___y_4777_ = v_a_4782_;
v___y_4778_ = v___x_4783_;
goto v___jp_4776_;
}
}
v___jp_4785_:
{
if (lean_obj_tag(v___y_4786_) == 0)
{
lean_object* v_a_4787_; lean_object* v_snd_4788_; 
lean_dec_ref(v_b_4763_);
v_a_4787_ = lean_ctor_get(v___y_4786_, 0);
lean_inc(v_a_4787_);
lean_dec_ref(v___y_4786_);
v_snd_4788_ = lean_ctor_get(v_a_4787_, 1);
lean_inc(v_snd_4788_);
lean_dec(v_a_4787_);
v_snd_4772_ = v_snd_4788_;
goto v___jp_4771_;
}
else
{
lean_object* v_a_4789_; 
v_a_4789_ = lean_ctor_get(v___y_4786_, 0);
lean_inc(v_a_4789_);
lean_dec_ref(v___y_4786_);
v_a_4782_ = v_a_4789_;
goto v___jp_4781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0___boxed(lean_object* v_lax_4901_, lean_object* v_only_4902_, lean_object* v_incremental_4903_, lean_object* v_as_4904_, lean_object* v_sz_4905_, lean_object* v_i_4906_, lean_object* v_b_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
uint8_t v_lax_boxed_4915_; uint8_t v_only_boxed_4916_; uint8_t v_incremental_boxed_4917_; size_t v_sz_boxed_4918_; size_t v_i_boxed_4919_; lean_object* v_res_4920_; 
v_lax_boxed_4915_ = lean_unbox(v_lax_4901_);
v_only_boxed_4916_ = lean_unbox(v_only_4902_);
v_incremental_boxed_4917_ = lean_unbox(v_incremental_4903_);
v_sz_boxed_4918_ = lean_unbox_usize(v_sz_4905_);
lean_dec(v_sz_4905_);
v_i_boxed_4919_ = lean_unbox_usize(v_i_4906_);
lean_dec(v_i_4906_);
v_res_4920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_boxed_4915_, v_only_boxed_4916_, v_incremental_boxed_4917_, v_as_4904_, v_sz_boxed_4918_, v_i_boxed_4919_, v_b_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec_ref(v_as_4904_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* v_params_4921_, lean_object* v_ps_4922_, uint8_t v_only_4923_, uint8_t v_lax_4924_, uint8_t v_incremental_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_){
_start:
{
size_t v_sz_4933_; size_t v___x_4934_; lean_object* v___x_4935_; 
v_sz_4933_ = lean_array_size(v_ps_4922_);
v___x_4934_ = ((size_t)0ULL);
v___x_4935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_elabGrindParams_spec__0(v_lax_4924_, v_only_4923_, v_incremental_4925_, v_ps_4922_, v_sz_4933_, v___x_4934_, v_params_4921_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* v_params_4936_, lean_object* v_ps_4937_, lean_object* v_only_4938_, lean_object* v_lax_4939_, lean_object* v_incremental_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_){
_start:
{
uint8_t v_only_boxed_4948_; uint8_t v_lax_boxed_4949_; uint8_t v_incremental_boxed_4950_; lean_object* v_res_4951_; 
v_only_boxed_4948_ = lean_unbox(v_only_4938_);
v_lax_boxed_4949_ = lean_unbox(v_lax_4939_);
v_incremental_boxed_4950_ = lean_unbox(v_incremental_4940_);
v_res_4951_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_4936_, v_ps_4937_, v_only_boxed_4948_, v_lax_boxed_4949_, v_incremental_boxed_4950_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
lean_dec(v_a_4946_);
lean_dec_ref(v_a_4945_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
lean_dec(v_a_4942_);
lean_dec_ref(v_a_4941_);
lean_dec_ref(v_ps_4937_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(lean_object* v_thm_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_){
_start:
{
lean_object* v_origin_4963_; 
v_origin_4963_ = lean_ctor_get(v_thm_4952_, 5);
if (lean_obj_tag(v_origin_4963_) == 0)
{
lean_object* v_declName_4964_; lean_object* v___x_4965_; 
lean_inc_ref(v_origin_4963_);
lean_dec_ref(v_thm_4952_);
v_declName_4964_ = lean_ctor_get(v_origin_4963_, 0);
lean_inc(v_declName_4964_);
lean_dec_ref(v_origin_4963_);
v___x_4965_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(v_declName_4964_, v_a_4960_, v_a_4961_);
return v___x_4965_;
}
else
{
lean_object* v_proof_4966_; lean_object* v___x_4967_; 
v_proof_4966_ = lean_ctor_get(v_thm_4952_, 1);
lean_inc_ref(v_proof_4966_);
lean_dec_ref(v_thm_4952_);
v___x_4967_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(v_proof_4966_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_);
return v___x_4967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep___boxed(lean_object* v_thm_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_thm_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec(v_a_4975_);
lean_dec_ref(v_a_4974_);
lean_dec(v_a_4973_);
lean_dec_ref(v_a_4972_);
lean_dec(v_a_4971_);
lean_dec_ref(v_a_4970_);
lean_dec(v_a_4969_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(lean_object* v_as_4980_, size_t v_sz_4981_, size_t v_i_4982_, lean_object* v_b_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
uint8_t v___x_4994_; 
v___x_4994_ = lean_usize_dec_lt(v_i_4982_, v_sz_4981_);
if (v___x_4994_ == 0)
{
lean_object* v___x_4995_; 
v___x_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4995_, 0, v_b_4983_);
return v___x_4995_;
}
else
{
lean_object* v_snd_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5022_; 
v_snd_4996_ = lean_ctor_get(v_b_4983_, 1);
v_isSharedCheck_5022_ = !lean_is_exclusive(v_b_4983_);
if (v_isSharedCheck_5022_ == 0)
{
lean_object* v_unused_5023_; 
v_unused_5023_ = lean_ctor_get(v_b_4983_, 0);
lean_dec(v_unused_5023_);
v___x_4998_ = v_b_4983_;
v_isShared_4999_ = v_isSharedCheck_5022_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_snd_4996_);
lean_dec(v_b_4983_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5022_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v_a_5000_; lean_object* v___x_5001_; 
v_a_5000_ = lean_array_uget_borrowed(v_as_4980_, v_i_4982_);
lean_inc(v_a_5000_);
v___x_5001_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5000_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5003_; lean_object* v_a_5005_; uint8_t v___x_5012_; 
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
lean_inc(v_a_5002_);
lean_dec_ref(v___x_5001_);
v___x_5003_ = lean_box(0);
v___x_5012_ = lean_unbox(v_a_5002_);
lean_dec(v_a_5002_);
if (v___x_5012_ == 0)
{
v_a_5005_ = v_snd_4996_;
goto v___jp_5004_;
}
else
{
lean_object* v___x_5013_; 
lean_inc(v_a_5000_);
v___x_5013_ = l_Lean_PersistentArray_push___redArg(v_snd_4996_, v_a_5000_);
v_a_5005_ = v___x_5013_;
goto v___jp_5004_;
}
v___jp_5004_:
{
lean_object* v___x_5007_; 
if (v_isShared_4999_ == 0)
{
lean_ctor_set(v___x_4998_, 1, v_a_5005_);
lean_ctor_set(v___x_4998_, 0, v___x_5003_);
v___x_5007_ = v___x_4998_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v___x_5003_);
lean_ctor_set(v_reuseFailAlloc_5011_, 1, v_a_5005_);
v___x_5007_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
size_t v___x_5008_; size_t v___x_5009_; 
v___x_5008_ = ((size_t)1ULL);
v___x_5009_ = lean_usize_add(v_i_4982_, v___x_5008_);
v_i_4982_ = v___x_5009_;
v_b_4983_ = v___x_5007_;
goto _start;
}
}
}
else
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
lean_del_object(v___x_4998_);
lean_dec(v_snd_4996_);
v_a_5014_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_5001_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_5001_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4___boxed(lean_object* v_as_5024_, lean_object* v_sz_5025_, lean_object* v_i_5026_, lean_object* v_b_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_){
_start:
{
size_t v_sz_boxed_5038_; size_t v_i_boxed_5039_; lean_object* v_res_5040_; 
v_sz_boxed_5038_ = lean_unbox_usize(v_sz_5025_);
lean_dec(v_sz_5025_);
v_i_boxed_5039_ = lean_unbox_usize(v_i_5026_);
lean_dec(v_i_5026_);
v_res_5040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5024_, v_sz_boxed_5038_, v_i_boxed_5039_, v_b_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_);
lean_dec(v___y_5036_);
lean_dec_ref(v___y_5035_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
lean_dec_ref(v_as_5024_);
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(lean_object* v_as_5041_, size_t v_sz_5042_, size_t v_i_5043_, lean_object* v_b_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
uint8_t v___x_5055_; 
v___x_5055_ = lean_usize_dec_lt(v_i_5043_, v_sz_5042_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5056_; 
v___x_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5056_, 0, v_b_5044_);
return v___x_5056_;
}
else
{
lean_object* v_snd_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5083_; 
v_snd_5057_ = lean_ctor_get(v_b_5044_, 1);
v_isSharedCheck_5083_ = !lean_is_exclusive(v_b_5044_);
if (v_isSharedCheck_5083_ == 0)
{
lean_object* v_unused_5084_; 
v_unused_5084_ = lean_ctor_get(v_b_5044_, 0);
lean_dec(v_unused_5084_);
v___x_5059_ = v_b_5044_;
v_isShared_5060_ = v_isSharedCheck_5083_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_snd_5057_);
lean_dec(v_b_5044_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5083_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
lean_object* v_a_5061_; lean_object* v___x_5062_; 
v_a_5061_ = lean_array_uget_borrowed(v_as_5041_, v_i_5043_);
lean_inc(v_a_5061_);
v___x_5062_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5061_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5064_; lean_object* v_a_5066_; uint8_t v___x_5073_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
lean_dec_ref(v___x_5062_);
v___x_5064_ = lean_box(0);
v___x_5073_ = lean_unbox(v_a_5063_);
lean_dec(v_a_5063_);
if (v___x_5073_ == 0)
{
v_a_5066_ = v_snd_5057_;
goto v___jp_5065_;
}
else
{
lean_object* v___x_5074_; 
lean_inc(v_a_5061_);
v___x_5074_ = l_Lean_PersistentArray_push___redArg(v_snd_5057_, v_a_5061_);
v_a_5066_ = v___x_5074_;
goto v___jp_5065_;
}
v___jp_5065_:
{
lean_object* v___x_5068_; 
if (v_isShared_5060_ == 0)
{
lean_ctor_set(v___x_5059_, 1, v_a_5066_);
lean_ctor_set(v___x_5059_, 0, v___x_5064_);
v___x_5068_ = v___x_5059_;
goto v_reusejp_5067_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5064_);
lean_ctor_set(v_reuseFailAlloc_5072_, 1, v_a_5066_);
v___x_5068_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5067_;
}
v_reusejp_5067_:
{
size_t v___x_5069_; size_t v___x_5070_; lean_object* v___x_5071_; 
v___x_5069_ = ((size_t)1ULL);
v___x_5070_ = lean_usize_add(v_i_5043_, v___x_5069_);
v___x_5071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1_spec__4(v_as_5041_, v_sz_5042_, v___x_5070_, v___x_5068_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_);
return v___x_5071_;
}
}
}
else
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5082_; 
lean_del_object(v___x_5059_);
lean_dec(v_snd_5057_);
v_a_5075_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5077_ = v___x_5062_;
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_5062_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1___boxed(lean_object* v_as_5085_, lean_object* v_sz_5086_, lean_object* v_i_5087_, lean_object* v_b_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
size_t v_sz_boxed_5099_; size_t v_i_boxed_5100_; lean_object* v_res_5101_; 
v_sz_boxed_5099_ = lean_unbox_usize(v_sz_5086_);
lean_dec(v_sz_5086_);
v_i_boxed_5100_ = lean_unbox_usize(v_i_5087_);
lean_dec(v_i_5087_);
v_res_5101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_as_5085_, v_sz_boxed_5099_, v_i_boxed_5100_, v_b_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
lean_dec(v___y_5089_);
lean_dec_ref(v_as_5085_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_5102_, size_t v_sz_5103_, size_t v_i_5104_, lean_object* v_b_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
uint8_t v___x_5116_; 
v___x_5116_ = lean_usize_dec_lt(v_i_5104_, v_sz_5103_);
if (v___x_5116_ == 0)
{
lean_object* v___x_5117_; 
v___x_5117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5117_, 0, v_b_5105_);
return v___x_5117_;
}
else
{
lean_object* v_snd_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5144_; 
v_snd_5118_ = lean_ctor_get(v_b_5105_, 1);
v_isSharedCheck_5144_ = !lean_is_exclusive(v_b_5105_);
if (v_isSharedCheck_5144_ == 0)
{
lean_object* v_unused_5145_; 
v_unused_5145_ = lean_ctor_get(v_b_5105_, 0);
lean_dec(v_unused_5145_);
v___x_5120_ = v_b_5105_;
v_isShared_5121_ = v_isSharedCheck_5144_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_snd_5118_);
lean_dec(v_b_5105_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5144_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v_a_5122_; lean_object* v___x_5123_; 
v_a_5122_ = lean_array_uget_borrowed(v_as_5102_, v_i_5104_);
lean_inc(v_a_5122_);
v___x_5123_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5122_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
if (lean_obj_tag(v___x_5123_) == 0)
{
lean_object* v_a_5124_; lean_object* v___x_5125_; lean_object* v_a_5127_; uint8_t v___x_5134_; 
v_a_5124_ = lean_ctor_get(v___x_5123_, 0);
lean_inc(v_a_5124_);
lean_dec_ref(v___x_5123_);
v___x_5125_ = lean_box(0);
v___x_5134_ = lean_unbox(v_a_5124_);
lean_dec(v_a_5124_);
if (v___x_5134_ == 0)
{
v_a_5127_ = v_snd_5118_;
goto v___jp_5126_;
}
else
{
lean_object* v___x_5135_; 
lean_inc(v_a_5122_);
v___x_5135_ = l_Lean_PersistentArray_push___redArg(v_snd_5118_, v_a_5122_);
v_a_5127_ = v___x_5135_;
goto v___jp_5126_;
}
v___jp_5126_:
{
lean_object* v___x_5129_; 
if (v_isShared_5121_ == 0)
{
lean_ctor_set(v___x_5120_, 1, v_a_5127_);
lean_ctor_set(v___x_5120_, 0, v___x_5125_);
v___x_5129_ = v___x_5120_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v___x_5125_);
lean_ctor_set(v_reuseFailAlloc_5133_, 1, v_a_5127_);
v___x_5129_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
size_t v___x_5130_; size_t v___x_5131_; 
v___x_5130_ = ((size_t)1ULL);
v___x_5131_ = lean_usize_add(v_i_5104_, v___x_5130_);
v_i_5104_ = v___x_5131_;
v_b_5105_ = v___x_5129_;
goto _start;
}
}
}
else
{
lean_object* v_a_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
lean_del_object(v___x_5120_);
lean_dec(v_snd_5118_);
v_a_5136_ = lean_ctor_get(v___x_5123_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5123_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5138_ = v___x_5123_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_a_5136_);
lean_dec(v___x_5123_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5136_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_5146_, lean_object* v_sz_5147_, lean_object* v_i_5148_, lean_object* v_b_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_){
_start:
{
size_t v_sz_boxed_5160_; size_t v_i_boxed_5161_; lean_object* v_res_5162_; 
v_sz_boxed_5160_ = lean_unbox_usize(v_sz_5147_);
lean_dec(v_sz_5147_);
v_i_boxed_5161_ = lean_unbox_usize(v_i_5148_);
lean_dec(v_i_5148_);
v_res_5162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5146_, v_sz_boxed_5160_, v_i_boxed_5161_, v_b_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_);
lean_dec(v___y_5158_);
lean_dec_ref(v___y_5157_);
lean_dec(v___y_5156_);
lean_dec_ref(v___y_5155_);
lean_dec(v___y_5154_);
lean_dec_ref(v___y_5153_);
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5151_);
lean_dec(v___y_5150_);
lean_dec_ref(v_as_5146_);
return v_res_5162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(lean_object* v_as_5163_, size_t v_sz_5164_, size_t v_i_5165_, lean_object* v_b_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_){
_start:
{
uint8_t v___x_5177_; 
v___x_5177_ = lean_usize_dec_lt(v_i_5165_, v_sz_5164_);
if (v___x_5177_ == 0)
{
lean_object* v___x_5178_; 
v___x_5178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5178_, 0, v_b_5166_);
return v___x_5178_;
}
else
{
lean_object* v_snd_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5205_; 
v_snd_5179_ = lean_ctor_get(v_b_5166_, 1);
v_isSharedCheck_5205_ = !lean_is_exclusive(v_b_5166_);
if (v_isSharedCheck_5205_ == 0)
{
lean_object* v_unused_5206_; 
v_unused_5206_ = lean_ctor_get(v_b_5166_, 0);
lean_dec(v_unused_5206_);
v___x_5181_ = v_b_5166_;
v_isShared_5182_ = v_isSharedCheck_5205_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_snd_5179_);
lean_dec(v_b_5166_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5205_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v_a_5183_; lean_object* v___x_5184_; 
v_a_5183_ = lean_array_uget_borrowed(v_as_5163_, v_i_5165_);
lean_inc(v_a_5183_);
v___x_5184_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_shouldKeep(v_a_5183_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
if (lean_obj_tag(v___x_5184_) == 0)
{
lean_object* v_a_5185_; lean_object* v___x_5186_; lean_object* v_a_5188_; uint8_t v___x_5195_; 
v_a_5185_ = lean_ctor_get(v___x_5184_, 0);
lean_inc(v_a_5185_);
lean_dec_ref(v___x_5184_);
v___x_5186_ = lean_box(0);
v___x_5195_ = lean_unbox(v_a_5185_);
lean_dec(v_a_5185_);
if (v___x_5195_ == 0)
{
v_a_5188_ = v_snd_5179_;
goto v___jp_5187_;
}
else
{
lean_object* v___x_5196_; 
lean_inc(v_a_5183_);
v___x_5196_ = l_Lean_PersistentArray_push___redArg(v_snd_5179_, v_a_5183_);
v_a_5188_ = v___x_5196_;
goto v___jp_5187_;
}
v___jp_5187_:
{
lean_object* v___x_5190_; 
if (v_isShared_5182_ == 0)
{
lean_ctor_set(v___x_5181_, 1, v_a_5188_);
lean_ctor_set(v___x_5181_, 0, v___x_5186_);
v___x_5190_ = v___x_5181_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v___x_5186_);
lean_ctor_set(v_reuseFailAlloc_5194_, 1, v_a_5188_);
v___x_5190_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
size_t v___x_5191_; size_t v___x_5192_; lean_object* v___x_5193_; 
v___x_5191_ = ((size_t)1ULL);
v___x_5192_ = lean_usize_add(v_i_5165_, v___x_5191_);
v___x_5193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2_spec__3(v_as_5163_, v_sz_5164_, v___x_5192_, v___x_5190_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
return v___x_5193_;
}
}
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
lean_del_object(v___x_5181_);
lean_dec(v_snd_5179_);
v_a_5197_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5184_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5184_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2___boxed(lean_object* v_as_5207_, lean_object* v_sz_5208_, lean_object* v_i_5209_, lean_object* v_b_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_){
_start:
{
size_t v_sz_boxed_5221_; size_t v_i_boxed_5222_; lean_object* v_res_5223_; 
v_sz_boxed_5221_ = lean_unbox_usize(v_sz_5208_);
lean_dec(v_sz_5208_);
v_i_boxed_5222_ = lean_unbox_usize(v_i_5209_);
lean_dec(v_i_5209_);
v_res_5223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_as_5207_, v_sz_boxed_5221_, v_i_boxed_5222_, v_b_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_);
lean_dec(v___y_5219_);
lean_dec_ref(v___y_5218_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
lean_dec(v___y_5211_);
lean_dec_ref(v_as_5207_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(lean_object* v_init_5224_, lean_object* v_n_5225_, lean_object* v_b_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
if (lean_obj_tag(v_n_5225_) == 0)
{
lean_object* v_cs_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; size_t v_sz_5240_; size_t v___x_5241_; lean_object* v___x_5242_; 
v_cs_5237_ = lean_ctor_get(v_n_5225_, 0);
v___x_5238_ = lean_box(0);
v___x_5239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5238_);
lean_ctor_set(v___x_5239_, 1, v_b_5226_);
v_sz_5240_ = lean_array_size(v_cs_5237_);
v___x_5241_ = ((size_t)0ULL);
v___x_5242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5224_, v_cs_5237_, v_sz_5240_, v___x_5241_, v___x_5239_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5257_; 
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5245_ = v___x_5242_;
v_isShared_5246_ = v_isSharedCheck_5257_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5242_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5257_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v_fst_5247_; 
v_fst_5247_ = lean_ctor_get(v_a_5243_, 0);
if (lean_obj_tag(v_fst_5247_) == 0)
{
lean_object* v_snd_5248_; lean_object* v___x_5249_; lean_object* v___x_5251_; 
v_snd_5248_ = lean_ctor_get(v_a_5243_, 1);
lean_inc(v_snd_5248_);
lean_dec(v_a_5243_);
v___x_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5249_, 0, v_snd_5248_);
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 0, v___x_5249_);
v___x_5251_ = v___x_5245_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
else
{
lean_object* v_val_5253_; lean_object* v___x_5255_; 
lean_inc_ref(v_fst_5247_);
lean_dec(v_a_5243_);
v_val_5253_ = lean_ctor_get(v_fst_5247_, 0);
lean_inc(v_val_5253_);
lean_dec_ref(v_fst_5247_);
if (v_isShared_5246_ == 0)
{
lean_ctor_set(v___x_5245_, 0, v_val_5253_);
v___x_5255_ = v___x_5245_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_val_5253_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
else
{
lean_object* v_a_5258_; lean_object* v___x_5260_; uint8_t v_isShared_5261_; uint8_t v_isSharedCheck_5265_; 
v_a_5258_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5265_ == 0)
{
v___x_5260_ = v___x_5242_;
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
else
{
lean_inc(v_a_5258_);
lean_dec(v___x_5242_);
v___x_5260_ = lean_box(0);
v_isShared_5261_ = v_isSharedCheck_5265_;
goto v_resetjp_5259_;
}
v_resetjp_5259_:
{
lean_object* v___x_5263_; 
if (v_isShared_5261_ == 0)
{
v___x_5263_ = v___x_5260_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_a_5258_);
v___x_5263_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
return v___x_5263_;
}
}
}
}
else
{
lean_object* v_vs_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; size_t v_sz_5269_; size_t v___x_5270_; lean_object* v___x_5271_; 
v_vs_5266_ = lean_ctor_get(v_n_5225_, 0);
v___x_5267_ = lean_box(0);
v___x_5268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5268_, 0, v___x_5267_);
lean_ctor_set(v___x_5268_, 1, v_b_5226_);
v_sz_5269_ = lean_array_size(v_vs_5266_);
v___x_5270_ = ((size_t)0ULL);
v___x_5271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__2(v_vs_5266_, v_sz_5269_, v___x_5270_, v___x_5268_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
if (lean_obj_tag(v___x_5271_) == 0)
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5286_; 
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5286_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5286_ == 0)
{
v___x_5274_ = v___x_5271_;
v_isShared_5275_ = v_isSharedCheck_5286_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5271_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5286_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v_fst_5276_; 
v_fst_5276_ = lean_ctor_get(v_a_5272_, 0);
if (lean_obj_tag(v_fst_5276_) == 0)
{
lean_object* v_snd_5277_; lean_object* v___x_5278_; lean_object* v___x_5280_; 
v_snd_5277_ = lean_ctor_get(v_a_5272_, 1);
lean_inc(v_snd_5277_);
lean_dec(v_a_5272_);
v___x_5278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5278_, 0, v_snd_5277_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 0, v___x_5278_);
v___x_5280_ = v___x_5274_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v___x_5278_);
v___x_5280_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
return v___x_5280_;
}
}
else
{
lean_object* v_val_5282_; lean_object* v___x_5284_; 
lean_inc_ref(v_fst_5276_);
lean_dec(v_a_5272_);
v_val_5282_ = lean_ctor_get(v_fst_5276_, 0);
lean_inc(v_val_5282_);
lean_dec_ref(v_fst_5276_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 0, v_val_5282_);
v___x_5284_ = v___x_5274_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_val_5282_);
v___x_5284_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
return v___x_5284_;
}
}
}
}
else
{
lean_object* v_a_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5294_; 
v_a_5287_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5289_ = v___x_5271_;
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_a_5287_);
lean_dec(v___x_5271_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
lean_object* v___x_5292_; 
if (v_isShared_5290_ == 0)
{
v___x_5292_ = v___x_5289_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_a_5287_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(lean_object* v_init_5295_, lean_object* v_as_5296_, size_t v_sz_5297_, size_t v_i_5298_, lean_object* v_b_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_){
_start:
{
uint8_t v___x_5310_; 
v___x_5310_ = lean_usize_dec_lt(v_i_5298_, v_sz_5297_);
if (v___x_5310_ == 0)
{
lean_object* v___x_5311_; 
v___x_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5311_, 0, v_b_5299_);
return v___x_5311_;
}
else
{
lean_object* v_snd_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5346_; 
v_snd_5312_ = lean_ctor_get(v_b_5299_, 1);
v_isSharedCheck_5346_ = !lean_is_exclusive(v_b_5299_);
if (v_isSharedCheck_5346_ == 0)
{
lean_object* v_unused_5347_; 
v_unused_5347_ = lean_ctor_get(v_b_5299_, 0);
lean_dec(v_unused_5347_);
v___x_5314_ = v_b_5299_;
v_isShared_5315_ = v_isSharedCheck_5346_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_snd_5312_);
lean_dec(v_b_5299_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5346_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v_a_5316_; lean_object* v___x_5317_; 
v_a_5316_ = lean_array_uget_borrowed(v_as_5296_, v_i_5298_);
lean_inc(v_snd_5312_);
v___x_5317_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5295_, v_a_5316_, v_snd_5312_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_);
if (lean_obj_tag(v___x_5317_) == 0)
{
lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5337_; 
v_a_5318_ = lean_ctor_get(v___x_5317_, 0);
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5337_ == 0)
{
v___x_5320_ = v___x_5317_;
v_isShared_5321_ = v_isSharedCheck_5337_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v___x_5317_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5337_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
if (lean_obj_tag(v_a_5318_) == 0)
{
lean_object* v___x_5322_; lean_object* v___x_5324_; 
v___x_5322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5322_, 0, v_a_5318_);
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 0, v___x_5322_);
v___x_5324_ = v___x_5314_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v___x_5322_);
lean_ctor_set(v_reuseFailAlloc_5328_, 1, v_snd_5312_);
v___x_5324_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
lean_object* v___x_5326_; 
if (v_isShared_5321_ == 0)
{
lean_ctor_set(v___x_5320_, 0, v___x_5324_);
v___x_5326_ = v___x_5320_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5324_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
else
{
lean_object* v_a_5329_; lean_object* v___x_5330_; lean_object* v___x_5332_; 
lean_del_object(v___x_5320_);
lean_dec(v_snd_5312_);
v_a_5329_ = lean_ctor_get(v_a_5318_, 0);
lean_inc(v_a_5329_);
lean_dec_ref(v_a_5318_);
v___x_5330_ = lean_box(0);
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 1, v_a_5329_);
lean_ctor_set(v___x_5314_, 0, v___x_5330_);
v___x_5332_ = v___x_5314_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v___x_5330_);
lean_ctor_set(v_reuseFailAlloc_5336_, 1, v_a_5329_);
v___x_5332_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
size_t v___x_5333_; size_t v___x_5334_; 
v___x_5333_ = ((size_t)1ULL);
v___x_5334_ = lean_usize_add(v_i_5298_, v___x_5333_);
v_i_5298_ = v___x_5334_;
v_b_5299_ = v___x_5332_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5345_; 
lean_del_object(v___x_5314_);
lean_dec(v_snd_5312_);
v_a_5338_ = lean_ctor_get(v___x_5317_, 0);
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5340_ = v___x_5317_;
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_a_5338_);
lean_dec(v___x_5317_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5343_; 
if (v_isShared_5341_ == 0)
{
v___x_5343_ = v___x_5340_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_a_5338_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
return v___x_5343_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1___boxed(lean_object* v_init_5348_, lean_object* v_as_5349_, lean_object* v_sz_5350_, lean_object* v_i_5351_, lean_object* v_b_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_){
_start:
{
size_t v_sz_boxed_5363_; size_t v_i_boxed_5364_; lean_object* v_res_5365_; 
v_sz_boxed_5363_ = lean_unbox_usize(v_sz_5350_);
lean_dec(v_sz_5350_);
v_i_boxed_5364_ = lean_unbox_usize(v_i_5351_);
lean_dec(v_i_5351_);
v_res_5365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0_spec__1(v_init_5348_, v_as_5349_, v_sz_boxed_5363_, v_i_boxed_5364_, v_b_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_);
lean_dec(v___y_5361_);
lean_dec_ref(v___y_5360_);
lean_dec(v___y_5359_);
lean_dec_ref(v___y_5358_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec(v___y_5353_);
lean_dec_ref(v_as_5349_);
lean_dec_ref(v_init_5348_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0___boxed(lean_object* v_init_5366_, lean_object* v_n_5367_, lean_object* v_b_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_){
_start:
{
lean_object* v_res_5379_; 
v_res_5379_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5366_, v_n_5367_, v_b_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_dec(v___y_5375_);
lean_dec_ref(v___y_5374_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
lean_dec(v___y_5369_);
lean_dec_ref(v_n_5367_);
lean_dec_ref(v_init_5366_);
return v_res_5379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(lean_object* v_t_5380_, lean_object* v_init_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
lean_object* v_root_5392_; lean_object* v_tail_5393_; lean_object* v___x_5394_; 
v_root_5392_ = lean_ctor_get(v_t_5380_, 0);
v_tail_5393_ = lean_ctor_get(v_t_5380_, 1);
lean_inc_ref(v_init_5381_);
v___x_5394_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__0(v_init_5381_, v_root_5392_, v_init_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_);
lean_dec_ref(v_init_5381_);
if (lean_obj_tag(v___x_5394_) == 0)
{
lean_object* v_a_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5431_; 
v_a_5395_ = lean_ctor_get(v___x_5394_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5394_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5397_ = v___x_5394_;
v_isShared_5398_ = v_isSharedCheck_5431_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_a_5395_);
lean_dec(v___x_5394_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5431_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
if (lean_obj_tag(v_a_5395_) == 0)
{
lean_object* v_a_5399_; lean_object* v___x_5401_; 
v_a_5399_ = lean_ctor_get(v_a_5395_, 0);
lean_inc(v_a_5399_);
lean_dec_ref(v_a_5395_);
if (v_isShared_5398_ == 0)
{
lean_ctor_set(v___x_5397_, 0, v_a_5399_);
v___x_5401_ = v___x_5397_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5399_);
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
lean_object* v_a_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; size_t v_sz_5406_; size_t v___x_5407_; lean_object* v___x_5408_; 
lean_del_object(v___x_5397_);
v_a_5403_ = lean_ctor_get(v_a_5395_, 0);
lean_inc(v_a_5403_);
lean_dec_ref(v_a_5395_);
v___x_5404_ = lean_box(0);
v___x_5405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5405_, 0, v___x_5404_);
lean_ctor_set(v___x_5405_, 1, v_a_5403_);
v_sz_5406_ = lean_array_size(v_tail_5393_);
v___x_5407_ = ((size_t)0ULL);
v___x_5408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0_spec__1(v_tail_5393_, v_sz_5406_, v___x_5407_, v___x_5405_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_);
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_object* v_a_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5422_; 
v_a_5409_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5411_ = v___x_5408_;
v_isShared_5412_ = v_isSharedCheck_5422_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_a_5409_);
lean_dec(v___x_5408_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5422_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v_fst_5413_; 
v_fst_5413_ = lean_ctor_get(v_a_5409_, 0);
if (lean_obj_tag(v_fst_5413_) == 0)
{
lean_object* v_snd_5414_; lean_object* v___x_5416_; 
v_snd_5414_ = lean_ctor_get(v_a_5409_, 1);
lean_inc(v_snd_5414_);
lean_dec(v_a_5409_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 0, v_snd_5414_);
v___x_5416_ = v___x_5411_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v_snd_5414_);
v___x_5416_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
return v___x_5416_;
}
}
else
{
lean_object* v_val_5418_; lean_object* v___x_5420_; 
lean_inc_ref(v_fst_5413_);
lean_dec(v_a_5409_);
v_val_5418_ = lean_ctor_get(v_fst_5413_, 0);
lean_inc(v_val_5418_);
lean_dec_ref(v_fst_5413_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 0, v_val_5418_);
v___x_5420_ = v___x_5411_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_val_5418_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
else
{
lean_object* v_a_5423_; lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5430_; 
v_a_5423_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5430_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5430_ == 0)
{
v___x_5425_ = v___x_5408_;
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
else
{
lean_inc(v_a_5423_);
lean_dec(v___x_5408_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
lean_object* v___x_5428_; 
if (v_isShared_5426_ == 0)
{
v___x_5428_ = v___x_5425_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v_a_5423_);
v___x_5428_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
return v___x_5428_;
}
}
}
}
}
}
else
{
lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5439_; 
v_a_5432_ = lean_ctor_get(v___x_5394_, 0);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5394_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5434_ = v___x_5394_;
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5394_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5437_; 
if (v_isShared_5435_ == 0)
{
v___x_5437_ = v___x_5434_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_a_5432_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
return v___x_5437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0___boxed(lean_object* v_t_5440_, lean_object* v_init_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_){
_start:
{
lean_object* v_res_5452_; 
v_res_5452_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_t_5440_, v_init_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v_t_5440_);
return v_res_5452_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0(void){
_start:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
v___x_5453_ = lean_unsigned_to_nat(32u);
v___x_5454_ = lean_mk_empty_array_with_capacity(v___x_5453_);
v___x_5455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5455_, 0, v___x_5454_);
return v___x_5455_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1(void){
_start:
{
size_t v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v_result_5461_; 
v___x_5456_ = ((size_t)5ULL);
v___x_5457_ = lean_unsigned_to_nat(0u);
v___x_5458_ = lean_unsigned_to_nat(32u);
v___x_5459_ = lean_mk_empty_array_with_capacity(v___x_5458_);
v___x_5460_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__0);
v_result_5461_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_result_5461_, 0, v___x_5460_);
lean_ctor_set(v_result_5461_, 1, v___x_5459_);
lean_ctor_set(v_result_5461_, 2, v___x_5457_);
lean_ctor_set(v_result_5461_, 3, v___x_5457_);
lean_ctor_set_usize(v_result_5461_, 4, v___x_5456_);
return v_result_5461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(lean_object* v_thms_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_){
_start:
{
lean_object* v_result_5473_; lean_object* v___x_5474_; 
v_result_5473_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1, &l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___closed__1);
v___x_5474_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms_spec__0(v_thms_5462_, v_result_5473_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_);
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms___boxed(lean_object* v_thms_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_, lean_object* v_a_5482_, lean_object* v_a_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_){
_start:
{
lean_object* v_res_5486_; 
v_res_5486_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5475_, v_a_5476_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_, v_a_5481_, v_a_5482_, v_a_5483_, v_a_5484_);
lean_dec(v_a_5484_);
lean_dec_ref(v_a_5483_);
lean_dec(v_a_5482_);
lean_dec_ref(v_a_5481_);
lean_dec(v_a_5480_);
lean_dec_ref(v_a_5479_);
lean_dec(v_a_5478_);
lean_dec_ref(v_a_5477_);
lean_dec(v_a_5476_);
lean_dec_ref(v_thms_5475_);
return v_res_5486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(lean_object* v_thms_5489_, lean_object* v_newThms_5490_, lean_object* v_gmt_5491_, lean_object* v_numInstances_5492_, lean_object* v_numDelayedInstances_5493_, lean_object* v_num_5494_, lean_object* v_preInstances_5495_, lean_object* v_nextThmIdx_5496_, lean_object* v_matchEqNames_5497_, lean_object* v_delayedThmInsts_5498_, lean_object* v_nextDeclIdx_5499_, lean_object* v_enodeMap_5500_, lean_object* v_exprs_5501_, lean_object* v_parents_5502_, lean_object* v_congrTable_5503_, lean_object* v_appMap_5504_, lean_object* v_indicesFound_5505_, lean_object* v_newFacts_5506_, uint8_t v_inconsistent_5507_, lean_object* v_nextIdx_5508_, lean_object* v_newRawFacts_5509_, lean_object* v_facts_5510_, lean_object* v_extThms_5511_, lean_object* v_inj_5512_, lean_object* v_split_5513_, lean_object* v_clean_5514_, lean_object* v_sstates_5515_, lean_object* v_mvarId_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_){
_start:
{
lean_object* v___x_5527_; 
v___x_5527_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_thms_5489_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
if (lean_obj_tag(v___x_5527_) == 0)
{
lean_object* v_a_5528_; lean_object* v___x_5529_; 
v_a_5528_ = lean_ctor_get(v___x_5527_, 0);
lean_inc(v_a_5528_);
lean_dec_ref(v___x_5527_);
v___x_5529_ = l___private_Lean_Elab_Tactic_Grind_Param_0__Lean_Elab_Tactic_Grind_filterThms(v_newThms_5490_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
if (lean_obj_tag(v___x_5529_) == 0)
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5541_; 
v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5541_ == 0)
{
v___x_5532_ = v___x_5529_;
v_isShared_5533_ = v_isSharedCheck_5541_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5529_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5541_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5539_; 
v___x_5534_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___closed__0));
v___x_5535_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5535_, 0, v___x_5534_);
lean_ctor_set(v___x_5535_, 1, v_gmt_5491_);
lean_ctor_set(v___x_5535_, 2, v_a_5528_);
lean_ctor_set(v___x_5535_, 3, v_a_5530_);
lean_ctor_set(v___x_5535_, 4, v_numInstances_5492_);
lean_ctor_set(v___x_5535_, 5, v_numDelayedInstances_5493_);
lean_ctor_set(v___x_5535_, 6, v_num_5494_);
lean_ctor_set(v___x_5535_, 7, v_preInstances_5495_);
lean_ctor_set(v___x_5535_, 8, v_nextThmIdx_5496_);
lean_ctor_set(v___x_5535_, 9, v_matchEqNames_5497_);
lean_ctor_set(v___x_5535_, 10, v_delayedThmInsts_5498_);
v___x_5536_ = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(v___x_5536_, 0, v_nextDeclIdx_5499_);
lean_ctor_set(v___x_5536_, 1, v_enodeMap_5500_);
lean_ctor_set(v___x_5536_, 2, v_exprs_5501_);
lean_ctor_set(v___x_5536_, 3, v_parents_5502_);
lean_ctor_set(v___x_5536_, 4, v_congrTable_5503_);
lean_ctor_set(v___x_5536_, 5, v_appMap_5504_);
lean_ctor_set(v___x_5536_, 6, v_indicesFound_5505_);
lean_ctor_set(v___x_5536_, 7, v_newFacts_5506_);
lean_ctor_set(v___x_5536_, 8, v_nextIdx_5508_);
lean_ctor_set(v___x_5536_, 9, v_newRawFacts_5509_);
lean_ctor_set(v___x_5536_, 10, v_facts_5510_);
lean_ctor_set(v___x_5536_, 11, v_extThms_5511_);
lean_ctor_set(v___x_5536_, 12, v___x_5535_);
lean_ctor_set(v___x_5536_, 13, v_inj_5512_);
lean_ctor_set(v___x_5536_, 14, v_split_5513_);
lean_ctor_set(v___x_5536_, 15, v_clean_5514_);
lean_ctor_set(v___x_5536_, 16, v_sstates_5515_);
lean_ctor_set_uint8(v___x_5536_, sizeof(void*)*17, v_inconsistent_5507_);
v___x_5537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5536_);
lean_ctor_set(v___x_5537_, 1, v_mvarId_5516_);
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 0, v___x_5537_);
v___x_5539_ = v___x_5532_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v___x_5537_);
v___x_5539_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
return v___x_5539_;
}
}
}
else
{
lean_object* v_a_5542_; lean_object* v___x_5544_; uint8_t v_isShared_5545_; uint8_t v_isSharedCheck_5549_; 
lean_dec(v_a_5528_);
lean_dec(v_mvarId_5516_);
lean_dec_ref(v_sstates_5515_);
lean_dec_ref(v_clean_5514_);
lean_dec_ref(v_split_5513_);
lean_dec_ref(v_inj_5512_);
lean_dec_ref(v_extThms_5511_);
lean_dec_ref(v_facts_5510_);
lean_dec_ref(v_newRawFacts_5509_);
lean_dec(v_nextIdx_5508_);
lean_dec_ref(v_newFacts_5506_);
lean_dec_ref(v_indicesFound_5505_);
lean_dec_ref(v_appMap_5504_);
lean_dec_ref(v_congrTable_5503_);
lean_dec_ref(v_parents_5502_);
lean_dec_ref(v_exprs_5501_);
lean_dec_ref(v_enodeMap_5500_);
lean_dec(v_nextDeclIdx_5499_);
lean_dec_ref(v_delayedThmInsts_5498_);
lean_dec_ref(v_matchEqNames_5497_);
lean_dec(v_nextThmIdx_5496_);
lean_dec_ref(v_preInstances_5495_);
lean_dec(v_num_5494_);
lean_dec(v_numDelayedInstances_5493_);
lean_dec(v_numInstances_5492_);
lean_dec(v_gmt_5491_);
v_a_5542_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5549_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5549_ == 0)
{
v___x_5544_ = v___x_5529_;
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
else
{
lean_inc(v_a_5542_);
lean_dec(v___x_5529_);
v___x_5544_ = lean_box(0);
v_isShared_5545_ = v_isSharedCheck_5549_;
goto v_resetjp_5543_;
}
v_resetjp_5543_:
{
lean_object* v___x_5547_; 
if (v_isShared_5545_ == 0)
{
v___x_5547_ = v___x_5544_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v_a_5542_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
else
{
lean_object* v_a_5550_; lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5557_; 
lean_dec(v_mvarId_5516_);
lean_dec_ref(v_sstates_5515_);
lean_dec_ref(v_clean_5514_);
lean_dec_ref(v_split_5513_);
lean_dec_ref(v_inj_5512_);
lean_dec_ref(v_extThms_5511_);
lean_dec_ref(v_facts_5510_);
lean_dec_ref(v_newRawFacts_5509_);
lean_dec(v_nextIdx_5508_);
lean_dec_ref(v_newFacts_5506_);
lean_dec_ref(v_indicesFound_5505_);
lean_dec_ref(v_appMap_5504_);
lean_dec_ref(v_congrTable_5503_);
lean_dec_ref(v_parents_5502_);
lean_dec_ref(v_exprs_5501_);
lean_dec_ref(v_enodeMap_5500_);
lean_dec(v_nextDeclIdx_5499_);
lean_dec_ref(v_delayedThmInsts_5498_);
lean_dec_ref(v_matchEqNames_5497_);
lean_dec(v_nextThmIdx_5496_);
lean_dec_ref(v_preInstances_5495_);
lean_dec(v_num_5494_);
lean_dec(v_numDelayedInstances_5493_);
lean_dec(v_numInstances_5492_);
lean_dec(v_gmt_5491_);
v_a_5550_ = lean_ctor_get(v___x_5527_, 0);
v_isSharedCheck_5557_ = !lean_is_exclusive(v___x_5527_);
if (v_isSharedCheck_5557_ == 0)
{
v___x_5552_ = v___x_5527_;
v_isShared_5553_ = v_isSharedCheck_5557_;
goto v_resetjp_5551_;
}
else
{
lean_inc(v_a_5550_);
lean_dec(v___x_5527_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5557_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
lean_object* v___x_5555_; 
if (v_isShared_5553_ == 0)
{
v___x_5555_ = v___x_5552_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v_a_5550_);
v___x_5555_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
return v___x_5555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_thms_5558_ = _args[0];
lean_object* v_newThms_5559_ = _args[1];
lean_object* v_gmt_5560_ = _args[2];
lean_object* v_numInstances_5561_ = _args[3];
lean_object* v_numDelayedInstances_5562_ = _args[4];
lean_object* v_num_5563_ = _args[5];
lean_object* v_preInstances_5564_ = _args[6];
lean_object* v_nextThmIdx_5565_ = _args[7];
lean_object* v_matchEqNames_5566_ = _args[8];
lean_object* v_delayedThmInsts_5567_ = _args[9];
lean_object* v_nextDeclIdx_5568_ = _args[10];
lean_object* v_enodeMap_5569_ = _args[11];
lean_object* v_exprs_5570_ = _args[12];
lean_object* v_parents_5571_ = _args[13];
lean_object* v_congrTable_5572_ = _args[14];
lean_object* v_appMap_5573_ = _args[15];
lean_object* v_indicesFound_5574_ = _args[16];
lean_object* v_newFacts_5575_ = _args[17];
lean_object* v_inconsistent_5576_ = _args[18];
lean_object* v_nextIdx_5577_ = _args[19];
lean_object* v_newRawFacts_5578_ = _args[20];
lean_object* v_facts_5579_ = _args[21];
lean_object* v_extThms_5580_ = _args[22];
lean_object* v_inj_5581_ = _args[23];
lean_object* v_split_5582_ = _args[24];
lean_object* v_clean_5583_ = _args[25];
lean_object* v_sstates_5584_ = _args[26];
lean_object* v_mvarId_5585_ = _args[27];
lean_object* v___y_5586_ = _args[28];
lean_object* v___y_5587_ = _args[29];
lean_object* v___y_5588_ = _args[30];
lean_object* v___y_5589_ = _args[31];
lean_object* v___y_5590_ = _args[32];
lean_object* v___y_5591_ = _args[33];
lean_object* v___y_5592_ = _args[34];
lean_object* v___y_5593_ = _args[35];
lean_object* v___y_5594_ = _args[36];
lean_object* v___y_5595_ = _args[37];
_start:
{
uint8_t v_inconsistent_boxed_5596_; lean_object* v_res_5597_; 
v_inconsistent_boxed_5596_ = lean_unbox(v_inconsistent_5576_);
v_res_5597_ = l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0(v_thms_5558_, v_newThms_5559_, v_gmt_5560_, v_numInstances_5561_, v_numDelayedInstances_5562_, v_num_5563_, v_preInstances_5564_, v_nextThmIdx_5565_, v_matchEqNames_5566_, v_delayedThmInsts_5567_, v_nextDeclIdx_5568_, v_enodeMap_5569_, v_exprs_5570_, v_parents_5571_, v_congrTable_5572_, v_appMap_5573_, v_indicesFound_5574_, v_newFacts_5575_, v_inconsistent_boxed_5596_, v_nextIdx_5577_, v_newRawFacts_5578_, v_facts_5579_, v_extThms_5580_, v_inj_5581_, v_split_5582_, v_clean_5583_, v_sstates_5584_, v_mvarId_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
lean_dec(v___y_5592_);
lean_dec_ref(v___y_5591_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec(v___y_5588_);
lean_dec_ref(v___y_5587_);
lean_dec(v___y_5586_);
lean_dec_ref(v_newThms_5559_);
lean_dec_ref(v_thms_5558_);
return v_res_5597_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5598_; 
v___x_5598_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_5598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(size_t v_sz_5599_, size_t v_i_5600_, lean_object* v_bs_5601_){
_start:
{
uint8_t v___x_5602_; 
v___x_5602_ = lean_usize_dec_lt(v_i_5600_, v_sz_5599_);
if (v___x_5602_ == 0)
{
return v_bs_5601_;
}
else
{
lean_object* v_v_5603_; lean_object* v_casesTypes_5604_; lean_object* v_extThms_5605_; lean_object* v_funCC_5606_; lean_object* v_inj_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5621_; 
v_v_5603_ = lean_array_uget(v_bs_5601_, v_i_5600_);
v_casesTypes_5604_ = lean_ctor_get(v_v_5603_, 0);
v_extThms_5605_ = lean_ctor_get(v_v_5603_, 1);
v_funCC_5606_ = lean_ctor_get(v_v_5603_, 2);
v_inj_5607_ = lean_ctor_get(v_v_5603_, 4);
v_isSharedCheck_5621_ = !lean_is_exclusive(v_v_5603_);
if (v_isSharedCheck_5621_ == 0)
{
lean_object* v_unused_5622_; 
v_unused_5622_ = lean_ctor_get(v_v_5603_, 3);
lean_dec(v_unused_5622_);
v___x_5609_ = v_v_5603_;
v_isShared_5610_ = v_isSharedCheck_5621_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_inj_5607_);
lean_inc(v_funCC_5606_);
lean_inc(v_extThms_5605_);
lean_inc(v_casesTypes_5604_);
lean_dec(v_v_5603_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5621_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5611_; lean_object* v_bs_x27_5612_; lean_object* v___x_5613_; lean_object* v___x_5615_; 
v___x_5611_ = lean_unsigned_to_nat(0u);
v_bs_x27_5612_ = lean_array_uset(v_bs_5601_, v_i_5600_, v___x_5611_);
v___x_5613_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___closed__0);
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 3, v___x_5613_);
v___x_5615_ = v___x_5609_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_casesTypes_5604_);
lean_ctor_set(v_reuseFailAlloc_5620_, 1, v_extThms_5605_);
lean_ctor_set(v_reuseFailAlloc_5620_, 2, v_funCC_5606_);
lean_ctor_set(v_reuseFailAlloc_5620_, 3, v___x_5613_);
lean_ctor_set(v_reuseFailAlloc_5620_, 4, v_inj_5607_);
v___x_5615_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
size_t v___x_5616_; size_t v___x_5617_; lean_object* v___x_5618_; 
v___x_5616_ = ((size_t)1ULL);
v___x_5617_ = lean_usize_add(v_i_5600_, v___x_5616_);
v___x_5618_ = lean_array_uset(v_bs_x27_5612_, v_i_5600_, v___x_5615_);
v_i_5600_ = v___x_5617_;
v_bs_5601_ = v___x_5618_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0___boxed(lean_object* v_sz_5623_, lean_object* v_i_5624_, lean_object* v_bs_5625_){
_start:
{
size_t v_sz_boxed_5626_; size_t v_i_boxed_5627_; lean_object* v_res_5628_; 
v_sz_boxed_5626_ = lean_unbox_usize(v_sz_5623_);
lean_dec(v_sz_5623_);
v_i_boxed_5627_ = lean_unbox_usize(v_i_5624_);
lean_dec(v_i_5624_);
v_res_5628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_boxed_5626_, v_i_boxed_5627_, v_bs_5625_);
return v_res_5628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg(lean_object* v_params_5629_, lean_object* v_ps_5630_, uint8_t v_only_5631_, lean_object* v_k_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_){
_start:
{
lean_object* v___y_5643_; lean_object* v___y_5644_; lean_object* v___y_5645_; lean_object* v___y_5646_; lean_object* v___y_5647_; lean_object* v___y_5648_; lean_object* v___y_5649_; lean_object* v___y_5650_; lean_object* v___y_5651_; uint8_t v___y_5664_; uint8_t v___y_5665_; lean_object* v_params_5666_; lean_object* v___y_5667_; lean_object* v___y_5668_; lean_object* v___y_5669_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v___y_5672_; lean_object* v___y_5673_; lean_object* v___y_5674_; uint8_t v___y_5775_; 
if (v_only_5631_ == 0)
{
lean_object* v___x_5797_; lean_object* v___x_5798_; uint8_t v___x_5799_; 
v___x_5797_ = lean_array_get_size(v_ps_5630_);
v___x_5798_ = lean_unsigned_to_nat(0u);
v___x_5799_ = lean_nat_dec_eq(v___x_5797_, v___x_5798_);
if (v___x_5799_ == 0)
{
v___y_5775_ = v___x_5799_;
goto v___jp_5774_;
}
else
{
lean_object* v___x_5800_; 
lean_dec_ref(v_params_5629_);
lean_inc(v_a_5640_);
lean_inc_ref(v_a_5639_);
lean_inc(v_a_5638_);
lean_inc_ref(v_a_5637_);
lean_inc(v_a_5636_);
lean_inc_ref(v_a_5635_);
lean_inc(v_a_5634_);
lean_inc_ref(v_a_5633_);
v___x_5800_ = lean_apply_9(v_k_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_, v_a_5640_, lean_box(0));
return v___x_5800_;
}
}
else
{
uint8_t v___x_5801_; 
v___x_5801_ = 0;
v___y_5775_ = v___x_5801_;
goto v___jp_5774_;
}
v___jp_5642_:
{
lean_object* v___x_5652_; lean_object* v___x_5653_; 
v___x_5652_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertExtra___boxed), 12, 1);
lean_closure_set(v___x_5652_, 0, v___y_5643_);
v___x_5653_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(v___x_5652_, v___y_5644_, v___y_5645_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v___x_5654_; 
lean_dec_ref(v___x_5653_);
lean_inc(v___y_5651_);
lean_inc_ref(v___y_5650_);
lean_inc(v___y_5649_);
lean_inc_ref(v___y_5648_);
lean_inc(v___y_5647_);
lean_inc_ref(v___y_5646_);
lean_inc(v___y_5645_);
v___x_5654_ = lean_apply_9(v_k_5632_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_, lean_box(0));
return v___x_5654_;
}
else
{
lean_object* v_a_5655_; lean_object* v___x_5657_; uint8_t v_isShared_5658_; uint8_t v_isSharedCheck_5662_; 
lean_dec_ref(v___y_5644_);
lean_dec_ref(v_k_5632_);
v_a_5655_ = lean_ctor_get(v___x_5653_, 0);
v_isSharedCheck_5662_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5662_ == 0)
{
v___x_5657_ = v___x_5653_;
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
else
{
lean_inc(v_a_5655_);
lean_dec(v___x_5653_);
v___x_5657_ = lean_box(0);
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
v_resetjp_5656_:
{
lean_object* v___x_5660_; 
if (v_isShared_5658_ == 0)
{
v___x_5660_ = v___x_5657_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v_a_5655_);
v___x_5660_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
return v___x_5660_;
}
}
}
}
v___jp_5663_:
{
lean_object* v___x_5675_; 
v___x_5675_ = l_Lean_Elab_Tactic_elabGrindParams(v_params_5666_, v_ps_5630_, v_only_5631_, v___y_5664_, v___y_5665_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
if (lean_obj_tag(v___x_5675_) == 0)
{
lean_object* v_a_5676_; lean_object* v_ctx_5677_; lean_object* v_anchorRefs_x3f_5678_; lean_object* v_toContext_5679_; lean_object* v_sctx_5680_; lean_object* v_methods_5681_; uint8_t v_sym_5682_; lean_object* v_simp_5683_; lean_object* v_simpMethods_5684_; lean_object* v_config_5685_; uint8_t v_cheapCases_5686_; uint8_t v_reportMVarIssue_5687_; lean_object* v_splitSource_5688_; lean_object* v_ematchDiagSource_5689_; lean_object* v_symPrios_5690_; lean_object* v_extensions_5691_; uint8_t v_debug_5692_; uint8_t v_ematchDiag_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; 
v_a_5676_ = lean_ctor_get(v___x_5675_, 0);
lean_inc_n(v_a_5676_, 2);
lean_dec_ref(v___x_5675_);
v_ctx_5677_ = lean_ctor_get(v___y_5667_, 1);
v_anchorRefs_x3f_5678_ = lean_ctor_get(v_a_5676_, 8);
v_toContext_5679_ = lean_ctor_get(v___y_5667_, 0);
v_sctx_5680_ = lean_ctor_get(v___y_5667_, 2);
v_methods_5681_ = lean_ctor_get(v___y_5667_, 3);
v_sym_5682_ = lean_ctor_get_uint8(v___y_5667_, sizeof(void*)*5);
v_simp_5683_ = lean_ctor_get(v_ctx_5677_, 0);
v_simpMethods_5684_ = lean_ctor_get(v_ctx_5677_, 1);
v_config_5685_ = lean_ctor_get(v_ctx_5677_, 2);
v_cheapCases_5686_ = lean_ctor_get_uint8(v_ctx_5677_, sizeof(void*)*8);
v_reportMVarIssue_5687_ = lean_ctor_get_uint8(v_ctx_5677_, sizeof(void*)*8 + 1);
v_splitSource_5688_ = lean_ctor_get(v_ctx_5677_, 4);
v_ematchDiagSource_5689_ = lean_ctor_get(v_ctx_5677_, 5);
v_symPrios_5690_ = lean_ctor_get(v_ctx_5677_, 6);
v_extensions_5691_ = lean_ctor_get(v_ctx_5677_, 7);
v_debug_5692_ = lean_ctor_get_uint8(v_ctx_5677_, sizeof(void*)*8 + 2);
v_ematchDiag_5693_ = lean_ctor_get_uint8(v_ctx_5677_, sizeof(void*)*8 + 3);
lean_inc_ref(v_extensions_5691_);
lean_inc_ref(v_symPrios_5690_);
lean_inc(v_ematchDiagSource_5689_);
lean_inc(v_splitSource_5688_);
lean_inc(v_anchorRefs_x3f_5678_);
lean_inc_ref(v_config_5685_);
lean_inc_ref(v_simpMethods_5684_);
lean_inc_ref(v_simp_5683_);
v___x_5694_ = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(v___x_5694_, 0, v_simp_5683_);
lean_ctor_set(v___x_5694_, 1, v_simpMethods_5684_);
lean_ctor_set(v___x_5694_, 2, v_config_5685_);
lean_ctor_set(v___x_5694_, 3, v_anchorRefs_x3f_5678_);
lean_ctor_set(v___x_5694_, 4, v_splitSource_5688_);
lean_ctor_set(v___x_5694_, 5, v_ematchDiagSource_5689_);
lean_ctor_set(v___x_5694_, 6, v_symPrios_5690_);
lean_ctor_set(v___x_5694_, 7, v_extensions_5691_);
lean_ctor_set_uint8(v___x_5694_, sizeof(void*)*8, v_cheapCases_5686_);
lean_ctor_set_uint8(v___x_5694_, sizeof(void*)*8 + 1, v_reportMVarIssue_5687_);
lean_ctor_set_uint8(v___x_5694_, sizeof(void*)*8 + 2, v_debug_5692_);
lean_ctor_set_uint8(v___x_5694_, sizeof(void*)*8 + 3, v_ematchDiag_5693_);
lean_inc_ref(v_methods_5681_);
lean_inc_ref(v_sctx_5680_);
lean_inc_ref(v_toContext_5679_);
v___x_5695_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_5695_, 0, v_toContext_5679_);
lean_ctor_set(v___x_5695_, 1, v___x_5694_);
lean_ctor_set(v___x_5695_, 2, v_sctx_5680_);
lean_ctor_set(v___x_5695_, 3, v_methods_5681_);
lean_ctor_set(v___x_5695_, 4, v_a_5676_);
lean_ctor_set_uint8(v___x_5695_, sizeof(void*)*5, v_sym_5682_);
if (v_only_5631_ == 0)
{
v___y_5643_ = v_a_5676_;
v___y_5644_ = v___x_5695_;
v___y_5645_ = v___y_5668_;
v___y_5646_ = v___y_5669_;
v___y_5647_ = v___y_5670_;
v___y_5648_ = v___y_5671_;
v___y_5649_ = v___y_5672_;
v___y_5650_ = v___y_5673_;
v___y_5651_ = v___y_5674_;
goto v___jp_5642_;
}
else
{
lean_object* v___x_5696_; 
v___x_5696_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_5668_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
if (lean_obj_tag(v___x_5696_) == 0)
{
lean_object* v_a_5697_; lean_object* v_toGoalState_5698_; lean_object* v_ematch_5699_; lean_object* v_mvarId_5700_; lean_object* v___x_5702_; uint8_t v_isShared_5703_; uint8_t v_isSharedCheck_5756_; 
v_a_5697_ = lean_ctor_get(v___x_5696_, 0);
lean_inc(v_a_5697_);
lean_dec_ref(v___x_5696_);
v_toGoalState_5698_ = lean_ctor_get(v_a_5697_, 0);
lean_inc_ref(v_toGoalState_5698_);
v_ematch_5699_ = lean_ctor_get(v_toGoalState_5698_, 12);
lean_inc_ref(v_ematch_5699_);
v_mvarId_5700_ = lean_ctor_get(v_a_5697_, 1);
v_isSharedCheck_5756_ = !lean_is_exclusive(v_a_5697_);
if (v_isSharedCheck_5756_ == 0)
{
lean_object* v_unused_5757_; 
v_unused_5757_ = lean_ctor_get(v_a_5697_, 0);
lean_dec(v_unused_5757_);
v___x_5702_ = v_a_5697_;
v_isShared_5703_ = v_isSharedCheck_5756_;
goto v_resetjp_5701_;
}
else
{
lean_inc(v_mvarId_5700_);
lean_dec(v_a_5697_);
v___x_5702_ = lean_box(0);
v_isShared_5703_ = v_isSharedCheck_5756_;
goto v_resetjp_5701_;
}
v_resetjp_5701_:
{
lean_object* v_nextDeclIdx_5704_; lean_object* v_enodeMap_5705_; lean_object* v_exprs_5706_; lean_object* v_parents_5707_; lean_object* v_congrTable_5708_; lean_object* v_appMap_5709_; lean_object* v_indicesFound_5710_; lean_object* v_newFacts_5711_; uint8_t v_inconsistent_5712_; lean_object* v_nextIdx_5713_; lean_object* v_newRawFacts_5714_; lean_object* v_facts_5715_; lean_object* v_extThms_5716_; lean_object* v_inj_5717_; lean_object* v_split_5718_; lean_object* v_clean_5719_; lean_object* v_sstates_5720_; lean_object* v_gmt_5721_; lean_object* v_thms_5722_; lean_object* v_newThms_5723_; lean_object* v_numInstances_5724_; lean_object* v_numDelayedInstances_5725_; lean_object* v_num_5726_; lean_object* v_preInstances_5727_; lean_object* v_nextThmIdx_5728_; lean_object* v_matchEqNames_5729_; lean_object* v_delayedThmInsts_5730_; lean_object* v___x_5731_; lean_object* v___f_5732_; lean_object* v___x_5733_; 
v_nextDeclIdx_5704_ = lean_ctor_get(v_toGoalState_5698_, 0);
lean_inc(v_nextDeclIdx_5704_);
v_enodeMap_5705_ = lean_ctor_get(v_toGoalState_5698_, 1);
lean_inc_ref(v_enodeMap_5705_);
v_exprs_5706_ = lean_ctor_get(v_toGoalState_5698_, 2);
lean_inc_ref(v_exprs_5706_);
v_parents_5707_ = lean_ctor_get(v_toGoalState_5698_, 3);
lean_inc_ref(v_parents_5707_);
v_congrTable_5708_ = lean_ctor_get(v_toGoalState_5698_, 4);
lean_inc_ref(v_congrTable_5708_);
v_appMap_5709_ = lean_ctor_get(v_toGoalState_5698_, 5);
lean_inc_ref(v_appMap_5709_);
v_indicesFound_5710_ = lean_ctor_get(v_toGoalState_5698_, 6);
lean_inc_ref(v_indicesFound_5710_);
v_newFacts_5711_ = lean_ctor_get(v_toGoalState_5698_, 7);
lean_inc_ref(v_newFacts_5711_);
v_inconsistent_5712_ = lean_ctor_get_uint8(v_toGoalState_5698_, sizeof(void*)*17);
v_nextIdx_5713_ = lean_ctor_get(v_toGoalState_5698_, 8);
lean_inc(v_nextIdx_5713_);
v_newRawFacts_5714_ = lean_ctor_get(v_toGoalState_5698_, 9);
lean_inc_ref(v_newRawFacts_5714_);
v_facts_5715_ = lean_ctor_get(v_toGoalState_5698_, 10);
lean_inc_ref(v_facts_5715_);
v_extThms_5716_ = lean_ctor_get(v_toGoalState_5698_, 11);
lean_inc_ref(v_extThms_5716_);
v_inj_5717_ = lean_ctor_get(v_toGoalState_5698_, 13);
lean_inc_ref(v_inj_5717_);
v_split_5718_ = lean_ctor_get(v_toGoalState_5698_, 14);
lean_inc_ref(v_split_5718_);
v_clean_5719_ = lean_ctor_get(v_toGoalState_5698_, 15);
lean_inc_ref(v_clean_5719_);
v_sstates_5720_ = lean_ctor_get(v_toGoalState_5698_, 16);
lean_inc_ref(v_sstates_5720_);
lean_dec_ref(v_toGoalState_5698_);
v_gmt_5721_ = lean_ctor_get(v_ematch_5699_, 1);
lean_inc(v_gmt_5721_);
v_thms_5722_ = lean_ctor_get(v_ematch_5699_, 2);
lean_inc_ref(v_thms_5722_);
v_newThms_5723_ = lean_ctor_get(v_ematch_5699_, 3);
lean_inc_ref(v_newThms_5723_);
v_numInstances_5724_ = lean_ctor_get(v_ematch_5699_, 4);
lean_inc(v_numInstances_5724_);
v_numDelayedInstances_5725_ = lean_ctor_get(v_ematch_5699_, 5);
lean_inc(v_numDelayedInstances_5725_);
v_num_5726_ = lean_ctor_get(v_ematch_5699_, 6);
lean_inc(v_num_5726_);
v_preInstances_5727_ = lean_ctor_get(v_ematch_5699_, 7);
lean_inc_ref(v_preInstances_5727_);
v_nextThmIdx_5728_ = lean_ctor_get(v_ematch_5699_, 8);
lean_inc(v_nextThmIdx_5728_);
v_matchEqNames_5729_ = lean_ctor_get(v_ematch_5699_, 9);
lean_inc_ref(v_matchEqNames_5729_);
v_delayedThmInsts_5730_ = lean_ctor_get(v_ematch_5699_, 10);
lean_inc_ref(v_delayedThmInsts_5730_);
lean_dec_ref(v_ematch_5699_);
v___x_5731_ = lean_box(v_inconsistent_5712_);
v___f_5732_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withParams___redArg___lam__0___boxed), 38, 28);
lean_closure_set(v___f_5732_, 0, v_thms_5722_);
lean_closure_set(v___f_5732_, 1, v_newThms_5723_);
lean_closure_set(v___f_5732_, 2, v_gmt_5721_);
lean_closure_set(v___f_5732_, 3, v_numInstances_5724_);
lean_closure_set(v___f_5732_, 4, v_numDelayedInstances_5725_);
lean_closure_set(v___f_5732_, 5, v_num_5726_);
lean_closure_set(v___f_5732_, 6, v_preInstances_5727_);
lean_closure_set(v___f_5732_, 7, v_nextThmIdx_5728_);
lean_closure_set(v___f_5732_, 8, v_matchEqNames_5729_);
lean_closure_set(v___f_5732_, 9, v_delayedThmInsts_5730_);
lean_closure_set(v___f_5732_, 10, v_nextDeclIdx_5704_);
lean_closure_set(v___f_5732_, 11, v_enodeMap_5705_);
lean_closure_set(v___f_5732_, 12, v_exprs_5706_);
lean_closure_set(v___f_5732_, 13, v_parents_5707_);
lean_closure_set(v___f_5732_, 14, v_congrTable_5708_);
lean_closure_set(v___f_5732_, 15, v_appMap_5709_);
lean_closure_set(v___f_5732_, 16, v_indicesFound_5710_);
lean_closure_set(v___f_5732_, 17, v_newFacts_5711_);
lean_closure_set(v___f_5732_, 18, v___x_5731_);
lean_closure_set(v___f_5732_, 19, v_nextIdx_5713_);
lean_closure_set(v___f_5732_, 20, v_newRawFacts_5714_);
lean_closure_set(v___f_5732_, 21, v_facts_5715_);
lean_closure_set(v___f_5732_, 22, v_extThms_5716_);
lean_closure_set(v___f_5732_, 23, v_inj_5717_);
lean_closure_set(v___f_5732_, 24, v_split_5718_);
lean_closure_set(v___f_5732_, 25, v_clean_5719_);
lean_closure_set(v___f_5732_, 26, v_sstates_5720_);
lean_closure_set(v___f_5732_, 27, v_mvarId_5700_);
v___x_5733_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_5732_, v___x_5695_, v___y_5668_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
if (lean_obj_tag(v___x_5733_) == 0)
{
lean_object* v_a_5734_; lean_object* v___x_5735_; lean_object* v___x_5737_; 
v_a_5734_ = lean_ctor_get(v___x_5733_, 0);
lean_inc(v_a_5734_);
lean_dec_ref(v___x_5733_);
v___x_5735_ = lean_box(0);
if (v_isShared_5703_ == 0)
{
lean_ctor_set_tag(v___x_5702_, 1);
lean_ctor_set(v___x_5702_, 1, v___x_5735_);
lean_ctor_set(v___x_5702_, 0, v_a_5734_);
v___x_5737_ = v___x_5702_;
goto v_reusejp_5736_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v_a_5734_);
lean_ctor_set(v_reuseFailAlloc_5747_, 1, v___x_5735_);
v___x_5737_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5736_;
}
v_reusejp_5736_:
{
lean_object* v___x_5738_; 
v___x_5738_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_5737_, v___y_5668_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
if (lean_obj_tag(v___x_5738_) == 0)
{
lean_dec_ref(v___x_5738_);
v___y_5643_ = v_a_5676_;
v___y_5644_ = v___x_5695_;
v___y_5645_ = v___y_5668_;
v___y_5646_ = v___y_5669_;
v___y_5647_ = v___y_5670_;
v___y_5648_ = v___y_5671_;
v___y_5649_ = v___y_5672_;
v___y_5650_ = v___y_5673_;
v___y_5651_ = v___y_5674_;
goto v___jp_5642_;
}
else
{
lean_object* v_a_5739_; lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5746_; 
lean_dec_ref(v___x_5695_);
lean_dec(v_a_5676_);
lean_dec_ref(v_k_5632_);
v_a_5739_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5746_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5746_ == 0)
{
v___x_5741_ = v___x_5738_;
v_isShared_5742_ = v_isSharedCheck_5746_;
goto v_resetjp_5740_;
}
else
{
lean_inc(v_a_5739_);
lean_dec(v___x_5738_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5746_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
lean_object* v___x_5744_; 
if (v_isShared_5742_ == 0)
{
v___x_5744_ = v___x_5741_;
goto v_reusejp_5743_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_a_5739_);
v___x_5744_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5743_;
}
v_reusejp_5743_:
{
return v___x_5744_;
}
}
}
}
}
else
{
lean_object* v_a_5748_; lean_object* v___x_5750_; uint8_t v_isShared_5751_; uint8_t v_isSharedCheck_5755_; 
lean_del_object(v___x_5702_);
lean_dec_ref(v___x_5695_);
lean_dec(v_a_5676_);
lean_dec_ref(v_k_5632_);
v_a_5748_ = lean_ctor_get(v___x_5733_, 0);
v_isSharedCheck_5755_ = !lean_is_exclusive(v___x_5733_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5750_ = v___x_5733_;
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
else
{
lean_inc(v_a_5748_);
lean_dec(v___x_5733_);
v___x_5750_ = lean_box(0);
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
v_resetjp_5749_:
{
lean_object* v___x_5753_; 
if (v_isShared_5751_ == 0)
{
v___x_5753_ = v___x_5750_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_a_5748_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
}
else
{
lean_object* v_a_5758_; lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5765_; 
lean_dec_ref(v___x_5695_);
lean_dec(v_a_5676_);
lean_dec_ref(v_k_5632_);
v_a_5758_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_5765_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5765_ == 0)
{
v___x_5760_ = v___x_5696_;
v_isShared_5761_ = v_isSharedCheck_5765_;
goto v_resetjp_5759_;
}
else
{
lean_inc(v_a_5758_);
lean_dec(v___x_5696_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5765_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v___x_5763_; 
if (v_isShared_5761_ == 0)
{
v___x_5763_ = v___x_5760_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5764_; 
v_reuseFailAlloc_5764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5764_, 0, v_a_5758_);
v___x_5763_ = v_reuseFailAlloc_5764_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
return v___x_5763_;
}
}
}
}
}
else
{
lean_object* v_a_5766_; lean_object* v___x_5768_; uint8_t v_isShared_5769_; uint8_t v_isSharedCheck_5773_; 
lean_dec_ref(v_k_5632_);
v_a_5766_ = lean_ctor_get(v___x_5675_, 0);
v_isSharedCheck_5773_ = !lean_is_exclusive(v___x_5675_);
if (v_isSharedCheck_5773_ == 0)
{
v___x_5768_ = v___x_5675_;
v_isShared_5769_ = v_isSharedCheck_5773_;
goto v_resetjp_5767_;
}
else
{
lean_inc(v_a_5766_);
lean_dec(v___x_5675_);
v___x_5768_ = lean_box(0);
v_isShared_5769_ = v_isSharedCheck_5773_;
goto v_resetjp_5767_;
}
v_resetjp_5767_:
{
lean_object* v___x_5771_; 
if (v_isShared_5769_ == 0)
{
v___x_5771_ = v___x_5768_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_a_5766_);
v___x_5771_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
return v___x_5771_;
}
}
}
}
v___jp_5774_:
{
uint8_t v___x_5776_; 
v___x_5776_ = 1;
if (v_only_5631_ == 0)
{
v___y_5664_ = v___y_5775_;
v___y_5665_ = v___x_5776_;
v_params_5666_ = v_params_5629_;
v___y_5667_ = v_a_5633_;
v___y_5668_ = v_a_5634_;
v___y_5669_ = v_a_5635_;
v___y_5670_ = v_a_5636_;
v___y_5671_ = v_a_5637_;
v___y_5672_ = v_a_5638_;
v___y_5673_ = v_a_5639_;
v___y_5674_ = v_a_5640_;
goto v___jp_5663_;
}
else
{
lean_object* v_config_5777_; lean_object* v_extensions_5778_; lean_object* v_extra_5779_; lean_object* v_extraInj_5780_; lean_object* v_extraFacts_5781_; lean_object* v_symPrios_5782_; lean_object* v_norm_5783_; lean_object* v_normProcs_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5795_; 
v_config_5777_ = lean_ctor_get(v_params_5629_, 0);
v_extensions_5778_ = lean_ctor_get(v_params_5629_, 1);
v_extra_5779_ = lean_ctor_get(v_params_5629_, 2);
v_extraInj_5780_ = lean_ctor_get(v_params_5629_, 3);
v_extraFacts_5781_ = lean_ctor_get(v_params_5629_, 4);
v_symPrios_5782_ = lean_ctor_get(v_params_5629_, 5);
v_norm_5783_ = lean_ctor_get(v_params_5629_, 6);
v_normProcs_5784_ = lean_ctor_get(v_params_5629_, 7);
v_isSharedCheck_5795_ = !lean_is_exclusive(v_params_5629_);
if (v_isSharedCheck_5795_ == 0)
{
lean_object* v_unused_5796_; 
v_unused_5796_ = lean_ctor_get(v_params_5629_, 8);
lean_dec(v_unused_5796_);
v___x_5786_ = v_params_5629_;
v_isShared_5787_ = v_isSharedCheck_5795_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_normProcs_5784_);
lean_inc(v_norm_5783_);
lean_inc(v_symPrios_5782_);
lean_inc(v_extraFacts_5781_);
lean_inc(v_extraInj_5780_);
lean_inc(v_extra_5779_);
lean_inc(v_extensions_5778_);
lean_inc(v_config_5777_);
lean_dec(v_params_5629_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5795_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
size_t v_sz_5788_; size_t v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v_params_5793_; 
v_sz_5788_ = lean_array_size(v_extensions_5778_);
v___x_5789_ = ((size_t)0ULL);
v___x_5790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Grind_withParams_spec__0(v_sz_5788_, v___x_5789_, v_extensions_5778_);
v___x_5791_ = lean_box(0);
if (v_isShared_5787_ == 0)
{
lean_ctor_set(v___x_5786_, 8, v___x_5791_);
lean_ctor_set(v___x_5786_, 1, v___x_5790_);
v_params_5793_ = v___x_5786_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_config_5777_);
lean_ctor_set(v_reuseFailAlloc_5794_, 1, v___x_5790_);
lean_ctor_set(v_reuseFailAlloc_5794_, 2, v_extra_5779_);
lean_ctor_set(v_reuseFailAlloc_5794_, 3, v_extraInj_5780_);
lean_ctor_set(v_reuseFailAlloc_5794_, 4, v_extraFacts_5781_);
lean_ctor_set(v_reuseFailAlloc_5794_, 5, v_symPrios_5782_);
lean_ctor_set(v_reuseFailAlloc_5794_, 6, v_norm_5783_);
lean_ctor_set(v_reuseFailAlloc_5794_, 7, v_normProcs_5784_);
lean_ctor_set(v_reuseFailAlloc_5794_, 8, v___x_5791_);
v_params_5793_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
v___y_5664_ = v___y_5775_;
v___y_5665_ = v___x_5776_;
v_params_5666_ = v_params_5793_;
v___y_5667_ = v_a_5633_;
v___y_5668_ = v_a_5634_;
v___y_5669_ = v_a_5635_;
v___y_5670_ = v_a_5636_;
v___y_5671_ = v_a_5637_;
v___y_5672_ = v_a_5638_;
v___y_5673_ = v_a_5639_;
v___y_5674_ = v_a_5640_;
goto v___jp_5663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___redArg___boxed(lean_object* v_params_5802_, lean_object* v_ps_5803_, lean_object* v_only_5804_, lean_object* v_k_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_){
_start:
{
uint8_t v_only_boxed_5815_; lean_object* v_res_5816_; 
v_only_boxed_5815_ = lean_unbox(v_only_5804_);
v_res_5816_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5802_, v_ps_5803_, v_only_boxed_5815_, v_k_5805_, v_a_5806_, v_a_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_);
lean_dec(v_a_5813_);
lean_dec_ref(v_a_5812_);
lean_dec(v_a_5811_);
lean_dec_ref(v_a_5810_);
lean_dec(v_a_5809_);
lean_dec_ref(v_a_5808_);
lean_dec(v_a_5807_);
lean_dec_ref(v_a_5806_);
lean_dec_ref(v_ps_5803_);
return v_res_5816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams(lean_object* v_00_u03b1_5817_, lean_object* v_params_5818_, lean_object* v_ps_5819_, uint8_t v_only_5820_, lean_object* v_k_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_, lean_object* v_a_5826_, lean_object* v_a_5827_, lean_object* v_a_5828_, lean_object* v_a_5829_){
_start:
{
lean_object* v___x_5831_; 
v___x_5831_ = l_Lean_Elab_Tactic_Grind_withParams___redArg(v_params_5818_, v_ps_5819_, v_only_5820_, v_k_5821_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_);
return v___x_5831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_withParams___boxed(lean_object* v_00_u03b1_5832_, lean_object* v_params_5833_, lean_object* v_ps_5834_, lean_object* v_only_5835_, lean_object* v_k_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_){
_start:
{
uint8_t v_only_boxed_5846_; lean_object* v_res_5847_; 
v_only_boxed_5846_ = lean_unbox(v_only_5835_);
v_res_5847_ = l_Lean_Elab_Tactic_Grind_withParams(v_00_u03b1_5832_, v_params_5833_, v_ps_5834_, v_only_boxed_5846_, v_k_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_, v_a_5844_);
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
